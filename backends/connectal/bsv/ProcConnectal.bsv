
// Copyright (c) 2016, 2017 Massachusetts Institute of Technology

// Permission is hereby granted, free of charge, to any person
// obtaining a copy of this software and associated documentation
// files (the "Software"), to deal in the Software without
// restriction, including without limitation the rights to use, copy,
// modify, merge, publish, distribute, sublicense, and/or sell copies
// of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:

// The above copyright notice and this permission notice shall be
// included in all copies or substantial portions of the Software.

// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
// EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
// MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
// NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
// BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
// ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
// CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.

`include "ProcConfig.bsv"

// ProcConnectal.bsv
// This is a wrapper to translate the generic Proc interface to an interface
// that is accepted by connectal.

import ConnectalConfig::*;

`ifdef CONFIG_ACCELERATOR
import Portal::*;
import AccelTop::*;
`ifdef CONFIG_STR_LEN_PINS
import StrLen::*;
`endif
`endif
`ifdef SIMULATION
import RS232::*;
`endif

import FIFOG::*;
import MemUtil::*;

// This assumes a Proc.bsv file that contains the mkProc definition
import Abstraction::*;
import BuildVector::*;
import ClientServer::*;
import Clocks::*;
import Connectable::*;
import FIFO::*;
import GetPut::*;
import Port::*;
import Proc::*;
import Vector::*;
import VerificationPacket::*;
import VerificationPacketFilter::*;
import MemTypes::*;
import ProcPins::*;
import RVTypes::*;
import SharedMemoryBridge::*;
import PerfMonitorConnectal::*;

// ProcControl
interface ProcControlRequest;
    method Action reset;
    method Action start(Bit#(64) startPc, Bit#(64) verificationPacketsToIgnore, Bool sendSynchronizationPackets);
    method Action stop;
endinterface
interface ProcControlIndication;
    method Action resetDone;
endinterface
// Platform
interface PlatformRequest;
    method Action configure(Bit#(32) ramSharedMemRefPointer, Bit#(64) ramSize);
    method Action memRequest(Bool write, Bit#(64) addr, Bit#(64) data);
endinterface
interface PlatformIndication;
    method Action memResponse(Bool write, Bit#(64) data);
endinterface
// Verification
interface VerificationIndication;
    method Action getVerificationPacket(VerificationPacket packet);
endinterface

// UART
interface UartBridgeRequest;
  method Action put (Bit#(8) data);
  method Action setDivisor(Bit#(16) divisor);
endinterface
interface UartBridgeIndication;
  method Action get(Bit#(8) data);
  method Action setDivisorDone;
endinterface
// PerfMonitor interfaces defined in PerfMonitor package
// ExternalMMIO
interface ExternalMMIOResponse;
    method Action response(Bool write, Bit#(64) data);
    method Action triggerExternalInterrupt;
endinterface
interface ExternalMMIORequest;
    method Action request(Bool write, Bit#(64) addr, Bit#(64) data);
endinterface

// This is the interface of all the requests, the indications are passed in as
// parameters to the mkProcConnectal module.
interface ProcConnectal;
    interface ProcControlRequest procControlRequest;
    interface PlatformRequest platformRequest;
    interface PerfMonitorRequest perfMonitorRequest;
    interface UartBridgeRequest uartBridgeRequest;
    interface ExternalMMIOResponse externalMMIOResponse;
    interface Vector#(1, MemReadClient#(DataBusWidth)) dmaReadClient;
    interface Vector#(1, MemWriteClient#(DataBusWidth)) dmaWriteClient;
    (* prefix = "" *)
    interface ProcPins pins;
endinterface

typedef enum { Accel, Ext } ExtMemUser deriving (Bits, Eq, FShow);

module [Module] mkProcConnectal#(ProcControlIndication procControlIndication,
                                 PlatformIndication platformIndication,
                                 VerificationIndication verificationIndication,
                                 PerfMonitorIndication perfMonitorIndication,
                                 UartBridgeIndication uartBridgeIndication,
                                 ExternalMMIORequest externalMMIORequest)
                                (ProcConnectal);
    Bool verbose = False;
    let clock <- exposeCurrentClock;
    let reset <- exposeCurrentReset;
    let procReset <- mkReset(10, True, clock);
    Reg#(Bool) resetSent <- mkReg(False);

    Proc#(MainMemoryWidth) proc <- mkProc(reset_by procReset.new_rst);

    // Address space: 0 - ramSz
    SharedMemoryBridge#(XLEN, TLog#(TDiv#(XLEN,8))) ramSharedMemoryBridge <- mkSharedMemoryBridge;
    let ramToSharedMem <- mkConnection(proc.ram, ramSharedMemoryBridge.to_proc);

    FIFOG#(CoarseMemReq#(XLEN, TLog#(TDiv#(XLEN,8)))) extMemReqFIFO <- mkFIFOG;
    FIFOG#(CoarseMemResp#(TLog#(TDiv#(XLEN,8)))) extMemRespFIFO <- mkFIFOG;
    FIFO#(ExtMemUser) extMemUserFIFO <- mkFIFO;

    FIFO#(VerificationPacket) verificationPacketFIFO <- mkFIFO;
    VerificationPacketFilter verificationPacketFilter <- mkVerificationPacketFilter(toGet(verificationPacketFIFO).get);

    rule getVerificationPackets(proc.currVerificationPacket matches tagged Valid .packet);
        verificationPacketFIFO.enq(packet);
    endrule
    rule stallProcessor(verificationPacketFilter.nearFull);
        proc.stallPipeline(True);
    endrule
    rule unstallProcessor(verificationPacketFilter.nearEmpty);
        proc.stallPipeline(False);
    endrule

    rule connectExtMemReq;
        let req = extMemReqFIFO.first;
        extMemReqFIFO.deq;
        proc.extmem.request.enq(req);
    endrule
    rule connectExtMemResp;
        let resp = proc.extmem.response.first;
        proc.extmem.response.deq;
        extMemRespFIFO.enq(resp);
    endrule

// Put the actual flag for Config Simulation
`ifdef CONFIG_RS232
`ifdef SIMULATION
    Reg#(Bit#(16)) uartDivisor <- mkReg(17);
    UART#(16) simUart <- mkUART(8, NONE, STOP_1, uartDivisor);
    Reg#(Maybe#(Bit#(8))) simUartTxCache <- mkReg(tagged Invalid);
    Reg#(Maybe#(Bit#(8))) simUartRxCache <- mkReg(tagged Invalid);
    let uartSimToFPGABridge <- mkConnection(toPut(proc.pins.uart.sin), toGet(simUart.rs232.sout));
    let uartFPGAToSimBridge <- mkConnection(toPut(simUart.rs232.sin), toGet(proc.pins.uart.sout));
`endif
`endif

`ifdef CONFIG_ACCELERATOR
`ifdef CONFIG_STR_LEN_PINS
    ConnectalTop#(StrLenPins) accelerator <- mkAccelTop();
`else
    ConnectalTop#(Empty) accelerator <- mkAccelTop();
`endif
    FIFO#(Bit#(1)) pendingAcceleratorReq <- mkFIFO;
    // accelerator.slave.write_server requires the writeReq to come before the
    // writeData, so writeDataFIFO holds the data until the accelerator is
    // ready for it
    FIFO#(MemData#(32)) writeDataFIFO <- mkFIFO;

    rule connectAcceleratorRequest;
        let req = proc.mmio.request.first;
        proc.mmio.request.deq;
        if (req.write) begin
            if (verbose) $fdisplay(stderr, "[Accelerator Write] addr = 0x%0x, data = 0x%0x", req.addr, req.data);
            accelerator.slave.write_server.writeReq.put(
                    PhysMemRequest{
                        addr: truncate(req.addr),
                        burstLen: 4, // 4 bytes, 32-bits
                        tag: 1
                    });
            writeDataFIFO.enq(
                    MemData{
                        data: truncate(req.data),
                        tag: 1,
                        last: True
                    });
            pendingAcceleratorReq.enq(1);
        end else begin
            if (verbose) $fdisplay(stderr, "[Accelerator Read] addr = 0x%0x", req.addr);
            accelerator.slave.read_server.readReq.put(
                    PhysMemRequest{
                        addr: truncate(req.addr),
                        burstLen: 4, // 4 bytes, 32-bits
                        tag: 0
                    });
            pendingAcceleratorReq.enq(0);
        end
    endrule
    rule connectalAcceleratorWriteData;
        if (verbose) $fdisplay(stderr, "[Accelerator Write] data = 0x%0x", writeDataFIFO.first.data);
        accelerator.slave.write_server.writeData.put(writeDataFIFO.first);
        writeDataFIFO.deq;
    endrule
    rule connectAcceleratorResponse;
        Data data = 0;
        if (pendingAcceleratorReq.first == 1) begin
            if (verbose) $fdisplay(stderr, "[Accelerator Write] response");
            let tag <- accelerator.slave.write_server.writeDone.get();
        end else begin
            let readData <- accelerator.slave.read_server.readData.get();
            data = zeroExtend(readData.data);
            if (verbose) $fdisplay(stderr, "[Accelerator Read] response data = 0x%0x", data);
        end
        pendingAcceleratorReq.deq;
        proc.mmio.response.enq(
                UncachedMemResp{
                    write: pendingAcceleratorReq.first == 1,
                    data: data
                });
    endrule

    // XXX: This is hard-coded for only 2 portals
    //rule connectInterrupts(accelerator.interrupt[0] || accelerator.interrupt[1]);
    //    proc.triggerExternalInterrupt;
    //endrule
    function t doRead(ReadOnly#(t) x) = x._read;
    rule connectInterrupts(fold( \|| , map(doRead, accelerator.interrupt)));
        proc.triggerExternalInterrupt;
    endrule

`ifdef CONFIG_STR_LEN_PINS
    // Only if accelerator has pins
    rule acceleratorMemReq;
        let req <- accelerator.pins.readReq;
        extMemReqFIFO.enq( CoarseMemReq{
                                write: False,
                                addr: truncate(req),
                                data: 0
                            });
        extMemUserFIFO.enq(Accel);
    endrule
    rule acceleratorMemResp(extMemUserFIFO.first == Accel);
        let resp = extMemRespFIFO.first;
        extMemRespFIFO.deq;
        extMemUserFIFO.deq;
        accelerator.pins.readData(resp.data);
    endrule
`endif
`endif

    // rules for connecting indications
    rule finishReset(resetSent && (!procReset.isAsserted)
                               && (ramSharedMemoryBridge.numberFlyingOperations == 0));
        // wait for procReset to finish
        resetSent <= False;
        procControlIndication.resetDone;
    endrule
    rule connectExternalMemResponse(extMemUserFIFO.first == Ext);
        let resp = extMemRespFIFO.first;
        extMemRespFIFO.deq;
        extMemUserFIFO.deq;
        platformIndication.memResponse(resp.write, zeroExtend(resp.data));
    endrule
    rule connectVerificationIndication;
        let msg <- verificationPacketFilter.getPacket;
        verificationIndication.getVerificationPacket(msg);
    endrule

`ifndef CONFIG_ACCELERATOR
    rule connectExternalMMIORequest;
        let msg = proc.mmio.request.first;
        proc.mmio.request.deq;
        // TODO: setup accelerator to only send coarse write requests
        // zero extend data in case XLEN is not 64
        externalMMIORequest.request(msg.write, zeroExtend(msg.addr), zeroExtend(msg.data));
    endrule
`endif

`ifdef SIMULATION
    // Put and Get rules for Sim Uart
    rule doPut (isValid(simUartTxCache));
      simUart.rx.put(fromMaybe(?, simUartTxCache));
      simUartTxCache <= tagged Invalid;
    endrule
    rule getData;
      let data <- simUart.tx.get;
      uartBridgeIndication.get(data);
    endrule
`endif

    // request interfaces
    interface ProcControlRequest procControlRequest;
        method Action reset() if (!resetSent);
            // resets the processor
            procReset.assertReset();
            // flushes the pending memory requests
            ramSharedMemoryBridge.flushRespReqMem;
            resetSent <= True;
        endmethod
        method Action start(Bit#(64) startPc, Bit#(64) verificationPacketsToIgnore, Bool sendSynchronizationPackets);
            // startPc is ignored
            proc.start;
            verificationPacketFilter.init(verificationPacketsToIgnore, sendSynchronizationPackets);
        endmethod
        method Action stop();
            proc.stop;
        endmethod
    endinterface
    interface PlatformRequest platformRequest;
        method Action configure(Bit#(32) ramSharedMemRefPointer, Bit#(64) ramSize);
            // configure shared memory
            ramSharedMemoryBridge.initSharedMem(ramSharedMemRefPointer, ramSize);
        endmethod
        method Action memRequest(Bool write, Bit#(64) addr, Bit#(64) data);
            extMemReqFIFO.enq( CoarseMemReq{
                                    write: write,
                                    addr: truncate(addr),
                                    data: truncate(data)
                                });
            extMemUserFIFO.enq(Ext);
        endmethod
    endinterface
    interface PerfMonitorRequest perfMonitorRequest;
        method Action reset;
            noAction;
        endmethod
        method Action setEnable(Bool en);
            noAction;
        endmethod
        method Action req(Bit#(32) index);
            perfMonitorIndication.resp(0);
        endmethod
    endinterface
`ifdef CONFIG_ACCELERATOR
    // don't connect External MMIO interface
    interface ExternalMMIOResponse externalMMIOResponse;
        method Action response(Bool write, Bit#(64) data) if (False);
            noAction;
        endmethod
        method Action triggerExternalInterrupt if (False);
            noAction;
        endmethod
    endinterface
`else
    interface ExternalMMIOResponse externalMMIOResponse;
        method Action response(Bool write, Bit#(64) data);
            // truncate data in case XLEN is not 64
            proc.mmio.response.enq( ByteEnMemResp{write: write, data: truncate(data)} );
        endmethod
        method Action triggerExternalInterrupt;
            proc.triggerExternalInterrupt;
        endmethod
    endinterface
`endif

`ifdef SIMULATION
    interface UartBridgeRequest uartBridgeRequest;
      method Action put (Bit#(8) data);
        if (!isValid(simUartTxCache)) begin
          simUart.rx.put(data);
        end
      endmethod
      method Action setDivisor (Bit#(16) divisor);
        uartDivisor <= divisor;
        uartBridgeIndication.setDivisorDone;
      endmethod
    endinterface
  `else
    interface UartBridgeRequest uartBridgeRequest;
      method Action put (Bit#(8) data);
        noAction;
      endmethod
      method Action setDivisor (Bit#(16) divisor);
        noAction;
      endmethod
    endinterface
  `endif

    // dma interfaces
    interface MemReadClient dmaReadClient = vec(ramSharedMemoryBridge.to_host_read);
    interface MemWriteClient dmaWriteClient = vec(ramSharedMemoryBridge.to_host_write);

    // pins interface
    interface ProcPins pins = proc.pins;
endmodule
