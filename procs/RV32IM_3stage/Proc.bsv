
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

import BuildVector::*;
import DefaultValue::*;
import ClientServer::*;
import Connectable::*;
import FIFO::*;
import GetPut::*;
import Vector::*;

import ClientServerUtil::*;
import FIFOG::*;
import Port::*;
import ServerUtil::*;

import Abstraction::*;
import BasicMemorySystemBlocks::*;
import BramIDMem::*;
import Core::*;
import MemoryMappedCSRs::*;
import ProcPins::*;
import RTC::*;
import RVUart::*;
import SPI::*;
import RVSPI::*;
import RVTypes::*;
import VerificationPacket::*;
import VerificationPacketFilter::*;

// This is used by ProcConnectal
typedef DataSz MainMemoryWidth;

(* synthesize *)
module mkProc(Proc#(DataSz));
    // Address map (some portions hard-coded in memory system
    // 0x0000_0000 - 0x2000_0000 : tightly coupled memory (not all used)
    // 0x2000_0000 - 0x2FFF_FFFF : rtc
    // 0x3000_0000 - 0x3FFF_FFFF : uart
    // 0x4000_0000 - 0xFFFF_FFFF : mmio

    let clock <- exposeCurrentClock();

`ifdef CONFIG_RV32
    RTC#(1) rtc <- mkRTC_RV32;
`else
    RTC#(1) rtc <- mkRTC_RV64;
`endif

    //   9600 baud: divisor = 26042
    // 115200 baud: divisor = 134
    RVUart#(1) uart_module <- mkRVUart_RV32(17);

    RVSPI spi_module <- mkRVSPI();

    Bool timer_interrupt = rtc.timerInterrupt[0];
    Bit#(64) timer_value = rtc.timerValue;

    Wire#(Bool) extInterruptWire <- mkDWire(False);

    // Shared I/D Memory
    // the type of the imem port is Server#(Bit#(XLEN), Bit#(32))
    // the type of the dmem port is Server#(UncachedMemReq, UncachedMemResp)
    let sram <- mkBramIDMem;

    // This is the new way:
    FIFOG#(UncachedMemReq) uncachedReqFIFO <- mkFIFOG;
    FIFOG#(UncachedMemResp) uncachedRespFIFO <- mkFIFOG;
    let mmio_server = toServerPort(uncachedReqFIFO, uncachedRespFIFO);
    let mmio_client = toClientPort(uncachedReqFIFO, uncachedRespFIFO);

    MemoryBusV2 memoryBus <- mkMemoryBusV2(vec(
                                busItemFromAddrRange( 'h0000_0000, 'h1FFF_FFFF, sram.dmem ),
                                busItemFromAddrRange( 'h2000_0000, 'h2FFF_FFFF, rtc.memifc ),
                                busItemFromAddrRange( 'h3000_0000, 'h3000_FFFF, uart_module.memifc ),
                                busItemFromAddrRange( 'h3001_0000, 'h3001_FFFF, spi_module.memifc ),
                                // split into two ranges to fit mask/match formatting that mkMemoryBusV2 uses
                                busItemFromAddrRange( 'h4000_0000, 'h7FFF_FFFF, mmio_server ),
                                busItemFromAddrRange( 'h8000_0000, 'hFFFF_FFFF, mmio_server )));

    // mkUncachedConverter converts UncachedMemServerPort to ServerPort#(RVDMemReq, RVDMemResp)
    let proc_dmem_ifc <- mkUncachedConverter(memoryBus.procIfc);

    Core core <- mkThreeStageCore(
                    sram.imem,
                    proc_dmem_ifc,
                    False, // inter-process interrupt
                    timer_interrupt, // timer interrupt
                    timer_value, // timer value
                    extInterruptWire, // external interrupt
                    0); // hart ID

    // Verification Packet Connection
    VerificationPacketFilter verificationPacketFilter <- mkVerificationPacketFilter(core.getVerificationPacket);

    // Processor Control
    method Action start(Bit#(64) startPc, Bit#(64) verificationPacketsToIgnore, Bool sendSynchronizationPackets);
        if (startPc != 0) begin
            // This processor does not have the same memory layout as spike,
            // so for now we are assuming this processor has rstvec = 0
            $fdisplay(stderr, "[WARNING] startPc != 0");
            $fflush(stderr);
        end
        core.start(truncate(startPc));
        verificationPacketFilter.init(verificationPacketsToIgnore, sendSynchronizationPackets);
    endmethod
    method Action stop();
        core.stop;
    endmethod

    // Verification
    method ActionValue#(VerificationPacket) getVerificationPacket;
        let verificationPacket <- verificationPacketFilter.getPacket;
        return verificationPacket;
    endmethod

    // Main Memory Connection
    // XXX: Currently unattached
    interface MainMemClientPort ram = nullClientPort;
    // XXX: Currently unattached
    interface MainMemClientPort rom = nullClientPort;

    interface UncachedMemClientPort mmio = mmio_client;

    interface GenericMemServerPort extmem;
        interface InputPort request;
            method Action enq(GenericMemReq#(XLEN) x);
                if (x.byteen != '1) begin
                    $fdisplay(stderr, "[ERROR] mkProc.extmem : expecting byteen to be all 1's, but byteen = ", fshow(x.byteen));
                end
                memoryBus.extIfc.request.enq(UncachedMemReq {
                        write:  x.write,
                        size:   (valueOf(XLEN) == 64 ? D : W),
                        addr:   x.addr,
                        data:   x.data
                    } );
            endmethod
            method Bool canEnq;
                return memoryBus.extIfc.request.canEnq;
            endmethod
        endinterface
        interface OutputPort response;
            method GenericMemResp#(XLEN) first;
                let x = memoryBus.extIfc.response.first;
                return GenericMemResp {
                        write: x.write,
                        data:  x.data
                    };
            endmethod
            method Action deq;
                memoryBus.extIfc.response.deq;
            endmethod
            method Bool canDeq;
                return memoryBus.extIfc.response.canDeq;
            endmethod
        endinterface
    endinterface

    // Interrupts
    method Action triggerExternalInterrupt;
        extInterruptWire <= True;
    endmethod

    interface ProcPins pins;
        // no other pins connected at the moment
        `ifdef CONFIG_RS232
            interface RS232 uart = uart_module.uart_pins;
        `endif
        `ifdef CONFIG_SPI
            interface SPIMasterPins spi = spi_module.spi_pins;
        `endif
        interface Clock deleteme_unused_clock = clock;
    endinterface
endmodule
