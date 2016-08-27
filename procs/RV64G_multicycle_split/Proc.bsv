
// Copyright (c) 2016 Massachusetts Institute of Technology

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
import Clocks::*;
import DefaultValue::*;
import ClientServer::*;
import Connectable::*;
import FIFO::*;
import GetPut::*;
import RVTypes::*;
import Vector::*;
import VerificationPacket::*;
import VerificationPacketFilter::*;

import ClientServerUtil::*;
import ServerUtil::*;

import Abstraction::*;
import FrontEnd::*;
import BackEnd::*;
import MemoryMappedCSRs::*;
import MemorySystem::*;

// This is used by ProcConnectal
typedef DataSz MainMemoryWidth;

(* synthesize *)
module mkProc(Proc#(DataSz));
    // Assumed Address Map
    // 0x0000_0000 - 0x0000_FFFF : Boot ROM
    // 0x0001_0000 - 0x3FFF_FFFF : Internal Devices
    // 0x4000_0000 - 0x0000_0000 : External Devices
    // 0x8000_0000 -       ?     : RAM

    function PMA getPMA(Addr addr);
        if (addr < 'h0001_0000) begin
            return IORom;
        end else if (addr < 'h8000_0000) begin
            return IODevice;
        end else begin
            return MainMemory;
        end
    endfunction

    Addr rstvec          = 'h0000_1000;
    Addr nmivec          = 'h0000_1004;
    Addr configStringPtr = 'h0000_100C;
    Addr mtvecDefault    = 'h0000_1010;
    Addr mmioBaseAddr    = 'h4000_0000;
    Addr rtcBaseAddr     = 'h4000_0000;
    Addr ipiBaseAddr     = 'h4000_1000;
    // DRAM at 0x8000_0000 - ?
    Addr dramBaseAddr    = 'h8000_0000;

    SingleCoreMemorySystem#(DataSz) memorySystem <- mkBasicMemorySystem(getPMA);
    MemoryMappedCSRs#(1) mmcsrs <- mkMemoryMappedCSRs(mmioBaseAddr);
    // Core core <- mkMulticycleCore(
    //                 memorySystem.core[0].ivat,
    //                 memorySystem.core[0].ifetch,
    //                 memorySystem.core[0].dvat,
    //                 memorySystem.core[0].dmem,
    //                 mmcsrs.ipi[0], // inter-process interrupt
    //                 mmcsrs.timerInterrupt[0], // timer interrupt
    //                 mmcsrs.timerValue,
    //                 False, // external interrupt
    //                 0); // hart ID
    // XXX: TODO
    FrontEnd#(void) frontend <- mkMulticycleFrontEnd(memorySystem.core[0].ivat, memorySystem.core[0].ifetch);
    BackEnd#(void) backend <- mkMulticycleBackEnd(
                                memorySystem.core[0].dvat,
                                memorySystem.core[0].dmem,
                                mmcsrs.ipi[0], // inter-processor interrupt
                                mmcsrs.timerInterrupt[0], // timer interrupt
                                mmcsrs.timerValue,
                                False, // external interrupt
                                0); // hart ID

    // +-------+ +------+ +---------------+
    // | front |-| back | | verification  |
    // |  end  |=| end  |-| packet filter |
    // +-------+ +------+ +---------------+
    //   || ||    || |||
    // +----------------+
    // | memory system  |
    // +----------------+

    let front_to_back <- mkConnection(frontend, backend);
    let front_to_mem <- mkConnection(frontend, memorySystem.core[0]);
    let back_to_mem <- mkConnection(backend, memorySystem.core[0]);

    // // Uncached Memory Connection
    // FIFO#(UncachedMemReq) externalUncachedReqFIFO <- mkFIFO;
    // FIFO#(UncachedMemResp) externalUncachedRespFIFO <- mkFIFO;
    // UncachedMemServer externalUncachedMemServer = toGPServer(externalUncachedReqFIFO, externalUncachedRespFIFO);
    // UncachedMemClient externalUncachedMemClient = toGPClient(externalUncachedReqFIFO, externalUncachedRespFIFO);
    // function Bit#(1) whichServer(UncachedMemReq r);
    //     if (r.addr >= mmioBaseAddr ) begin
    //         return 1; // mmiocsrs - hardware devices
    //     end else begin
    //         return 0; // external - software devices
    //     end
    // endfunction
    // function Bool getsResponse(UncachedMemReq r);
    //     return True;
    // endfunction
    // Integer maxPendingReq = 4;
    // let uncachedMem <- mkServerJoiner(
    //                         whichServer,
    //                         getsResponse,
    //                         maxPendingReq,
    //                         vec(externalUncachedMemServer, mmcsrs.memifc));
    // let uncached_mem_connection <- mkConnection(memorySystem.uncachedMemory, uncachedMem);

    // Uncached Memory Connection
    // connect all uncached memory connections to the memory mapped CSRs
    let uncached_mem_connection <- mkConnection(memorySystem.uncachedMemory, mmcsrs.memifc);

    // Cached Memory Connection
    // 0x0000_0000 - 0x0000_FFFF : ROM
    // 0x8000_0000 - 0x0000_0000 : RAM
    FIFO#(MainMemReq) romReqFIFO <- mkFIFO;
    FIFO#(MainMemResp) romRespFIFO <- mkFIFO;
    MainMemServer romServer = toGPServer(romReqFIFO, romRespFIFO);
    MainMemClient romClient = toGPClient(romReqFIFO, romRespFIFO);
    FIFO#(MainMemReq) ramReqFIFO <- mkFIFO;
    FIFO#(MainMemResp) ramRespFIFO <- mkFIFO;
    MainMemServer ramServer = toGPServer(ramReqFIFO, ramRespFIFO);
    MainMemClient ramClient = toGPClient(ramReqFIFO, ramRespFIFO);
    function Bit#(1) whichServer(MainMemReq r);
        if (r.addr >= dramBaseAddr ) begin
            return 1; // ram
        end else begin
            return 0; // rom
        end
    endfunction
    function Bool getsResponse(MainMemReq r);
        return True;
    endfunction
    function MainMemReq adjustAddress(Addr a, MainMemReq r);
        r.addr = r.addr - a;
        return r;
    endfunction
    Integer maxPendingReq = 4;
    let cachedMemBridge <- mkServerJoiner(
                            whichServer,
                            getsResponse,
                            maxPendingReq,
                            vec( transformReq(adjustAddress(0), romServer),
                                 transformReq(adjustAddress(dramBaseAddr), ramServer) ));
    let cached_mem_connection <- mkConnection(memorySystem.cachedMemory, cachedMemBridge);

    // Verification Packet Connection
    VerificationPacketFilter verificationPacketFilter <- mkVerificationPacketFilter(backend.getVerificationPacket);

    // Processor Control
    method Action start(Bit#(64) startPc, Bit#(64) verificationPacketsToIgnore, Bool sendSynchronizationPackets);
        frontend.start(startPc);
        verificationPacketFilter.init(verificationPacketsToIgnore, sendSynchronizationPackets);
    endmethod
    method Action stop();
        frontend.stop;
    endmethod

    // Verification
    method ActionValue#(VerificationPacket) getVerificationPacket;
        let verificationPacket <- verificationPacketFilter.getPacket;
        return verificationPacket;
    endmethod

    // Main Memory Connection
    interface ram = ramClient;
    interface rom = romClient;
    // XXX: Currently unattached
    interface UncachedMemClient mmio;
        interface Get request;
            method ActionValue#(UncachedMemReq) get if (False);
                return ?;
            endmethod
        endinterface
        interface Put response;
            method Action put(UncachedMemResp resp);
                noAction;
            endmethod
        endinterface
    endinterface
    // XXX: Currently unattached
    interface GenericMemServer extmem;
        interface Put request;
            method Action put(GenericMemReq#(XLEN) r) if (False);
                noAction;
            endmethod
        endinterface
        interface Get response;
            method ActionValue#(GenericMemResp#(XLEN)) get if (False);
                return ?;
            endmethod
        endinterface
    endinterface

    // Interrupts
    method Action triggerExternalInterrupt;
        // XXX: implement this
        noAction;
    endmethod
endmodule

