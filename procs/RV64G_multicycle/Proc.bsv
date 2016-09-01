
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
import DefaultValue::*;
import ClientServer::*;
import Connectable::*;
import FIFO::*;
import GetPut::*;
import Vector::*;

import ClientServerUtil::*;
import PrintTrace::*;
import ServerUtil::*;

import Abstraction::*;
import Core::*;
import MemorySystem::*;
import MemoryMappedCSRs::*;
import RVTypes::*;
import VerificationPacket::*;
import VerificationPacketFilter::*;

// This is used by ProcConnectal
typedef DataSz MainMemoryWidth;

(* synthesize *)
module mkProc(Proc#(DataSz));
    // ROM Addresses
    // 0x0000_0000 - 0x3FFF_FFFF
    Addr romBaseAddr            = 'h0000_0000;
    Addr rstvec                 = 'h0000_1000;
    Addr nmivec                 = 'h0000_1004;
    Addr configStringPtr        = 'h0000_100C;
    Addr mtvecDefault           = 'h0000_1010;
    // Internal Memory-Mapped IO Addresses
    // 0x4000_0000 - 0x5FFF_FFFF
    Addr mmioBaseAddr           = 'h4000_0000;
    Addr rtcBaseAddr            = 'h4000_0000;
    Addr ipiBaseAddr            = 'h4000_1000;
    // External Memory-Mapped IO Addresses
    // 0x6000_0000 - 0x7FFF_FFFF
    Addr externalMMIOBaseAddr   = 'h6000_0000;
    // DRAM Addresses
    // 0x8000_0000 - end of address space
    Addr dramBaseAddr           = 'h8000_0000;

    // This function assumes romBaseAddr < mmioBaseAddr < dramBaseAddr
    function PMA getPMA(Addr addr);
        if (addr < mmioBaseAddr) begin
            return IORom;
        end else if (addr < dramBaseAddr) begin
            return IODevice;
        end else begin
            return MainMemory;
        end
    endfunction

    Wire#(Bool) extInterruptWire <- mkDWire(False);

    SingleCoreMemorySystem#(DataSz) memorySystem <- mkBasicMemorySystem(getPMA);
    MemoryMappedCSRs#(1) mmcsrs <- mkMemoryMappedCSRs(mmioBaseAddr);
    Core core <- mkMulticycleCore(
                    memorySystem.core[0].ivat,
                    memorySystem.core[0].ifetch,
                    memorySystem.core[0].dvat,
                    memorySystem.core[0].dmem,
                    mmcsrs.ipi[0], // inter-process interrupt
                    mmcsrs.timerInterrupt[0], // timer interrupt
                    mmcsrs.timerValue,
                    extInterruptWire, // external interrupt
                    0); // hart ID

    // +----------------+ +---------------+
    // |      Core      | | verification  |
    // |                |-| packet filter |
    // +----------------+ +---------------+
    //   || ||    || |||
    // +----------------+
    // | memory system  |
    // +----------------+

    let core_to_mem <- mkConnection(core, memorySystem.core[0]);

    // Memory Mapped IO connections
    FIFO#(UncachedMemReq) externalMMIOReqFIFO <- mkFIFO;
    FIFO#(UncachedMemResp) externalMMIORespFIFO <- mkFIFO;
    UncachedMemServer externalMMIOServer = toGPServer(externalMMIOReqFIFO, externalMMIORespFIFO);
    UncachedMemClient externalMMIOClient = toGPClient(externalMMIOReqFIFO, externalMMIORespFIFO);
    function Bit#(1) whichMMIOServer(UncachedMemReq r);
        if (r.addr >= externalMMIOBaseAddr ) begin
            return 1; // external devices
        end else begin
            return 0; // internal devices (memory mapped CSRs)
        end
    endfunction
    Integer maxPendingReq = 4;
    function UncachedMemReq adjustMMIOAddress(Addr a, UncachedMemReq r);
        r.addr = r.addr - a;
        return r;
    endfunction
    let memoryMappedIO <- mkServerJoiner(
                            whichMMIOServer,
                            constFn(True), // if a given request gets a response
                            maxPendingReq,
                            vec(mmcsrs.memifc, transformReq(adjustMMIOAddress(externalMMIOBaseAddr), externalMMIOServer)));
    let uncached_mem_connection <- mkConnection(memorySystem.uncachedMemory, memoryMappedIO);

    // Cached Memory Connection
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
    function MainMemReq adjustAddress(Addr a, MainMemReq r);
        r.addr = r.addr - a;
        return r;
    endfunction
    let cachedMemBridge <- mkServerJoiner(
                            whichServer,
                            constFn(True), // if a given request gets a response
                            maxPendingReq,
                            vec( transformReq(adjustAddress(0), romServer),
                                 transformReq(adjustAddress(dramBaseAddr), ramServer) ));
    let cached_mem_connection <- mkConnection(memorySystem.cachedMemory, cachedMemBridge);

    // Verification Packet Connection
    VerificationPacketFilter verificationPacketFilter <- mkVerificationPacketFilter(core.getVerificationPacket);

    // Processor Control
    method Action start(Bit#(64) startPc, Bit#(64) verificationPacketsToIgnore, Bool sendSynchronizationPackets);
        core.start(startPc);
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
    interface ram = ramClient;
    interface rom = romClient;
    interface UncachedMemClient mmio = externalMMIOClient;
    interface GenericMemServer extmem = memorySystem.extMemory;

    // Interrupts
    method Action triggerExternalInterrupt;
        extInterruptWire <= True;
    endmethod
endmodule

