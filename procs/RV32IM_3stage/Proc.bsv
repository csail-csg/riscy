
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
    // Address map (some portions hard-coded in memory system
    // 0x0000_0000 - 0x4000_0000 : tightly coupled memory (not all used)
    // 0x4000_0000 - 0xFFFF_FFFF : mmio

    // simple timer
    Reg#(Bit#(TAdd#(64,10))) timer <- mkReg(0);
    rule incrementTiemr;
        timer <= timer + 1;
    endrule

    Wire#(Bool) extInterruptWire <- mkDWire(False);

    // TCM as main memory
    TightlyCoupledMemorySystem memorySystem <- mkTightlyCoupledMemorySystem;
    Core core <- mkThreeStageCore(
                    memorySystem.ifetch,
                    memorySystem.dmem,
                    False, // inter-process interrupt
                    False, // timer interrupt
                    truncateLSB(timer), // timer value
                    extInterruptWire, // external interrupt
                    0); // hart ID

    // +----------------+ +---------------+
    // |      Core      | | verification  |
    // |                |-| packet filter |
    // +----------------+ +---------------+
    //     ||      ||
    // +----------------+
    // | memory system  |
    // +----------------+

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
    interface MainMemClient ram;
        interface Get request;
            method ActionValue#(MainMemReq) get if (False);
                return ?;
            endmethod
        endinterface
        interface Put response;
            method Action put(MainMemResp resp);
                noAction;
            endmethod
        endinterface
    endinterface
    // XXX: Currently unattached
    interface MainMemClient rom;
        interface Get request;
            method ActionValue#(MainMemReq) get if (False);
                return ?;
            endmethod
        endinterface
        interface Put response;
            method Action put(MainMemResp resp);
                noAction;
            endmethod
        endinterface
    endinterface

    interface UncachedMemClient mmio = memorySystem.mmio;

    interface GenericMemServer extmem = memorySystem.ext;

    // Interrupts
    method Action triggerExternalInterrupt;
        extInterruptWire <= True;
    endmethod
endmodule

