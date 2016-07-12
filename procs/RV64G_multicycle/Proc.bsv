
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

import Clocks::*;
import DefaultValue::*;
import ClientServer::*;
import Connectable::*;
import GetPut::*;
import RVTypes::*;
import Vector::*;
import VerificationPacket::*;
import VerificationPacketFilter::*;

import Abstraction::*;
import Core::*;
import MemorySystem::*;

// This is used by ProcConnectal
typedef DataSz MainMemoryWidth;

(* synthesize *)
module mkProc(Proc#(DataSz));
    SingleCoreMemorySystem#(DataSz) memorySystem <- mkBasicMemorySystem;
    Core core <- mkMulticycleCore(memorySystem.core[0].ivat, memorySystem.core[0].ifetch, memorySystem.core[0].dvat, memorySystem.core[0].dmem);

    // +----------------+ +---------------+
    // |      Core      | | verification  |
    // |                |-| packet filter |
    // +----------------+ +---------------+
    //   || ||    || |||
    // +----------------+
    // | memory system  |
    // +----------------+

    let core_to_mem <- mkConnection(core, memorySystem.core[0]);

    VerificationPacketFilter verificationPacketFilter <- mkVerificationPacketFilter(core.getVerificationPacket);

    // Processor Control
    method Action start(Bit#(64) startPc, Bit#(64) verificationPacketsToIgnore, Bool sendSynchronizationPackets);
        core.start(startPc);
        verificationPacketFilter.init(verificationPacketsToIgnore, sendSynchronizationPackets);
    endmethod
    method Action stop();
        core.stop;
    endmethod
    method Action configure(Data miobase);
        core.configure(miobase);
        memorySystem.configure(miobase);
    endmethod

    // Verification
    method ActionValue#(VerificationPacket) getVerificationPacket;
        let verificationPacket <- verificationPacketFilter.getPacket;
        return verificationPacket;
    endmethod

    // HTIF
    method Action fromHost(Bit#(64) v);
        // $fdisplay(stderr, "[PROC] fromHost: 0x%08x", v);
        core.htif.response.put(v);
    endmethod
    method ActionValue#(Bit#(64)) toHost;
        let msg <- core.htif.request.get;
        // $fdisplay(stderr, "[PROC] toHost: 0x%08x", msg);
        return msg;
    endmethod

    // Main Memory Connection
    interface mainMemory = memorySystem.mainMemory;
    interface uncachedMemory = memorySystem.uncachedMemory;

    // Interrupts
    method Action triggerExternalInterrupt;
        core.triggerExternalInterrupt;
    endmethod
endmodule

