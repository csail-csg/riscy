
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
import FrontEnd::*;
import BackEnd::*;
import MemorySystem::*;

// This is used by ProcConnectal
typedef DataSz MainMemoryWidth;

(* synthesize *)
module mkProc(Proc#(DataSz));
    FrontEnd#(void) frontend <- mkMulticycleFrontEnd;
    BackEnd#(void) backend <- mkMulticycleBackEnd;
    SingleCoreMemorySystem#(DataSz) memorySystem <- mkBasicMemorySystem;

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

    VerificationPacketFilter verificationPacketFilter <- mkVerificationPacketFilter(backend.getVerificationPacket);

    // Processor Control
    method Action start(Bit#(64) startPc, Bit#(64) verificationPacketsToIgnore, Bool sendSynchronizationPackets);
        frontend.start(startPc);
        verificationPacketFilter.init(verificationPacketsToIgnore, sendSynchronizationPackets);
    endmethod
    method Action stop();
        frontend.stop;
    endmethod
    method Action configure(Data miobase);
        backend.configure(miobase);
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
        backend.htif.response.put(v);
    endmethod
    method ActionValue#(Bit#(64)) toHost;
        let msg <- backend.htif.request.get;
        // $fdisplay(stderr, "[PROC] toHost: 0x%08x", msg);
        return msg;
    endmethod

    // Main Memory Connection
    interface mainMemory = memorySystem.mainMemory;
    interface uncachedMemory = memorySystem.uncachedMemory;

    // Interrupts
    method Action triggerExternalInterrupt;
        backend.triggerExternalInterrupt;
    endmethod
endmodule

