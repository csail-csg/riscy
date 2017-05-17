
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

import ClientServer::*;
import Connectable::*;
import DefaultValue::*;
import GetPut::*;
import Vector::*;

import MemUtil::*;
import Port::*;

import ProcPins::*;
import RVTypes::*;
import VerificationPacket::*;

/////////////////////////////////////////////
// Types for the three module abstraction: //
/////////////////////////////////////////////

typedef struct {
    VMInfo#(xlen) vmI; // only if MMU is in front-end
    CsrState    state; // Bit#(2) prv;
                       // Bit#(3) frm;
                       // Bool f_enabled;
                       // Bool x_enabled;
} FrontEndCsrs#(numeric type xlen) deriving (Bits, Eq, FShow);
instance DefaultValue#(CsrState);
    function CsrState defaultValue = CsrState {prv: prvM, frm: 0, f_enabled: False, x_enabled: False};
endinstance
instance DefaultValue#(FrontEndCsrs#(xlen));
    function FrontEndCsrs#(xlen) defaultValue = FrontEndCsrs {vmI: defaultValue, state: defaultValue};
endinstance

typedef Bit#(addrSz) RVIMMUReq#(numeric type addrSz); // maybe add prv
typedef struct {
    Bit#(xlen)              addr;
    Maybe#(ExceptionCause)  exception;
} RVIMMUResp#(numeric type xlen) deriving (Bits, Eq, FShow);

typedef struct {
    Bit#(xlen) addr;
    RVMemSize  size; // for address misaligned
    RVMemOp    op; // really just load or store (amo counts as store)
} RVDMMUReq#(numeric type xlen) deriving (Bits, Eq, FShow);
typedef RVIMMUResp#(addrSz) RVDMMUResp#(numeric type addrSz);

// typedef struct {
//     RVMemAmoOp      op;
//     RVMemSize       size;
//     Bool            isUnsigned;
//     PAddr           addr;
//     Data            data;
//     // Bool aq; // XXX: I don't think these are necessary
//     // Bool rl; // XXX: I don't think these are necessary
// } RVDMemReq deriving (Bits, Eq, FShow);
// typedef Data RVDMemResp;

typedef Fence FenceReq;
typedef void FenceResp;

interface Proc#(numeric type mainMemoryWidth);
    // Processor Control
    method Action start();
    method Action stop();

    // Verification
    method Maybe#(VerificationPacket) currVerificationPacket;

    // Cached Connections
    interface CoarseMemClientPort#(XLEN, TLog#(TDiv#(mainMemoryWidth,8))) ram;
    // Uncached Connections
    interface CoarseMemClientPort#(XLEN, TLog#(TDiv#(XLEN,8))) mmio;
    // External Connections
    interface CoarseMemServerPort#(XLEN, TLog#(TDiv#(XLEN,8))) extmem;
    // Interrupts
    method Action triggerExternalInterrupt;

    method Action stallPipeline(Bool stall);

    // Pins
    (* prefix = "" *)
    interface ProcPins pins;
endinterface
