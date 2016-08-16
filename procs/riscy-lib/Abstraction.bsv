
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

import ClientServer::*;
import Connectable::*;
import DefaultValue::*;
import GetPut::*;
import Vector::*;

import RVTypes::*;
import VerificationPacket::*;

/////////////////////////////////////////////
// Types for the three module abstraction: //
/////////////////////////////////////////////

typedef struct {
    Addr                    pc;
    Maybe#(Addr)            ppc; // invalid if front-end made no prediction
                                 // (i.e. it is waiting for a redirection)
    Instruction             inst;
    RVDecodedInst           dInst;
    Maybe#(ExceptionCause)  cause;
    epochType               backendEpoch;
} FrontEndToBackEnd#(type epochType) deriving (Bits, Eq, FShow);

typedef struct {
    Addr                pc;
    epochType           epoch;
    FrontEndCsrs        frontEndCsrs;
} Redirect#(type epochType) deriving (Bits, Eq, FShow);

typedef struct {
    VMInfo      vmI; // only if MMU is in front-end
    CsrState    state; // Bit#(2) prv;
                       // Bit#(3) frm;
                       // Bool f_enabled;
                       // Bool x_enabled;
} FrontEndCsrs deriving (Bits, Eq, FShow);
instance DefaultValue#(CsrState);
    function CsrState defaultValue = CsrState {prv: prvM, frm: 0, f_enabled: False, x_enabled: False};
endinstance
instance DefaultValue#(FrontEndCsrs);
    function FrontEndCsrs defaultValue = FrontEndCsrs {vmI: defaultValue, state: defaultValue};
endinstance

typedef struct {
    Addr    pc;
    Addr    nextPc;
    BrFunc  brFunc;
    Bool    taken;
} TrainingData deriving (Bits, Eq, FShow);

// front-end memory ports
typedef Addr RVIMMUReq; // maybe add prv
typedef struct {
    PAddr                   addr;
    Maybe#(ExceptionCause)  exception;
} RVIMMUResp deriving (Bits, Eq, FShow);

typedef PAddr RVIMemReq;
typedef Instruction RVIMemResp;

// back-end memory ports
typedef struct {
    Addr      addr;
    RVMemSize size; // for address misaligned
    RVMemOp   op; // really just load or store (amo counts as store)
} RVDMMUReq deriving (Bits, Eq, FShow);
typedef RVIMMUResp RVDMMUResp;

typedef struct {
    RVMemAmoOp      op;
    RVMemSize       size;
    Bool            isUnsigned;
    PAddr           addr;
    Data            data;
    // Bool aq; // XXX: I don't think these are necessary
    // Bool rl; // XXX: I don't think these are necessary
} RVDMemReq deriving (Bits, Eq, FShow);
typedef Data RVDMemResp;

typedef Fence FenceReq;
typedef void FenceResp;

typedef struct {
    Bool                     write;
    Bit#(TDiv#(dataWidth,8)) byteen;
    PAddr                    addr;
    Bit#(dataWidth)          data;
} GenericMemReq#(numeric type dataWidth) deriving (Bits, Eq, FShow);
typedef struct {
    Bool            write;
    Bit#(dataWidth) data;
} GenericMemResp#(numeric type dataWidth) deriving (Bits, Eq, FShow);
typedef Client#(GenericMemReq#(dataWidth), GenericMemResp#(dataWidth)) GenericMemClient#(numeric type dataWidth);
typedef Server#(GenericMemReq#(dataWidth), GenericMemResp#(dataWidth)) GenericMemServer#(numeric type dataWidth);

// main memory ports
typedef enum {IMMU, ICache, DMMU, DCache} MemoryClientType deriving (Bits, Eq, FShow);
typedef GenericMemReq#(DataSz) MainMemReq;
typedef MainMemReq MainMemoryReq; // TODO: use only one of these types
typedef GenericMemResp#(DataSz) MainMemResp;
typedef MainMemResp MainMemoryResp; // TODO: use only one of these types
typedef Client#(MainMemReq,MainMemResp) MainMemoryClient;
typedef Server#(MainMemReq,MainMemResp) MainMemoryServer;
typedef MainMemoryServer MainMemServer;
typedef MainMemoryClient MainMemClient;

// uncached memory port
typedef struct {
    Bool            write;
    RVMemSize       size;
    PAddr           addr;
    Data            data;
} UncachedMemReq deriving (Bits, Eq, FShow);
typedef struct {
    Bool            write;
    Data            data;
} UncachedMemResp deriving (Bits, Eq, FShow);
typedef Client#(UncachedMemReq, UncachedMemResp) UncachedMemClient;
typedef Server#(UncachedMemReq, UncachedMemResp) UncachedMemServer;

interface FrontEnd#(type epochType);
    // To Front-End
    method ActionValue#(FrontEndToBackEnd#(epochType)) instToBackEnd;
    method Action redirect(Redirect#(epochType) r);
    method Action train(TrainingData d);
    // To Memory System
    // interface Client#(RVIMMUReq, RVIMMUResp) ivat;
    // interface Client#(RVIMemReq, RVIMemResp) ifetch;
    // Debugging Interface
    method Action start(Addr pc);
    method Action stop;
endinterface

interface BackEnd#(type epochType);
    // To Front-End
    method Action instFromFrontEnd(FrontEndToBackEnd#(epochType) inst);
    method ActionValue#(Redirect#(epochType)) getRedirect;
    method ActionValue#(TrainingData) getTrain;
    // To Memory System
    // interface Client#(RVDMMUReq, RVDMMUResp) dvat;
    // interface Client#(RVDMemReq, RVDMemResp) dmem;
    interface Client#(FenceReq, FenceResp) fence;
    method ActionValue#(VMInfo) updateVMInfoI;
    method ActionValue#(VMInfo) updateVMInfoD;
    // Debugging Interface
    method ActionValue#(VerificationPacket) getVerificationPacket;
endinterface

interface MemorySystem;
    // To Front-End
    interface Server#(RVIMMUReq, RVIMMUResp) ivat;
    interface Server#(RVIMemReq, RVIMemResp) ifetch;
    // To Back-End
    interface Server#(RVDMMUReq, RVDMMUResp) dvat;
    interface Server#(RVDMemReq, RVDMemResp) dmem;
    interface Server#(FenceReq, FenceResp) fence;
    method Action updateVMInfoI(VMInfo vmI);
    method Action updateVMInfoD(VMInfo vmD);
endinterface

interface MulticoreMemorySystem#(numeric type numCores, numeric type mainMemWidth);
    interface Vector#(numCores, MemorySystem) core;
    // To main memory and devices
    interface GenericMemClient#(mainMemWidth) cachedMemory;
    interface UncachedMemClient uncachedMemory;
endinterface

typedef MulticoreMemorySystem#(1, mainMemWidth) SingleCoreMemorySystem#(numeric type mainMemWidth);

interface Proc#(numeric type mainMemoryWidth);
    // Processor Control
    method Action start(Bit#(64) startPc, Bit#(64) verificationPacketsToIgnore, Bool sendSynchronizationPackets);
    method Action stop();

    // Verification
    method ActionValue#(VerificationPacket) getVerificationPacket;

    // Cached Connections
    interface GenericMemClient#(mainMemoryWidth) ram;
    interface GenericMemClient#(mainMemoryWidth) rom;
    // Uncached Connections
    interface UncachedMemClient mmio;
    // Interrupts
    method Action triggerExternalInterrupt;
endinterface

instance Connectable#(FrontEnd#(epochType), BackEnd#(epochType));
    module mkConnection#(FrontEnd#(epochType) fe, BackEnd#(epochType) be)(Empty);
        rule connectInstToBackEnd;
            let x <- fe.instToBackEnd;
            be.instFromFrontEnd(x);
        endrule
        rule connectRedirectToFrontEnd;
            let x <- be.getRedirect;
            fe.redirect(x);
        endrule
        rule connectTrainToBackEnd;
            let x <- be.getTrain;
            fe.train(x);
        endrule
    endmodule
endinstance
instance Connectable#(FrontEnd#(epochType), MemorySystem);
    module mkConnection#(FrontEnd#(epochType) fe, MemorySystem mem)(Empty);
        // let ivatConnection <- mkConnection(fe.ivat, mem.ivat);
        // let imemConnection <- mkConnection(fe.ifetch, mem.ifetch);
    endmodule
endinstance
instance Connectable#(BackEnd#(epochType), MemorySystem);
    module mkConnection#(BackEnd#(epochType) be, MemorySystem mem)(Empty);
        // let dvatConnection <- mkConnection(be.dvat, mem.dvat);
        // let dmemConnection <- mkConnection(be.dmem, mem.dmem);
        let fenceConnection <- mkConnection(be.fence, mem.fence);
        let ivmConnection <- mkConnection(toGet(be.updateVMInfoI), toPut(mem.updateVMInfoI));
        let dvmConnection <- mkConnection(toGet(be.updateVMInfoD), toPut(mem.updateVMInfoD));
    endmodule
endinstance
