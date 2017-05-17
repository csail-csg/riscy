
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

import ClockGate::*;
import FIFOG::*;
import MemUtil::*;
import Port::*;

import Abstraction::*;
import RegUtil::*;
import RVRegFile::*;
import RVCsrFile::*;
import RVExec::*;
import RVFpu::*;
import RVMulDiv::*;
import RVTypes::*;
import VerificationPacket::*;

import RVAlu::*;
import RVControl::*;
import RVDecode::*;
import RVMemory::*;

import MemorySystem::*;

// This interface is the combination of FrontEnd and BackEnd
interface Core#(numeric type xlen);
    method Action start(Bit#(xlen) startPc);
    method Action stop;
    method Action stallPipeline(Bool stall);

    method Maybe#(VerificationPacket) currVerificationPacket;
    method ActionValue#(VMInfo#(xlen)) updateVMInfoI;
    method ActionValue#(VMInfo#(xlen)) updateVMInfoD;

    interface Client#(FenceReq, FenceResp) fence;
endinterface

instance Connectable#(Core#(xlen), MemorySystem#(xlen));
    module mkConnection#(Core#(xlen) core, MemorySystem#(xlen) mem)(Empty);
        mkConnection(core.fence, mem.fence);
        mkConnection(toGet(core.updateVMInfoI), toPut(mem.updateVMInfoI));
        mkConnection(toGet(core.updateVMInfoD), toPut(mem.updateVMInfoD));
    endmodule
endinstance

typedef enum {
    Wait,
    IMMU,
    IF,
    Dec,
    RegRead,
    Execute,
    Mem,
    WB,
    Trap,
    Trap2
} ProcState deriving (Bits, Eq, FShow);

module mkMulticycleCore#(
        ServerPort#(RVIMMUReq#(xlen), RVIMMUResp#(xlen)) ivat,
        // ServerPort#(RVIMemReq, RVIMemResp) ifetch,
        ReadOnlyMemServerPort#(xlen, 2) ifetch,
        ServerPort#(RVDMMUReq#(xlen), RVDMMUResp#(xlen)) dvat,
        // ServerPort#(RVDMemReq, RVDMemResp) dmem,
        AtomicMemServerPort#(xlen, TLog#(TDiv#(xlen,8))) dmem,
        Bool ipi,
        Bool timerInterrupt,
        Data timer,
        Bool externalInterrupt,
        Data hartID
    )
        (Core#(xlen)) provisos (NumAlias#(xlen, XLEN));
    File fout = stdout;

    // This is used in a few places for configuring the core
    RiscVISASubset misa = defaultValue;

    Reg#(Bool) stallReg <- mkReg(False);

    RVRegFile#(xlen) rf <- mkRVRegFile(misa.f);
    RVCsrFile#(xlen) csrf <- mkRVCsrFile(hartID, timer, timerInterrupt, ipi, externalInterrupt);
    MulDivExec#(xlen) mulDiv <- mkBoothRoughMulDivExec;
    FpuExec fpu <- mkFpuExecPipeline;

    Reg#(Bool) running <- mkReg(False);
    Reg#(ProcState) state <- mkReg(Wait);

    Reg#(Addr) pc <- mkReg(0);
    Reg#(Maybe#(ExceptionCause)) exception <- mkReg(tagged Invalid);
    Reg#(Instruction) inst <- mkReg(0);
    Reg#(RVDecodedInst) dInst <- mkReg(unpack(0));
    Reg#(FrontEndCsrs#(xlen)) csrState <- mkReadOnlyReg( FrontEndCsrs { vmI: csrf.vmI, state: csrf.csrState } );

    Reg#(Data) rVal1 <- mkReg(0);
    Reg#(Data) rVal2 <- mkReg(0);
    Reg#(Data) rVal3 <- mkReg(0);
    Reg#(Data) data <- mkReg(0);
    Reg#(Data) addr <- mkReg(0);
    Reg#(Data) nextPc <- mkReg(0);

    FIFOG#(VerificationPacket) verificationPackets <- mkLFIFOG;

    rule doInstMMU(running && state == IMMU);
        // request address translation from MMU
        ivat.request.enq(pc);
        // reset states
        inst <= unpack(0);
        dInst <= unpack(0);
        exception <= tagged Invalid;
        // go to InstFetch stage
        state <= IF;
    endrule

    rule doInstFetch(state == IF);
        // I wanted notation like this:
        // let {addr: .phyPc, exception: .exMMU} = mmuResp.first;
        let resp = ivat.response.first;
        ivat.response.deq;
        let phyPc = resp.addr;
        let exMMU = resp.exception;

        if (!isValid(exMMU)) begin
            // no translation exception
            ifetch.request.enq(ReadOnlyMemReq{ addr: phyPc });
            // go to decode stage
            state <= Dec;
        end else begin
            // translation exception (instruction access fault)
            exception <= exMMU;
            // send instruction to backend
            state <= Trap;
        end
    endrule

    rule doDecode(state == Dec);
        let fInst = ifetch.response.first.data;
        ifetch.response.deq;

        let decInst = decodeInst(misa.rv64, misa.m, misa.a, misa.f, misa.d, fInst);

        if (decInst matches tagged Valid .validDInst) begin
            // Legal instruction
            dInst <= validDInst;
        end else begin
            // Illegal instruction
            exception <= tagged Valid IllegalInst;
        end

        inst <= fInst;
        state <= isValid(decInst) ? RegRead : Trap;
    endrule

    rule doRegRead(state == RegRead);
        rVal1 <= rf.rd1(toFullRegIndex(dInst.rs1, getInstFields(inst).rs1));
        rVal2 <= rf.rd2(toFullRegIndex(dInst.rs2, getInstFields(inst).rs2));
        rVal3 <= rf.rd3(toFullRegIndex(dInst.rs3, getInstFields(inst).rs3));
        state <= Execute;
    endrule

    rule doExecute(state == Execute);
        let execResult = basicExec(dInst, rVal1, rVal2, pc);

        case (dInst.execFunc) matches
            tagged Mem    .memInst:    dvat.request.enq(RVDMMUReq {addr: execResult.addr, size: memInst.size, op: (memInst.op matches tagged Mem .memOp ? memOp : St)});
            tagged MulDiv .mulDivInst: mulDiv.exec(mulDivInst, rVal1, rVal2);
            tagged Fpu    .fpuInst:    fpu.exec(fpuInst, getInstFields(inst).rm, rVal1, rVal2, rVal3);
        endcase

        data <= execResult.data;
        addr <= execResult.addr;
        nextPc <= execResult.nextPc;

        state <= dInst.execFunc matches tagged Mem .* ? Mem : WB;
    endrule

    rule doMem(state == Mem);
        let resp = dvat.response.first;
        dvat.response.deq;
        let pAddr = resp.addr;
        let exMMU = resp.exception;

        // TODO: make this type safe! get rid of .Mem accesses to tagged union
        if (!isValid(exMMU)) begin
            // physical addr should have same byte offset as virtual addr
            Bit#(TLog#(TDiv#(xlen,8))) offset = truncate(addr);
            Bit#(TDiv#(xlen,8)) byteen = (case(dInst.execFunc.Mem.size)
                        B: 'b0001;
                        H: 'b0011;
                        W: 'b1111;
                        D: '1;
                    endcase) << offset;
            AtomicMemOp atomic_op = None;
            if (dInst.execFunc.Mem.op matches tagged Amo .rvamo) begin
                atomic_op = (case (rvamo)
                        Swap:    Swap;
                        Add:     Add;
                        Xor:     Xor;
                        And:     And;
                        Or:      Or;
                        Min:     Min;
                        Max:     Max;
                        Minu:    Minu;
                        Maxu:    Maxu;
                        default: None;
                    endcase);
            end
            dmem.request.enq( AtomicMemReq {
                    write_en: ((dInst.execFunc.Mem.op == tagged Mem Ld) ? 0 : byteen),
                    atomic_op: atomic_op,
                    addr: pAddr,
                    data: (data << {offset, 3'b0})
                } );
            //dmem.request.enq( RVDMemReq {
            //        op: dInst.execFunc.Mem.op,
            //        size: dInst.execFunc.Mem.size,
            //        isUnsigned: dInst.execFunc.Mem.isUnsigned,
            //        addr: pAddr,
            //        data: data } );
            state <= WB;
        end else begin
            exception <= exMMU;
            state <= Trap;
        end
    endrule

    rule doWB(!stallReg && state == WB);
        let dataWb = data;
        let addrWb = addr;
        let nextPcWb = nextPc;
        let fflagsWb = 0;
        let exceptionWB = exception;

        case(dInst.execFunc) matches
            tagged MulDiv .*: begin
                    dataWb = mulDiv.result_data();
                    mulDiv.result_deq;
                end
            tagged Fpu .*: begin
                    dataWb = fpu.result_data.data;
                    fflagsWb = fpu.result_data.fflags;
                    fpu.result_deq;
                end
            tagged Mem .memInst:
                begin
                    if (getsResponse(memInst.op)) begin
                        dataWb = dmem.response.first.data;
                        Bit#(TLog#(TDiv#(xlen,8))) offset = truncate(addr);
                        dataWb = dataWb >> {offset, 3'b0};
                        let extendFunc = memInst.isUnsigned ? zeroExtend : signExtend;
                        dataWb = (case(memInst.size)
                                    B: extendFunc(dataWb[7:0]);
                                    H: extendFunc(dataWb[15:0]);
                                    W: extendFunc(dataWb[31:0]);
                                    default: dataWb;
                                endcase);
                    end
                    dmem.response.deq;
                end
        endcase

        Maybe#(TrapCause) trap = tagged Invalid;
        if (exceptionWB matches tagged Valid .validException) begin
            trap = tagged Valid (tagged Exception validException);
        end else if ((nextPcWb & 'b011) != 0) begin
            trap = tagged Valid (tagged Exception InstAddrMisaligned);
        end

        if (dInst.execFunc matches tagged Mem .*) begin
            // don't bother checking for interrupts since you just did a memory operation
        end else begin
            // check for interrupts (this overwrites current exceptions)
            if (csrf.readyInterrupt matches tagged Valid .validInterrupt) begin
                trap = tagged Valid (tagged Interrupt validInterrupt);
            end
        end
        Bool extensionDirty = False;
        Bool fpuDirty = (dInst.dst == tagged Valid Fpu);
        let csrfResult <- csrf.wr(
                pc,
                // performing system instructions
                dInst.execFunc matches tagged System .sysInst ? tagged Valid sysInst : tagged Invalid,
                getInstFields(inst).csr,
                dataWb, // either rf[rs1] or zimm, computed in basicExec
                addrWb,
                // handling exceptions
                trap,
                // indirect writes
                fflagsWb,
                fpuDirty,
                extensionDirty);

        Maybe#(Addr) maybeNextPc = tagged Invalid;
        Maybe#(Data) maybeData = tagged Invalid;
        Maybe#(TrapCause) maybeTrap = tagged Invalid;
        case (csrfResult) matches
            tagged Exception .exc:
                begin
                    maybeNextPc = tagged Valid exc.trapHandlerPC;
                    maybeTrap = tagged Valid exc.exception;
                end
            tagged RedirectPC .newPc:
                maybeNextPc = tagged Valid newPc;
            tagged CsrData .data:
                maybeData = tagged Valid data;
            tagged None:
                noAction;
        endcase

        // send verification packet
        Bool isInterrupt = False;
        Bool isException = False;
        Bit#(4) trapCause = 0;
        case (maybeTrap) matches
            tagged Valid (tagged Interrupt .x):
                begin
                    isInterrupt = True;
                    trapCause = pack(x);
                end
            tagged Valid (tagged Exception .x):
                begin
                    isException = True;
                    trapCause = pack(x);
                end
        endcase
        verificationPackets.enq( VerificationPacket {
                skippedPackets: 0,
                pc: pc,
                data: fromMaybe(dataWb, maybeData),
                addr: addr,
                instruction: inst,
                dst: {pack(dInst.dst), getInstFields(inst).rd},
                exception: isException,
                interrupt: isInterrupt,
                cause: trapCause } );

        if (maybeNextPc matches tagged Valid .replayPc) begin
            // This instruction didn't retire

            // redirect happens in Trap2
            nextPc <= replayPc;
            state <= Trap2;
        end else begin
            // This instruction retired
            // write to the register file
            rf.wr(toFullRegIndex(dInst.dst, getInstFields(inst).rd), fromMaybe(dataWb, maybeData));
            // always redirect
            pc <= nextPc;
            state <= IMMU;
        end
    endrule

    rule doTrap(!stallReg && state == Trap);
        // TODO: move this to WB
        let csrfResult <- csrf.wr(
                pc,
                tagged Invalid,
                getInstFields(inst).csr,
                0, // data
                addr,
                (exception matches tagged Valid .e ? tagged Valid (tagged Exception e) : tagged Invalid), // exception cause
                0,
                False,
                False);

        Maybe#(Addr) maybeNextPc = tagged Invalid;
        Maybe#(Data) maybeData = tagged Invalid;
        Maybe#(TrapCause) maybeTrap = tagged Invalid;
        case (csrfResult) matches
            tagged Exception .exc:
                begin
                    maybeNextPc = tagged Valid exc.trapHandlerPC;
                    maybeTrap = tagged Valid exc.exception;
                end
            tagged RedirectPC .newPc:
                maybeNextPc = tagged Valid newPc;
            tagged CsrData .data:
                maybeData = tagged Valid data;
            tagged None:
                noAction;
        endcase

        // send verification packet
        Bool isInterrupt = False;
        Bool isException = False;
        Bit#(4) trapCause = 0;
        case (maybeTrap) matches
            tagged Valid (tagged Interrupt .x):
                begin
                    isInterrupt = True;
                    trapCause = pack(x);
                end
            tagged Valid (tagged Exception .x):
                begin
                    isException = True;
                    trapCause = pack(x);
                end
        endcase
        verificationPackets.enq( VerificationPacket {
                skippedPackets: 0,
                pc: pc,
                data: fromMaybe(data, maybeData),
                addr: addr,
                instruction: inst,
                dst: {pack(dInst.dst), getInstFields(inst).rd},
                exception: isException,
                interrupt: isInterrupt,
                cause: trapCause } );

        // redirection will happpen in trap2
        // by construction maybeNextPc is always valid
        nextPc <= fromMaybe(nextPc, maybeNextPc);
        state <= Trap2;
    endrule

    // There is a second trap state to ensure that the frontEndCsrs reflect the updated state of the processor
    rule doTrap2(state == Trap2);
        pc <= nextPc;
        state <= IMMU;
    endrule

    rule deqVerificationPacket(!stallReg);
        verificationPackets.deq;
    endrule

    method Action start(Addr startPc);
        running <= True;
        pc <= startPc;
        state <= IMMU;
        csrState <= defaultValue;
        stallReg <= False;
    endmethod
    method Action stop;
        running <= False;
        state <= Wait;
    endmethod
    method Action stallPipeline(Bool stall);
        stallReg <= stall;
    endmethod

    method Maybe#(VerificationPacket) currVerificationPacket;
        if (verificationPackets.canDeq) begin
            return tagged Valid verificationPackets.first;
        end else begin
            return tagged Invalid;
        end
    endmethod

    method ActionValue#(VMInfo#(xlen)) updateVMInfoI;
        return csrf.vmI;
    endmethod
    method ActionValue#(VMInfo#(xlen)) updateVMInfoD;
        return csrf.vmD;
    endmethod

endmodule
