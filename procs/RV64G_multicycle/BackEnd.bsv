
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
import DefaultValue::*;
import FIFO::*;
import Vector::*;

import Abstraction::*;
import RVRFile::*;
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

typedef enum {
    Wait,
    RegRead,
    Execute,
    Mem,
    WB,
    Trap,
    Trap2
} BEState deriving (Bits, Eq, FShow);

(* synthesize *)
module mkMulticycleBackEnd(BackEnd#(void));
    let verbose = False;
    File fout = stdout;

    Reg#(Bool) htifStall <- mkReg(False);

    Reg#(Addr) pc <- mkReg(0);
    Reg#(Instruction) inst <- mkReg(0);
    Reg#(Maybe#(ExceptionCause)) exception <- mkReg(tagged Invalid);
    Reg#(RVDecodedInst) dInst <- mkReg(unpack(0));
    Reg#(BEState) state <- mkReg(Wait);
    Reg#(Data) rVal1 <- mkReg(0);
    Reg#(Data) rVal2 <- mkReg(0);
    Reg#(Data) rVal3 <- mkReg(0);
    Reg#(Data) data <- mkReg(0);
    Reg#(Data) addr <- mkReg(0);
    Reg#(Data) nextPc <- mkReg(0);

    ArchRFile rf <- mkArchRFile;
    RVCsrFile csrf <- mkRVCsrFile;
    MulDivExec mulDiv <- mkBoothRoughMulDivExec;
    FpuExec fpu <- mkFpuExecPipeline;

    FIFO#(FrontEndToBackEnd#(void)) toBackEnd <- mkFIFO;
    FIFO#(Redirect#(void)) redirect <- mkFIFO;

    FIFO#(RVDMMUReq)    mmuReq <- mkFIFO;
    FIFO#(RVDMMUResp)   mmuResp <- mkFIFO;

    FIFO#(RVDMemReq)    memReq <- mkFIFO;
    FIFO#(RVDMemResp)   memResp <- mkFIFO;

    FIFO#(Data)         toHost <- mkFIFO;
    FIFO#(Data)         fromHost <- mkFIFO;

    FIFO#(VerificationPacket) verificationPackets <- mkFIFO;

    rule doRegRead(!htifStall && state == RegRead);
        if (verbose) $display("RegRead");
        rVal1 <= rf.rd1(toFullRegIndex(dInst.rs1, getInstFields(inst).rs1));
        rVal2 <= rf.rd2(toFullRegIndex(dInst.rs2, getInstFields(inst).rs2));
        rVal3 <= rf.rd3(toFullRegIndex(dInst.rs3, getInstFields(inst).rs3));
        state <= Execute;
    endrule

    rule doExecute(state == Execute);
        if (verbose) $display("Execute");
        let dataEx = 0;
        let addrEx = 0;
        let nextPcEx = pc + 4;

        Maybe#(Data) imm = getImmediate(dInst.imm, dInst.inst);
        case (dInst.execFunc) matches
            tagged Alu    .aluInst:
                begin
                    dataEx = execAluInst(aluInst, rVal1, rVal2, imm, pc);
                end
            tagged Br     .brFunc:
                begin
                    // data for jal
                    dataEx = pc + 4;
                    nextPcEx = execControl(brFunc, rVal1, rVal2, imm, pc);
                end
            tagged Mem    .memInst:
                begin
                    // data for store and AMO
                    dataEx = rVal2;
                    addrEx = addrCalc(rVal1, imm);
                    mmuReq.enq(RVDMMUReq {addr: addrEx, size: memInst.size, op: (memInst.op matches tagged Mem .memOp ? memOp : St)});
                end
            tagged MulDiv .mulDivInst: mulDiv.exec(mulDivInst, rVal1, rVal2);
            tagged Fence  .fenceInst:  noAction;
            // TODO: Handle dynamic rounding mode
            tagged Fpu    .fpuInst:    fpu.exec(fpuInst, getInstFields(inst).rm, rVal1, rVal2, rVal3);
            tagged System .systemInst:
                begin
                    // data for CSR instructions
                    dataEx = fromMaybe(rVal1, imm);
                end
        endcase

        data <= dataEx;
        addr <= addrEx;
        nextPc <= nextPcEx;

        state <= dInst.execFunc matches tagged Mem .* ? Mem : WB;
    endrule

    rule doMem(state == Mem);
        if (verbose) $display("Mem");
        let pAddr = mmuResp.first.addr;
        let exMMU = mmuResp.first.exception;
        mmuResp.deq;

        // TODO: make this type safe! get rid of .Mem accesses to tagged union
        if (!isValid(exMMU)) begin
            memReq.enq( RVDMemReq {
                    op: dInst.execFunc.Mem.op,
                    size: dInst.execFunc.Mem.size,
                    isUnsigned: dInst.execFunc.Mem.isUnsigned,
                    addr: pAddr,
                    data: data } );
            state <= WB;
        end else begin
            exception <= exMMU;
            state <= Trap;
        end
    endrule

    rule doWB(state == WB);
        if (verbose) $display("WB");
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
                    let fpuResult = toFullResult(fpu.result_data);
                    dataWb = fpuResult.data;
                    fflagsWb = fpuResult.fflags;
                    fpu.result_deq;
                end
            tagged Mem .memInst:
                begin
                    if (getsResponse(memInst.op)) begin
                        dataWb = memResp.first;
                        memResp.deq;
                    end
                end
        endcase

        // TODO: add comment
        Bool checkForInterrupts = dInst.execFunc matches tagged Mem .* ? False : True;
        Bool extensionDirty = False;
        Bool fpuDirty = (dInst.dst == tagged Valid Fpu);
        let {maybeTrap, maybeData, maybeNextPc} <- csrf.wr(
                // performing system instructions
                dInst.execFunc matches tagged System .sysInst ? tagged Valid sysInst : tagged Invalid,
                getInstFields(inst).csr,
                dataWb,  // either rf[rs1] or zimm, computed in basicExec
                // handling exceptions
                exceptionWB,    // exception cause
                checkForInterrupts,
                pc,             // for writing to mepc/sepc
                dInst.execFunc matches tagged Br .* ? True : False, // check inst allignment if Br Func
                dInst.execFunc matches tagged Br .* ? nextPcWb : addrWb, // either data address or next PC, used to detect misaligned instruction addresses
                // indirect writes
                fflagsWb,
                fpuDirty,
                extensionDirty);

        // send verification packet
        verificationPackets.enq( VerificationPacket {
                skippedPackets: 0,
                pc: pc,
                nextPc: fromMaybe(nextPcWb, maybeNextPc),
                data: fromMaybe(dataWb, maybeData),
                addr: addr,
                instruction: inst,
                dst: {pack(dInst.dst), getInstFields(inst).rd},
                trap: isValid(maybeTrap),
                trapType: (case (fromMaybe(unpack(0), maybeTrap)) matches
                        tagged Exception .x: (zeroExtend(pack(x)));
                        tagged Interrupt .x: (zeroExtend(pack(x)) | 8'h80);
                    endcase) });

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
            redirect.enq( Redirect {
                    pc: nextPc,
                    epoch: ?,
                    frontEndCsrs: FrontEndCsrs { vmI: csrf.vmI, state: csrf.csrState } } );
            state <= Wait;
        end
    endrule

    rule doTrap(state == Trap);
        if (verbose) $display("Trap");
        // TODO: move this to WB
        let {maybeTrap, maybeData, maybeNextPc} <- csrf.wr(
                tagged Invalid,
                getInstFields(inst).csr,
                0, // data
                exception, // exception cause
                True,
                pc, // pc
                False, 
                addr, // vaddr
                0,
                False,
                False);

        // send verification packet
        verificationPackets.enq( VerificationPacket {
                skippedPackets: 0,
                pc: pc,
                nextPc: fromMaybe(?, maybeNextPc),
                data: fromMaybe(data, maybeData),
                addr: addr,
                instruction: inst,
                dst: {pack(dInst.dst), getInstFields(inst).rd},
                trap: isValid(maybeTrap),
                trapType: (case (fromMaybe(unpack(0), maybeTrap)) matches
                        tagged Exception .x: (zeroExtend(pack(x)));
                        tagged Interrupt .x: (zeroExtend(pack(x)) | 8'h80);
                    endcase) });

        // redirection will happpen in trap2
        // by construction maybeNextPc is always valid
        nextPc <= fromMaybe(?, maybeNextPc);
        state <= Trap2;
    endrule

    // There is a second trap state to ensure that the frontEndCsrs reflect the updated state of the processor
    rule doTrap2(state == Trap2);
        if (verbose) $display("trap2");
        redirect.enq( Redirect {
            pc: nextPc,
            epoch: ?,
            frontEndCsrs: FrontEndCsrs { vmI: csrf.vmI, state: csrf.csrState }
        } );

        state <= Wait;
    endrule

    rule htifToHost;
        if (verbose) $display("htifToHost");
        let msg <- csrf.csrfToHost;
        if (truncateLSB(msg) != 16'h0100) begin
            htifStall <= True;
        end
        toHost.enq(msg);
    endrule

    rule htifFromHost;
        if (verbose) $display("Htif from host");
        htifStall <= False;
        let msg = fromHost.first;
        fromHost.deq;
        csrf.hostToCsrf(msg);
    endrule

    method Action instFromFrontEnd(FrontEndToBackEnd#(void) x) if (state == Wait);
        if (verbose) $fdisplay(fout, "[backend] receiving instruction for pc: 0x%08x - intruction: 0x%08x - dInst: ", x.pc, x.inst, fshow(x.dInst));
        pc <= x.pc;
        inst <= x.inst;
        dInst <= x.dInst;
        exception <= x.cause;
        state <= isValid(x.cause) ? Trap : RegRead;
    endmethod
    method ActionValue#(Redirect#(void)) getRedirect;
        if (verbose) $fdisplay(fout, "[backend] sending redirecting to 0x%08x", redirect.first.pc);
        redirect.deq;
        return redirect.first;
    endmethod
    method ActionValue#(TrainingData) getTrain if (False);
        return ?;
    endmethod

    interface Client dvat = toGPClient(mmuReq, mmuResp);
    interface Client dmem = toGPClient(memReq, memResp);
    interface Client htif = toGPClient(toHost, fromHost);

    method Action configure(Data miobase);
        if (verbose) $display("configure");
        csrf.configure(miobase);
    endmethod
    method ActionValue#(VerificationPacket) getVerificationPacket;
        if (verbose) $display("getverificationPacket");
        let verificationPacket = verificationPackets.first;
        verificationPackets.deq;
        return verificationPacket;
    endmethod

    method ActionValue#(VMInfo) updateVMInfoI;
        if (verbose) $display("Update VMi");
        return csrf.vmI;
    endmethod
    method ActionValue#(VMInfo) updateVMInfoD;
        if (verbose) $display("update VMD");
        return csrf.vmD;
    endmethod
    method Action triggerExternalInterrupt;
        if (verbose) $display("TriggerExternalInterrupt");
        csrf.triggerExternalInterrupt;
    endmethod
endmodule
