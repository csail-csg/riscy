
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
import GetPut::*;

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

module mkMulticycleBackEnd#(
        Server#(RVDMMUReq, RVDMMUResp) dvat,
        Server#(RVDMemReq, RVDMemResp) dmem,
        Bool ipi,
        Bool timerInterrupt,
        Data timer,
        Bool externalInterrupt,
        Data hartID
    )
        (BackEnd#(void));
    let verbose = False;
    File fout = stdout;

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
    RVCsrFile csrf <- mkRVCsrFile(hartID, timer, timerInterrupt, ipi, externalInterrupt);
    MulDivExec mulDiv <- mkBoothRoughMulDivExec;
    FpuExec fpu <- mkFpuExecPipeline;

    FIFO#(FrontEndToBackEnd#(void)) toBackEnd <- mkFIFO;
    FIFO#(Redirect#(void)) redirect <- mkFIFO;

    FIFO#(VerificationPacket) verificationPackets <- mkFIFO;

    rule doRegRead(state == RegRead);
        if (verbose) $display("RegRead");
        rVal1 <= rf.rd1(toFullRegIndex(dInst.rs1, getInstFields(inst).rs1));
        rVal2 <= rf.rd2(toFullRegIndex(dInst.rs2, getInstFields(inst).rs2));
        rVal3 <= rf.rd3(toFullRegIndex(dInst.rs3, getInstFields(inst).rs3));
        state <= Execute;
    endrule

    rule doExecute(state == Execute);
        if (verbose) $display("Execute");

        let execResult = basicExec(dInst, rVal1, rVal2, pc);

        case (dInst.execFunc) matches
            tagged Mem    .memInst:    dvat.request.put(RVDMMUReq {addr: execResult.addr, size: memInst.size, op: (memInst.op matches tagged Mem .memOp ? memOp : St)});
            tagged MulDiv .mulDivInst: mulDiv.exec(mulDivInst, rVal1, rVal2);
            tagged Fpu    .fpuInst:    fpu.exec(fpuInst, getInstFields(inst).rm, rVal1, rVal2, rVal3);
        endcase

        data <= execResult.data;
        addr <= execResult.addr;
        nextPc <= execResult.nextPc;

        state <= dInst.execFunc matches tagged Mem .* ? Mem : WB;
    endrule

    rule doMem(state == Mem);
        if (verbose) $display("Mem");
        let resp <- dvat.response.get;
        let pAddr = resp.addr;
        let exMMU = resp.exception;

        // TODO: make this type safe! get rid of .Mem accesses to tagged union
        if (!isValid(exMMU)) begin
            dmem.request.put( RVDMemReq {
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
                        dataWb <- dmem.response.get;
                    end
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
                dataWb,  // either rf[rs1] or zimm, computed in basicExec
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
endmodule
