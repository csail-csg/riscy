
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

import ClientServer::*;
import Connectable::*;
import DefaultValue::*;
import FIFO::*;
import GetPut::*;
import Vector::*;

import Ehr::*;

import Abstraction::*;
import RegUtil::*;
import RVRFile::*;
`ifdef CONFIG_U
import RVCsrFile::*;
`else
import RVCsrFileMCU::*;
`endif
import RVExec::*;
import RVTypes::*;
import VerificationPacket::*;

import RVAlu::*;
import RVControl::*;
import RVDecode::*;
import RVMemory::*;
`ifdef CONFIG_M
import RVMulDiv::*;
`endif

interface Core;
    method Action start(Addr startPc);
    method Action stop;
    method ActionValue#(VerificationPacket) getVerificationPacket;
endinterface

typedef struct {
    Addr pc;
} FetchState deriving (Bits, Eq, FShow);

typedef struct {
    Addr pc;
} ExecuteState deriving (Bits, Eq, FShow);

typedef struct {
    Addr              pc;
    Maybe#(TrapCause) trap;
    RVDecodedInst     dInst;
    Addr              addr;
    Data              data;
} WriteBackState deriving (Bits, Eq, FShow);

module mkThreeStageCore#(
            Server#(Addr, Instruction) ifetch,
            Server#(RVDMemReq, RVDMemResp) dmem,
            Bool ipi,
            Bool timerInterrupt,
            Bit#(64) timer,
            Bool externalInterrupt,
            Data hartID
        )(Core);
    ArchRFile rf <- mkBypassArchRFile;
`ifdef CONFIG_U
    // If user mode is supported, use the full CSR File
    RVCsrFile csrf <- mkRVCsrFile(hartID, timer, timerInterrupt, ipi, externalInterrupt);
`else
    // Otherwise use the M-only CSR File designed for MCUs
    RVCsrFileMCU csrf <- mkRVCsrFileMCU(hartID, timer, timerInterrupt, ipi, externalInterrupt);
`endif

`ifdef CONFIG_M
    MulDivExec mulDiv <- mkBoothRoughMulDivExec;
`endif

    Ehr#(4, Maybe#(FetchState)) fetchStateEhr <- mkEhr(tagged Invalid);
    Ehr#(4, Maybe#(ExecuteState)) executeStateEhr <- mkEhr(tagged Invalid);
    Ehr#(4, Maybe#(WriteBackState)) writeBackStateEhr <- mkEhr(tagged Invalid);

    FIFO#(VerificationPacket) verificationPackets <- mkFIFO;

    rule doFetch(fetchStateEhr[2] matches tagged Valid .fetchState
                    &&& executeStateEhr[2] == tagged Invalid);
        // get and clear the fetch state
        let pc = fetchState.pc;
        fetchStateEhr[2] <= tagged Invalid;

        // request instruction
        ifetch.request.put(pc);

        // pass to execute state
        executeStateEhr[2] <= tagged Valid ExecuteState{ pc: pc };
    endrule

    rule doExecute(executeStateEhr[1] matches tagged Valid .executeState
                    &&& writeBackStateEhr[1] == tagged Invalid);
        // get and clear the execute state
        let pc = executeState.pc;
        executeStateEhr[1] <= tagged Invalid;

        // check for interrupts
        Maybe#(TrapCause) trap = tagged Invalid;
        if (csrf.readyInterrupt matches tagged Valid .validInterrupt) begin
            trap = tagged Valid (tagged Interrupt validInterrupt);
        end

        // get the instruction
        let inst <- ifetch.response.get;

        // decode the instruction
        let maybeDInst = decodeInst(inst);
        if (maybeDInst == tagged Invalid && trap == tagged Invalid) begin
            trap = tagged Valid (tagged Exception IllegalInst);
        end
        let dInst = fromMaybe(?, maybeDInst);

        // $display("[Execute] pc: 0x%0x, inst: 0x%0x, dInst: ", pc, inst, fshow(dInst));

        // read registers
        let rVal1 = rf.rd1(toFullRegIndex(dInst.rs1, getInstFields(inst).rs1));
        let rVal2 = rf.rd2(toFullRegIndex(dInst.rs2, getInstFields(inst).rs2));

        // execute instruction
        let execResult = basicExec(dInst, rVal1, rVal2, pc);
        let data = execResult.data;
        let addr = execResult.addr;
        let nextPc = execResult.nextPc;

        // check for next address alignment
        if (nextPc[1:0] != 0 && trap == tagged Invalid) begin
            trap = tagged Valid (tagged Exception InstAddrMisaligned);
        end

`ifdef CONFIG_M
        if (dInst.execFunc matches tagged MulDiv .mulDivInst &&& trap == tagged Invalid) begin
            mulDiv.exec(mulDivInst, rVal1, rVal2);
        end
`endif

        if (dInst.execFunc matches tagged Mem .memInst &&& trap == tagged Invalid) begin
            // check allignment
            Bool aligned = (case (memInst.size)
                                B: True;
                                H: (execResult.addr[0] == 0);
                                W: (execResult.addr[1:0] == 0);
                                D: (execResult.addr[2:0] == 0);
                            endcase);
            if (aligned) begin
                // send the request to the memory
                dmem.request.put( RVDMemReq {
                    op: dInst.execFunc.Mem.op,
                    size: dInst.execFunc.Mem.size,
                    isUnsigned: dInst.execFunc.Mem.isUnsigned,
                    addr: zeroExtend(addr),
                    data: data } );
            end else begin
                // misaligned address exception
                if ((memInst.op == tagged Mem Ld) || (memInst.op == tagged Mem Lr)) begin
                    trap = tagged Valid (tagged Exception LoadAddrMisaligned);
                end else begin
                    trap = tagged Valid (tagged Exception StoreAddrMisaligned);
                end
            end
        end

        // update next pc for fetch stage if no trap
        if (trap == tagged Invalid) begin
            fetchStateEhr[1] <= tagged Valid FetchState{ pc: nextPc };
        end
        // store things for next stage
        writeBackStateEhr[1] <= tagged Valid WriteBackState{
                                                    pc: pc,
                                                    trap: trap,
                                                    dInst: dInst,
                                                    addr: addr,
                                                    data: data
                                                };
    endrule

    rule doWriteBack(writeBackStateEhr[0] matches tagged Valid .writeBackState
                        &&& (writeBackState.dInst.execFunc != tagged System WFI || csrf.wakeFromWFI()));
        let pc = writeBackState.pc;
        let trap = writeBackState.trap;
        let dInst = writeBackState.dInst;
        let inst = dInst.inst;
        let addr = writeBackState.addr;
        let data = writeBackState.data;
        writeBackStateEhr[0] <= tagged Invalid;

`ifdef CONFIG_M
        if (dInst.execFunc matches tagged MulDiv .* &&& trap == tagged Invalid) begin
            data = mulDiv.result_data;
            mulDiv.result_deq;
        end
`endif

        if (dInst.execFunc matches tagged Mem .memInst &&& trap == tagged Invalid) begin
            if (getsResponse(memInst.op)) begin
                data <- dmem.response.get;
            end
        end

        let csrfResult <- csrf.wr(
                pc,
                // performing system instructions
                dInst.execFunc matches tagged System .sysInst ? tagged Valid sysInst : tagged Invalid,
                getInstFields(inst).csr,
                data, // either rf[rs1] or zimm, computed in basicExec
                addr,
                // handling exceptions
                trap,
                // indirect writes
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
                pc: signExtend(pc),
                data: signExtend(fromMaybe(data, maybeData)),
                addr: signExtend(addr),
                instruction: inst,
                dst: {pack(dInst.dst), getInstFields(inst).rd},
                exception: isException,
                interrupt: isInterrupt,
                cause: trapCause } );

        // This split attribute is required to produce multiple rules so the
        // ifetch.response.get method doesn't cause this rule to conflict
        // with the execute rule.
        (* split *)
        if (maybeNextPc matches tagged Valid .replayPc) begin
            // This instruction is not writing to the register file
            // it is either an instruction that requires flushing the pipeline
            // or it caused an exception
            fetchStateEhr[0] <= tagged Valid FetchState{ pc: replayPc };
            // kill other instructions
            if (executeStateEhr[0] matches tagged Valid .*) begin
                let ignore <- ifetch.response.get;
            end
            executeStateEhr[0] <= tagged Invalid;
        end else begin
            // This instruction retired
            // write to the register file
            rf.wr(toFullRegIndex(dInst.dst, getInstFields(inst).rd), fromMaybe(data, maybeData));
        end
    endrule

    method Action start(Addr startPc);
        fetchStateEhr[3] <= tagged Valid FetchState { pc: startPc };
        executeStateEhr[3] <= tagged Invalid;
        writeBackStateEhr[3] <= tagged Invalid;
    endmethod
    method Action stop;
        fetchStateEhr[3] <= tagged Invalid;
        executeStateEhr[3] <= tagged Invalid;
        writeBackStateEhr[3] <= tagged Invalid;
    endmethod

    method ActionValue#(VerificationPacket) getVerificationPacket;
        let verificationPacket = verificationPackets.first;
        verificationPackets.deq;
        return verificationPacket;
    endmethod
endmodule
