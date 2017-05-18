
// Copyright (c) 2017 Massachusetts Institute of Technology

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

import FIFO::*;
import GetPut::*;

import MemUtil::*;
import Port::*;

import Abstraction::*;
import RVRegFile::*;
`ifdef CONFIG_U
import RVCsrFile::*;
`else
import RVCsrFileMCU::*;
`endif
import RVTypes::*;
import VerificationPacket::*;

import RVMemory::*;
`ifdef CONFIG_M
import RVMulDiv::*;
`endif

import CoreStates::*;

interface WriteBackStage;
endinterface

typedef struct {
    Reg#(Maybe#(FetchState#(xlen))) fs;
    Reg#(Maybe#(ExecuteState#(xlen))) es;
    Reg#(Maybe#(WriteBackState#(xlen))) ws;
    // OutputPort#(RVDMemResp) dmemres;
    OutputPort#(AtomicMemResp#(2)) dmemres;
`ifdef CONFIG_M
    MulDivExec#(xlen) mulDiv;
`endif
    RVCsrFile#(xlen) csrf;
    RVRegFile#(xlen) rf;
    Reg#(Maybe#(VerificationPacket)) verificationPackets;
} WriteBackRegs#(numeric type xlen);

module mkWriteBackStage#(WriteBackRegs#(xlen) wr, Bool stall)(WriteBackStage) provisos (NumAlias#(xlen, 32));
    let dmemres = wr.dmemres;
    let csrf = wr.csrf;
    let rf = wr.rf;
`ifdef CONFIG_M
    let mulDiv = wr.mulDiv;
`endif

    rule doWriteBack(wr.ws matches tagged Valid .writeBackState
                        &&& (writeBackState.dInst.execFunc != tagged System WFI || csrf.wakeFromWFI())
                        &&& !stall);
        let pc = writeBackState.pc;
        let trap = writeBackState.trap;
        let dInst = writeBackState.dInst;
        let inst = dInst.inst;
        let addr = writeBackState.addr;
        let data = writeBackState.data;
        wr.ws <= tagged Invalid;

`ifdef CONFIG_M
        if (dInst.execFunc matches tagged MulDiv .* &&& trap == tagged Invalid) begin
            data = mulDiv.result_data;
            mulDiv.result_deq;
        end
`endif

        if (dInst.execFunc matches tagged Mem .memInst &&& trap == tagged Invalid) begin
            if (getsResponse(memInst.op)) begin
                data = dmemres.first.data >> {addr[1:0], 3'b0};
                let extendFunc = memInst.isUnsigned ? zeroExtend : signExtend;
                data = (case (memInst.size)
                        B: extendFunc(data[7:0]);
                        H: extendFunc(data[15:0]);
                        W: extendFunc(data[31:0]);
                    endcase);
            end
            dmemres.deq;
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
        wr.verificationPackets <= tagged Valid VerificationPacket {
                skippedPackets: 0,
                pc: signExtend(pc),
                data: signExtend(fromMaybe(data, maybeData)),
                addr: signExtend(addr),
                instruction: inst,
                dst: {pack(dInst.dst), getInstFields(inst).rd},
                exception: isException,
                interrupt: isInterrupt,
                cause: trapCause };

        if (maybeNextPc matches tagged Valid .replayPc) begin
            // This instruction is not writing to the register file
            // it is either an instruction that requires flushing the pipeline
            // or it caused an exception
            wr.fs <= tagged Valid FetchState{ pc: replayPc };
            // kill other instructions
            if (wr.es matches tagged Valid .validExecuteState) begin
                wr.es <= tagged Valid ExecuteState{ poisoned: True, pc: validExecuteState.pc };
            end
        end else begin
            // This instruction retired
            // write to the register file
            rf.wr(toFullRegIndex(dInst.dst, getInstFields(inst).rd), fromMaybe(data, maybeData));
        end
    endrule
endmodule
