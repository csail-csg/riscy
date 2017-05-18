
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

import DefaultValue::*;
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
import RVExec::*;
import RVTypes::*;

import RVAlu::*;
import RVControl::*;
import RVDecode::*;
import RVMemory::*;
`ifdef CONFIG_M
import RVMulDiv::*;
`endif

import CoreStates::*;

interface ExecStage;
endinterface

typedef struct {
    Reg#(Maybe#(FetchState#(xlen))) fs;
    Reg#(Maybe#(ExecuteState#(xlen))) es;
    Reg#(Maybe#(WriteBackState#(xlen))) ws;
    OutputPort#(ReadOnlyMemResp#(2)) ifetchres;
    InputPort#(AtomicMemReq#(32,2)) dmemreq;
    // InputPort#(RVDMemReq) dmemreq;
`ifdef CONFIG_M
    MulDivExec#(xlen) mulDiv;
`endif
    RVCsrFile#(xlen) csrf;
    RVRegFile#(xlen) rf;
} ExecRegs#(numeric type xlen);

module mkExecStage#(ExecRegs#(xlen) er)(ExecStage) provisos (NumAlias#(xlen, 32));

    let ifetchres = er.ifetchres;
    let dmemreq = er.dmemreq;
    let csrf = er.csrf;
    let rf = er.rf;
`ifdef CONFIG_M
    let mulDiv = er.mulDiv;
`endif

    rule doExecute(er.es matches tagged Valid .executeState
                    &&& er.ws == tagged Invalid);
        // get and clear the execute state
        let poisoned = executeState.poisoned;
        let pc = executeState.pc;
        er.es <= tagged Invalid;

        // get the instruction
        let inst = ifetchres.first.data;
        ifetchres.deq;

        if (!poisoned) begin
            // check for interrupts
            Maybe#(TrapCause) trap = tagged Invalid;
            if (csrf.readyInterrupt matches tagged Valid .validInterrupt) begin
                trap = tagged Valid (tagged Interrupt validInterrupt);
            end

            // decode the instruction
            RiscVISASubset misa = defaultValue;
            let maybeDInst = decodeInst(misa.rv64, misa.m, misa.a, misa.f, misa.d, inst);
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
                    // dmemreq.enq( RVDMemReq {
                    //     op: dInst.execFunc.Mem.op,
                    //     size: dInst.execFunc.Mem.size,
                    //     isUnsigned: dInst.execFunc.Mem.isUnsigned,
                    //     addr: zeroExtend(addr),
                    //     data: data } );

                    //// This assumes xlen == 32
                    Bit#(32) aligned_data = data << {addr[1:0], 3'b0};
                    Bit#(4) write_en = dInst.execFunc.Mem.op == tagged Mem Ld ? 0 : 
                                        (case(memInst.size)
                                            B: ('b0001 << addr[1:0]);
                                            H: ('b0011 << addr[1:0]);
                                            W: ('b1111);
                                        endcase);
                    dmemreq.enq( AtomicMemReq {
                        write_en: write_en,
                        atomic_op: None,
                        addr: addr,
                        data: aligned_data} );
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
                er.fs <= tagged Valid FetchState{ pc: nextPc };
            end
            // store things for next stage
            er.ws <= tagged Valid WriteBackState{
                                                        pc: pc,
                                                        trap: trap,
                                                        dInst: dInst,
                                                        addr: addr,
                                                        data: data
                                                    };
        end
    endrule
endmodule
