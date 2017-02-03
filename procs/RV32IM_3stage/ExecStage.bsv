import CoreStates::*;

import GetPut::*;

import Abstraction::*;
import RVRFile::*;
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

interface ExecStage;
endinterface

typedef struct {
    Reg#(Maybe#(FetchState)) fs;
    Reg#(Maybe#(ExecuteState)) es;
    Reg#(Maybe#(WriteBackState)) ws;
    Get#(Instruction) ifetchres;
    Put#(RVDMemReq) dmemreq;
`ifdef CONFIG_M
    MulDivExec mulDiv;
`endif
`ifdef CONFIG_U
    // If user mode is supported, use the full CSR File
    RVCsrFile csrf;
`else
    // Otherwise use the M-only CSR File designed for MCUs
    RVCsrFileMCU csrf;
`endif
    ArchRFile rf;
} ExecRegs;

module mkExecStage#(ExecRegs er)(ExecStage);

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
        let inst <- ifetchres.get;

        if (!poisoned) begin
            // check for interrupts
            Maybe#(TrapCause) trap = tagged Invalid;
            if (csrf.readyInterrupt matches tagged Valid .validInterrupt) begin
                trap = tagged Valid (tagged Interrupt validInterrupt);
            end

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
                    dmemreq.put( RVDMemReq {
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
