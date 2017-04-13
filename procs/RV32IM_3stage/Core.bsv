
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

`include "ProcConfig.bsv"

import CoreStates::*;
import FetchStage::*;
import ExecStage::*;
import WriteBackStage::*;

import ClientServer::*;
import GetPut::*;
import Connectable::*;
import DefaultValue::*;
import FIFO::*;
import GetPut::*;

import ClockGate::*;
import Ehr::*;
import Port::*;

import Abstraction::*;
import RegUtil::*;
import RVRFile::*;
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

interface Core;
    method Action start(Addr startPc);
    method Action stop;
    method Maybe#(VerificationPacket) currVerificationPacket;
endinterface

module mkThreeStageCore#(
            ServerPort#(Addr, Instruction) ifetch,
            ServerPort#(RVDMemReq, RVDMemResp) dmem,
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
    Ehr#(2, Maybe#(VerificationPacket)) verificationPacketEhr <- mkEhr(tagged Invalid);

    Bool clock_gate <- exposeCurrentClockGate();
    
    let fetchRegs = FetchRegs{
            fs: fetchStateEhr[2],
            es: executeStateEhr[2],
            ifetchreq: ifetch.request};
    FetchStage f <- mkFetchStage(fetchRegs);

    let execRegs = ExecRegs{
        fs: fetchStateEhr[1],
        es: executeStateEhr[1],
        ws: writeBackStateEhr[1],
        ifetchres: ifetch.response,
        dmemreq: dmem.request,
`ifdef CONFIG_M
        mulDiv: mulDiv,
`endif
        csrf: csrf,
        rf: rf};
    ExecStage e <- mkExecStage(execRegs); 

    let writeBackRegs = WriteBackRegs{ 
        fs: fetchStateEhr[0],
        es: executeStateEhr[0],
        ws: writeBackStateEhr[0],
        dmemres: dmem.response,
`ifdef CONFIG_M
        mulDiv: mulDiv,
`endif
        csrf: csrf,
        rf: rf,
        verificationPackets: verificationPacketEhr[1]};
    WriteBackStage w <- mkWriteBackStage(writeBackRegs);

    rule clearVerificationPacketEhr;
        verificationPacketEhr[0] <= tagged Invalid;
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

    method Maybe#(VerificationPacket) currVerificationPacket;
        return clock_gate ? verificationPacketEhr[0] : tagged Invalid;
    endmethod
endmodule
