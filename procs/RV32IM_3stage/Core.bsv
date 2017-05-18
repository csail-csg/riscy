
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

import Ehr::*;
import MemUtil::*;
import Port::*;

import Abstraction::*;
import RegUtil::*;
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

interface Core#(numeric type xlen);
    method Action start(Bit#(xlen) startPc);
    method Action stop;
    method Action stallPipeline(Bool stall);
    method Maybe#(VerificationPacket) currVerificationPacket;
endinterface

module mkThreeStageCore#(
            ReadOnlyMemServerPort#(xlen, 2) ifetch,
            AtomicMemServerPort#(xlen, TLog#(TDiv#(xlen,8))) dmem,
            Bool ipi,
            Bool timerInterrupt,
            Bit#(64) timer,
            Bool externalInterrupt,
            Bit#(xlen) hartID
        )(Core#(xlen)) provisos (NumAlias#(xlen, 32));

    Reg#(Bool) stallReg <- mkReg(False);

    RVRegFile#(xlen) rf <- mkRVRegFileBypass(False); // make this true if you add an FPU

    // TODO: make this depend on a bool
    // If user mode is supported, use the full CSR File
    RVCsrFile#(xlen) csrf <-
`ifdef CONFIG_U
        mkRVCsrFile(hartID, timer, timerInterrupt, ipi, externalInterrupt);
`else
        mkRVCsrFileMCU(hartID, timer, timerInterrupt, ipi, externalInterrupt);
`endif

    // TODO: make this depend on a bool
`ifdef CONFIG_M
    MulDivExec#(xlen) mulDiv <- mkBoothRoughMulDivExec;
`endif

    Ehr#(4, Maybe#(FetchState#(xlen))) fetchStateEhr <- mkEhr(tagged Invalid);
    Ehr#(4, Maybe#(ExecuteState#(xlen))) executeStateEhr <- mkEhr(tagged Invalid);
    Ehr#(4, Maybe#(WriteBackState#(xlen))) writeBackStateEhr <- mkEhr(tagged Invalid);

    Ehr#(2, Maybe#(VerificationPacket)) verificationPacketEhr <- mkEhr(tagged Invalid);

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
    WriteBackStage w <- mkWriteBackStage(writeBackRegs, stallReg);

    rule clearVerificationPacketEhr;
        verificationPacketEhr[0] <= tagged Invalid;
    endrule

    method Action start(Bit#(xlen) startPc);
        fetchStateEhr[3] <= tagged Valid FetchState { pc: startPc };
        executeStateEhr[3] <= tagged Invalid;
        writeBackStateEhr[3] <= tagged Invalid;
        stallReg <= False;
    endmethod
    method Action stop;
        fetchStateEhr[3] <= tagged Invalid;
        executeStateEhr[3] <= tagged Invalid;
        writeBackStateEhr[3] <= tagged Invalid;
    endmethod

    method Action stallPipeline(Bool stall);
        stallReg <= stall;
    endmethod

    method Maybe#(VerificationPacket) currVerificationPacket;
        return stallReg ? tagged Invalid : verificationPacketEhr[0];
    endmethod
endmodule
