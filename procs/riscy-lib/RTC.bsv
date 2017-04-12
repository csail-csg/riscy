
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

import ClientServer::*;
import GetPut::*;
import Vector::*;
import BuildVector::*;
import Ehr::*;

import Abstraction::*;
import MemoryMappedServer::*;

interface RTC#(numeric type cores);
    // memory-mapped interface
    // 0x0000 = timer
    // 0x0008 = timecmp0
    // 0x0010 = timecmp1
    //  ...
    interface UncachedMemServerPort memifc;
    method Bit#(64) timerValue;
    method Vector#(cores, Bool) timerInterrupt;
endinterface

`ifdef CONFIG_RV32
// This is only supported on RV32 systems
// Only supports full-word memory accesses
module mkRTC_RV32(RTC#(1));
    // memory mapped registers
    Reg#(Bit#(32)) timeRegLo <- mkReg(0);
    Reg#(Bit#(32)) timeRegHi <- mkReg(0);
    Reg#(Bit#(32)) timeCmpLo <- mkReg(0);
    Reg#(Bit#(32)) timeCmpHi <- mkReg(0);

    Bool timerInterruptEn = {timeRegHi, timeRegLo} >= {timeCmpHi, timeCmpLo};

    Vector#(4, Reg#(Bit#(32))) memoryMappedRegisters = vec(
        asReg(timeRegLo),
        asReg(timeRegHi),
        asReg(timeCmpLo),
        asReg(timeCmpHi));
    UncachedMemServerPort memoryMappedIfc <- mkMemoryMappedServerPort(memoryMappedRegisters);

    rule incrementTimer;
        Bit#(64) timeValue = {timeRegHi, timeRegLo};
        Bit#(64) newTimeValue = timeValue + 1;
        timeRegLo <= newTimeValue[31:0];
        timeRegHi <= newTimeValue[63:32];
    endrule

    interface UncachedMemServerPort memifc = memoryMappedIfc;
    method Bit#(64) timerValue = {timeRegHi, timeRegLo};
    method Vector#(1, Bool) timerInterrupt = vec(timerInterruptEn);
endmodule
`endif

`ifdef CONFIG_RV64
// This is only supported on RV64 systems
// Only supports full-word memory accesses
module mkRTC_RV64(RTC#(1))
        provisos (NumAlias#(internalAddrSize, 4));
    // Address space:
    Bit#(internalAddrSize) timerAddr   = 'h0;
    Bit#(internalAddrSize) timeCmpAddr = 'h8;

    Reg#(Bit#(64)) timeReg <- mkReg(0);
    Reg#(Bit#(64)) timeCmp <- mkReg(0);

    Ehr#(2, Maybe#(Tuple2#(Bool, Bit#(internalAddrSize)))) pendingReq <- mkEhr(tagged Invalid);

    Bool timerInterruptEn = timeReg >= timeCmp;

    rule incrementTimer;
        timeReg <= timeReg + 1;
    endrule

    interface UncachedMemServer memifc;
        interface Put request;
            method Action put(UncachedMemReq req) if (!isValid(pendingReq[1]));
                if (req.write) begin
                    case (truncate(req.addr))
                        timerAddr:      timeReg <= req.data;
                        timeCmpAddr:    timeCmp <= req.data;
                        default:        noAction;
                    endcase
                    pendingReq[1] <= tagged Valid tuple2(True, truncate(req.addr));
                end else begin
                    pendingReq[1] <= tagged Valid tuple2(False, truncate(req.addr));
                end
            endmethod
        endinterface
        interface Get response;
            method ActionValue#(UncachedMemResp) get if (pendingReq[0] matches tagged Valid .reqTuple);
                Bool write = tpl_1(reqTuple);
                Bit#(internalAddrSize) addr = tpl_2(reqTuple);
                Bit#(64) retVal = 0;
                case (truncate(addr))
                    timerAddr:      retVal = timeReg;
                    timeCmpAddr:    retVal = timeCmp;
                    default:        retVal = 0;
                endcase
                pendingReq[0] <= tagged Invalid;
                return UncachedMemResp{ write: write, data: write ? 0 : retVal };
            endmethod
        endinterface
    endinterface
    method Bit#(64) timerValue = timeReg;
    method Vector#(1, Bool) timerInterrupt = vec(timerInterruptEn);
endmodule
`endif
