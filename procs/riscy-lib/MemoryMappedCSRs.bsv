
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
import GetPut::*;
import Vector::*;

import CompareProvisos::*;
import Ehr::*;

import Abstraction::*;
import RVTypes::*;

interface MemoryMappedCSRs#(numeric type cores);
    // memory-mapped interface
    // 0x0000 = timer
    // 0x0008 = timecmp0
    // 0x0010 = timecmp1
    //  ...
    // 0x1000 = ipi0
    // 0x2000 = ipi1
    //  ...
    interface UncachedMemServer memifc;
    method Bit#(64) timerValue;
    method Vector#(cores, Bool) timerInterrupt;
    method Vector#(cores, Bool) ipi;
endinterface

module mkMemoryMappedCSRs#(PAddr baseaddr)(MemoryMappedCSRs#(cores)) provisos (LT#(cores, 16));
`ifdef rv32
    // TODO: needs to support single-word writes to support RV32
    warningM("mkMemoryMappedCSRs does not support RV32 yet");
`else
    // this doesn't work for 16 or more cores since it assumes a 16 bit address space
    Reg#(Maybe#(UncachedMemResp)) resp <- mkReg(tagged Invalid);

    Reg#(Bit#(10)) subTimer <- mkReg(0);
    Reg#(Bit#(64)) timer <- mkReg(0);
    Ehr#(2, Maybe#(Bit#(64))) newTimeEhr <- mkEhr(tagged Invalid);
    Vector#(cores, Reg#(Bit#(64))) timeCmp <- replicateM(mkReg('1));
    Vector#(cores, Reg#(Bool)) ipiReg <- replicateM(mkReg(False));

    rule incrementTimer;
        if (newTimeEhr[1] matches tagged Valid .validNewTime) begin
            subTimer <= 0;
            timer <= validNewTime;
        end else begin
            Bool overflow = subTimer == 999;
            subTimer <= overflow ? 0 : subTimer + 1;
            timer <= overflow ? timer + 1 : timer;
        end
        newTimeEhr[1] <= tagged Invalid;
    endrule

    interface UncachedMemServer memifc;
        interface Put request;
            method Action put(UncachedMemReq req) if (!isValid(resp));
                UncachedMemResp newResp = UncachedMemResp{write: req.write, data: 0};
                Bit#(16) addr = truncate(req.addr - baseaddr);
                if (addr < 16'h1000) begin
                    // RTC registers
                    if (((addr & 16'h0007) == 0) && (req.size == D)) begin
                        let index = addr >> 3;
                        if (index <= fromInteger(valueof(cores))) begin
                            if (index == 0) begin
                                if (req.write) begin
                                    newTimeEhr[0] <= tagged Valid req.data;
                                end else begin
                                    newResp.data = timer;
                                end
                            end else begin
                                if (req.write) begin
                                    timeCmp[index] <= req.data;
                                end else begin
                                    newResp.data = timeCmp[index];
                                end
                            end
                        end else begin
                            $fdisplay(stderr, "[ERROR] MemoryMappedCSRs: unexpected mem request: ", fshow(req));
                        end
                    end else begin
                        $fdisplay(stderr, "[ERROR] MemoryMappedCSRs: unexpected mem request: ", fshow(req));
                    end
                end else begin
                    // IPI registers
                    if ((addr & 16'h0FFF) == 0) begin
                        let index = addr >> 12;
                        if (index < fromInteger(valueof(cores))) begin
                            if (req.write) begin
                                ipiReg[index] <= unpack(req.data[0]);
                            end else begin
                                newResp.data = zeroExtend(pack(ipiReg[index]));
                            end
                        end else begin
                            $fdisplay(stderr, "[ERROR] MemoryMappedCSRs: unexpected mem request: ", fshow(req));
                        end
                    end else begin
                        $fdisplay(stderr, "[ERROR] MemoryMappedCSRs: unexpected mem request: ", fshow(req));
                    end
                end
                resp <= tagged Valid newResp;
            endmethod
        endinterface
        interface Get response;
            method ActionValue#(UncachedMemResp) get if (resp matches tagged Valid .validResp);
                resp <= tagged Invalid;
                return validResp;
            endmethod
        endinterface
    endinterface
    method Bit#(64) timerValue = timer;
    method Vector#(cores, Bool) timerInterrupt = zipWith( \>= , replicate(timer), readVReg(timeCmp));
    method Vector#(cores, Bool) ipi = readVReg(ipiReg);
`endif
endmodule
