
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

import Ehr::*;
import Vector::*;

import RegUtil::*;

import RVTypes::*;

interface RVRegFile#(numeric type xlen);
    method Action wr(Maybe#(FullRegIndex) fullRegIndex, Bit#(xlen) data);
    method Bit#(xlen) rd1(Maybe#(FullRegIndex) fullRegIndex);
    method Bit#(xlen) rd2(Maybe#(FullRegIndex) fullRegIndex);
    method Bit#(xlen) rd3(Maybe#(FullRegIndex) fullRegIndex);
endinterface

// This is a merged GPR/FPU register file
module mkRVRegFile#(Bool hasFPU)(RVRegFile#(xlen));
    let verbose = False;
    File fout = stdout;

    Vector#(32, Reg#(Bit#(xlen))) gpr_rfile <- replicateM(mkReg(0));
    gpr_rfile[0] = readOnlyReg(0);
    Vector#(32, Reg#(Bit#(xlen))) fpu_rfile <- hasFPU ? replicateM(mkReg(0)) : replicateM(mkReadOnlyRegError(0, "Trying to write to FPU registers in RVRegFile without FPU registers. Use mkRVRegFile(True) instead."));

    function Bit#(xlen) read(Maybe#(FullRegIndex) fullRegIndex);
        return (case (fullRegIndex) matches
                tagged Valid (tagged Gpr 0): 0;
                tagged Valid (tagged Gpr .rIndex): gpr_rfile[rIndex];
                tagged Valid (tagged Fpu .rIndex): fpu_rfile[rIndex];
                default: 0;
            endcase);
    endfunction

    method Action wr(Maybe#(FullRegIndex) fullRegIndex, Bit#(xlen) data);
        if (verbose) $fdisplay(fout, fshow(fullRegIndex), " <= %h", data);
        case (fullRegIndex) matches
            tagged Valid (tagged Gpr 0): noAction;
            tagged Valid (tagged Gpr .rIndex): gpr_rfile[rIndex] <= data;
            tagged Valid (tagged Fpu .rIndex): fpu_rfile[rIndex] <= data;
            default: noAction;
        endcase
    endmethod

    method Bit#(xlen) rd1(Maybe#(FullRegIndex) fullRegIndex) = read(fullRegIndex);
    method Bit#(xlen) rd2(Maybe#(FullRegIndex) fullRegIndex) = read(fullRegIndex);
    method Bit#(xlen) rd3(Maybe#(FullRegIndex) fullRegIndex) = read(fullRegIndex);
endmodule

// wr < {rd1, rd2, rd3}
module mkRVRegFileBypass#(Bool hasFPU)(RVRegFile#(xlen));
    let verbose = False;
    File fout = stdout;

    Vector#(32, Reg#(Bit#(xlen))) gpr_rfile <- replicateM(mkReg(0));
    gpr_rfile[0] = readOnlyReg(0);
    Vector#(32, Reg#(Bit#(xlen))) fpu_rfile <- hasFPU ? replicateM(mkReg(0)) : replicateM(mkReadOnlyRegError(0, "Trying to write to FPU registers in RVRegFile without FPU registers. Use mkRVRegFileBypass(True) instead."));

    // A write req to gpr 0 is the same as no write request
    Ehr#(2, Tuple2#(FullRegIndex, Bit#(xlen))) writeReq <- mkEhr(tuple2(tagged Gpr 0, 0));

    rule performWrite;
        case (tpl_1(writeReq[1])) matches
            tagged Gpr 0: noAction;
            tagged Gpr .rIndex: gpr_rfile[rIndex] <= tpl_2(writeReq[1]);
            tagged Fpu .rIndex: fpu_rfile[rIndex] <= tpl_2(writeReq[1]);
            default: noAction;
        endcase
        writeReq[1] <= tuple2(tagged Gpr 0, 0);
    endrule

    function Bit#(xlen) read(Maybe#(FullRegIndex) fullRegIndex);
        Bit#(xlen) result = 0;
        if (fullRegIndex matches tagged Valid .validIndex) begin
            if (validIndex == tagged Gpr 0) begin
                result = 0;
            end else if (validIndex == tpl_1(writeReq[1])) begin
                // bypass path from write to read
                result = tpl_2(writeReq[1]);
            end else begin
                result = (case (validIndex) matches
                        tagged Gpr .rIndex: gpr_rfile[rIndex];
                        tagged Fpu .rIndex: fpu_rfile[rIndex];
                    endcase);
            end
        end
        return result;
    endfunction

    method Action wr(Maybe#(FullRegIndex) fullRegIndex, Bit#(xlen) data) if (tpl_1(writeReq[0]) == tagged Gpr 0);
        if (verbose) $fdisplay(fout, fshow(fullRegIndex), " <= %h", data);
        writeReq[0] <= tuple2(fromMaybe(tagged Gpr 0, fullRegIndex), data);
    endmethod

    method Bit#(xlen) rd1(Maybe#(FullRegIndex) fullRegIndex) = read(fullRegIndex);
    method Bit#(xlen) rd2(Maybe#(FullRegIndex) fullRegIndex) = read(fullRegIndex);
    method Bit#(xlen) rd3(Maybe#(FullRegIndex) fullRegIndex) = read(fullRegIndex);
endmodule

(* synthesize, gate_all_clocks *)
module mkRVRegFile32WithFPU(RVRegFile#(32));
    let _m <- mkRVRegFile(True);
    return _m;
endmodule

(* synthesize, gate_all_clocks *)
module mkRVRegFile32WithoutFPU(RVRegFile#(32));
    let _m <- mkRVRegFile(False);
    return _m;
endmodule

(* synthesize, gate_all_clocks *)
module mkRVRegFileBypass32WithFPU(RVRegFile#(32));
    let _m <- mkRVRegFileBypass(True);
    return _m;
endmodule

(* synthesize, gate_all_clocks *)
module mkRVRegFileBypass32WithoutFPU(RVRegFile#(32));
    let _m <- mkRVRegFileBypass(False);
    return _m;
endmodule

(* synthesize, gate_all_clocks *)
module mkRVRegFile64WithFPU(RVRegFile#(64));
    let _m <- mkRVRegFile(True);
    return _m;
endmodule

(* synthesize, gate_all_clocks *)
module mkRVRegFile64WithoutFPU(RVRegFile#(64));
    let _m <- mkRVRegFile(False);
    return _m;
endmodule

(* synthesize, gate_all_clocks *)
module mkRVRegFileBypass64WithFPU(RVRegFile#(64));
    let _m <- mkRVRegFileBypass(True);
    return _m;
endmodule

(* synthesize, gate_all_clocks *)
module mkRVRegFileBypass64WithoutFPU(RVRegFile#(64));
    let _m <- mkRVRegFileBypass(False);
    return _m;
endmodule

typeclass MkRVRegFile#(numeric type xlen);
    module mkSynRVRegFile#(Bool hasFPU)(RVRegFile#(xlen));
    module mkSynRVRegFileBypass#(Bool hasFPU)(RVRegFile#(xlen));
endtypeclass

instance MkRVRegFile#(32);
    module mkSynRVRegFile#(Bool hasFPU)(RVRegFile#(32));
        RVRegFile#(32) _m <- hasFPU ? mkRVRegFile32WithFPU : mkRVRegFile32WithoutFPU;
        return _m;
    endmodule
    module mkSynRVRegFileBypass#(Bool hasFPU)(RVRegFile#(32));
        RVRegFile#(32) _m <- hasFPU ? mkRVRegFileBypass32WithFPU : mkRVRegFileBypass32WithoutFPU;
        return _m;
    endmodule
endinstance

instance MkRVRegFile#(64);
    module mkSynRVRegFile#(Bool hasFPU)(RVRegFile#(64));
        RVRegFile#(64) _m <- hasFPU ? mkRVRegFile64WithFPU : mkRVRegFile64WithoutFPU;
        return _m;
    endmodule
    module mkSynRVRegFileBypass#(Bool hasFPU)(RVRegFile#(64));
        RVRegFile#(64) _m <- hasFPU ? mkRVRegFileBypass64WithFPU : mkRVRegFileBypass64WithoutFPU;
        return _m;
    endmodule
endinstance
