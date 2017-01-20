
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

import Ehr::*;
import RVTypes::*;
import Vector::*;

interface ArchRFile;
    // TODO: change Bit#(5) to named type
    method Action wr(Maybe#(FullRegIndex) fullRegIndex, Data data);
    method Data rd1(Maybe#(FullRegIndex) fullRegIndex);
    method Data rd2(Maybe#(FullRegIndex) fullRegIndex);
    method Data rd3(Maybe#(FullRegIndex) fullRegIndex);
endinterface

// This is a merged GPR/FPU register file
(* synthesize *)
module mkArchRFile( ArchRFile );
    let verbose = False;
    File fout = stdout;

    Vector#(32, Reg#(Data)) gpr_rfile <- replicateM(mkReg(0));
`ifdef CONFIG_F
    Vector#(32, Reg#(Data)) fpu_rfile <- replicateM(mkReg(0));
`else
    Vector#(32, Reg#(Data)) fpu_rfile <- replicateM(mkReadOnlyReg(0));
`endif

    function Data read(Maybe#(FullRegIndex) fullRegIndex);
        return (case (fullRegIndex) matches
                tagged Valid (tagged Gpr 0): 0;
                tagged Valid (tagged Gpr .rIndex): gpr_rfile[rIndex];
                tagged Valid (tagged Fpu .rIndex): fpu_rfile[rIndex];
                default: 0;
            endcase);
    endfunction

    method Action wr(Maybe#(FullRegIndex) fullRegIndex, Data data);
        if (verbose) $fdisplay(fout, fshow(fullRegIndex), " <= %h", data);
        case (fullRegIndex) matches
            tagged Valid (tagged Gpr 0): noAction;
            tagged Valid (tagged Gpr .rIndex): gpr_rfile[rIndex] <= data;
            tagged Valid (tagged Fpu .rIndex): fpu_rfile[rIndex] <= data;
            default: noAction;
        endcase
    endmethod

    method Data rd1(Maybe#(FullRegIndex) fullRegIndex) = read(fullRegIndex);
    method Data rd2(Maybe#(FullRegIndex) fullRegIndex) = read(fullRegIndex);
    method Data rd3(Maybe#(FullRegIndex) fullRegIndex) = read(fullRegIndex);
endmodule

import RegUtil::*;

// wr < {rd1, rd2, rd3}
(* synthesize *)
module mkBypassArchRFile( ArchRFile );
    let verbose = False;
    File fout = stdout;

    Vector#(32, Reg#(Data)) gpr_rfile <- replicateM(mkReg(0));
`ifdef CONFIG_F
    Vector#(32, Reg#(Data)) fpu_rfile <- replicateM(mkReg(0));
`else
    Vector#(32, Reg#(Data)) fpu_rfile <- replicateM(mkReadOnlyReg(0));
`endif
    // gpr_rfile[0]._write = constfn(noAction);
    gpr_rfile[0] = readOnlyReg(0);

    // A write req to gpr 0 is the same as no write request
    Ehr#(2, Tuple2#(FullRegIndex, Data)) writeReq <- mkEhr(tuple2(tagged Gpr 0, 0));

    rule performWrite;
        case (tpl_1(writeReq[1])) matches
            tagged Gpr 0: noAction;
            tagged Gpr .rIndex: gpr_rfile[rIndex] <= tpl_2(writeReq[1]);
            tagged Fpu .rIndex: fpu_rfile[rIndex] <= tpl_2(writeReq[1]);
            default: noAction;
        endcase
        writeReq[1] <= tuple2(tagged Gpr 0, 0);
    endrule

    function Data read(Maybe#(FullRegIndex) fullRegIndex);
        Data result = 0;
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

    method Action wr(Maybe#(FullRegIndex) fullRegIndex, Data data) if (tpl_1(writeReq[0]) == tagged Gpr 0);
        if (verbose) $fdisplay(fout, fshow(fullRegIndex), " <= %h", data);
        writeReq[0] <= tuple2(fromMaybe(tagged Gpr 0, fullRegIndex), data);
    endmethod

    method Data rd1(Maybe#(FullRegIndex) fullRegIndex) = read(fullRegIndex);
    method Data rd2(Maybe#(FullRegIndex) fullRegIndex) = read(fullRegIndex);
    method Data rd3(Maybe#(FullRegIndex) fullRegIndex) = read(fullRegIndex);
endmodule

