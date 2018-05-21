
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
// Fpu.bsv
// This file contains modules needed for hardware floating-point arithmetic.
// The FpuExec module abstracts away the ISA implementation simplifying the
// requirements for the hardware FPU units.

import RVTypes::*;
import FIFO::*;
import FIFOF::*;
import ClientServer::*;
import GetPut::*;
import Divide::*;
import SquareRoot::*;
import FloatingPoint::*;

function FloatingPoint#(e,m) canonicalNaN = FloatingPoint{sign: False, exp: '1, sfd: 1 << (valueof(m)-1)};

typedef struct {
    Bit#(64) data;
    Bit#(5)  fflags;
} FpuResult deriving(Bits, Eq, FShow);

module mkFullResultSubset(FullResultSubset#(FpuResult, 64));
    method FullResult#(64) updateFullResult(FpuResult x, FullResult#(64) full_result);
        full_result.data = x.data;
        full_result.fflags = x.fflags;
        return full_result;
    endmethod
endmodule

interface FpuExec;
    method Action       exec(FpuInst fInst, RVRoundMode rm, Bit#(64) rVal1, Bit#(64) rVal2, Bit#(64) rVal3);
    method Bool         notEmpty; // True if there is any instruction in this pipeline
    // output
    method Bool         result_rdy;
    method FpuResult    result_data;
    method Action       result_deq;
endinterface

`ifndef USE_DUMMY_FPU

function Tuple2#(FloatingPoint#(e,m), Exception) fmaFP(FloatingPoint#(e,m) in1, FloatingPoint#(e,m) in2, FloatingPoint#(e,m) in3, RoundMode rmode)
        provisos (Add#(a__, TLog#(TAdd#(1, TAdd#(m, 5))), TAdd#(e, 1)),
                  Add#(b__, TLog#(TAdd#(1, TAdd#(TAdd#(m, 1), TAdd#(m, 1)))), TAdd#(e, 1)));
    let {mult_data, mult_exception} = multFP(in1, in2, rmode);
    let {final_data, add_exception} = addFP(mult_data, in3, rmode);
    return tuple2(final_data, mult_exception | add_exception);
endfunction

// Double Precision FPU Pipelines
`ifndef REUSE_FMA
// If reusing the FMA, don't bother compiling these.
// Hopefully this reduces compilation/synthesis time.
(* synthesize, gate_all_clocks *)
module mkDoubleAdd(Server#(Tuple3#(Double, Double, RoundMode), Tuple2#(Double, Exception)));
    let fpu <- mkFloatingPointAdder;
    return fpu;
endmodule
(* synthesize, gate_all_clocks *)
module mkDoubleMult(Server#(Tuple3#(Double, Double, RoundMode), Tuple2#(Double, Exception)));
    let fpu <- mkFloatingPointMultiplier;
    return fpu;
endmodule
`endif
`ifndef NO_FDIV
(* synthesize, gate_all_clocks *)
module mkDoubleDiv(Server#(Tuple3#(Double, Double, RoundMode), Tuple2#(Double, Exception)));
    let int_div <- mkDivider(2);
    let fpu <- mkFloatingPointDivider(int_div);
    return fpu;
endmodule
`endif
`ifndef NO_FSQRT
(* synthesize, gate_all_clocks *)
module mkDoubleSqrt(Server#(Tuple2#(Double, RoundMode), Tuple2#(Double, Exception)));
    let int_sqrt <- mkSquareRooter(3);
    let fpu <- mkFloatingPointSquareRooter(int_sqrt);
    return fpu;
endmodule
`endif
(* synthesize, gate_all_clocks *)
module mkDoubleFMA(Server#(Tuple4#(Maybe#(Double), Double, Double, RoundMode), Tuple2#(Double, Exception)));
    let fpu <- mkFloatingPointFusedMultiplyAccumulate;
    return fpu;
endmodule
// Single Precision FPU Pipelines
// These aren't used anymore, so don't synthesize them
// (* synthesize, gate_all_clocks *)
module mkFloatAdd(Server#(Tuple3#(Float, Float, RoundMode), Tuple2#(Float, Exception)));
    let fpu <- mkFloatingPointAdder;
    return fpu;
endmodule
// (* synthesize, gate_all_clocks *)
module mkFloatMult(Server#(Tuple3#(Float, Float, RoundMode), Tuple2#(Float, Exception)));
    let fpu <- mkFloatingPointMultiplier;
    return fpu;
endmodule
`ifndef NO_FDIV
// (* synthesize, gate_all_clocks *)
module mkFloatDiv(Server#(Tuple3#(Float, Float, RoundMode), Tuple2#(Float, Exception)));
    let int_div <- mkDivider(2);
    let fpu <- mkFloatingPointDivider(int_div);
    return fpu;
endmodule
`endif
`ifndef NO_FSQRT
// (* synthesize, gate_all_clocks *)
module mkFloatSqrt(Server#(Tuple2#(Float, RoundMode), Tuple2#(Float, Exception)));
    let int_sqrt <- mkSquareRooter(3);
    let fpu <- mkFloatingPointSquareRooter(int_sqrt);
    return fpu;
endmodule
`endif
// (* synthesize, gate_all_clocks *)
module mkFloatFMA(Server#(Tuple4#(Maybe#(Float), Float, Float, RoundMode), Tuple2#(Float, Exception)));
    let fpu <- mkFloatingPointFusedMultiplyAccumulate;
    return fpu;
endmodule

module mkFloatWrapperForBinaryOp#(Server#(Tuple3#(Double, Double, RoundMode),Tuple2#(Double, Exception)) double_fpu)(Server#(Tuple3#(Float, Float, RoundMode), Tuple2#(Float, Exception)));
    let verbose = False;
    FIFO#(Tuple2#(RoundMode,Exception)) rmode_exc_fifo <- mkFIFO;
    interface Put request;
        method Action put(Tuple3#(Float, Float, RoundMode) x);
            let rmode = tpl_3(x);
            Double d1; Exception exc1;
            Double d2; Exception exc2;
            {d1, exc1} = convert(tpl_1(x), rmode, True);
            {d2, exc2} = convert(tpl_2(x), rmode, True);
            double_fpu.request.put(tuple3(d1, d2, rmode));
            rmode_exc_fifo.enq(tuple2(rmode, exc1 | exc2));
            if (verbose) $display("    exc1 = ", fshow(exc1));
            if (verbose) $display("    exc2 = ", fshow(exc2));
        endmethod
    endinterface
    interface Get response;
        method ActionValue#(Tuple2#(Float, Exception)) get;
            rmode_exc_fifo.deq;
            let {rmode, exc_in} = rmode_exc_fifo.first;
            let x <- double_fpu.response.get;
            let exc_op = tpl_2(x);
            Float f; Exception exc_conv;
            {f, exc_conv} = convert(tpl_1(x), rmode, True);
            if (verbose) $display("    exc_in = ", fshow(exc_in));
            if (verbose) $display("    exc_op = ", fshow(exc_op));
            if (verbose) $display("    exc_conv = ", fshow(exc_conv));
            return tuple2(f, exc_in | exc_op | exc_conv);
        endmethod
    endinterface
endmodule
module mkFloatWrapperForSqrt#(Server#(Tuple2#(Double, RoundMode),Tuple2#(Double, Exception)) double_fpu)(Server#(Tuple2#(Float, RoundMode), Tuple2#(Float, Exception)));
    FIFO#(Tuple2#(RoundMode,Exception)) rmode_exc_fifo <- mkFIFO;
    interface Put request;
        method Action put(Tuple2#(Float, RoundMode) x);
            let rmode = tpl_2(x);
            Double d1; Exception exc1;
            {d1, exc1} = convert(tpl_1(x), rmode, True);
            double_fpu.request.put(tuple2(d1, rmode));
            rmode_exc_fifo.enq(tuple2(rmode, exc1 ));
        endmethod
    endinterface
    interface Get response;
        method ActionValue#(Tuple2#(Float, Exception)) get;
            rmode_exc_fifo.deq;
            let {rmode, exc_in} = rmode_exc_fifo.first;
            let x <- double_fpu.response.get;
            let exc_op = tpl_2(x);
            Float f; Exception exc_conv;
            {f, exc_conv} = convert(tpl_1(x), rmode, True);
            return tuple2(f, exc_in | exc_op | exc_conv);
        endmethod
    endinterface
endmodule
module mkFloatWrapperForFMA#(Server#(Tuple4#(Maybe#(Double), Double, Double, RoundMode),Tuple2#(Double, Exception)) double_fpu)(Server#(Tuple4#(Maybe#(Float), Float, Float, RoundMode), Tuple2#(Float, Exception)));
    FIFO#(Tuple2#(RoundMode,Exception)) rmode_exc_fifo <- mkFIFO;
    interface Put request;
        method Action put(Tuple4#(Maybe#(Float), Float, Float, RoundMode) x);
            let rmode = tpl_4(x);
            Maybe#(Double) d1_maybe = tagged Invalid;
            Exception exc1 = unpack(0);
            if (isValid(tpl_1(x))) begin
                Double d1;
                {d1, exc1} = convert(fromMaybe(?,tpl_1(x)), rmode, True);
                d1_maybe = tagged Valid d1;
            end
            Double d2; Exception exc2;
            Double d3; Exception exc3;
            {d2, exc2} = convert(tpl_2(x), rmode, True);
            {d3, exc3} = convert(tpl_3(x), rmode, True);
            double_fpu.request.put(tuple4(d1_maybe, d2, d3, rmode));
            rmode_exc_fifo.enq(tuple2(rmode, exc1 | exc2 | exc3));
        endmethod
    endinterface
    interface Get response;
        method ActionValue#(Tuple2#(Float, Exception)) get;
            rmode_exc_fifo.deq;
            let {rmode, exc_in} = rmode_exc_fifo.first;
            let x <- double_fpu.response.get;
            let exc_op = tpl_2(x);
            Float f; Exception exc_conv;
            {f, exc_conv} = convert(tpl_1(x), rmode, True);
            return tuple2(f, exc_in | exc_op | exc_conv);
        endmethod
    endinterface
endmodule
module mkAddWrapperForFMA#(Server#(Tuple4#(Maybe#(ft), ft, ft, RoundMode), Tuple2#(ft, Exception)) fma_module)
                            (Server#(Tuple3#(ft, ft, RoundMode), Tuple2#(ft, Exception)))
                            provisos(Alias#(ft, FloatingPoint#(e,m)));
    interface Put request;
        method Action put(Tuple3#(ft, ft, RoundMode) x);
            let in1 = tpl_1(x);
            let in2 = tpl_2(x);
            let rm = tpl_3(x);
            ft one_const = one(False);
            fma_module.request.put(tuple4(tagged Valid in1, in2, one_const, rm));
        endmethod
    endinterface
    interface Get response;
        method ActionValue#(Tuple2#(ft, Exception)) get;
            let x <- fma_module.response.get();
            return x;
        endmethod
    endinterface
endmodule
module mkMulWrapperForFMA#(Server#(Tuple4#(Maybe#(ft), ft, ft, RoundMode), Tuple2#(ft, Exception)) fma_module)
                            (Server#(Tuple3#(ft, ft, RoundMode), Tuple2#(ft, Exception)))
                            provisos(Alias#(ft, FloatingPoint#(e,m)));
    interface Put request;
        method Action put(Tuple3#(ft, ft, RoundMode) x);
            let in1 = tpl_1(x);
            let in2 = tpl_2(x);
            let rm = tpl_3(x);
            fma_module.request.put(tuple4(tagged Invalid, in1, in2, rm));
        endmethod
    endinterface
    interface Get response;
        method ActionValue#(Tuple2#(ft, Exception)) get;
            let x <- fma_module.response.get();
            return x;
        endmethod
    endinterface
endmodule

// FCVT float -> float functions
function Tuple2#(Double, Exception) fcvt_d_s (Float in, RoundMode rmode);
    return convert(in, rmode, True);
endfunction
function Tuple2#(Float, Exception) fcvt_s_d (Double in, RoundMode rmode);
    return convert(in, rmode, True);
endfunction

// FCVT float -> int functions
function Tuple2#(Bit#(64), Exception) fcvt_l_f (FloatingPoint#(e,m) in, RoundMode rmode);
    return float_to_int(in, False, False, rmode);
endfunction
function Tuple2#(Bit#(64), Exception) fcvt_lu_f (FloatingPoint#(e,m) in, RoundMode rmode);
    return float_to_int(in, False, True, rmode);
endfunction
function Tuple2#(Bit#(64), Exception) fcvt_w_f (FloatingPoint#(e,m) in, RoundMode rmode);
    return float_to_int(in, True, False, rmode);
endfunction
function Tuple2#(Bit#(64), Exception) fcvt_wu_f (FloatingPoint#(e,m) in, RoundMode rmode);
    return float_to_int(in, True, True, rmode);
endfunction

// FCVT int -> float functions
function Tuple2#(FloatingPoint#(e,m), Exception) fcvt_f_l (Bit#(64) in_bits, RoundMode rmode)
        provisos (FixedFloatCVT#(FloatingPoint#(e, m), Int#(64)));
    Int#(64) in = unpack(in_bits);
    return vFixedToFloat(in, 1'b0, rmode);
endfunction
function Tuple2#(FloatingPoint#(e,m), Exception) fcvt_f_lu (Bit#(64) in_bits, RoundMode rmode)
        provisos (FixedFloatCVT#(FloatingPoint#(e, m), UInt#(64)));
    UInt#(64) in = unpack(in_bits);
    return vFixedToFloat(in, 1'b0, rmode);
endfunction
function Tuple2#(FloatingPoint#(e,m), Exception) fcvt_f_w (Bit#(64) in_bits, RoundMode rmode)
        provisos (FixedFloatCVT#(FloatingPoint#(e, m), Int#(32)));
    Int#(32) in = unpack(truncate(in_bits));
    return vFixedToFloat(in, 1'b0, rmode);
endfunction
function Tuple2#(FloatingPoint#(e,m), Exception) fcvt_f_wu (Bit#(64) in_bits, RoundMode rmode)
        provisos (FixedFloatCVT#(FloatingPoint#(e, m), UInt#(32)));
    UInt#(32) in = unpack(truncate(in_bits));
    return vFixedToFloat(in, 1'b0, rmode);
endfunction

function Tuple2#(Bit#(64), Exception) fmin_s(Bit#(64) in1, Bit#(64) in2);
    Float in1_f = unpack(in1[31:0]);
    Float in2_f = unpack(in2[31:0]);
    Float nan_f = qnan(); // canonical NAN
    Exception e = unpack(0);

    if (isSNaN(in1_f) || isSNaN(in2_f) || (isNaN(in1_f) && isNaN(in2_f))) begin
        e.invalid_op = True;
        return tuple2(zeroExtend(pack(nan_f)), e);
    end else if (isNaN(in2_f)) begin
        return tuple2(in1, e);
    end else if (isNaN(in1_f)) begin
        return tuple2(in2, e);
    end else begin
        let signLT = (in1_f.sign && !in2_f.sign);
        let signEQ = in1_f.sign == in2_f.sign;
        let absLT = {in1_f.exp, in1_f.sfd} < {in2_f.exp, in2_f.sfd};
        if (signLT || (signEQ && (in1_f.sign ? !absLT : absLT))) begin
            return tuple2(in1, e);
        end else begin
            return tuple2(in2, e);
        end
    end
endfunction

function Tuple2#(Bit#(64), Exception) fmin_d(Bit#(64) in1, Bit#(64) in2);
    Double in1_f = unpack(in1);
    Double in2_f = unpack(in2);
    Double nan_f = qnan(); // canonical NAN
    Exception e = unpack(0);

    if (isSNaN(in1_f) || isSNaN(in2_f) || (isNaN(in1_f) && isNaN(in2_f))) begin
        e.invalid_op = True;
        return tuple2(pack(nan_f), e);
    end else if (isNaN(in2_f)) begin
        return tuple2(in1, e);
    end else if (isNaN(in1_f)) begin
        return tuple2(in2, e);
    end else begin
        let signLT = (in1_f.sign && !in2_f.sign);
        let signEQ = in1_f.sign == in2_f.sign;
        let absLT = {in1_f.exp, in1_f.sfd} < {in2_f.exp, in2_f.sfd};
        if (signLT || (signEQ && (in1_f.sign ? !absLT : absLT))) begin
            return tuple2(in1, e);
        end else begin
            return tuple2(in2, e);
        end
    end
endfunction

function Tuple2#(Bit#(64), Exception) fmax_s(Bit#(64) in1, Bit#(64) in2);
    Float in1_f = unpack(in1[31:0]);
    Float in2_f = unpack(in2[31:0]);
    Float nan_f = qnan(); // canonical NAN
    Exception e = unpack(0);

    if (isSNaN(in1_f) || isSNaN(in2_f) || (isNaN(in1_f) && isNaN(in2_f))) begin
        e.invalid_op = True;
        return tuple2(zeroExtend(pack(nan_f)), e);
    end else if (isNaN(in2_f)) begin
        return tuple2(in1, e);
    end else if (isNaN(in1_f)) begin
        return tuple2(in2, e);
    end else begin
        let signGT = (!in1_f.sign && in2_f.sign);
        let signEQ = in1_f.sign == in2_f.sign;
        let absGT = {in1_f.exp, in1_f.sfd} > {in2_f.exp, in2_f.sfd};
        if (signGT || (signEQ && (in1_f.sign ? !absGT : absGT))) begin
            return tuple2(in1, e);
        end else begin
            return tuple2(in2, e);
        end
    end
endfunction

function Tuple2#(Bit#(64), Exception) fmax_d(Bit#(64) in1, Bit#(64) in2);
    Double in1_f = unpack(in1);
    Double in2_f = unpack(in2);
    Double nan_f = qnan(); // canonical NAN
    Exception e = unpack(0);

    if (isSNaN(in1_f) || isSNaN(in2_f) || (isNaN(in1_f) && isNaN(in2_f))) begin
        e.invalid_op = True;
        return tuple2(pack(nan_f), e);
    end else if (isNaN(in2_f)) begin
        return tuple2(in1, e);
    end else if (isNaN(in1_f)) begin
        return tuple2(in2, e);
    end else begin
        let signGT = (!in1_f.sign && in2_f.sign);
        let signEQ = in1_f.sign == in2_f.sign;
        let absGT = {in1_f.exp, in1_f.sfd} > {in2_f.exp, in2_f.sfd};
        if (signGT || (signEQ && (in1_f.sign ? !absGT : absGT))) begin
            return tuple2(in1, e);
        end else begin
            return tuple2(in2, e);
        end
    end
endfunction

function Tuple2#(Bit#(64), Exception) float_to_int(FloatingPoint#(e, m) in, Bool is_32bit, Bool is_unsigned, RoundMode rmode);
    // 3 cases of exponents:
    Bit#(64) out = 0;
    Bit#(64) max_val = is_unsigned ? '1 : (is_32bit ? 64'h000000007FFFFFFF : 64'h7FFFFFFFFFFFFFFF);
    Bit#(64) min_val = is_unsigned ? 0 : (is_32bit ? 64'hFFFFFFFF80000000 : 64'h8000000000000000);

    Exception exc = unpack(0);
    if (isNaN(in)) begin
        out = max_val;
        exc.invalid_op = True;
    end else if (isInfinity(in)) begin
        out = in.sign ? min_val : max_val;
        exc.invalid_op = True;
    end else if (isZero(in)) begin
        out = 0;
    end else begin
        // Now actually do the conversion
        Int#(TAdd#(e,TLog#(m))) bias_exp = fromInteger((2**(valueOf(e)-1))-1);
        Int#(TAdd#(e,TLog#(m))) in_exp = unpack(zeroExtend(in.exp));
        // The bottom two bits of int_val will be fractional data.
        // The bottom bit holds information about all bits with lesser
        // significance that were shifted out - same for top bit - this is
        // necessary for rounding and overflow detection.
        Bit#(TAdd#(66,m)) int_val = {64'b1, in.sfd, 2'b0}; // this is 2**m times larger than it should be - we will shift this to correct for that
        int_val = saturating_shift_right(int_val, fromInteger(valueOf(m)) + bias_exp - in_exp);
        
        // do rounding
        // 00 : exact
        // 01 : < 0.5
        // 10 : = 0.5
        // 11 : > 0.5
        Bool round_up = False; // by magnitude (default behavior will be drop bits)
        if (int_val[1:0] != 0) begin
            exc.inexact = True;
            case (rmode)
                Rnd_Nearest_Even:       round_up = (int_val[1:0] == 2'b11) || ((int_val[1:0] == 2'b10) && (int_val[2] == 1));
                Rnd_Nearest_Away_Zero:  round_up = (int_val[1] == 1);
                Rnd_Plus_Inf:           round_up = !in.sign;
                Rnd_Minus_Inf:          round_up = in.sign;
                Rnd_Zero:               round_up = False;
            endcase
        end

        // Take the integer part of int_val and round it up if necessary
        Bit#(TAdd#(64,m)) int_val_rnd = truncateLSB(int_val) + (round_up ? 1 : 0);
        // correct the output sign for negative numbers rounded to 0
        Bool out_sign = (int_val_rnd == 0) ? False : in.sign;

        // Now check to see if int_val_rnd is in range
        Bit#(TAdd#(64,m)) mask_32bit = {0, 32'hFFFFFFFF};
        Bit#(TAdd#(64,m)) mask_64bit = {0, 64'hFFFFFFFFFFFFFFFF};
        if (is_unsigned) begin
            if (out_sign) begin
                // negative number - out of range
                out = 0;
                exc.invalid_op = True;
            end else begin
                // positive number
                if (is_32bit) begin
                    // WU
                    if ((int_val_rnd & mask_32bit) == int_val_rnd) begin
                        Bit#(32) val = truncate(int_val_rnd);
                        out = signExtend(val);
                    end else begin
                        // out of range
                        out = '1;
                        exc.invalid_op = True;
                    end
                end else begin
                    // LU
                    if ((int_val_rnd & mask_64bit) == int_val_rnd) begin
                        out = truncate(int_val_rnd);
                    end else begin
                        // out of range
                        out = '1;
                        exc.invalid_op = True;
                    end
                end
            end
        end else begin
            // signed
            if (is_32bit) begin
                // W
                Bit#(32) max_val = out_sign ? 32'h80000000 : 32'h7FFFFFFF;
                if (((int_val_rnd & mask_32bit) == int_val_rnd) && (truncate(int_val_rnd) <= max_val)) begin
                    Bit#(32) val = truncate(int_val_rnd);
                    val = out_sign ? ((~val) + 1) : val;
                    out = signExtend(val);
                end else begin
                    // out of range
                    out = signExtend(max_val);
                    exc.invalid_op = True;
                end
            end else begin
                // L
                Bit#(64) max_val = out_sign ? 64'h8000000000000000 : 64'h7FFFFFFFFFFFFFFF;
                if (((int_val_rnd & mask_64bit) == int_val_rnd) && (truncate(int_val_rnd) <= max_val)) begin
                    Bit#(64) val = truncate(int_val_rnd);
                    out = out_sign ? ((~val) + 1) : val;
                end else begin
                    // out of range
                    out = max_val;
                    exc.invalid_op = True;
                end
            end
        end
    end
    if (exc.invalid_op) begin
        // by convention
        exc.inexact = False;
    end
    return tuple2(out, exc);
endfunction

function Bit#(n) saturating_shift_right(Bit#(n) in, Int#(m) amt)
        provisos (Add#(a__,1,n));
    // This function saturates in each direction
    Bool amt_sign = msb(amt) == 1;
    Bit#(m) amt_abs = amt_sign ? ((~pack(amt))+1) : pack(amt);
    Bit#(n) shifted = amt_sign ? (in << amt_abs) : (in >> amt_abs);
    Bit#(n) shifted_out_mask = amt_sign ? ~('1 >> amt_abs) : ~('1 << amt_abs);
    Bit#(1) saturated_bit = |(in & shifted_out_mask);
    shifted = amt_sign ? (shifted | {saturated_bit, 0}) : (shifted | {0, saturated_bit});
    return shifted;
endfunction

function Tuple2#(FloatingPoint#(e, m), Exception) int_to_float( Bit#(65) in, Bool is_32bit, Bool is_unsigned, RoundMode rmode )
        provisos (FixedFloatCVT#(FloatingPoint#(e, m), Int#(65)));
    Int#(65) in_signed;
    if (is_32bit && is_unsigned) begin
        in_signed = unpack(zeroExtend(in[31:0]));
    end else if (is_32bit && !is_unsigned) begin
        in_signed = unpack(signExtend(in[31:0]));
    end else if(!is_32bit && is_unsigned) begin
        in_signed = unpack(zeroExtend(in));
    end else if(!is_32bit && !is_unsigned) begin
        in_signed = unpack(signExtend(in));
    end
    return vFixedToFloat(in_signed, 1'b0, rmode);
endfunction

// exec function for simple operations
(* noinline *)
function FpuResult execFpuSimple(FpuInst fpu_inst, RVRoundMode rm, Bit#(64) rVal1, Bit#(64) rVal2);
    FpuResult fpu_result = FpuResult{data: 0, fflags: 0};

    // Convert the Risc-V RVRoundMode to FloatingPoint::RoundMode
    RoundMode fpu_rm = (case (rm)
            RNE:      Rnd_Nearest_Even;
            RTZ:      Rnd_Zero;
            RDN:      Rnd_Minus_Inf;
            RUP:      Rnd_Plus_Inf;
            RMM:      Rnd_Nearest_Away_Zero;
            RDyn:     Rnd_Nearest_Even;
            default:  Rnd_Nearest_Even;
        endcase);

    if (fpu_inst.precision == Single) begin
        // single precision
        Float in1 = unpack(rVal1[31:0]);
        Float in2 = unpack(rVal2[31:0]);
        Float dst = unpack(0);
        Maybe#(Bit#(64)) full_dst = Invalid;
        Exception e = unpack(0);
        let fpu_f = fpu_inst.func;
        // Fpu Decoding
        case (fpu_f)
            // combinational instructions
            FMin:     begin
                Bit#(64) x;
                {x, e} = fmin_s(rVal1, rVal2);
                full_dst = tagged Valid x;
            end
            FMax:     begin
                Bit#(64) x;
                {x, e} = fmax_s(rVal1, rVal2);
                full_dst = tagged Valid x;
            end
            FEq:        dst = unpack(zeroExtend(pack(compareFP(in1, in2) == EQ)));
            FLt:        begin
                dst = unpack(zeroExtend(pack(compareFP(in1, in2) == LT)));
                if (isNaN(in1) || isNaN(in2)) begin
                    e.invalid_op = True;
                end
            end
            FLe:        begin
                dst = unpack(zeroExtend(pack((compareFP(in1, in2) == LT) || (compareFP(in1, in2) == EQ))));
                if (isNaN(in1) || isNaN(in2)) begin
                    e.invalid_op = True;
                end
            end
            // CLASS functions
            FClass: begin
                Bool exp_0s = (in1.exp == 0);
                Bool exp_1s = (in1.exp == '1);
                Bool sfd_0s = (in1.sfd == 0);
                Bit#(10) res = 0;
                res[0] = pack(in1.sign && exp_1s && sfd_0s);                // -inf
                res[1] = pack(in1.sign && !exp_1s && !exp_0s);              // -normal
                res[2] = pack(in1.sign && exp_0s && !sfd_0s);               // -subnormal
                res[3] = pack(in1.sign && exp_0s && sfd_0s);                // -0
                res[4] = pack(!in1.sign && exp_0s && sfd_0s);               // +0
                res[5] = pack(!in1.sign && exp_0s && !sfd_0s);              // +subnormal
                res[6] = pack(!in1.sign && !exp_1s && !exp_0s);             // +normal
                res[7] = pack(!in1.sign && exp_1s && sfd_0s);               // -inf
                res[8] = pack(exp_1s && !sfd_0s && (msb(in1.sfd) == 0));    // signaling NaN
                res[9] = pack(exp_1s && !sfd_0s && (msb(in1.sfd) == 1));    // quiet NaN
                full_dst = tagged Valid zeroExtend(res);
            end
            // Sign Injection
            FSgnj:    begin
                dst = in1;
                dst.sign = in2.sign;
            end
            FSgnjn: begin
                dst = in1;
                dst.sign = !in2.sign;
            end
            FSgnjx: begin
                dst = in1;
                dst.sign = unpack(pack(in1.sign) ^ pack(in2.sign));
            end
            // Float -> Bits
            FMv_XF:     full_dst = tagged Valid signExtend(pack(in1));
            // Bits -> Float
            FMv_FX:     full_dst = tagged Valid zeroExtend(pack(in1));
            // Float -> Float
            FCvt_FF:    begin
                Double in1_double = unpack(rVal1);
                {dst, e} = fcvt_s_d(in1_double, fpu_rm);
                if (isNaN(dst)) dst = canonicalNaN;
            end
            // Float -> Int
            FCvt_WF:    begin
                Bit#(64) dst_bits;
                {dst_bits, e} = fcvt_w_f(in1, fpu_rm);
                full_dst = tagged Valid dst_bits;
            end
            FCvt_WUF: begin
                Bit#(64) dst_bits;
                {dst_bits, e} = fcvt_wu_f(in1, fpu_rm);
                full_dst = tagged Valid dst_bits;
            end
            FCvt_LF:    begin
                Bit#(64) dst_bits;
                {dst_bits, e} = fcvt_l_f(in1, fpu_rm);
                full_dst = tagged Valid dst_bits;
            end
            FCvt_LUF: begin
                Bit#(64) dst_bits;
                {dst_bits, e} = fcvt_lu_f(in1, fpu_rm);
                full_dst = tagged Valid dst_bits;
            end
            // Int -> Float
            FCvt_FW: begin
                {dst, e} = fcvt_f_w(rVal1, fpu_rm);
                if (isNaN(dst)) dst = canonicalNaN;
            end
            FCvt_FWU: begin
                {dst, e} = fcvt_f_wu(rVal1, fpu_rm);
                if (isNaN(dst)) dst = canonicalNaN;
            end
            FCvt_FL: begin
                {dst, e} = fcvt_f_l(rVal1, fpu_rm);
                if (isNaN(dst)) dst = canonicalNaN;
            end
            FCvt_FLU: begin
                {dst, e} = fcvt_f_lu(rVal1, fpu_rm);
                if (isNaN(dst)) dst = canonicalNaN;
            end
        endcase
        fpu_result.data = (full_dst matches tagged Valid .data ? data : zeroExtend(pack(dst)));
        fpu_result.fflags = pack(e);
    end else if (fpu_inst.precision == Double) begin
        // double precision
        Double in1 = unpack(rVal1);
        Double in2 = unpack(rVal2);
        Double dst = unpack(0);
        Maybe#(Bit#(64)) full_dst = Invalid;
        Exception e = unpack(0);
        let fpu_f = fpu_inst.func;
        // Fpu Decoding
        case (fpu_f)
            // combinational instructions
            FMin:     begin
                Bit#(64) x;
                {x, e} = fmin_d(rVal1, rVal2);
                full_dst = tagged Valid x;
            end
            FMax:     begin
                Bit#(64) x;
                {x, e} = fmax_d(rVal1, rVal2);
                full_dst = tagged Valid x;
            end
            FEq:        dst = unpack(zeroExtend(pack(compareFP(in1, in2) == EQ)));
            FLt:        begin
                dst = unpack(zeroExtend(pack(compareFP(in1, in2) == LT)));
                if (isNaN(in1) || isNaN(in2)) begin
                    e.invalid_op = True;
                end
            end
            FLe:        begin
                dst = unpack(zeroExtend(pack((compareFP(in1, in2) == LT) || (compareFP(in1, in2) == EQ))));
                if (isNaN(in1) || isNaN(in2)) begin
                    e.invalid_op = True;
                end
            end
            // CLASS functions
            FClass: begin
                Bool exp_0s = (in1.exp == 0);
                Bool exp_1s = (in1.exp == '1);
                Bool sfd_0s = (in1.sfd == 0);
                Bit#(10) res = 0;
                res[0] = pack(in1.sign && exp_1s && sfd_0s);                // -inf
                res[1] = pack(in1.sign && !exp_1s && !exp_0s);              // -normal
                res[2] = pack(in1.sign && exp_0s && !sfd_0s);               // -subnormal
                res[3] = pack(in1.sign && exp_0s && sfd_0s);                // -0
                res[4] = pack(!in1.sign && exp_0s && sfd_0s);               // +0
                res[5] = pack(!in1.sign && exp_0s && !sfd_0s);              // +subnormal
                res[6] = pack(!in1.sign && !exp_1s && !exp_0s);             // +normal
                res[7] = pack(!in1.sign && exp_1s && sfd_0s);               // -inf
                res[8] = pack(exp_1s && !sfd_0s && (msb(in1.sfd) == 0));    // signaling NaN
                res[9] = pack(exp_1s && !sfd_0s && (msb(in1.sfd) == 1));    // quiet NaN
                full_dst = tagged Valid zeroExtend(res);
            end
            // Sign Injection
            FSgnj:    begin
                dst = in1;
                dst.sign = in2.sign;
            end
            FSgnjn: begin
                dst = in1;
                dst.sign = !in2.sign;
            end
            FSgnjx: begin
                dst = in1;
                dst.sign = unpack(pack(in1.sign) ^ pack(in2.sign));
            end
            // Float -> Bits
            FMv_XF:     full_dst = tagged Valid pack(in1);
            // Bits -> Float
            FMv_FX:     full_dst = tagged Valid pack(in1);
            // Float -> Float
            FCvt_FF:    begin
                Float in1_float = unpack(rVal1[31:0]);
                {dst, e} = fcvt_d_s(in1_float, fpu_rm);
                if (isNaN(dst)) dst = canonicalNaN;
            end
            // Float -> Int
            FCvt_WF:    begin
                Bit#(64) dst_bits;
                {dst_bits, e} = fcvt_w_f(in1, fpu_rm);
                full_dst = tagged Valid dst_bits;
            end
            FCvt_WUF: begin
                Bit#(64) dst_bits;
                {dst_bits, e} = fcvt_wu_f(in1, fpu_rm);
                full_dst = tagged Valid dst_bits;
            end
            FCvt_LF:    begin
                Bit#(64) dst_bits;
                {dst_bits, e} = fcvt_l_f(in1, fpu_rm);
                full_dst = tagged Valid dst_bits;
            end
            FCvt_LUF: begin
                Bit#(64) dst_bits;
                {dst_bits, e} = fcvt_lu_f(in1, fpu_rm);
                full_dst = tagged Valid dst_bits;
            end
            // Int -> Float
            FCvt_FW: begin
                {dst, e} = fcvt_f_w(rVal1, fpu_rm);
                if (isNaN(dst)) dst = canonicalNaN;
            end
            FCvt_FWU: begin
                {dst, e} = fcvt_f_wu(rVal1, fpu_rm);
                if (isNaN(dst)) dst = canonicalNaN;
            end
            FCvt_FL: begin
                {dst, e} = fcvt_f_l(rVal1, fpu_rm);
                if (isNaN(dst)) dst = canonicalNaN;
            end
            FCvt_FLU: begin
                {dst, e} = fcvt_f_lu(rVal1, fpu_rm);
                if (isNaN(dst)) dst = canonicalNaN;
            end
        endcase
        fpu_result.data = (full_dst matches tagged Valid .data ? data : pack(dst));
        fpu_result.fflags = pack(e);
    end
    return fpu_result;
endfunction

(* synthesize, gate_all_clocks *)
module mkFpuExecPipeline(FpuExec);
    FIFO#(FpuResult) fpu_exec_fifo <- mkFIFO; // in parallel with pipelined FPUs
    FIFO#(FpuInst) fpu_func_fifo <- mkFIFO; // in parallel with pipelined FPUs
    FIFOF#(FpuResult) fpu_exec_fifo_out <- mkFIFOF; // all pipelined FPUs dequeue into this

    // Pipelined units
    // Double
    let double_fma <- mkDoubleFMA;

`ifdef REUSE_FMA
    let double_add <- mkAddWrapperForFMA(double_fma);
    let double_mult <- mkMulWrapperForFMA(double_fma);
`else
    let double_add <- mkDoubleAdd;
    let double_mult <- mkDoubleMult;
`endif

`ifndef NO_FDIV
    let double_div <- mkDoubleDiv;
`endif
`ifndef NO_FSQRT
    let double_sqrt <- mkDoubleSqrt;
`endif

    // // Float
    // let float_add <- mkFloatAdd;
    // let float_mult <- mkFloatMult;
    // let float_div <- mkFloatDiv;
    // let float_sqrt <- mkFloatSqrt;
    // let float_fma <- mkFloatFMA;

    // Float ops implemented with Double FPUs
    let float_fma <- mkFloatWrapperForFMA(double_fma);
    let float_add <- mkFloatWrapperForBinaryOp(double_add);
    let float_mult <- mkFloatWrapperForBinaryOp(double_mult);
`ifndef NO_FDIV
    let float_div <- mkFloatWrapperForBinaryOp(double_div);
`endif
`ifndef NO_FSQRT
    let float_sqrt <- mkFloatWrapperForSqrt(double_sqrt);
`endif

    rule finish;
        let x = fpu_exec_fifo.first;
        let fpu_inst = fpu_func_fifo.first;
        let fpu_f = fpu_inst.func;
        fpu_exec_fifo.deq;
        fpu_func_fifo.deq;

        if (fpu_inst.precision == Single) begin
            Float out = unpack(0);
            Exception exc = unpack(0);
            Bool pipeline_result = False;
            // Fpu Decoding
            case (fpu_f)
                // pipeline instructions
                FAdd:   begin {out, exc} <- float_add.response.get; pipeline_result = True; end
                FSub:   begin {out, exc} <- float_add.response.get; pipeline_result = True; end
                FMul:   begin {out, exc} <- float_mult.response.get; pipeline_result = True; end
`ifndef NO_FDIV
                FDiv:   begin {out, exc} <- float_div.response.get; pipeline_result = True; end
`endif
`ifndef NO_FSQRT
                FSqrt:  begin {out, exc} <- float_sqrt.response.get; pipeline_result = True; end
`endif
                FMAdd:  begin {out, exc} <- float_fma.response.get; pipeline_result = True; end
                FMSub:  begin {out, exc} <- float_fma.response.get; pipeline_result = True; end
                FNMSub: begin {out, exc} <- float_fma.response.get; out = -out; pipeline_result = True; end
                FNMAdd: begin {out, exc} <- float_fma.response.get; out = -out; pipeline_result = True; end
            endcase
            if (pipeline_result) begin
                // canonicalize NaNs
                if (isNaN(out)) out = canonicalNaN;
                // update data and exception in x
                x.data = zeroExtend(pack(out));
                x.fflags = pack(exc);
            end
        end else if (fpu_inst.precision == Double) begin
            Double out = unpack(0);
            Exception exc = unpack(0);
            Bool pipeline_result = False;
            // Fpu Decoding
            case (fpu_f)
                // pipeline instructions
                FAdd:   begin {out, exc} <- double_add.response.get; pipeline_result = True; end
                FSub:   begin {out, exc} <- double_add.response.get; pipeline_result = True; end
                FMul:   begin {out, exc} <- double_mult.response.get; pipeline_result = True; end
`ifndef NO_FDIV
                FDiv:   begin {out, exc} <- double_div.response.get; pipeline_result = True; end
`endif
`ifndef NO_FSQRT
                FSqrt:  begin {out, exc} <- double_sqrt.response.get; pipeline_result = True; end
`endif
                FMAdd:  begin {out, exc} <- double_fma.response.get; pipeline_result = True; end
                FMSub:  begin {out, exc} <- double_fma.response.get; pipeline_result = True; end
                FNMSub: begin {out, exc} <- double_fma.response.get; out = -out; pipeline_result = True; end
                FNMAdd: begin {out, exc} <- double_fma.response.get; out = -out; pipeline_result = True; end
            endcase
            if (pipeline_result) begin
                // canonicalize NaNs
                if (isNaN(out)) out = canonicalNaN;
                // update data and exception in x
                x.data = pack(out);
                x.fflags = pack(exc);
            end
        end
        fpu_exec_fifo_out.enq(x);
    endrule

    method Action exec(FpuInst fpu_inst, RVRoundMode rm, Bit#(64) rVal1, Bit#(64) rVal2, Bit#(64) rVal3);
        // Convert the Risc-V RVRoundMode to FloatingPoint::RoundMode
        RoundMode fpu_rm = (case (rm)
                RNE:        Rnd_Nearest_Even;
                RTZ:        Rnd_Zero;
                RDN:        Rnd_Minus_Inf;
                RUP:        Rnd_Plus_Inf;
                RMM:        Rnd_Nearest_Away_Zero;
                RDyn:       Rnd_Nearest_Even;
                default:    Rnd_Nearest_Even;
            endcase);

        FpuResult fpu_result = execFpuSimple(fpu_inst, rm, rVal1, rVal2);

        if (fpu_inst.precision == Single) begin
            // single precision
            Float in1 = unpack(rVal1[31:0]);
            Float in2 = unpack(rVal2[31:0]);
            Float in3 = unpack(rVal3[31:0]);
            Float dst = unpack(0);
            Maybe#(Bit#(64)) full_dst = Invalid;
            Exception e = unpack(0);
            let fpu_f = fpu_inst.func;
            // Fpu Decoding
            case (fpu_f)
                // pipeline instructions
                FAdd:   float_add.request.put(tuple3(in1, in2, fpu_rm));
                FSub:   float_add.request.put(tuple3(in1, -in2, fpu_rm));
                FMul:   float_mult.request.put(tuple3(in1, in2, fpu_rm));
`ifndef NO_FDIV
                FDiv:   float_div.request.put(tuple3(in1, in2, fpu_rm));
`endif
`ifndef NO_FSQRT
                FSqrt:  float_sqrt.request.put(tuple2(in1, fpu_rm));
`endif
                FMAdd:  float_fma.request.put(tuple4(tagged Valid in3, in1, in2, fpu_rm));
                FMSub:  float_fma.request.put(tuple4(tagged Valid (-in3), in1, in2, fpu_rm));
                FNMSub: float_fma.request.put(tuple4(tagged Valid (-in3), in1, in2, fpu_rm));
                FNMAdd: float_fma.request.put(tuple4(tagged Valid in3, in1, in2, fpu_rm));
            endcase
        end else if (fpu_inst.precision == Double) begin
            // double precision
            Double in1 = unpack(rVal1);
            Double in2 = unpack(rVal2);
            Double in3 = unpack(rVal3);
            Double dst = unpack(0);
            Maybe#(Bit#(64)) full_dst = Invalid;
            Exception e = unpack(0);
            let fpu_f = fpu_inst.func;
            // Fpu Decoding
            case (fpu_f)
                // pipeline instructions
                FAdd:   double_add.request.put(tuple3(in1, in2, fpu_rm));
                FSub:   double_add.request.put(tuple3(in1, -in2, fpu_rm));
                FMul:   double_mult.request.put(tuple3(in1, in2, fpu_rm));
`ifndef NO_FDIV
                FDiv:   double_div.request.put(tuple3(in1, in2, fpu_rm));
`endif
`ifndef NO_FSQRT
                FSqrt:  double_sqrt.request.put(tuple2(in1, fpu_rm));
`endif
                FMAdd:  double_fma.request.put(tuple4(tagged Valid in3, in1, in2, fpu_rm));
                FMSub:  double_fma.request.put(tuple4(tagged Valid (-in3), in1, in2, fpu_rm));
                FNMSub: double_fma.request.put(tuple4(tagged Valid (-in3), in1, in2, fpu_rm));
                FNMAdd: double_fma.request.put(tuple4(tagged Valid in3, in1, in2, fpu_rm));
            endcase
        end
        fpu_exec_fifo.enq(fpu_result);
        fpu_func_fifo.enq(fpu_inst);
    endmethod

    method Bool         notEmpty = fpu_exec_fifo_out.notEmpty;
    // output
    method Bool       result_rdy = fpu_exec_fifo_out.notEmpty;
    method FpuResult result_data = fpu_exec_fifo_out.first;
    method Action     result_deq = fpu_exec_fifo_out.deq;
endmodule

`else

(* synthesize, gate_all_clocks *)
module mkFpuExecPipeline(FpuExec);
    FIFOF#(FpuResult) fpu_exec_fifo <- mkFIFOF;

    method Action exec(FpuInst fpu_inst, RVRoundMode rm, Bit#(64) rVal1, Bit#(64) rVal2, Bit#(64) rVal3);
        $fdisplay(stderr, "[ERROR] mkFpuExecDummy is in use");
        // don't do the function...
        FpuResult res = unpack(0);
        // ...and enqueue it into fpu_exec_fifo
        fpu_exec_fifo.enq(res);
    endmethod

    method Bool         notEmpty = fpu_exec_fifo.notEmpty;
    // output
    method Bool       result_rdy = fpu_exec_fifo.notEmpty;
    method FpuResult result_data = fpu_exec_fifo.first;
    method Action     result_deq = fpu_exec_fifo.deq;
endmodule

`endif
