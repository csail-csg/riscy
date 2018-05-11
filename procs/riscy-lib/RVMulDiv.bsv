
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
// MulDiv.bsv
// This file contains modules needed for hardware multiplication and division.
// The MulDivExec module abstracts away the ISA implementation simplifying the
// requirements for the hardware multiplier and divider. Multiplier and
// Divider are just a multiplier and a divider that do 65-bit signed math.
// All other details of the ISA is handled in MulDivExec.

import RVTypes::*;
import FIFOF::*;

// Functions for easily checking things about muldiv instructions
function Bool isMul(MulDivFunc func);
  return (case(func)
    Mul, Mulh: True;
    default: False;
  endcase);
endfunction
function Bool isDiv(MulDivFunc func);
  return (case(func)
    Div, Rem: True;
    default: False;
  endcase);
endfunction


interface Multiplier#(numeric type xlen);
  // input
  method Action                          multiply(Bit#(TAdd#(xlen, 1)) multiplicand, Bit#(TAdd#(xlen, 1)) multiplier);
  // output
  method Bool                            result_rdy;
  method Tuple2#(Bit#(xlen), Bit#(xlen)) result_data;
  method Action                          result_deq;
endinterface

interface Divider#(numeric type xlen);
  // input
  method Action                          divide(Bit#(TAdd#(xlen, 1)) dividend, Bit#(TAdd#(xlen, 1)) divisor);
  // output
  method Bool                            result_rdy;
  method Tuple2#(Bit#(xlen), Bit#(xlen)) result_data;
  method Action                          result_deq;
endinterface

// This module takes in the same operands as exec
interface MulDivExec#(numeric type xlen);
    method Action   exec(MulDivInst mdInst, Bit#(xlen) rVal1, Bit#(xlen) rVal2);
    method Bool     notEmpty; // True if there is any instruction in this pipeline
    // output
    method Bool     result_rdy;
    method Bit#(xlen)     result_data;
    method Action   result_deq;
endinterface

module mkBluesimMultiplier(Multiplier#(xlen));
  FIFOF#(Tuple2#(Bit#(xlen), Bit#(xlen))) result_fifo <- mkSizedFIFOF(4);

  method Action multiply(Bit#(TAdd#(xlen, 1)) multiplicand, Bit#(TAdd#(xlen, 1)) multiplier);
    Int#(TAdd#(TAdd#(xlen, xlen), 1)) a = unpack(signExtend(multiplicand));
    Int#(TAdd#(TAdd#(xlen, xlen), 1)) b = unpack(signExtend(multiplier));

    // This is a 65-bit signed multiplication
    // FIXME: Replace this with an efficient multiplication implementation like a booth multiplier
    Bit#(TAdd#(TAdd#(xlen, xlen), 1)) r = pack(a * b);

    Tuple2#(Bit#(xlen), Bit#(xlen)) answer = tuple2( r[2*valueOf(xlen)-1:valueOf(xlen)], r[valueOf(xlen)-1:0] );
    result_fifo.enq(answer);
  endmethod

  method Bool result_rdy = result_fifo.notEmpty;
  method Tuple2#(Bit#(xlen), Bit#(xlen)) result_data = result_fifo.first;
  method Action result_deq = result_fifo.deq;
endmodule

// This is a radix-4 Booth multiplier was taken from the 6.175 Lab
module mkBoothMultiplier(Multiplier#(xlen))
    provisos (
      NumAlias#(TAdd#(xlen, 2),                         _InputSize), // This _could_ be xlen+1 if we tried harder
      NumAlias#(TAdd#(TAdd#(_InputSize, _InputSize), 2),  _MultSize),
      NumAlias#(TAdd#(TLog#(_InputSize), 1),              _IndexSize)
    );
  Reg#(Bit#(_MultSize)) m_neg <- mkReg(0);
  Reg#(Bit#(_MultSize)) m_pos <- mkReg(0);
  Reg#(Bit#(_MultSize)) p <- mkReg(0);
  Reg#(Bit#(_IndexSize)) i <- mkReg(fromInteger(valueOf(_InputSize)/2+1));

  rule mul_step( i < fromInteger(valueOf(_InputSize)/2) );
    let pr = p[2:0];
    Int#(_MultSize) new_p = unpack(p);
    case (pr)
      3'b001: new_p = new_p + unpack(m_pos);
      3'b010: new_p = new_p + unpack(m_pos);
      3'b011: new_p = new_p + unpack(m_pos << 1);
      3'b100: new_p = new_p + unpack(m_neg << 1);
      3'b101: new_p = new_p + unpack(m_neg);
      3'b110: new_p = new_p + unpack(m_neg);
    endcase
    new_p = new_p >> 2;
    p <= pack(new_p);
    i <= i+1;
  endrule

  method Action multiply(Bit#(TAdd#(xlen, 1)) multiplicand, Bit#(TAdd#(xlen, 1)) multiplier) if (i == fromInteger(valueOf(_InputSize)/2+1));
    Bit#(_InputSize) x = signExtend(multiplicand);
    Bit#(_InputSize) y = signExtend(multiplier);
    m_pos <= {msb(x), x, 0};
    m_neg <= {msb(-x), -x, 0};
    p <= {0, y, 1'b0};
    i <= 0;
  endmethod

  method Bool result_rdy;
    return i == fromInteger(valueOf(_InputSize)/2);
  endmethod
  method Tuple2#(Bit#(xlen), Bit#(xlen)) result_data if (i == fromInteger(valueOf(_InputSize)/2));
    // was: return tuple2(p[128:65], p[64:1]);
    return tuple2(p[2*valueOf(xlen):valueOf(xlen)+1], p[valueOf(xlen):1]);
  endmethod
  method Action result_deq if (i == fromInteger(valueOf(_InputSize)/2));
    i <= fromInteger(valueOf(_InputSize)/2+1);
  endmethod
endmodule



module mkBluesimDivider(Divider#(xlen)) provisos (Add#(1, a__, xlen));
  FIFOF#(Tuple2#(Bit#(xlen), Bit#(xlen))) result_fifo <- mkSizedFIFOF(4);

  method Action divide(Bit#(TAdd#(xlen, 1)) dividend, Bit#(TAdd#(xlen, 1)) divisor);
    // This is a 65-bit signed division
    // FIXME: Replace this with an efficient division implementation
    // Bluesim causes a runtime error when dividing by zero, even if the
    // division is part of an unused part of a ternary operation. To avoid
    // this we change the divisor to 1 if it is zero.
    Int#(TAdd#(xlen, 1)) quotent = (divisor != 0) ? (unpack(dividend) / ((divisor != 0) ? unpack(divisor) : unpack(1))) : unpack('1);
    Int#(TAdd#(xlen, 1)) remainder = (divisor != 0) ? (unpack(dividend) % ((divisor != 0) ? unpack(divisor) : unpack(1))) : unpack(dividend);

    if ((dividend == {2'b11, 0}) && (divisor == '1)) begin
      quotent = unpack(dividend);
      remainder = 0;
    end
    result_fifo.enq(tuple2(truncate(pack(quotent)), truncate(pack(remainder))));
  endmethod

  method Bool result_rdy = result_fifo.notEmpty;
  method Tuple2#(Bit#(xlen), Bit#(xlen)) result_data = result_fifo.first;
  method Action result_deq = result_fifo.deq;
endmodule


module mkRoughDivider(Divider#(xlen))
    provisos (
      Add#(1, a__, xlen),
      NumAlias#(TAdd#(xlen, 1),                 _InputSize),
      NumAlias#(TAdd#(_InputSize, _InputSize),  _DivSize),
      NumAlias#(TAdd#(TLog#(_InputSize), 2),    _IndexSize)
    );
  // These are probably bigger than needed. This isn't called a rough divider for nothing
  Reg#(Int#(_DivSize)) remainder <- mkReg(0);
  Reg#(Int#(_DivSize)) quotent <- mkReg(0);
  Reg#(Int#(_DivSize)) divisor_reg <- mkReg(0);
  Reg#(Bit#(_IndexSize)) current_bit <- mkReg(fromInteger(valueOf(_InputSize) + 1));
  Reg#(Bool) quotent_negative <- mkReg(False);
  Reg#(Bool) remainder_negative <- mkReg(False);

  rule doBit(current_bit < fromInteger(valueOf(_InputSize)));
    // add if doesn't change sign
    let tmp_remainder = remainder - (divisor_reg << current_bit);
    if ((((divisor_reg << current_bit) >> current_bit) == divisor_reg) && (msb(tmp_remainder) == 0)) begin
      // it divides!
      remainder <= tmp_remainder;
      quotent <= quotent | (1 << current_bit);
    end
    current_bit <= (current_bit == 0) ? fromInteger(valueOf(_InputSize)) : current_bit - 1;
  endrule

  method Action divide(Bit#(TAdd#(xlen, 1)) dividend, Bit#(TAdd#(xlen, 1)) divisor) if (current_bit == fromInteger(valueOf(_InputSize) + 1));
    // Optimization: Divide by zero and handle signed overflow very fast
    if ((dividend == {2'b11, 0}) && (divisor == '1)) begin
      quotent <= unpack(signExtend(dividend));
      remainder <= 0;
      quotent_negative <= False;
      remainder_negative <= False;
      current_bit <= fromInteger(valueOf(_InputSize));
    end else if (divisor == 0) begin
      quotent <= unpack('1);
      remainder <= unpack(signExtend(dividend));
      quotent_negative <= False;
      remainder_negative <= False;
      current_bit <= fromInteger(valueOf(_InputSize));
    end else begin
      // Lets make everything positive because I can't think about signed division right now
      Bool top_negative = (msb(dividend) == 1);
      Bool bottom_negative = (msb(divisor) == 1);

      quotent <= 0;

      if (top_negative)
        remainder <= -unpack(signExtend(dividend));
      else
        remainder <= unpack(signExtend(dividend));

      if (bottom_negative)
        divisor_reg <= -unpack(signExtend(divisor));
      else
        divisor_reg <= unpack(signExtend(divisor));

      quotent_negative <= (top_negative != bottom_negative);
      remainder_negative <= top_negative;

      Int#(TAdd#(xlen, 1)) quotent = (divisor != 0) ? (unpack(dividend) / ((divisor != 0) ? unpack(divisor) : unpack(1))) : unpack('1);
      Int#(TAdd#(xlen, 1)) remainder = (divisor != 0) ? (unpack(dividend) % ((divisor != 0) ? unpack(divisor) : unpack(1))) : unpack(dividend);

      current_bit <= fromInteger(valueOf(_InputSize)-1);
    end
  endmethod

  method Bool result_rdy;
    return (current_bit == fromInteger(valueOf(_InputSize)));
  endmethod
  method Tuple2#(Bit#(xlen), Bit#(xlen)) result_data if (current_bit == fromInteger(valueOf(_InputSize)));
    Int#(_DivSize) final_quotent = quotent_negative ? -quotent : quotent;
    Int#(_DivSize) final_remainder = remainder_negative ? -remainder : remainder;
    return tuple2(truncate(pack(final_quotent)), truncate(pack(final_remainder)));
  endmethod
  method Action result_deq if (current_bit == fromInteger(valueOf(_InputSize)));
    current_bit <= fromInteger(valueOf(_InputSize) + 1);
  endmethod
endmodule

module mkMulDivExec#(Multiplier#(xlen) mul_unit, Divider#(xlen) div_unit)(MulDivExec#(xlen))
        provisos (Add#(a__, 32, xlen));
  Bool verbose = False;

  // This fifo holds what operation is being done by the unit
  // If the value is invalid, then the result is already in muldiv_exec_fifo
  FIFOF#(MulDivInst) func_fifo <- mkFIFOF();

  method Action exec(MulDivInst mdInst, Bit#(xlen) rVal1, Bit#(xlen) rVal2);
    if (verbose) $display("[MulDiv] ", fshow(mdInst), ", ", fshow(rVal1), ", ", fshow(rVal2) );

    Bit#(TAdd#(xlen, 1)) a = 0;
    Bit#(TAdd#(xlen, 1)) b = 0;
    case (mdInst.sign)
      Signed: begin
        a = signExtend(rVal1);
        b = signExtend(rVal2);
      end
      Unsigned: begin
        a = zeroExtend(rVal1);
        b = zeroExtend(rVal2);
      end
      SignedUnsigned: begin
        a = signExtend(rVal1);
        b = zeroExtend(rVal2);
      end
    endcase

    case (mdInst.func)
      Mul, Mulh : mul_unit.multiply(a, b);
      Div, Rem  : div_unit.divide(a, b);
    endcase

    func_fifo.enq(mdInst);
  endmethod

  method Bool notEmpty = func_fifo.notEmpty;

  // output
  method Bool result_rdy;
    MulDivInst mdInst = func_fifo.first;
    return (isMul(mdInst.func)) ? mul_unit.result_rdy : div_unit.result_rdy;
  endmethod
  method Bit#(xlen) result_data;
    MulDivInst mdInst = func_fifo.first;
    Bit#(xlen) data = (case(mdInst.func)
        Mul  : tpl_2(mul_unit.result_data);
        Mulh : tpl_1(mul_unit.result_data);
        Div  : tpl_1(div_unit.result_data);
        Rem  : tpl_2(div_unit.result_data);
      endcase);
    // correct for w instructions
    if (mdInst.w) begin
      data = signExtend(data[31:0]);
    end
    return data;
  endmethod
  method Action result_deq;
    MulDivInst mdInst = func_fifo.first;

    // For debugging
    // This can't be included in the above method because it is not an Action
    if (verbose) begin
      Bit#(xlen) data = (case(mdInst.func)
          Mul  : tpl_2(mul_unit.result_data);
          Mulh : tpl_1(mul_unit.result_data);
          Div  : tpl_1(div_unit.result_data);
          Rem  : tpl_2(div_unit.result_data);
        endcase);
      // correct for w instructions
      if (mdInst.w) begin
        data = signExtend(data[31:0]);
      end
      $display("[MulDiv] result: ", fshow(data));
    end

    // Actual action
    func_fifo.deq;
    case (mdInst.func)
      Mul, Mulh : mul_unit.result_deq;
      Div, Rem  : div_unit.result_deq;
    endcase
  endmethod
endmodule

module mkBluesimMulDivExec(MulDivExec#(xlen)) provisos (Add#(a__, 32, xlen), Add#(1, b__, xlen));
  Multiplier#(xlen) mul_unit <- mkBluesimMultiplier();
  Divider#(xlen) div_unit <- mkBluesimDivider();
  MulDivExec#(xlen) ifc <- mkMulDivExec(mul_unit, div_unit);
  return ifc;
endmodule

module mkBoothRoughMulDivExec(MulDivExec#(xlen)) provisos (Add#(a__, 32, xlen), Add#(1, b__, xlen));
  Multiplier#(xlen) mul_unit <- mkBoothMultiplier();
  Divider#(xlen) div_unit <- mkRoughDivider();
  MulDivExec#(xlen) ifc <- mkMulDivExec(mul_unit, div_unit);
  return ifc;
endmodule

module mkMulDivExecDummy(MulDivExec#(xlen));
  FIFOF#(Bit#(xlen)) muldiv_exec_fifo <- mkFIFOF();

  method Action exec(MulDivInst mdInst, Bit#(xlen) rVal1, Bit#(xlen) rVal2);
    $fdisplay(stderr, "[ERROR] mkMulDivExecDummy is in use");
    Bit#(xlen) res = 0;
    muldiv_exec_fifo.enq(res);
  endmethod

  method Bool notEmpty = muldiv_exec_fifo.notEmpty;

  // output
  method Bool result_rdy = muldiv_exec_fifo.notEmpty;
  method Bit#(xlen) result_data = muldiv_exec_fifo.first;
  method Action result_deq = muldiv_exec_fifo.deq;
endmodule
