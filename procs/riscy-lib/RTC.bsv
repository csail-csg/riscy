
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

import BuildVector::*;
import ClientServer::*;
import ConfigReg::*;
import GetPut::*;
import Vector::*;

import Ehr::*;
import PolymorphicMem::*;
import Port::*;

import Abstraction::*;

interface RTC#(numeric type cores, type memIfcT);
    // memory-mapped interface
    // 0x0000 = timer
    // 0x0008 = timecmp0
    // 0x0010 = timecmp1
    //  ...
    interface memIfcT memifc;
    method Bit#(64) timerValue;
    method Vector#(cores, Bool) timerInterrupt;
endinterface

// This is only supported on RV32 systems
// Only supports full-word memory accesses
module mkRTC_RV32(RTC#(1, ServerPort#(reqT, respT))) provisos (MkPolymorphicMemFromRegs#(reqT, respT, 4, 32));
    // memory mapped registers
    // make the time registers config registers to avoid complicated
    // scheduling constraints between the memory system and the CSRF
    Reg#(Bit#(32)) timeRegLo <- mkConfigReg(0);
    Reg#(Bit#(32)) timeRegHi <- mkConfigReg(0);
    Reg#(Bit#(32)) timeCmpLo <- mkConfigReg(0);
    Reg#(Bit#(32)) timeCmpHi <- mkConfigReg(0);

    Bool timerInterruptEn = {timeRegHi, timeRegLo} >= {timeCmpHi, timeCmpLo};

    Vector#(4, Reg#(Bit#(32))) memoryMappedRegisters = vec(
        asReg(timeRegLo),  // 0x00
        asReg(timeRegHi),  // 0x04
        asReg(timeCmpLo),  // 0x08
        asReg(timeCmpHi)); // 0x0C
    ServerPort#(reqT, respT) memoryMappedIfc <- mkPolymorphicMemFromRegs(memoryMappedRegisters);

    rule incrementTimer;
        Bit#(64) timeValue = {timeRegHi, timeRegLo};
        Bit#(64) newTimeValue = timeValue + 1;
        timeRegLo <= newTimeValue[31:0];
        timeRegHi <= newTimeValue[63:32];
    endrule

    interface ServerPort memifc = memoryMappedIfc;
    method Bit#(64) timerValue = {timeRegHi, timeRegLo};
    method Vector#(1, Bool) timerInterrupt = vec(timerInterruptEn);
endmodule

// This is only supported on RV64 systems
// Only supports full-word memory accesses
// Also, this doesn't support polymorphic mem yet
module mkRTC_RV64(RTC#(1, ServerPort#(reqT, respT))) provisos (MkPolymorphicMemFromRegs#(reqT, respT, 2, 64));
    // memory mapped registers
    // make the time registers config registers to avoid complicated
    // scheduling constraints between the memory system and the CSRF
    Reg#(Bit#(64)) timeReg <- mkConfigReg(0);
    Reg#(Bit#(64)) timeCmp <- mkConfigReg(0);

    Bool timerInterruptEn = timeReg >= timeCmp;

    Vector#(2, Reg#(Bit#(64))) memoryMappedRegisters = vec(
        asReg(timeReg),  // 0x00
        asReg(timeCmp)); // 0x08
    ServerPort#(reqT, respT) memoryMappedIfc <- mkPolymorphicMemFromRegs(memoryMappedRegisters);

    rule incrementTimer;
        timeReg <= timeReg + 1;
    endrule

    interface ServerPort memifc = memoryMappedIfc;
    method Bit#(64) timerValue = timeReg;
    method Vector#(1, Bool) timerInterrupt = vec(timerInterruptEn);
endmodule
