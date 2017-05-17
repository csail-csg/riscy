
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

import BRAM::*;
import BuildVector::*;
import Vector::*;

import ConcatReg::*;
import Ehr::*;
import MemUtil::*;
import PolymorphicMem::*;
import Port::*;
import RegUtil::*;

import Abstraction::*;
import RVExec::*;
import RVTypes::*;

typedef struct {
    Addr bootrom_addr;
    Addr start_addr;
    Addr config_string_addr;
} BootRomConfig deriving (Eq);

module mkBasicBootRom32#(BootRomConfig cfg)(ReadOnlyMemServerPort#(addrSz, 2))
        provisos (MkPolymorphicMemFromRegs#(ReadOnlyMemReq#(addrSz, 2), ReadOnlyMemResp#(2), 4, 32));
    Vector#(4, Reg#(Bit#(32))) rom =
        vec(
            readOnlyReg('h297 + truncate(cfg.start_addr - cfg.bootrom_addr)),
            readOnlyReg(32'h00028067),
            readOnlyReg(32'h00000000),
            readOnlyReg(truncate(cfg.config_string_addr))
        );
    let memIfc <- mkPolymorphicMemFromRegs(rom);
    return memIfc;
endmodule

module mkBasicBootRom64#(BootRomConfig cfg)(ReadOnlyMemServerPort#(addrSz, 3))
        provisos (MkPolymorphicMemFromRegs#(ReadOnlyMemReq#(addrSz, 3), ReadOnlyMemResp#(3), 2, 64));
    Vector#(2, Reg#(Bit#(64))) rom =
        vec(
            concatReg2(readOnlyReg(32'h00028067), readOnlyReg('h297 + truncate(cfg.start_addr - cfg.bootrom_addr))),
            concatReg2(readOnlyReg(truncate(cfg.config_string_addr)), readOnlyReg(32'h00000000))
        );
    let memIfc <- mkPolymorphicMemFromRegs(rom);
    return memIfc;
endmodule

