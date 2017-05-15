
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
import MemoryMappedServer::*;
import RVExec::*;
import RVTypes::*;

interface BootRom#(numeric type numBytes);
    interface UncachedMemServerPort memIfc;
    // It might be nice to have PMA information in this interface to say this
    // is a ROM that doesn't support 64-bit accesses.
endinterface

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

typedef struct {
    Bool write;
    Bit#(2) addrByteSel;
    RVMemSize size;
} BootRomPendingReq deriving (Bits, Eq, FShow);

// 32-bit BootRom
module mkBRAMBootRom32#(parameter String rom_hex_file)(BootRom#(numBytes)) provisos (Add#(a__, TLog#(TDiv#(numBytes, 4)), 64));
    BRAM_Configure cfg = defaultValue;
    cfg.loadFormat = tagged Hex rom_hex_file;

    BRAM1Port#(Bit#(TLog#(TDiv#(numBytes,4))), Bit#(32)) bram_rom <- mkBRAM1Server(cfg);

    Ehr#(2, Maybe#(BootRomPendingReq)) pendingReq <- mkEhr(tagged Invalid);

    Ehr#(2, Maybe#(Bit#(32))) pendingResp <- mkEhr(tagged Invalid);

    rule getPendingResp(!isValid(pendingResp[0]));
        let resp <- bram_rom.portA.response.get;
        pendingResp[0] <= tagged Valid resp;
    endrule

    interface UncachedMemServerPort memIfc;
        interface InputPort request;
            method Action enq(UncachedMemReq r) if (pendingReq[1] == tagged Invalid);
                // since this is a rom, don't write to bram
                bram_rom.portA.request.put( BRAMRequest {
                        write:              False,
                        responseOnWrite:    True,
                        address:            truncate(r.addr >> 2), // get word address
                        datain:             0
                    } );
                pendingReq[1] <= tagged Valid BootRomPendingReq {
                        write: r.write,
                        addrByteSel: truncate(r.addr),
                        size: r.size
                    };
            endmethod
            method Bool canEnq;
                return pendingReq[1] == tagged Invalid;
            endmethod
        endinterface
        interface OutputPort response;
            method UncachedMemResp first if (pendingReq[0] matches tagged Valid .req &&& pendingResp[1] matches tagged Valid .resp);
                let data = gatherLoad(zeroExtend(req.addrByteSel), req.size, True /* was isUnsigned */, zeroExtend(resp));
                return UncachedMemResp{write: req.write, data: data};
            endmethod
            method Action deq if (pendingReq[0] matches tagged Valid .req &&& pendingResp[1] matches tagged Valid .resp);
                pendingReq[0] <= tagged Invalid;
                pendingResp[1] <= tagged Invalid;
            endmethod
            method Bool canDeq;
                return isValid(pendingReq[0]) && isValid(pendingResp[1]);
            endmethod
        endinterface
    endinterface
endmodule
