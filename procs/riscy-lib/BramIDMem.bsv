
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

import BRAM::*;
import ClientServer::*;
import FIFOF::*;
import FIFO::*;
import GetPut::*;
import Vector::*;

import Ehr::*;

import Abstraction::*;
import RVExec::*; // for scatterStore and gatherLoad
import RVTypes::*;

// A custom implementation of BRAM2PortBE using a BRAM per byte since the
// Bluespec provided implementation isn't working in Vivado at the moment.
module mkCustomBRAM2ServerBE#(BRAM_Configure cfg)(BRAM2PortBE#(addrT, dataT, numByteEnables))
        provisos (Bits#(addrT, addrSz),
                  Bits#(dataT, dataSz),
                  Mul#(byteSz, numByteEnables, dataSz),
                  Alias#(Bit#(byteSz), byteT));

    // Instantiate one bram per byte enable
    Vector#(numByteEnables, BRAM2Port#(addrT, byteT)) brams <- replicateM(mkBRAM2Server(cfg));

    interface BRAMServerBE portA;
        interface Put request;
            method Action put(BRAMRequestBE#(addrT, dataT, numByteEnables) r);
                Bool isLd = r.writeen == 0;
                Vector#(numByteEnables, byteT) data = unpack(pack(r.datain));
                Vector#(numByteEnables, Bool) write = unpack(r.writeen);
                for (Integer i = 0 ; i < valueOf(numByteEnables) ; i = i+1) begin
                    if (isLd || write[i] || r.responseOnWrite) begin
                        brams[i].portA.request.put(
                                BRAMRequest {
                                    write: write[i],
                                    responseOnWrite: r.responseOnWrite,
                                    address: r.address,
                                    datain: data[i]
                                });
                    end
                end
            endmethod
        endinterface
        interface Get response;
            method ActionValue#(dataT) get();
                Vector#(numByteEnables, byteT) data = ?;
                for (Integer i = 0 ; i < valueOf(numByteEnables) ; i = i+1) begin
                    data[i] <- brams[i].portA.response.get();
                end
                dataT result = unpack(pack(data));
                return result;
            endmethod
        endinterface
    endinterface
    interface BRAMServerBE portB;
        interface Put request;
            method Action put(BRAMRequestBE#(addrT, dataT, numByteEnables) r);
                Bool isLd = r.writeen == 0;
                Vector#(numByteEnables, byteT) data = unpack(pack(r.datain));
                Vector#(numByteEnables, Bool) write = unpack(r.writeen);
                for (Integer i = 0 ; i < valueOf(numByteEnables) ; i = i+1) begin
                    if (isLd || write[i] || r.responseOnWrite) begin
                        brams[i].portB.request.put(
                                BRAMRequest {
                                    write: write[i],
                                    responseOnWrite: r.responseOnWrite,
                                    address: r.address,
                                    datain: data[i]
                                });
                    end
                end
            endmethod
        endinterface
        interface Get response;
            method ActionValue#(dataT) get();
                Vector#(numByteEnables, byteT) data = ?;
                for (Integer i = 0 ; i < valueOf(numByteEnables) ; i = i+1) begin
                    data[i] <- brams[i].portB.response.get();
                end
                dataT result = unpack(pack(data));
                return result;
            endmethod
        endinterface
    endinterface
    method Action portAClear;
        for (Integer i = 0 ; i < valueOf(numByteEnables) ; i = i+1) begin
            brams[i].portAClear;
        end
    endmethod
    method Action portBClear;
        for (Integer i = 0 ; i < valueOf(numByteEnables) ; i = i+1) begin
            brams[i].portBClear;
        end
    endmethod
endmodule

interface BramIDMem;
    interface Server#(Addr, Instruction) imem;
    interface Server#(UncachedMemReq, UncachedMemResp) dmem;
endinterface

typedef struct {
    Bool write;
    DataByteSel addrByteSel;
    RVMemSize size;
    Bool isUnsigned;
} BramDMemPendingReq deriving (Bits, Eq, FShow);

module mkBramIDMem(BramIDMem);
    BRAM_Configure cfg = defaultValue;
    BRAM2PortBE#(Bit#(12), Data, TDiv#(XLEN,8)) bram <- mkBRAM2ServerBE(cfg);

    Ehr#(2, Maybe#(BramDMemPendingReq)) pendingIReq <- mkEhr(tagged Invalid);
    Ehr#(2, Maybe#(BramDMemPendingReq)) pendingDReq <- mkEhr(tagged Invalid);

    interface Server imem;
        interface Put request;
            method Action put(Addr addr) if (pendingIReq[1] == tagged Invalid);
                if (addr[1:0] != 0) begin
                    $fdisplay(stderr, "[ERROR] mkBramIDMem.imem.request.put() - address is not aligned to a word boundary");
                    $fdisplay(stderr, "[WARNING] mkBramIDMem - compressed ISA extension is currently unsupported");
                end
                bram.portA.request.put( BRAMRequestBE {
                        writeen:            0,
                        responseOnWrite:    False,
                        address:            truncate(addr >> valueOf(TLog#(TDiv#(XLEN,8)))), // get word address
                        datain:             0
                    } );
                pendingIReq[1] <= tagged Valid BramDMemPendingReq {
                        write: False,
                        addrByteSel: truncate(addr),
                        size: W,
                        isUnsigned: False
                    };
            endmethod
        endinterface
        interface Get response;
            method ActionValue#(Instruction) get if (pendingIReq[0] matches tagged Valid .req);
                let resp <- bram.portA.response.get;
                Instruction inst = truncate(gatherLoad(req.addrByteSel, req.size, req.isUnsigned, resp));
                pendingIReq[0] <= tagged Invalid;
                return inst;
            endmethod
        endinterface
    endinterface

    interface Server dmem;
        interface Put request;
            method Action put(UncachedMemReq r) if (pendingDReq[1] == tagged Invalid);
                Bool isLd = !r.write;
                let {permutedDataByteEn, permutedStData} = scatterStore(truncate(r.addr), r.size, r.data);
                bram.portB.request.put( BRAMRequestBE {
                        writeen:            isLd ? 0 : permutedDataByteEn,
                        responseOnWrite:    True,
                        address:            truncate(r.addr >> valueOf(TLog#(TDiv#(XLEN,8)))), // get word address
                        datain:             permutedStData
                    } );
                pendingDReq[1] <= tagged Valid BramDMemPendingReq {
                        write: !isLd,
                        addrByteSel: truncate(r.addr),
                        size: r.size,
                        isUnsigned: ? // not used
                    };
            endmethod
        endinterface
        interface Get response;
            method ActionValue#(UncachedMemResp) get if (pendingDReq[0] matches tagged Valid .req);
                let resp <- bram.portB.response.get;
                let data = gatherLoad(req.addrByteSel, req.size, True /* was isUnsigned */, resp);
                pendingDReq[0] <= tagged Invalid;
                return UncachedMemResp{write: req.write, data: data};
            endmethod
        endinterface
    endinterface
endmodule

