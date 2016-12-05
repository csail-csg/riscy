
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

import BRAM::*;
import ClientServer::*;
import FIFOF::*;
import FIFO::*;
import GetPut::*;
import Vector::*;

import Ehr::*;

import Abstraction::*;
import RVAmo::*;
import RVExec::*; // for scatterStore and gatherLoad
import RVTypes::*;

typedef struct {
    Bool write;
    DataByteSel addrByteSel;
    RVMemSize size;
    Bool isUnsigned;
} BramDMemPendingReq deriving (Bits, Eq, FShow);

// schedule: response.get < request.put
module mkBramDMem(Server#(RVDMemReq, RVDMemResp));
    BRAM_Configure cfg = defaultValue;
    BRAM1PortBE#(Bit#(12), Data, TDiv#(XLEN,8)) bram <- mkBRAM1ServerBE(cfg);

    Ehr#(2, Maybe#(BramDMemPendingReq)) pendingReq <- mkEhr(tagged Invalid);
    interface Put request;
        method Action put(RVDMemReq r) if (pendingReq[1] == tagged Invalid);
            Bool isLd = r.op == tagged Mem Ld;
            let {permutedDataByteEn, permutedStData} = scatterStore(truncate(r.addr), r.size, r.data);
            bram.portA.request.put( BRAMRequestBE {
                    writeen:            isLd ? 0 : permutedDataByteEn,
                    responseOnWrite:    False,
                    address:            truncate(r.addr >> valueOf(TLog#(TDiv#(XLEN,8)))), // get word address
                    datain:             permutedStData
                } );
            if (isLd) begin
                pendingReq[1] <= tagged Valid BramDMemPendingReq {
                        write: False,
                        addrByteSel: truncate(r.addr),
                        size: r.size,
                        isUnsigned: r.isUnsigned
                    };
            end
        endmethod
    endinterface
    interface Get response;
        method ActionValue#(RVDMemResp) get if (pendingReq[0] matches tagged Valid .req);
            let resp <- bram.portA.response.get;
            let data = gatherLoad(req.addrByteSel, req.size, req.isUnsigned, resp);
            pendingReq[0] <= tagged Invalid;
            return data;
        endmethod
    endinterface
endmodule

module mkBramIMem(Server#(RVIMemReq, RVIMemResp));
    BRAM_Configure cfg = defaultValue;
    BRAM1PortBE#(Bit#(12), Data, TDiv#(XLEN,8)) bram <- mkBRAM1ServerBE(cfg);

    Ehr#(2, Maybe#(BramDMemPendingReq)) pendingReq <- mkEhr(tagged Invalid);
    interface Put request;
        method Action put(RVIMemReq r) if (pendingReq[1] == tagged Invalid);
            bram.portA.request.put( BRAMRequestBE {
                    writeen:            0,
                    responseOnWrite:    False,
                    address:            truncate(r >> valueOf(TLog#(TDiv#(XLEN,8)))), // get word address
                    datain:             0
                } );
            pendingReq[1] <= tagged Valid BramDMemPendingReq {
                    write: False,
                    addrByteSel: truncate(r),
                    size: W,
                    isUnsigned: False
                };
        endmethod
    endinterface
    interface Get response;
        method ActionValue#(RVIMemResp) get if (pendingReq[0] matches tagged Valid .req);
            let resp <- bram.portA.response.get;
            Instruction inst = truncate(gatherLoad(req.addrByteSel, req.size, req.isUnsigned, resp));
            pendingReq[0] <= tagged Invalid;
            return inst;
        endmethod
    endinterface
endmodule

interface IDMem;
    interface Server#(RVIMemReq, RVIMemResp) imem;
    interface Server#(RVDMemReq, RVDMemResp) dmem;
endinterface

module mkBramIDMem(IDMem);
    BRAM_Configure cfg = defaultValue;
    BRAM2PortBE#(Bit#(12), Data, TDiv#(XLEN,8)) bram <- mkBRAM2ServerBE(cfg);

    Ehr#(2, Maybe#(BramDMemPendingReq)) pendingIReq <- mkEhr(tagged Invalid);
    Ehr#(2, Maybe#(BramDMemPendingReq)) pendingDReq <- mkEhr(tagged Invalid);

    interface Server imem;
        interface Put request;
            method Action put(RVIMemReq r) if (pendingIReq[1] == tagged Invalid);
                bram.portA.request.put( BRAMRequestBE {
                        writeen:            0,
                        responseOnWrite:    False,
                        address:            truncate(r >> valueOf(TLog#(TDiv#(XLEN,8)))), // get word address
                        datain:             0
                    } );
                pendingIReq[1] <= tagged Valid BramDMemPendingReq {
                        write: False,
                        addrByteSel: truncate(r),
                        size: W,
                        isUnsigned: False
                    };
            endmethod
        endinterface
        interface Get response;
            method ActionValue#(RVIMemResp) get if (pendingIReq[0] matches tagged Valid .req);
                let resp <- bram.portA.response.get;
                Instruction inst = truncate(gatherLoad(req.addrByteSel, req.size, req.isUnsigned, resp));
                pendingIReq[0] <= tagged Invalid;
                return inst;
            endmethod
        endinterface
    endinterface

    interface Server dmem;
        interface Put request;
            method Action put(RVDMemReq r) if (pendingDReq[1] == tagged Invalid);
                Bool isLd = r.op == tagged Mem Ld;
                let {permutedDataByteEn, permutedStData} = scatterStore(truncate(r.addr), r.size, r.data);
                bram.portA.request.put( BRAMRequestBE {
                        writeen:            isLd ? 0 : permutedDataByteEn,
                        responseOnWrite:    False,
                        address:            truncate(r.addr >> valueOf(TLog#(TDiv#(XLEN,8)))), // get word address
                        datain:             permutedStData
                    } );
                if (isLd) begin
                    pendingDReq[1] <= tagged Valid BramDMemPendingReq {
                            write: !isLd,
                            addrByteSel: truncate(r.addr),
                            size: r.size,
                            isUnsigned: r.isUnsigned
                        };
                end
            endmethod
        endinterface
        interface Get response;
            method ActionValue#(RVDMemResp) get if (pendingDReq[0] matches tagged Valid .req);
                let resp <- bram.portA.response.get;
                let data = gatherLoad(req.addrByteSel, req.size, req.isUnsigned, resp);
                pendingDReq[0] <= tagged Invalid;
                return data;
            endmethod
        endinterface
    endinterface
endmodule

interface IDMemWLoader;
    interface Server#(RVIMemReq, RVIMemResp) imem;
    interface Server#(RVDMemReq, RVDMemResp) dmem;
    interface Server#(GenericMemReq#(XLEN), GenericMemResp#(XLEN)) ext;
endinterface

typedef enum {DMem, Ext} PortBUser deriving (Bits, Eq, FShow);
module mkBramIDExtMem(IDMemWLoader);
    BRAM_Configure cfg = defaultValue;
    // BRAM2PortBE#(Bit#(12), Data, TDiv#(XLEN,8)) bram <- mkBRAM2ServerBE(cfg);
    BRAM2PortBE#(Bit#(16), Data, TDiv#(XLEN,8)) bram <- mkCustomBRAM2ServerBE(cfg);

    Ehr#(2, Maybe#(BramDMemPendingReq)) pendingIReq   <- mkEhr(tagged Invalid);
    Ehr#(2, Maybe#(BramDMemPendingReq)) pendingDReq   <- mkEhr(tagged Invalid);
    Ehr#(2, Maybe#(BramDMemPendingReq)) pendingExtReq <- mkEhr(tagged Invalid);

    // for multiplexing portB between DMem and ExtMem
    Ehr#(4, Maybe#(PortBUser)) portBReq <- mkEhr(tagged Invalid);

    rule clearDMemStResp(pendingDReq[0] matches tagged Valid .req &&& req.write &&& portBReq[0] == tagged Valid DMem);
        let ignore <- bram.portB.response.get;
        pendingDReq[0] <= tagged Invalid;
        portBReq[0] <= tagged Invalid;
    endrule

    interface Server imem;
        interface Put request;
            method Action put(RVIMemReq r) if (pendingIReq[1] == tagged Invalid);
                bram.portA.request.put( BRAMRequestBE {
                        writeen:            0,
                        responseOnWrite:    False,
                        address:            truncate(r >> valueOf(TLog#(TDiv#(XLEN,8)))), // get word address
                        datain:             0
                    } );
                pendingIReq[1] <= tagged Valid BramDMemPendingReq {
                        write: False,
                        addrByteSel: truncate(r),
                        size: W,
                        isUnsigned: False
                    };
            endmethod
        endinterface
        interface Get response;
            method ActionValue#(RVIMemResp) get if (pendingIReq[0] matches tagged Valid .req);
                let resp <- bram.portA.response.get;
                Instruction inst = truncate(gatherLoad(req.addrByteSel, req.size, req.isUnsigned, resp));
                pendingIReq[0] <= tagged Invalid;
                return inst;
            endmethod
        endinterface
    endinterface

    interface Server dmem;
        interface Put request;
            method Action put(RVDMemReq r) if (pendingDReq[1] == tagged Invalid && portBReq[2] == tagged Invalid);
                Bool isLd = r.op == tagged Mem Ld;
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
                        isUnsigned: r.isUnsigned
                    };
                portBReq[2] <= tagged Valid DMem;
            endmethod
        endinterface
        interface Get response;
            method ActionValue#(RVDMemResp) get if (pendingDReq[0] matches tagged Valid .req &&& portBReq[0] == tagged Valid DMem);
                let resp <- bram.portB.response.get;
                let data = gatherLoad(req.addrByteSel, req.size, req.isUnsigned, resp);
                pendingDReq[0] <= tagged Invalid;
                portBReq[0] <= tagged Invalid;
                return data;
            endmethod
        endinterface
    endinterface

    interface Server ext;
        interface Put request;
            method Action put(GenericMemReq#(XLEN) r) if (pendingExtReq[1] == tagged Invalid && portBReq[3] == tagged Invalid);
                Bool isLd = !r.write;
                // XXX: This method assumes all accesses are word aligned
                Bit#(TLog#(TDiv#(XLEN,8))) offset = truncate(r.addr);
                if (offset != 0) begin
                    $fdisplay(stderr, "[ERROR] ExtMemReq is not word aligned");
                end

                bram.portB.request.put( BRAMRequestBE {
                        writeen:            isLd ? 0 : r.byteen,
                        responseOnWrite:    True,
                        address:            truncate(r.addr >> valueOf(TLog#(TDiv#(XLEN,8)))), // get word address
                        datain:             r.data
                    } );
                pendingExtReq[1] <= tagged Valid BramDMemPendingReq {
                        write: !isLd,
                        addrByteSel: truncate(r.addr),
`ifdef CONFIG_RV64
                        size: D,
`else
                        size: W,
`endif
                        isUnsigned: False
                    };
                portBReq[3] <= tagged Valid Ext;
            endmethod
        endinterface
        interface Get response;
            method ActionValue#(GenericMemResp#(XLEN)) get if (pendingExtReq[0] matches tagged Valid .req &&& portBReq[1] == tagged Valid Ext);
                let data <- bram.portB.response.get;
                pendingExtReq[0] <= tagged Invalid;
                portBReq[1] <= tagged Invalid;
                return GenericMemResp {
                            write: req.write,
                            data: data
                        };
            endmethod
        endinterface
    endinterface
endmodule

// My own custom implementation of BRAM2PortBE using a BRAM per byte since the
// provided implementation isn't working in Vivado at the moment.
module mkCustomBRAM2ServerBE#(BRAM_Configure cfg)(BRAM2PortBE#(addrT, dataT, numByteEnables))
        provisos (Bits#(addrT, addrSz),
                  Bits#(dataT, dataSz),
                  FShow#(addrT),
                  FShow#(dataT),
                  Mul#(byteSz, numByteEnables, dataSz),
                  Alias#(Bit#(byteSz), byteT));
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
