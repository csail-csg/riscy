
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

// This is a wrapper for SPI.bsv to provide a memory-mapped interface for
// integration with the Riscy processors.

import ClientServer::*;
import Vector::*;
import GetPut::*;
import Vector::*;
import Ehr::*;

import Abstraction::*;
import SPI::*;

interface RVSPI;
    // Memory mapped interface
    interface UncachedMemServer memifc;

    // Pins
    (* prefix = "" *)
    interface SPIMasterPins spi_pins;
endinterface

module mkRVSPI(RVSPI) provisos (NumAlias#(internalAddrSize, 4));
    // Layout of memory interface
    // Address   Name     Description
    // 0x0000    txData   Transmit data register
    // 0x0004    rxData   Receive data register
    // 0x0008    enable   Chip select enable register
    //                      bit 0 - set to enable SD card
    // 0x000C    div      Sclk divider
    Bit#(internalAddrSize) txDataAddr = 'h00;
    Bit#(internalAddrSize) rxDataAddr = 'h04;
    Bit#(internalAddrSize) enableAddr = 'h08;
    Bit#(internalAddrSize) divAddr    = 'h0C;

    Ehr#(2, Maybe#(Tuple2#(Bool, Bit#(internalAddrSize)))) pendingReq <- mkEhr(tagged Invalid);

    SPIMaster spi <- mkSPIMaster;

    // Data registers
    Reg#(Maybe#(Bit#(8))) txDataReg <- mkReg(tagged Invalid);
    Reg#(Maybe#(Bit#(8))) rxDataReg <- mkReg(tagged Invalid);

    rule doTxData (txDataReg matches tagged Valid .x);
        spi.put(x);
        txDataReg <= tagged Invalid;
    endrule

    rule doRxData (rxDataReg matches tagged Invalid .x);
        let data <- spi.get;
        rxDataReg <= Valid(data);
    endrule

    interface UncachedMemServer memifc;
        interface Put request;
            method Action put(UncachedMemReq req) if (!isValid(pendingReq[1]));
                if (req.write) begin
                    case (truncate(req.addr))
                        txDataAddr: begin
                                        txDataReg <= tagged Valid(truncate(req.data));
                                    end
                        rxDataAddr: begin
                                        rxDataReg <= tagged Invalid;
                                    end
                        enableAddr: begin
                                        spi.setNcs(~req.data[0]);
                                    end
                        divAddr:    spi.setSclkDiv(truncate(req.data));
                        default:    noAction;
                    endcase
                    pendingReq[1] <= tagged Valid tuple2(True, truncate(req.addr));
                end else begin
                    pendingReq[1] <= tagged Valid tuple2(False, truncate(req.addr));
                end
            endmethod
        endinterface
        interface Get response;
            method ActionValue#(UncachedMemResp) get if (pendingReq[0] matches tagged Valid .reqTuple);
                Bool write = tpl_1(reqTuple);
                Bit#(internalAddrSize) addr = tpl_2(reqTuple);
                Bit#(32) retVal = 0;
                $display("memory read: %h", addr);
                case (truncate(addr))
                    txDataAddr: begin
                                    if (txDataReg matches tagged Valid .x) begin
                                        retVal = {1'b1, '0, x};
                                    end
                                end
                    rxDataAddr: begin
                                    if (rxDataReg matches tagged Valid .x) begin
                                        retVal = {1'b1, '0, x};
                                        rxDataReg <= tagged Invalid;
                                    end
                                end
                    enableAddr: retVal = {0, pack(spi.isChipSelectEnabled())};
                    divAddr:    retVal = 0;
                    default:    retVal = 0;
                endcase
                pendingReq[0] <= tagged Invalid;
                return UncachedMemResp{ write: write, data: write? 0: retVal };
            endmethod
        endinterface
    endinterface

    interface SPIMasterPins spi_pins = spi.pins;
endmodule
