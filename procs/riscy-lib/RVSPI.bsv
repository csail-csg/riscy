
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

import BuildVector::*;
import ClientServer::*;
import Vector::*;
import GetPut::*;
import Vector::*;

import ConcatReg::*;
import Ehr::*;
import PolymorphicMem::*;
import Port::*;
import RegUtil::*;

import Abstraction::*;
import SPI::*;

interface RVSPI#(type memIfcT);
    // Memory mapped interface
    interface memIfcT memifc;

    // Pins
    (* prefix = "" *)
    interface SPIMasterPins spi_pins;
endinterface

module mkRVSPI(RVSPI#(ServerPort#(reqT, respT))) provisos (MkPolymorphicMemFromRegs#(reqT, respT, 4, 32));
    // Layout of memory interface
    // Address   Name     Description
    // 0x0000    txData   Transmit data register
    // 0x0004    rxData   Receive data register
    // 0x0008    enable   Chip select enable register
    //                      bit 0 - set to enable SD card
    // 0x000C    div      Sclk divider

    SPIMaster spi <- mkSPIMaster;

    Reg#(Maybe#(Bit#(8))) txDataReg <- mkReg(tagged Invalid);
    Reg#(Maybe#(Bit#(8))) rxDataReg <- mkReg(tagged Invalid);
    Reg#(Bit#(32)) enableReg =
        (interface Reg;
            method Action _write(Bit#(32) x);
                spi.setNcs(~x[0]);
            endmethod
            method Bit#(32) _read;
                return {0, pack(spi.isChipSelectEnabled())};
            endmethod
        endinterface);
    Reg#(Bit#(32)) divReg =
        (interface Reg;
            method Action _write(Bit#(32) x);
                spi.setSclkDiv(truncate(x));
            endmethod
            method Bit#(32) _read;
                return 0;
            endmethod
        endinterface);

    Vector#(4, Reg#(Bit#(32))) memoryMappedRegisters = vec(
            concatReg3(readOnlyReg(pack(isValid(txDataReg))), readOnlyReg(0), fromMaybeReg(0, txDataReg)),
            concatReg3(readOnlyReg(pack(isValid(rxDataReg))), readOnlyReg(0), fromMaybeReg(0, rxDataReg)),
            enableReg,
            divReg);

    ServerPort#(reqT, respT) memoryMappedIfc <- mkPolymorphicMemFromRegs(memoryMappedRegisters);

    rule doTxData (txDataReg matches tagged Valid .x);
        spi.put(x);
        txDataReg <= tagged Invalid;
    endrule

    rule doRxData (rxDataReg matches tagged Invalid .x);
        let data <- spi.get;
        rxDataReg <= tagged Valid data;
    endrule

    interface ServerPort memifc = memoryMappedIfc;

    interface SPIMasterPins spi_pins = spi.pins;
endmodule
