
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

import BuildVector::*;
import ClientServer::*;
import GetPut::*;
import RS232::*;
import Vector::*;

import ConcatReg::*;
import Ehr::*;
import PolymorphicMem::*;
import Port::*;
import RegUtil::*;

import Abstraction::*;

interface RVUart#(type memIfcT);
    // Internal connections
    interface memIfcT memifc;

    // external connections for rx/tx (to be connected to a UART
    (* prefix = "" *)
    interface RS232 uart_pins;
    method Bit#(16) divisor;
    method Bool interrupt;
endinterface

module mkRVUart_RV32#(Bit#(16) divisor)(RVUart#(ServerPort#(reqT, respT))) provisos (MkPolymorphicMemFromRegs#(reqT, respT, 5, 32));
    Bool verbose = False;

    // memory mapped registers
    Reg#(Maybe#(Bit#(8))) txDataReg <- mkReg(tagged Invalid);
    Reg#(Maybe#(Bit#(8))) rxDataReg <- mkReg(tagged Invalid);
    Reg#(Bit#(32)) txCtrlReg <- mkReg(0);
    Reg#(Bit#(32)) rxCtrlReg <- mkReg(0);
    Reg#(Bit#(16)) divReg <- mkReg(divisor);

    Vector#(5, Reg#(Bit#(32))) memoryMappedRegisters =
        vec(
            concatReg3(readOnlyReg(pack(isValid(txDataReg))), readOnlyReg(0), fromMaybeReg(0, txDataReg)),
            concatReg3(readOnlyReg(pack(isValid(rxDataReg))), readOnlyReg(0), fromMaybeReg(0, rxDataReg)),
            txCtrlReg,
            rxCtrlReg,
            zeroExtendReg(divReg)
        );
    ServerPort#(reqT, respT) memoryMappedIfc <- mkPolymorphicMemFromRegs(memoryMappedRegisters);

    UART#(16) uart <- mkUART(8, NONE, STOP_1, divReg);

    rule doTxData (txDataReg matches tagged Valid .x);
        // There is an implicit guard on the Fifo for uart.put
        uart.rx.put(x);
        txDataReg <= tagged Invalid;
    endrule

    rule doRxData (rxDataReg matches tagged Invalid .x);
        // There is an implicit guard on the Fifo for uart.get
        let data <- uart.tx.get;
        rxDataReg <= Valid(data);
    endrule

    interface ServerPort memifc = memoryMappedIfc;

    interface RS232 uart_pins = uart.rs232;
    method Bit#(16) divisor = divReg;
    method Bool interrupt = isValid(rxDataReg);
endmodule
