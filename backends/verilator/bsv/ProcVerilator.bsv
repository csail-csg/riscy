
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

// ProcVerilator.bsv
// This is a wrapper to translate the generic Proc interface to an interface
// that is accepted by verilator.

import RS232::*;

import MemUtil::*;

// This assumes a Proc.bsv file that contains the mkProc definition
import Abstraction::*;
import BuildVector::*;
import ClientServer::*;
import Clocks::*;
import Connectable::*;
import FIFO::*;
import GetPut::*;
import Port::*;
import Proc::*;
import Vector::*;
import VerificationPacket::*;
import VerificationPacketFilter::*;
import ProcPins::*;
import RVTypes::*;

import SimRam::*;

interface ProcVerilator;
    // Processor Control
    method Action start();
    method Action stop();
    method Action stallPipeline(Bool stall);

    // Verification
    method Maybe#(VerificationPacket) currVerificationPacket;

    // TODO: re-enable this port
    // interface UncachedMemClientPort mmio;
    interface CoarseMemServerPort#(XLEN, TLog#(TDiv#(XLEN,8))) extmem;
    // Interrupts
    method Action triggerExternalInterrupt;

    method Action sendUartChar(Bit#(8) x);
    method ActionValue#(Bit#(8)) receiveUartChar;
endinterface

module mkProcVerilator(ProcVerilator);
    CoarseMemServerPort#(XLEN, TLog#(TDiv#(MainMemoryWidth,8))) simRam <- mkSimRam(`CONFIG_RAM_INIT_HEX_FILE);
    Proc#(MainMemoryWidth) proc <- mkProc;

    // connect the processor to the simRam
    mkConnection(proc.ram, simRam);

    // some of our processors write to a certain location when finished executing:
    rule checkForFinish if ((proc.mmio.request.first.addr == 'h6000_0000) && (proc.mmio.request.first.write));
        if (proc.mmio.request.first.data == 0) begin
            $display("PASSED");
        end else begin
            $display("FAILED %0d", proc.mmio.request.first.data);
        end
        $finish;
    endrule

`ifdef CONFIG_SPI
    rule tieOff;
        proc.pins.spi.miso(0);
    endrule
`endif

`ifdef CONFIG_RS232
    Reg#(Bit#(16)) uartDivisor <- mkReg(17);
    UART#(16) simUart <- mkUART(8, NONE, STOP_1, uartDivisor);
    let uartSimToFPGABridge <- mkConnection(toPut(proc.pins.uart.sin), toGet(simUart.rs232.sout));
    let uartFPGAToSimBridge <- mkConnection(toPut(simUart.rs232.sin), toGet(proc.pins.uart.sout));

    rule displayMsg;
        let x <- simUart.tx.get();
        $write("%c", x);
    endrule
`endif

    // Processor Control
    method Action start;
        proc.start;
    endmethod
    method Action stop();
        proc.stop;
    endmethod
    method Action stallPipeline(Bool stall);
        proc.stallPipeline(stall);
    endmethod

    // Verification
    method Maybe#(VerificationPacket) currVerificationPacket;
        return proc.currVerificationPacket;
    endmethod

    // Uncached Connections
    // interface UncachedMemClientPort mmio = proc.mmio;
    // External Connections
    interface GenericMemServerPort extmem = proc.extmem;
    // Interrupts
    method Action triggerExternalInterrupt = proc.triggerExternalInterrupt;

`ifdef CONFIG_RS232
    method Action sendUartChar(Bit#(8) x);
        simUart.rx.put(x);
    endmethod
    method ActionValue#(Bit#(8)) receiveUartChar;
        let x <- simUart.tx.get;
        return x;
    endmethod
`else
    method Action sendUartChar(Bit#(8) x) if (False);
        noAction;
    endmethod
    method ActionValue#(Bit#(8)) receiveUartChar if (False);
        return ?;
    endmethod
`endif
endmodule
