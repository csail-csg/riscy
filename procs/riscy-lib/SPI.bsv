
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

// For information about SPI, check wikipedia:
//   https://en.wikipedia.org/wiki/Serial_Peripheral_Interface_Bus

(* always_ready, always_enabled *)
interface SPIMasterPins;
    // serial clock
    (* prefix = "", result = "sclk" *)
    method Bit#(1) sclk;
    // master-out slave-in
    (* prefix = "", result = "mosi" *)
    method Bit#(1) mosi;
    // master-in slave-out
    (* prefix = "" *)
    method Action miso((* port = "miso" *)Bit#(1) x);
    // active-low chip select
    (* prefix = "", result = "ncs" *)
    method Bit#(1) ncs;
endinterface

interface SPIMaster;
    // configuration
    method Action setSclkDiv(Bit#(16) d);
    method Action setNcs(Bit#(1) new_ncs);
    method Action setCpol(Bit#(1) new_cpol); // idle value of clock
    method Action setCpha(Bit#(1) new_cpha); // which clock transition captures data
                                             // cpha = 0 => odd transitions (1st, 3rd, etc.)
                                             // cpha = 1 => even transitions (2nd, 4th, etc.)
    // status
    method Bool isChipSelectEnabled();
    // data
    method Action put(Bit#(8) x);
    method ActionValue#(Bit#(8)) get();
    // pins
    (* prefix = "" *)
    interface SPIMasterPins pins;
endinterface

module mkSPIMaster(SPIMaster);
    let clock <- exposeCurrentClock();
    // registers for the interface pins
    Reg#(Bit#(1)) sclkReg <- mkReg(0);
    Reg#(Bit#(16)) sclkDiv <- mkReg(1);
    Wire#(Bit#(1)) misoWire <- mkDWire(0);
    Reg#(Bit#(1)) misoReg <- mkReg(0);
    Reg#(Bit#(1)) ncsReg <- mkReg(1);
    // MSB gets shifted out
    Reg#(Bit#(8)) shiftReg <- mkReg(0);

    // SPI configuration
    Reg#(Bit#(1)) cpol <- mkReg(0);
    Reg#(Bit#(1)) cpha <- mkReg(0);

    // 17 ticks per SPI cycle, between each tick is a clock transition
    Reg#(Bool) running <- mkReg(False);
    Reg#(Bool) resultReady <- mkReg(False);
    Reg#(Bit#(5)) tickCount <- mkReg(0);
    // sclkReg determines how many mini ticks make up a tick
    Reg#(Bit#(16)) miniTickCount <- mkReg(0);

    (* fire_when_enabled, no_implicit_conditions *)
    rule run(running);
        let nextMiniTickCount = miniTickCount + 1;
        if ((nextMiniTickCount == sclkDiv) || sclkDiv == 0) begin
            miniTickCount <= 0;
            if (tickCount == 16) begin
                // done
                running <= False;
                resultReady <= True;
                tickCount <= 0;
            end else begin
                // tick clock
                sclkReg <= ~sclkReg;
                // increment tickCount
                tickCount <= tickCount + 1;
                // either capture input or shift output
                if (tickCount[0] == cpha) begin
                    // capture input
                    misoReg <= misoWire;
                end else begin
                    // shift output
                    if (tickCount == 0) begin
                        // but never on the first tick
                    end else begin
                        shiftReg <= {shiftReg[6:0], misoReg};
                    end
                end
            end
        end else begin
            miniTickCount <= nextMiniTickCount;
        end
    endrule

    method Action setSclkDiv(Bit#(16) d);
        sclkDiv <= d;
    endmethod
    method Action setNcs(Bit#(1) new_ncs);
        ncsReg <= new_ncs;
    endmethod
    method Action setCpol(Bit#(1) new_cpol);
        cpol <= new_cpol;
    endmethod
    method Action setCpha(Bit#(1) new_cpha);
        cpha <= new_cpha;
    endmethod

    method Bool isChipSelectEnabled();
        return ncsReg == 0;
    endmethod

    method Action put(Bit#(8) x) if (!running);
        resultReady <= False;
        running <= True;
        tickCount <= 0;
        miniTickCount <= 0;
        shiftReg <= x;
    endmethod
    method ActionValue#(Bit#(8)) get() if (resultReady);
        resultReady <= False;
        return shiftReg;
    endmethod

    interface SPIMasterPins pins;
        method Bit#(1) sclk;
            return sclkReg;
        endmethod
        method Bit#(1) mosi;
            return running ? shiftReg[7] : 1;
        endmethod
        method Action miso(Bit#(1) x);
            misoWire <= x;
        endmethod
        method Bit#(1) ncs;
            return ncsReg;
        endmethod
    endinterface
endmodule

