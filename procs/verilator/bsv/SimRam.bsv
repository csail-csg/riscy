
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
import Vector::*;

import Port::*;
import ShiftRegister::*;

import Abstraction::*;
import RVTypes::*;

/// This module creates a GenericMemServerPort from a BRAM that is initialized
/// by a hex file
module mkSimRam#(String hex_file_name)(GenericMemServerPort#(data_sz)) provisos (Mul#(32, num_words, data_sz), Mul#(num_words, 4, TDiv#(data_sz, 8)));
    BRAM_Configure bram_config = defaultValue;
    bram_config.loadFormat = tagged Hex hex_file_name;

    BRAM1PortBE#(Bit#(16), Bit#(32), TDiv#(32,8)) bram <- mkBRAM1ServerBE(bram_config);

    ShiftRegister#(num_words, 32) dataShiftRegister <- mkShiftRegister;
    ShiftRegister#(num_words, 4) byteEnShiftRegister <- mkShiftRegister;

    Reg#(PAddr) currAddr <- mkReg(0);
    Reg#(Maybe#(Bool)) pendingReqIsStore <- mkReg(tagged Invalid);
    Reg#(Bit#(TLog#(TAdd#(num_words, 1)))) wordsLeft <- mkReg(0);

    rule handleStoreReq(pendingReqIsStore matches tagged Valid .isStore &&& (isStore && (wordsLeft != 0)));
        let word = dataShiftRegister.serial.response.first;
        dataShiftRegister.serial.response.deq;
        let byteEn = byteEnShiftRegister.serial.response.first;
        byteEnShiftRegister.serial.response.deq;
        bram.portA.request.put(BRAMRequestBE {
                                    writeen: byteEn,
                                    responseOnWrite: False,
                                    address: truncate(currAddr >> 2),
                                    datain: word});
        currAddr <= currAddr + 4;
        wordsLeft <= wordsLeft - 1;
    endrule

    rule handleLoadReq(pendingReqIsStore matches tagged Valid .isStore &&& (!isStore && (wordsLeft != 0)));
        bram.portA.request.put(BRAMRequestBE {
                                    writeen: 0,
                                    responseOnWrite: False,
                                    address: truncate(currAddr >> 2),
                                    datain: 0});
        currAddr <= currAddr + 4;
        wordsLeft <= wordsLeft - 1;
    endrule

    rule handleResp(pendingReqIsStore matches tagged Valid .isStore &&& !isStore);
        let x <- bram.portA.response.get();
        dataShiftRegister.serial.request.enq(x);
    endrule

    interface InputPort request;
        method Action enq(GenericMemReq#(data_sz) req) if (!isValid(pendingReqIsStore));
            if (req.write) begin
                Vector#(num_words, Bit#(32)) data_vec = unpack(req.data);
                dataShiftRegister.parallel.request.enq(data_vec);
                Vector#(num_words, Bit#(4)) byteEn_vec = unpack(req.byteen);
                byteEnShiftRegister.parallel.request.enq(byteEn_vec);
            end
            pendingReqIsStore <= tagged Valid req.write;
            currAddr <= req.addr;
            wordsLeft <= fromInteger(valueOf(num_words));
        endmethod
        method Bool canEnq;
            return !isValid(pendingReqIsStore);
        endmethod
    endinterface
    interface OutputPort response;
        method GenericMemResp#(data_sz) first if (pendingReqIsStore matches tagged Valid .isStore &&& ((isStore || dataShiftRegister.parallel.response.canDeq) && (wordsLeft == 0)));
            if (!isStore) begin
                let data_vec = dataShiftRegister.parallel.response.first;
                return GenericMemResp {
                            write: False,
                            data: pack(data_vec) };
            end else begin
                return GenericMemResp {
                            write: True,
                            data: 0 };
            end
        endmethod
        method Action deq if (pendingReqIsStore matches tagged Valid .isStore &&& ((isStore || dataShiftRegister.parallel.response.canDeq) && (wordsLeft == 0)));
            if (!isStore) begin
                dataShiftRegister.parallel.response.deq;
            end
            pendingReqIsStore <= tagged Invalid;
        endmethod
        method Bool canDeq;
            if (pendingReqIsStore matches tagged Valid .isStore) begin
                return (isStore || dataShiftRegister.parallel.response.canDeq);
            end else begin
                return False;
            end
        endmethod
    endinterface
endmodule
