
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

import MemUtil::*;
import Port::*;
import ShiftRegister::*;

import Abstraction::*;
import RVTypes::*;

/// This module creates a GenericMemServerPort from a BRAM that is initialized
/// by a hex file
module mkSimRam#(String hex_file_name)(CoarseMemServerPort#(addrSz, logNumBytes))
        provisos (NumAlias#(TExp#(TSub#(logNumBytes, 2)), numWords),
                  Mul#(4, numWords, TExp#(logNumBytes)),
                  Add#(a__, 16, addrSz));
    BRAM_Configure bram_config = defaultValue;
    bram_config.loadFormat = tagged Hex hex_file_name;

    BRAM1Port#(Bit#(16), Bit#(32)) bram <- mkBRAM1Server(bram_config);

    ShiftRegister#(numWords, 32) dataShiftRegister <- mkShiftRegister;

    Reg#(Bit#(addrSz)) currAddr <- mkReg(0);
    Reg#(Maybe#(Bool)) pendingReqIsStore <- mkReg(tagged Invalid);
    Reg#(Bit#(TLog#(TAdd#(numWords, 1)))) wordsLeft <- mkReg(0);

    rule handleStoreReq(pendingReqIsStore matches tagged Valid .isStore &&& (isStore && (wordsLeft != 0)));
        let word = dataShiftRegister.serial.response.first;
        dataShiftRegister.serial.response.deq;
        bram.portA.request.put(BRAMRequest {
                                    write: True,
                                    responseOnWrite: False,
                                    address: truncate(currAddr >> 2),
                                    datain: word});
        currAddr <= currAddr + 4;
        wordsLeft <= wordsLeft - 1;
    endrule

    rule handleLoadReq(pendingReqIsStore matches tagged Valid .isStore &&& (!isStore && (wordsLeft != 0)));
        bram.portA.request.put(BRAMRequest {
                                    write: False,
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
        method Action enq(CoarseMemReq#(addrSz, logNumBytes) req) if (!isValid(pendingReqIsStore));
            if (req.write) begin
                Vector#(numWords, Bit#(32)) data_vec = unpack(req.data);
                dataShiftRegister.parallel.request.enq(data_vec);
            end
            pendingReqIsStore <= tagged Valid req.write;
            let addr_mask = ~fromInteger((valueOf(numWords) * 4) - 1);
            currAddr <= req.addr & addr_mask;
            wordsLeft <= fromInteger(valueOf(numWords));
        endmethod
        method Bool canEnq;
            return !isValid(pendingReqIsStore);
        endmethod
    endinterface
    interface OutputPort response;
        method CoarseMemResp#(logNumBytes) first if (pendingReqIsStore matches tagged Valid .isStore &&& ((isStore || dataShiftRegister.parallel.response.canDeq) && (wordsLeft == 0)));
            if (!isStore) begin
                let data_vec = dataShiftRegister.parallel.response.first;
                return CoarseMemResp {
                            write: False,
                            data: pack(data_vec) };
            end else begin
                return CoarseMemResp {
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
