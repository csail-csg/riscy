
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
import RVTypes::*;
import VerificationPacket::*;
import FIFO::*;

interface VerificationPacketFilter;
    method Action init(Bit#(64) verificationPacketsToIgnore, Bool sendSynchronizationPackets);
    method ActionValue#(VerificationPacket) getPacket;
endinterface

module mkVerificationPacketFilter#(function ActionValue#(VerificationPacket) packetIn)(VerificationPacketFilter);
    Reg#(Bit#(64)) ignoreCounter <- mkReg(0);
    Reg#(Bit#(64)) skippedCounter <- mkReg(0);
    Reg#(Bool) sendSynchronization <- mkReg(False);
    FIFO#(VerificationPacket) packets <- mkFIFO;

    rule getPackets;
        let packet <- packetIn;

        // update skippedPackets field
        packet.skippedPackets = skippedCounter;

        // detect if the packet is for synchronization - a packet is a
        // synchronization packet if it is a timer or host interrupt, or if it
        // reads a non-deterministic CSR
        Bool isSynchronizationPacket = False;
        if (packet.trap) begin
            if (packet.trapType == 8'h81 || packet.trapType == 8'h82) begin
                // timer or host interrupt
                isSynchronizationPacket = True;
            end
        end
        if ((packet.instruction[6:0] == 7'b1110011) && (packet.instruction[14:12] != 0)) begin
            CSR csr = unpack(packet.instruction[31:20]);
            case (csr)
                CSRmtime, CSRstime, CSRstimew, CSRtime, CSRtimew, CSRcycle, CSRcyclew, CSRinstret, CSRinstretw, CSRmip, CSRmfromhost:
                    isSynchronizationPacket = True;
            endcase
        end

        // figure out if packet should be sent or not
        if (ignoreCounter == 0) begin
            // send and clear skippedCounter
            packets.enq(packet);
            skippedCounter <= 0;
        end else begin
            if (ignoreCounter != '1) begin
                // decrement ignoreCounter
                ignoreCounter <= ignoreCounter - 1;
            end
            if (isSynchronizationPacket && sendSynchronization) begin
                // send and clear skippedCounter
                packets.enq(packet);
                skippedCounter <= 0;
            end else begin
                // don't send; increment skippedCounter
                skippedCounter <= skippedCounter + 1;
            end
        end
    endrule
    
    method Action init(Bit#(64) verificationPacketsToIgnore, Bool sendSynchronizationPackets);
        ignoreCounter <= verificationPacketsToIgnore;
        sendSynchronization <= sendSynchronizationPackets;
        skippedCounter <= 0;
    endmethod
    method ActionValue#(VerificationPacket) getPacket;
        packets.deq;
        return packets.first;
    endmethod
endmodule
