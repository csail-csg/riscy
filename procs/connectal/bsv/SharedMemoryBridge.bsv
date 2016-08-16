
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

import Abstraction::*;
import RVTypes::*;
import CompareProvisos::*;
import ClientServer::*;
import ConnectalConfig::*;
import Ehr::*;
import GetPut::*;
import RegFile::*;
import Vector::*;
import FIFO::*;
import FIFOF::*;
import HostInterface::*;
import MemTypes::*;
import PrintTrace::*;
typedef Bit#(4) PendMemRespCnt;

import BRAMFIFO::*;
import DefaultValue::*;

interface SharedMemoryBridge#(numeric type dataSz);
    // Processor Interface
    interface Server#(GenericMemReq#(dataSz),GenericMemResp#(dataSz)) to_proc;

    // Shared Memory Interfaces
    interface MemReadClient#(DataBusWidth)  to_host_read;
    interface MemWriteClient#(DataBusWidth) to_host_write;

    // Initialize the shared memory with the ref pointer and size.
    // If an address is out of range, it will handled (somehow)
    method Action initSharedMem(Bit#(32) refPointer, Bit#(64) memSize);

    // Methods for clearing pending requests before reset
    method Action flushRespReqMem;
    method PendMemRespCnt numberFlyingOperations;
endinterface

// This bridge assumes the shared memory responds to load requests in order
module mkSharedMemoryBridge(SharedMemoryBridge#(dataSz)) provisos (
        Mul#(DataBusWidth, packetsPerWrite, dataSz),
        Mul#(8, bytesPerReq, dataSz)
    );
    Bool verbose = False;
    File tracefile = verbose ? stdout : tagged InvalidFile;

    Ehr#(2, Bit#(dataSz)) writeData <- mkEhr(0);
    Ehr#(2, Maybe#(Bit#(TLog#(packetsPerWrite)))) writeDataIndex <- mkEhr(tagged Invalid);
    Ehr#(2, Bit#(dataSz)) readData <- mkEhr(0);
    Ehr#(2, Maybe#(Bit#(TLog#(packetsPerWrite)))) readDataIndex <- mkEhr(tagged Valid 0);

    // TODO: Make pendingReqs larger than 1 and add a way to enforce
    // per-address ordering between loads and stores

    // Bool is for isWrite
    FIFOF#(Bool)                            pendingReqs   <- fprintTraceM(tracefile, "SharedMemoryBridge::pendingReqs",   mkSizedFIFOF(1));
    FIFO#(MemRequest)                       readReqFifo   <- fprintTraceM(tracefile, "SharedMemoryBridge::readReqFifo",   mkFIFO);
    FIFO#(MemRequest)                       writeReqFifo  <- fprintTraceM(tracefile, "SharedMemoryBridge::writeReqFifo",  mkFIFO);
    FIFO#(MemData#(DataBusWidth))           writeDataFifo <- fprintTraceM(tracefile, "SharedMemoryBridge::writeDataFifo", mkSizedBRAMFIFO(2 * valueOf(packetsPerWrite)));
    FIFO#(MemData#(DataBusWidth))           readDataFifo  <- fprintTraceM(tracefile, "SharedMemoryBridge::readDataFifo",  mkFIFO);
    FIFO#(Bit#(MemTagSize))                 writeDoneFifo <- fprintTraceM(tracefile, "SharedMemoryBridge::writeDoneFifo", mkFIFO);

    Reg#(SGLId)                             refPointerReg <- mkReg(0);
    Reg#(PAddr)                             memSizeReg    <- mkReg(64 << 20); // 64 MB by default
    Reg#(Bool)                              flushRespReq  <- mkReg(False);

    // addr aligned with 8B boundary
    function PAddr getDWordAlignAddr(PAddr a);
        // FIXME: Clean this up
`ifdef rv64
        return {truncateLSB(a), 3'b0};
`else
        return {truncateLSB(a), 2'b0};
`endif
    endfunction

    // This function adjusts the address to point to a valid location in memory
    // If the memory size is a power of 2, it simply truncates it.
    // Otherwise is uses a weird mask derived form memSizeReg - 1
    function PAddr adjustAddress(PAddr a);
        // This works really well if the address is a power of 2, otherwise it has
        // weird behavior (but still functions as desired).
        let memSizeMask = memSizeReg - 1;
        // If the address needs adjusting, and it with memSizeMask
        return (a >= memSizeReg) ? (a & memSizeMask) : a;
    endfunction

    rule sendWriteData(writeDataIndex[1] matches tagged Valid .index);
        Vector#(packetsPerWrite, Bit#(DataBusWidth)) dataVector = unpack(writeData[1]);
        Bit#(DataBusWidth) writePacketData = dataVector[index];
        Bool last = (index == fromInteger(valueOf(packetsPerWrite) - 1));
        writeDataFifo.enq(MemData{data: writePacketData, tag: 0, last: last});
        if (last) begin
            writeDataIndex[1] <= tagged Invalid;
        end else begin
            writeDataIndex[1] <= tagged Valid (index + 1);
        end
    endrule

    rule formatReadData(readDataIndex[0] matches tagged Valid .index);
        Vector#(packetsPerWrite, Bit#(DataBusWidth)) dataVector = unpack(readData[0]);
        dataVector[index] = readDataFifo.first.data;
        readData[0] <= pack(dataVector);
        Bool last = (index == fromInteger(valueOf(packetsPerWrite) - 1) || readDataFifo.first.last);
        if (last) begin
            readDataIndex[0] <= tagged Invalid;
        end else begin
            readDataIndex[0] <= tagged Valid (index + 1);
        end
        readDataFifo.deq;
    endrule

    interface Server to_proc;
        interface Put request;
            method Action put(GenericMemReq#(dataSz) r) if (!isValid(writeDataIndex[0]));
                if (pack(r.byteen) != '1) begin
                    $fdisplay(stderr, "[ERROR] [SharedMem] request - byteEn != '1");
                end

                PAddr addr = adjustAddress(getDWordAlignAddr(r.addr));
                if (r.write) begin
                    // $display("[SharedMem] write - addr: 0x%08x, data: 0x%08x", addr, r.data);
                    writeReqFifo.enq(MemRequest{sglId: refPointerReg, offset: truncate(addr), burstLen: fromInteger(valueOf(bytesPerReq)), tag: 0});
                    pendingReqs.enq(True);
                    writeData[0] <= r.data;
                    writeDataIndex[0] <= tagged Valid 0;
                end else begin
                    // $display("[SharedMem] read - addr: 0x%08x", addr);
                    readReqFifo.enq(MemRequest{sglId: refPointerReg, offset: truncate(addr), burstLen: fromInteger(valueOf(bytesPerReq)), tag: 1});
                    pendingReqs.enq(False);
                end
            endmethod
        endinterface
        interface Get response;
            method ActionValue#(GenericMemResp#(dataSz)) get;
                let isWrite = pendingReqs.first;
                pendingReqs.deq;

                if (isWrite) begin
                    writeDoneFifo.deq;
                    return GenericMemResp{write: True, data: 0};
                end else begin
                    // only fire if formatReadData is done
                    when(!isValid(readDataIndex[1]), noAction);
                    readData[1] <= 0;
                    readDataIndex[1] <= tagged Valid 0;
                    return GenericMemResp{write: False, data: readData[1]};
                end
            endmethod
        endinterface
    endinterface

    interface MemReadClient to_host_read;
        interface Get readReq = toGet(readReqFifo);
        interface Put readData = toPut(readDataFifo);
    endinterface

    interface MemWriteClient to_host_write;
        interface Get writeReq = toGet(writeReqFifo);
        interface Get writeData = toGet(writeDataFifo);
        interface Put writeDone = toPut(writeDoneFifo);
    endinterface

    method Action initSharedMem(Bit#(32) refPointer, Bit#(64) memSize);
        // $display("[SharedMem] refPointer = 0x%08x. memSize = 0x%08x", refPointer, memSize);
        refPointerReg <= refPointer;
        // PAddrSz should be 64 or less
        memSizeReg <= truncate(memSize);
    endmethod

    method Action flushRespReqMem;
        flushRespReq <= True;
    endmethod
    method PendMemRespCnt numberFlyingOperations;
        return pendingReqs.notEmpty ? 1 : 0;
    endmethod
endmodule
