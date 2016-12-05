
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
import ClientServer::*;
import SpecialFIFOs::*;
import FIFO::*;
import FIFOF::*;
import Ehr::*;
import GetPut::*;
import RVTypes::*;
import RVExec::*; // for gatherLoad and scatterStore
import RWBram::*;
import Vector::*;
import RVAmo::*;
import DefaultValue::*;
import SafeCounter::*;
import CompareProvisos::*;


typedef Bit#(4) PendMemRespCount;

// type parameters
typedef 4 DCacheWayNum;
typedef 128 DCacheSetNum;

typedef enum {I, S, M} MSI deriving(Bits, Eq);

typedef enum {
    Init,
    ProcReq,
    Flush
} CacheStatus deriving(Bits, Eq);

typedef enum {
    Ready, 
    SendFillReq, 
    WaitFillResp
} MissStatus deriving(Bits, Eq);

// cache pipeline: issue -> match
typedef struct {
    RVDMemReq req;
    // bypass info
    Vector#(wayNum, Maybe#(cacheLine)) lineVec;
    Vector#(wayNum, Maybe#(tagT)) tagVec;
    Vector#(wayNum, Maybe#(MSI)) stateVec;
} Issue2Match#(type cacheLine, numeric type wayNum, type tagT) deriving(Bits, Eq);

// cache pipeline: match -> process
typedef struct {
    RVDMemReq req;
    Bool hit;
    // info of the hit/replace way
    wayT way;
    cacheLine line;
    tagT tag;
    MSI state;
} Match2Process#(type cacheLine, type wayT, type tagT) deriving(Bits, Eq);

// cache pipeline: bypass write to ram
typedef struct {
    indexT index;
    wayT way;
    Maybe#(cacheLine) line;
    Maybe#(tagT) tag;
    Maybe#(MSI) state;
} BypassInfo#(type cacheLine, type indexT, type wayT, type tagT) deriving(Bits, Eq);

interface Cache;
    interface Server#(RVDMemReq, RVDMemResp) to_proc;
    method Action flush; // invalidate whole cache
    method Bool flush_done;
endinterface

// blocking cache: 2-cycle latency from req to resp
// cache size = setNum * wayNum * LineDataNum * 8B
module mkDCache#(GenericMemServer#(cacheLineSz) mainMemory)(Cache) provisos (
        // get params
        NumAlias#(wayNum, DCacheWayNum),
        NumAlias#(setNum, DCacheSetNum),
        NumAlias#(cacheLineSz, CacheLineSz), // If this is omitted, then cache size will be a parameter
        Alias#(reqIdT, Bit#(0)),

        // deduce param
        NumAlias#(logWayNum, TLog#(wayNum)),

        NumAlias#(logSetNum, TLog#(setNum)),
            EQ#(TExp#(logSetNum), setNum), // setNum must be a power of 2

        NumAlias#(clineNumData, TDiv#(cacheLineSz, DataSz)),
            EQ#(TMul#(clineNumData, DataSz), cacheLineSz), // dataSz must divide cacheLineSz

        NumAlias#(logCLineNumData, TLog#(clineNumData)),
            EQ#(TExp#(logCLineNumData), clineNumData), // clineNumData must be a power of 2

        NumAlias#(clineNumBytes, TDiv#(cacheLineSz, 8)),
            EQ#(TMul#(clineNumBytes, 8), cacheLineSz), // 8 must divide cacheLineSz

        NumAlias#(logCLineNumBytes, TLog#(clineNumBytes)),
            EQ#(TExp#(logCLineNumBytes), clineNumBytes), // clineNumBytes must be a power of 2

        NumAlias#(cacheTagSz, TSub#(AddrSz, TAdd#(logSetNum, logCLineNumBytes))),

        Alias#(cacheIndex, Bit#(logSetNum)),
        Alias#(cacheTag, Bit#(cacheTagSz)),
        Alias#(cacheWay, Bit#(logWayNum)),
        Alias#(cacheLine, Bit#(cacheLineSz)),
        Alias#(issue2Match, Issue2Match#(cacheLine, wayNum, cacheTag)),
        Alias#(match2Process, Match2Process#(cacheLine, cacheWay, cacheTag)),
        Alias#(bypassInfo, BypassInfo#(cacheLine, cacheIndex, cacheWay, cacheTag))
    );

    function cacheIndex getIndex(Addr a);
        return truncate(a >> valueOf(logCLineNumBytes));
    endfunction

    function cacheTag getTag(Addr a);
        return truncateLSB(a);
    endfunction

    function logCLineNumData getCLineDataSel(Addr a);
        return truncate(a >> valueOf(TLog#(TDiv#(XLEN,8))));
    endfunction

    // RAMs
    Vector#(wayNum, RWBram#(cacheIndex, cacheLine)) dataRam <- replicateM(mkRWBram);
    Vector#(wayNum, RWBram#(cacheIndex, cacheTag)) tagRam <- replicateM(mkRWBram);
    Vector#(wayNum, RWBram#(cacheIndex, MSI)) stateRam <- replicateM(mkRWBram);

    // init
    Reg#(cacheIndex) initIndex <- mkReg(0);

    // flush cache
    Reg#(Bool) flushDone <- mkReg(True);
    // stage 1: issue read
    Reg#(cacheIndex) flushReadIndex <- mkReg(0);
    Reg#(cacheWay) flushReadWay <- mkReg(0);
    Reg#(Bool) lastToFlush <- mkReg(False); // asserted when only 1 line to flush in stage 2
    // stage 2: invalidate
    Reg#(cacheIndex) flushInvIndex <- mkRegU;
    Reg#(cacheWay) flushInvWay <- mkRegU;
    // need to wait all write-backs are committed
    Reg#(Bool) waitWBCommit <- mkReg(False);

    FIFO#(Tuple3#(DataByteSel,RVMemSize,Bool)) outstanding <- mkFIFO;

    // record pending write-back resp num to make sure all stores are committed
    SafeCounter#(PendMemRespCount) pendWBRespCnt <- mkSafeCounter(0);

    // blocking pipelined cache
    // stage 1: issue read req to rams
    // stage 2: get ram outputs & match tags
    // stage 3: process req

    // stage 1 -> 2 pipeline reg
    Ehr#(3, Maybe#(issue2Match)) iss2Mat <- mkEhr(tagged Invalid);
    // port 0: bypass overwrite contents
    Reg#(Maybe#(issue2Match)) iss2Mat_bypass = iss2Mat[0];
    // port 1: read & reset to invalid by stage 2
    Reg#(Maybe#(issue2Match)) iss2Mat_match = iss2Mat[1];
    // port 2: check invalid & write by stage 1
    Reg#(Maybe#(issue2Match)) iss2Mat_issue = iss2Mat[2];

    // stage 2 -> 3 pipeline reg
    Ehr#(2, Maybe#(match2Process)) mat2Proc <- mkEhr(tagged Invalid);
    // port 0: read & reset to invalid by stage 3
    Reg#(Maybe#(match2Process)) mat2Proc_process = mat2Proc[0];
    // port 1: check invalid & write by stage 2
    Reg#(Maybe#(match2Process)) mat2Proc_match = mat2Proc[1];
    // no bypass is needed for this reg

    // stage 3
    // miss status
    Reg#(MissStatus) missStatus <- mkReg(Ready);
    // bypass the write made in this stage to previous stages
    Ehr#(2, Maybe#(bypassInfo)) bypass2Issue <- mkEhr(tagged Invalid);
    Ehr#(2, Maybe#(bypassInfo)) bypass2Match <- mkEhr(tagged Invalid);

    // resp to processor
    // size = 3 = size of f22f2 (I fetch FIFO) & m12m2 (D access FIFO)
    // so sending resp to proc will never be blocked
    // otherwise when I D are coherent, I$ D$ may block each other => deadlock
    FIFOF#(RVDMemResp) procRespQ <- mkSizedBypassFIFOF(3);

    // We need a buffer to keep responses from main memory to ensure they do
    // not block other responses
    FIFO#(GenericMemResp#(cacheLineSz)) mainMemRespFIFO <- mkBypassFIFO;

    // overall cache status
    Reg#(CacheStatus) status <- mkReg(Init);
    // init is only done once
    // ProcReq (process pending req) is the normal state
    // priority: process pending req > flush cache
    // Once starting flush cache, cannot exit before finish
    // When flush cache finishes, go back to ProcReq
    // flush cache can start if 
    // (1) no pending req 
    // (2) in ProcReq state

    // flush cache is started in a non-blocking way: 
    // first reset Done flag
    // then wait right time to start real flush
    Bool noProcReq = !isValid(iss2Mat[0]) && !isValid(mat2Proc[0]);
    Bool startFlush = status == ProcReq && noProcReq && !flushDone;

    // random replacement policy
    Reg#(cacheWay) randWay <- mkReg(0);

    rule incRandWay;
        randWay <= randWay + 1;
    endrule

    function cacheWay getRandReplaceWay(Vector#(wayNum, MSI) stateVec);
        Maybe#(cacheWay) invWay = tagged Invalid;
        for(Integer i = 0; i < valueOf(wayNum); i = i+1) begin
            if(stateVec[i] == I) begin
                invWay = Valid (fromInteger(i));
            end
        end
        return fromMaybe(randWay, invWay);
    endfunction

    rule getMainMemResp;
        let resp <- mainMemory.response.get();
        if (resp.write) begin
            // decrement counter and drop response
            pendWBRespCnt.decr(1);
        end else begin
            mainMemRespFIFO.enq(resp);
        end
    endrule

    // initialize: make cache all invalid
    rule doInit(status == Init);
        for(Integer i = 0; i < valueOf(wayNum); i=i+1) begin
            stateRam[i].wrReq(initIndex, I);
        end
        initIndex <= initIndex + 1;
        if(initIndex == maxBound) begin
            status <= ProcReq;
        end
    endrule

    // flush cache
    rule doStartFlush(startFlush);
        status <= Flush;
        flushReadWay <= 0;
        flushReadIndex <= 0;
        lastToFlush <= False;
        waitWBCommit <= False;
    endrule

    rule doFlushCache(status == Flush && !flushDone && !waitWBCommit); 
        // !flushDone in guard to prevent conflict rule

        cacheWay maxWayId = fromInteger(valueOf(wayNum) - 1);

        // pipe stage 1: issue read to cache line
        if(!lastToFlush) begin
            dataRam[flushReadWay].rdReq(flushReadIndex);
            tagRam[flushReadWay].rdReq(flushReadIndex);
            stateRam[flushReadWay].rdReq(flushReadIndex);
            // incr way/index
            if(flushReadWay == maxWayId) begin
                flushReadWay <= 0;
                flushReadIndex <= flushReadIndex + 1;
            end
            else begin
                flushReadWay <= flushReadWay + 1;
            end
            // record old way/index for stage 2
            flushInvWay <= flushReadWay;
            flushInvIndex <= flushReadIndex;
        end

        // pipe stage 2: get cache line & invalidate & may write back
        if(flushReadIndex != 0 || flushReadWay != 0 || lastToFlush) begin
            let way = flushInvWay;
            let index = flushInvIndex;
            // get cache line
            let data <- dataRam[way].rdResp;
            let tag <- tagRam[way].rdResp;
            let state <- stateRam[way].rdResp;
            // invalidate
            stateRam[way].wrReq(index, I);
            // write back
            if(state == M) begin
                mainMemory.request.put(GenericMemReq{write: True, byteen: '1, addr: {tag, index, 0}, data: data});
                pendWBRespCnt.incr(1); // record pending write resp
            end
        end

        // change lastToFlush & start waiting
        if(flushReadWay == maxWayId && flushReadIndex == maxBound && !lastToFlush) begin
            lastToFlush <= True;
        end
        else if(flushReadWay == 0 && flushReadIndex == 0 && lastToFlush) begin
            lastToFlush <= False;
            waitWBCommit <= True;
        end
    endrule

    rule doWaitFlush(status == Flush && !flushDone && waitWBCommit && pendWBRespCnt == 0);
        // !flushDone in guard to prevent conflict rule
        // all write-backs have committed, flush done
        flushDone <= True;
        status <= ProcReq;
        waitWBCommit <= False;
    endrule

    // stage 2 of cache: first get bypass
    (* fire_when_enabled, no_implicit_conditions *)
    rule doBypassToMatch(isValid(bypass2Match[1]) && isValid(iss2Mat_bypass));
        let b = fromMaybe(?, bypass2Match[1]);
        let i2m = fromMaybe(?, iss2Mat_bypass);
        let reqIndex = getIndex(i2m.req.addr);
        // merge with bypass
        if(reqIndex == b.index) begin
            if(isValid(b.tag)) begin
                i2m.tagVec[b.way] = b.tag;
            end
            if(isValid(b.state)) begin
                i2m.stateVec[b.way] = b.state;
            end
            if(isValid(b.line)) begin
                i2m.lineVec[b.way] = b.line;
            end
            // set reg
            iss2Mat_bypass <= Valid (i2m);
        end
    endrule

    // stage 2 of cache: get cache result & tag match
    // resolve conflict with start flush
    (* descending_urgency = "doStartFlush, doTagMatch" *)
    rule doTagMatch(status == ProcReq && isValid(iss2Mat_match) && !isValid(mat2Proc_match));
        let i2m = fromMaybe(?, iss2Mat_match);
        // get cache result
        Vector#(wayNum, cacheLine) lineVec = ?;
        Vector#(wayNum, cacheTag) tagVec = ?;
        Vector#(wayNum, MSI) stateVec = ?;
        for(Integer i = 0; i < valueOf(wayNum); i = i+1) begin
            lineVec[i] <- dataRam[i].rdResp;
            tagVec[i] <- tagRam[i].rdResp;
            stateVec[i] <- stateRam[i].rdResp;
        end
        // merge with bypassing data
        for(Integer i = 0; i < valueOf(wayNum); i = i+1) begin
            if(i2m.tagVec[i] matches tagged Valid .t) begin
                tagVec[i] = t;
            end
            if(i2m.stateVec[i] matches tagged Valid .s) begin
                stateVec[i] = s;
            end
            if(i2m.lineVec[i] matches tagged Valid .l) begin
                lineVec[i] = l;
            end
        end
        // do tag match
        cacheTag reqTag = getTag(i2m.req.addr);
        Maybe#(cacheWay) hitWay = tagged Invalid;
        for(Integer i = 0; i < valueOf(wayNum); i = i+1) begin
            if(reqTag == tagVec[i] && stateVec[i] != I) begin
                hitWay = Valid (fromInteger(i));
            end
        end
        // get replace way
        cacheWay repWay = getRandReplaceWay(stateVec);
        // get the final way to occupy
        cacheWay occWay = fromMaybe(repWay, hitWay);
        Bool hit = isValid(hitWay);
        // set pipeline reg
        mat2Proc_match <= Valid (Match2Process {
            req: i2m.req,
            hit: hit,
            way: occWay,
            line: lineVec[occWay],
            tag: tagVec[occWay],
            state: stateVec[occWay]
        });
        // reset pipeline reg
        iss2Mat_match <= tagged Invalid;
    endrule

    // stage 3 of cache: process req

    // handle req:
    // (1) enq resp
    // (2) write cache
    // (3) set bypass
    // (4) reset pipeline reg to invalid
    // XXX: curState must be S if refill = True
    function Action handleReq(RVDMemReq r, cacheWay way, Vector#(clineNumData, Data) curLine, MSI curState, Bool refill);
        return action
            cacheIndex reqIndex = getIndex(r.addr);
            cacheTag reqTag = getTag(r.addr);
            CLineDataSel reqDataSel = getCLineDataSel(r.addr);

            // value to be written back to ram
            Vector#(clineNumData, Data) newLine = curLine;
            MSI newState = curState;

            // process
            if (isLoad(r.op)) begin
                procRespQ.enq(curLine[reqDataSel]);
                // keep state & data same
            end else if (isStore(r.op) || isAmo(r.op)) begin // includes AMO
                newState = M; // set state to dirty
                Data curData = curLine[reqDataSel];
                // both AMO and normal stores are handled with amoExec
                RVAmoOp amoFunc = r.op matches tagged Amo .amoFunc ? amoFunc : Swap;
                let {permutedDataByteEn, permutedStData} = scatterStore(truncate(r.addr), r.size, r.data);
                newLine[reqDataSel] = amoExec(amoFunc, permutedDataByteEn, curData, permutedStData);
                if (r.op matches tagged Amo .*) begin
                    procRespQ.enq(curData);
                end else if (r.op == tagged Mem Sc) begin
                    // Sc is always successful
                    procRespQ.enq(0);
                end
            end

            // write to RAM
            if (refill || isStore(r.op) || isAmo(r.op)) begin
                // write ram
                dataRam[way].wrReq(reqIndex, pack(newLine));
                tagRam[way].wrReq(reqIndex, reqTag);
                stateRam[way].wrReq(reqIndex, newState);
                // set bypass
                bypassInfo b = BypassInfo {
                    index: reqIndex,
                    way: way,
                    line: Valid (pack(newLine)),
                    tag: Valid (reqTag),
                    state: Valid (newState)
                };
                bypass2Issue[0] <= tagged Valid (b);
                bypass2Match[0] <= tagged Valid (b);
            end

            // reset pipeline reg
            mat2Proc_process <= tagged Invalid;
        endaction;
    endfunction

    Bool processReq = status == ProcReq && isValid(mat2Proc_process);

    rule doProcReq_checkHit(processReq && missStatus == Ready);
        let m2p = fromMaybe(?, mat2Proc_process);
        if(m2p.hit) begin
            // hit: process
            handleReq(m2p.req, m2p.way, unpack(m2p.line), m2p.state, False);
        end else begin
            // miss: replace cacheline if needed
            if(m2p.state == M) begin
                let index = getIndex(m2p.req.addr);
                mainMemory.request.put(GenericMemReq{write: True, byteen: '1, addr: {m2p.tag, index, 0}, data: m2p.line});
                pendWBRespCnt.incr(1); // record pending write resp
                // XXX: no need to write ram: 
                // (1) younger req cannot reach Process stage before the miss resolves
                // (2) there is no invalidation from mem
            end
            // change status
            missStatus <= SendFillReq;

            // performance counter: always record begin time
            // even if doStats = False
        end
    endrule

    rule doProcReq_sendFillReq(processReq && missStatus == SendFillReq);
        let m2p = fromMaybe(?, mat2Proc_process);
        RVDMemReq r = m2p.req;
        cacheIndex index = getIndex(r.addr);
        cacheTag tag = getTag(r.addr);
        mainMemory.request.put(GenericMemReq{write: False, byteen: '1, addr: {tag, index, 0}, data: ?});
        // change miss status
        missStatus <= WaitFillResp;
    endrule

    rule doProcReq_waitFillResp(processReq && missStatus == WaitFillResp);
        let m2p = fromMaybe(?, mat2Proc_process);
        // handle req: curState must be set to S (line is valid now)
        let resp = mainMemRespFIFO.first;
        mainMemRespFIFO.deq;
        when(resp.write == False, noAction);
        handleReq(m2p.req, m2p.way, unpack(resp.data), S, True);
        // change miss status
        missStatus <= Ready;
    endrule

    // reset bypass EHRs
    (* fire_when_enabled, no_implicit_conditions *)
    rule resetBypass;
        bypass2Issue[1] <= tagged Invalid;
        bypass2Match[1] <= tagged Invalid;
    endrule

    method Action flush if(flushDone);
        flushDone <= False;
    endmethod

    method Bool flush_done = flushDone;

    interface Server to_proc;
        interface Put request;
            // stage 1: accept new processor req & issue cache read
            // only accept new req from processor when
            // (1) in normal ProcReq status
            // (2) nothing special is pending
            // (3) issue->match pipeline reg is empty
            method Action put(RVDMemReq r) if(status == ProcReq && flushDone && !isValid(iss2Mat_issue));
                // XXX: enqueuing into outstanding FIFO for gatherLoad
                if (isLoad(r.op) || isAmo(r.op)) begin
                    DataByteSel addrByteSel = truncate(r.addr);
                    outstanding.enq(tuple3(addrByteSel, r.size, r.isUnsigned));
                end else if (r.op == tagged Mem Sc) begin
                    outstanding.enq(tuple3(0, B, False));
                end

                cacheIndex index = getIndex(r.addr);
                for(Integer i = 0; i < valueOf(wayNum); i = i+1) begin
                    dataRam[i].rdReq(index);
                    tagRam[i].rdReq(index);
                    stateRam[i].rdReq(index);
                end
                // write pipeline reg & get bypass
                issue2Match i2m = Issue2Match {
                    req: r,
                    lineVec: replicate(tagged Invalid),
                    tagVec: replicate(tagged Invalid),
                    stateVec: replicate(tagged Invalid)
                };
                if(bypass2Issue[1] matches tagged Valid .b &&& b.index == index) begin
                    i2m.lineVec[b.way] = b.line;
                    i2m.tagVec[b.way] = b.tag;
                    i2m.stateVec[b.way] = b.state;
                end
                iss2Mat_issue <= Valid (i2m);
            endmethod
        endinterface

        interface Get response;
            method ActionValue#(RVDMemResp) get;
                let {addrByteSel, size, isUnsigned} = outstanding.first;
                outstanding.deq;
                procRespQ.deq;
                return gatherLoad(addrByteSel, size, isUnsigned, procRespQ.first);
            endmethod
        endinterface
    endinterface
endmodule

