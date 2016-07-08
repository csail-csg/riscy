
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

import RVTypes::*;
import List::*;

// TlbStorage.bsv
// Only for Sv39

typedef 27 VpnSz;
typedef Bit#(27) Vpn;
typedef 38 PpnSz;
typedef Bit#(38) Ppn;
typedef 12 OffsetSz;
typedef Bit#(OffsetSz) Offset;
typedef 9 VpnISz;
typedef Bit#(VpnISz) VpnI;

typedef Bit#(2) PageSize;

interface TlbStorage;
    method Action flush_translation(Vpn vpn, Asid asid, Bool all);
    method ActionValue#(Maybe#(Tuple4#(Ppn,PTE_Type,PageSize,Bool))) translate(Vpn vpn, Asid asid, Bool write_supervisor, Bool write_user);
    method Action add_translation(TlbRow x);
endinterface

typedef struct {
    Bool        valid;
    Vpn         vpn;
    Ppn         ppn;
    PTE_Type    page_perm;
    PageSize    page_size;
    Asid        asid;
    Bool        dirty;
} TlbRow deriving (Bits, Eq, FShow);

function Maybe#(Tuple4#(Ppn,PTE_Type,PageSize,Bool)) filter_matches(Vpn vpn, Asid asid, TlbRow tlbrow);
    let ret = tagged Invalid;
    Vpn masked_vpn = (case (tlbrow.page_size)
            0:  vpn;
            1:  (vpn & 27'h7FFFE00); // megapage mask
            2:  (vpn & 27'h7FC0000); // gigapage mask
            3:  0;
        endcase);
    if (tlbrow.valid && (tlbrow.vpn == masked_vpn) && ((asid == tlbrow.asid) || tlbrow.page_perm.global)) begin
        ret = tagged Valid tuple4(tlbrow.ppn, tlbrow.page_perm, tlbrow.page_size, tlbrow.dirty);
    end
    return ret;
endfunction

function Maybe#(a) tlb_fold_search_results(Maybe#(a) x, Maybe#(a) y) provisos (Bits#(a, aSz));
    // At most one of x and y should be tagged valid
    Bool out_valid = isValid(x) || isValid(y);
    a out_data = unpack(pack(fromMaybe(unpack(0),x)) | pack(fromMaybe(unpack(0),y)));
    return out_valid ? tagged Valid out_data : tagged Invalid;
endfunction

function Action tlb_array_flush(Reg#(a) tlb_reg, Bool flush) provisos (Bits#(a, aSz));
    return flush ? tlb_reg._write(unpack(0)) : noAction;
endfunction

function Action update_dirty_bit(Reg#(TlbRow) tlb_reg, Bool dirty);
    return (action
            if (dirty) begin
                let val = tlb_reg._read();
                val.dirty = True;
                tlb_reg._write(val);
            end
        endaction);
endfunction

// TODO: replace read_reg with built in BSV function
function List#(a) readListReg(List#(Reg#(a)) l);
    function a read_reg(Reg#(a) r) = r._read;
    return map(read_reg, l);
endfunction

module mkTlbStorage#(Integer tlb_size)(TlbStorage);
    List#(Reg#(TlbRow)) tlb_array_data  <- replicateM(tlb_size, mkReg(unpack(0)));

    // TODO: replace this register with something else
    Reg#(Bit#(8)) i <- mkReg(0);

    method Action flush_translation(Vpn vpn, Asid asid, Bool all);
        // XXX: This could be used to select a line to flush:
        // List#(Bool) lines_to_flush = map(compose( \|| (all) ,compose(isValid, filter_matches(vpn, asid))), tlb_array_data);
        // But for now, flush the whole thing because the above solution would require
        // two associative searches ... and risc-v linux doesn't use precise flushes at the moment
        List#(Bool) lines_to_flush = replicate(tlb_size, True);
        joinActions(zipWith(tlb_array_flush, tlb_array_data, lines_to_flush));
    endmethod

    method ActionValue#(Maybe#(Tuple4#(Ppn,PTE_Type,PageSize,Bool))) translate(Vpn vpn, Asid asid, Bool write, Bool supervisor);
        // Apply the filter_matches function to each entry in the TLB. At most one should return a valid match.
        List#(Maybe#(Tuple4#(Ppn,PTE_Type,PageSize,Bool))) map_result = map(filter_matches(vpn, asid), readListReg(tlb_array_data));
        // Combine the matches with an OR - This is slightly faster/cheaper than a mux
        Maybe#(Tuple4#(Ppn,PTE_Type,PageSize,Bool)) search_result = foldr1(tlb_fold_search_results, map_result);
        if (isValid(search_result)) begin
            // Update the dirty bits as necessary
            Bool first_write_to_page = False;
            let {ppn, pageperm, pagesize, dirty} = fromMaybe(unpack(0), search_result);
            if ((write && supervisor && pageperm.s_w) || (write && !supervisor && pageperm.u_w)) begin
                // write will happen
                if (!dirty) begin
                    // this is the first write to the page
                    first_write_to_page = True;
                    joinActions(zipWith(update_dirty_bit, tlb_array_data, map(isValid, map_result)));
                end
            end
            // update the 4th entry to be true if the page table entry needs to be updated
            search_result = tagged Valid tuple4(ppn, pageperm, pagesize, first_write_to_page);
        end
        return search_result;
    endmethod

    method Action add_translation(TlbRow x);
        // TODO: implement a better replacement policy for the TLB
        tlb_array_data[i] <= x;
        i <= (i == fromInteger(tlb_size-1) ? 0 : i+1);
    endmethod
endmodule

module mkEmptyTlbStorage(TlbStorage);
    method Action flush_translation(Vpn vpn, Asid asid, Bool all);
        noAction;
    endmethod

    method ActionValue#(Maybe#(Tuple4#(Ppn,PTE_Type,PageSize,Bool))) translate(Vpn vpn, Asid asid, Bool write, Bool supervisor);
        return tagged Invalid;
    endmethod

    method Action add_translation(TlbRow x);
        noAction;
    endmethod
endmodule
