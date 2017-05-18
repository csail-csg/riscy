
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
import ConcatReg::*;
import ConfigReg::*;
import DefaultValue::*;
import RegUtil::*;
import Vector::*;

typedef union tagged {
    struct {
        TrapCause exception;
        Bit#(xlen) trapHandlerPC;
    } Exception;     // exception/interrupt redirection
    Bit#(xlen) RedirectPC; // non-trap redirection (xRET)
    Bit#(xlen) CsrData;    // CSR read operations
    void None;       // all other operations
} CsrReturn#(numeric type xlen) deriving (Bits, Eq, FShow);

interface RVCsrFile#(numeric type xlen);
    // Read and Write ports
    // method Data rd(CSR csr);
    method ActionValue#(CsrReturn#(xlen))
        wr( Bit#(xlen) pc,
            Maybe#(SystemInst) sysInst,
            CSR csr,
            Bit#(xlen) data, // zimm or rval
            Bit#(xlen) addr, // badaddr
            Maybe#(TrapCause) trap, // exception or interrupt
            // indirect updates
            Bit#(5) fflags,
            Bool fpuDirty,
            Bool xDirty);

    // Outputs for CSRs that the rest of the processor needs to know about
    method VMInfo#(xlen) vmI;
    method VMInfo#(xlen) vmD;
    method CsrState csrState; // prv, frm, f_enabled, x_enabled
    method Maybe#(InterruptCause) readyInterrupt; // TODO: fix this data type
    method Bool wakeFromWFI;
endinterface

module mkRVCsrFile#(
            Data hartid,                      // Compile-time constant
            Bit#(64) time_counter, Bool mtip, // From RTC
            Bool msip,                        // From IPI
            Bool meip                         // From interrupt controller
        )(RVCsrFile#(xlen)) provisos (NumAlias#(XLEN, xlen));

    let verbose = False;
    File fout = stdout;

    RiscVISASubset isa = defaultValue;
    Bool is32bit       = valueOf(xlen) == 32;
    Data mvendorid     = 0; // non-commercial
    Data marchid       = 0; // not implemented
    Data mimpid        = 0; // not implemented
    Addr default_mtvec = 'h0000_1000;
    Addr default_stvec = 'h0000_8000;

    // This is used to allow the readyInterruptSignal to be read after writing to the CSRF
    Wire#(Maybe#(InterruptCause)) readyInterruptWire <- mkDWire(tagged Invalid);

    Reg#(Bit#(2)) prv <- mkReg(prvM); // resets to machine mode

    // Counters
    Reg#(Bit#(64)) cycle_counter <- mkReg(0);
    Reg#(Bit#(64)) instret_counter <- mkReg(0);

    // Counter enables
    Reg#(Bit#(1)) u_ir_field <- mkReg(0);
    Reg#(Bit#(1)) u_tm_field <- mkReg(0);
    Reg#(Bit#(1)) u_cy_field <- mkReg(0);
    Reg#(Bit#(1)) s_ir_field <- mkReg(0);
    Reg#(Bit#(1)) s_tm_field <- mkReg(0);
    Reg#(Bit#(1)) s_cy_field <- mkReg(0);

    // FPU Fields
    Reg#(Bit#(5)) fflags_field  <- mkReg(0);
    Reg#(Bit#(3)) frm_field     <- mkReg(0);

    // vm fields
`ifdef CONFIG_RV64
    // XLEN = 64
    Reg#(Bit#(26)) asid_field      <- mkReg(0);
    Reg#(Bit#(38)) sptbr_ppn_field <- mkReg(0);
`else
    // XLEN = 32
    Reg#(Bit#(10)) asid_field      <- mkReg(0);
    Reg#(Bit#(22)) sptbr_ppn_field <- mkReg(0);
`endif

    // trap delegation fields
    Reg#(Bit#(12)) sedeleg_field <- mkReg(0);
    Reg#(Bit#(12)) sideleg_field <- mkReg(0);
    Reg#(Bit#(12)) medeleg_field <- mkReg(0);
    Reg#(Bit#(12)) mideleg_field <- mkReg(0);

    // trap vector fields (same as CSR without bottom 2 bits)
    Reg#(Bit#(TSub#(xlen,2))) mtvec_field <- mkReg(truncateLSB(default_mtvec));
    Reg#(Bit#(TSub#(xlen,2))) stvec_field <- mkReg(truncateLSB(default_stvec));

    // mstatus fields
    Reg#(Bit#(5)) vm_field   <- mkReg(0); // WARL
    Reg#(Bit#(1)) mxr_field  <- mkReg(0);
    Reg#(Bit#(1)) pum_field  <- mkReg(0);
    Reg#(Bit#(1)) mprv_field <- mkReg(0);
    Reg#(Bit#(2)) xs_field   <- mkReg(0);
    Reg#(Bit#(2)) fs_field   <- mkReg(0);
    Reg#(Bit#(2)) mpp_field  <- mkReg(0);
    Reg#(Bit#(2)) hpp_field  =  readOnlyReg(0);
    Reg#(Bit#(1)) spp_field  <- mkReg(0);
    Reg#(Bit#(1)) mpie_field <- mkReg(0);
    Reg#(Bit#(1)) hpie_field =  readOnlyReg(0);
    Reg#(Bit#(1)) spie_field <- mkReg(0);
    Reg#(Bit#(1)) upie_field <- mkReg(0);
    Reg#(Bit#(1)) mie_field  <- mkReg(0);
    Reg#(Bit#(1)) hie_field  =  readOnlyReg(0);
    Reg#(Bit#(1)) sie_field  <- mkReg(0);
    Reg#(Bit#(1)) uie_field  <- mkReg(0);
    Reg#(Bit#(1)) sd_field   =  readOnlyReg(pack((xs_field == 2'b11) || (fs_field == 2'b11)));

    // mie fields
    Reg#(Bit#(1)) meie_field <- mkReg(0);
    Reg#(Bit#(1)) heie_field =  readOnlyReg(0);
    Reg#(Bit#(1)) seie_field <- mkReg(0);
    Reg#(Bit#(1)) ueie_field <- mkReg(0);
    Reg#(Bit#(1)) mtie_field <- mkReg(0);
    Reg#(Bit#(1)) htie_field =  readOnlyReg(0);
    Reg#(Bit#(1)) stie_field <- mkReg(0);
    Reg#(Bit#(1)) utie_field <- mkReg(0);
    Reg#(Bit#(1)) msie_field <- mkReg(0);
    Reg#(Bit#(1)) hsie_field =  readOnlyReg(0);
    Reg#(Bit#(1)) ssie_field <- mkReg(0);
    Reg#(Bit#(1)) usie_field <- mkReg(0);

    // mip fields
    Reg#(Bit#(1)) meip_field =  readOnlyReg(pack(meip));
    Reg#(Bit#(1)) heip_field =  readOnlyReg(0);
    Reg#(Bit#(1)) seip_field <- mkReg(0);
    Reg#(Bit#(1)) ueip_field <- mkReg(0);
    Reg#(Bit#(1)) mtip_field =  readOnlyReg(pack(mtip));
    Reg#(Bit#(1)) htip_field =  readOnlyReg(0);
    Reg#(Bit#(1)) stip_field <- mkReg(0);
    Reg#(Bit#(1)) utip_field <- mkReg(0);
    Reg#(Bit#(1)) msip_field =  readOnlyReg(pack(msip));
    Reg#(Bit#(1)) hsip_field =  readOnlyReg(0);
    Reg#(Bit#(1)) ssip_field <- mkReg(0);
    Reg#(Bit#(1)) usip_field <- mkReg(0);

    // Priv 1.9 CSRs

    // Machine Timers and Counters
    Reg#(Data) mcycle_csr   = readOnlyReg(truncate(cycle_counter));
    Reg#(Data) mtime_csr    = readOnlyReg(truncate(time_counter));
    Reg#(Data) minstret_csr = readOnlyReg(truncate(instret_counter));

    // Upper 32-bits of CSRs for RV32: (these will just be unused copies of
    // the other cycle/time/instret registers for RV64)
    Reg#(Data) mcycleh_csr   = readOnlyReg(truncateLSB(cycle_counter));
    Reg#(Data) mtimeh_csr    = readOnlyReg(truncateLSB(time_counter));
    Reg#(Data) minstreth_csr = readOnlyReg(truncateLSB(instret_counter));

    // Machine Counter-Delta Registers
    Reg#(Bit#(64)) mucycle_delta_field   <- mkReg(0);
    Reg#(Bit#(64)) mutime_delta_field    <- mkReg(0);
    Reg#(Bit#(64)) muinstret_delta_field <- mkReg(0);
    Reg#(Bit#(64)) mscycle_delta_field   <- mkReg(0);
    Reg#(Bit#(64)) mstime_delta_field    <- mkReg(0);
    Reg#(Bit#(64)) msinstret_delta_field <- mkReg(0);

    Reg#(Data) mucycle_delta_csr    = truncateReg(mucycle_delta_field);
    Reg#(Data) mutime_delta_csr     = truncateReg(mutime_delta_field);
    Reg#(Data) muinstret_delta_csr  = truncateReg(muinstret_delta_field);
    Reg#(Data) mscycle_delta_csr    = truncateReg(mscycle_delta_field);
    Reg#(Data) mstime_delta_csr     = truncateReg(mstime_delta_field);
    Reg#(Data) msinstret_delta_csr  = truncateReg(msinstret_delta_field);
    Reg#(Data) mucycle_deltah_csr   = truncateRegLSB(mucycle_delta_field);
    Reg#(Data) mutime_deltah_csr    = truncateRegLSB(mutime_delta_field);
    Reg#(Data) muinstret_deltah_csr = truncateRegLSB(muinstret_delta_field);
    Reg#(Data) mscycle_deltah_csr   = truncateRegLSB(mscycle_delta_field);
    Reg#(Data) mstime_deltah_csr    = truncateRegLSB(mstime_delta_field);
    Reg#(Data) msinstret_deltah_csr = truncateRegLSB(msinstret_delta_field);

    // User FPU
    Reg#(Data) fflags_csr = addWriteSideEffect(zeroExtendReg(fflags_field), fs_field._write(2'b11));
    Reg#(Data) frm_csr    = addWriteSideEffect(zeroExtendReg(frm_field), fs_field._write(2'b11));
    Reg#(Data) fcsr_csr   = addWriteSideEffect(zeroExtendReg(concatReg2(frm_field, fflags_field)), fs_field._write(2'b11));

    // User Timers and Counters
    Bit#(64) ucycle_counter   = cycle_counter + mucycle_delta_field;
    Bit#(64) utime_counter    = time_counter + mutime_delta_field;
    Bit#(64) uinstret_counter = instret_counter + muinstret_delta_field;

    Reg#(Data) cycle_csr   = readOnlyReg(truncate(ucycle_counter));
    Reg#(Data) time_csr    = readOnlyReg(truncate(utime_counter));
    Reg#(Data) instret_csr = readOnlyReg(truncate(uinstret_counter));

    // Upper 32-bits of CSRs for RV32: (these will just be unused copies of
    // the other cycle/time/instret registers for RV64)
    Reg#(Data) cycleh_csr   = readOnlyReg(truncateLSB(ucycle_counter));
    Reg#(Data) timeh_csr    = readOnlyReg(truncateLSB(utime_counter));
    Reg#(Data) instreth_csr = readOnlyReg(truncateLSB(uinstret_counter));

    // Supervisor
    Reg#(Data) sstatus_csr =  concatReg20(
            sd_field,
            readOnlyReg(0), // flexible width to support XLEN = 32 or 64
            vm_field,
            readOnlyReg(4'b0),
            readOnlyReg(1'b0), pum_field, readOnlyReg(1'b0), // memory privilege
            xs_field, fs_field, // coprocessor states
            readOnlyReg(2'b0), readOnlyReg(2'b0), spp_field, // previous privileges
            readOnlyReg(1'b0), readOnlyReg(1'b0), spie_field, upie_field, // previous interrupt enables
            readOnlyReg(1'b0), readOnlyReg(1'b0), sie_field, uie_field); // interrupt enables
    Reg#(Data) sedeleg_csr  =  concatReg2(readOnlyReg(0), sedeleg_field); // WARL - 12 legal exceptions
    Reg#(Data) sideleg_csr  =  concatReg2(readOnlyReg(0), sideleg_field); // WARL - 12 legal interrupts
    Reg#(Data) sie_csr      =  concatReg13(
            readOnlyReg(0),
            readOnlyReg(1'b0), readOnlyReg(1'b0), seie_field, ueie_field,
            readOnlyReg(1'b0), readOnlyReg(1'b0), stie_field, utie_field,
            readOnlyReg(1'b0), readOnlyReg(1'b0), ssie_field, usie_field);
    Reg#(Data) stvec_csr    =  concatReg2(stvec_field, readOnlyReg(2'd0));
    Reg#(Data) sscratch_csr <- mkReg(0);
    Reg#(Data) sepc_csr     <- mkReg(0);
    Reg#(Data) scause_csr   <- mkReg(0);
    Reg#(Data) sbadaddr_csr <- mkReg(0);
    Reg#(Data) sip_csr      =  concatReg13(
            readOnlyReg(0),
            readOnlyReg(1'b0), readOnlyReg(1'b0), readOnlyReg(seip_field), readOnlyReg(ueip_field),
            readOnlyReg(1'b0), readOnlyReg(1'b0), readOnlyReg(stip_field), readOnlyReg(utip_field),
            readOnlyReg(1'b0), readOnlyReg(1'b0), ssip_field, usip_field);

    Reg#(Data) sptbr_csr    = concatReg2(asid_field, sptbr_ppn_field);

    Bit#(64) scycle_counter   = cycle_counter + mscycle_delta_field;
    Bit#(64) stime_counter    = time_counter + mstime_delta_field;
    Bit#(64) sinstret_counter = instret_counter + msinstret_delta_field;

    Reg#(Data) scycle_csr   = readOnlyReg(truncate(scycle_counter));
    Reg#(Data) stime_csr    = readOnlyReg(truncate(stime_counter));
    Reg#(Data) sinstret_csr = readOnlyReg(truncate(sinstret_counter));

    // Upper 32-bits of CSRs for RV32: (these will just be unused copies of
    // the other cycle/time/instret registers for RV64)
    Reg#(Data) scycleh_csr   = readOnlyReg(truncateLSB(scycle_counter));
    Reg#(Data) stimeh_csr    = readOnlyReg(truncateLSB(stime_counter));
    Reg#(Data) sinstreth_csr = readOnlyReg(truncateLSB(sinstret_counter));

    // Machine Information Registers
    Reg#(Data) misa_csr      = readOnlyReg(getMISA(isa));
    Reg#(Data) mvendorid_csr = readOnlyReg(mvendorid);
    Reg#(Data) marchid_csr   = readOnlyReg(marchid);
    Reg#(Data) mimpid_csr    = readOnlyReg(mimpid);
    Reg#(Data) mhartid_csr   = readOnlyReg(hartid);

    // Machine Trap Setup
    Reg#(Data) mstatus_csr =  concatReg20(
            sd_field,
            readOnlyReg(0),
            vm_field,
            readOnlyReg(4'b0),
            mxr_field, pum_field, mprv_field, // memory privilege
            xs_field, fs_field, // coprocessor states
            mpp_field, hpp_field, spp_field, // previous privileges
            mpie_field, hpie_field, spie_field, upie_field, // previous interrupt enables
            mie_field, hie_field, sie_field, uie_field); // interrupt enables
    Reg#(Data) medeleg_csr =  concatReg2(readOnlyReg(0), medeleg_field); // WARL - 12 legal exceptions
    Reg#(Data) mideleg_csr =  concatReg2(readOnlyReg(0), mideleg_field); // WARL - 12 legal interrupts
    Reg#(Data) mie_csr     =  concatReg13(
            readOnlyReg(0),
            meie_field, heie_field, seie_field, ueie_field,
            mtie_field, htie_field, stie_field, utie_field,
            msie_field, hsie_field, ssie_field, usie_field);
    Reg#(Data) mtvec_csr   =  concatReg2(mtvec_field, readOnlyReg(2'd0));

    // Machine Trap Handling
    Reg#(Data) mscratch_csr <- mkReg(0);
    Reg#(Data) mepc_csr     <- mkReg(0);
    Reg#(Data) mcause_csr   <- mkReg(0);
    Reg#(Data) mbadaddr_csr <- mkReg(0);
    Reg#(Data) mip_csr      =  concatReg13(
            readOnlyReg(0),
            readOnlyReg(meip_field), readOnlyReg(heip_field), readOnlyReg(seip_field), readOnlyReg(ueip_field),
            readOnlyReg(mtip_field), htip_field, stip_field, utip_field,
            readOnlyReg(msip_field), hsip_field, ssip_field, usip_field);

    // Machine Protection and Translation
    Reg#(Data) mbase_csr   <- mkReg(0);
    Reg#(Data) mbound_csr  <- mkReg(0);
    Reg#(Data) mibase_csr  <- mkReg(0);
    Reg#(Data) mibound_csr <- mkReg(0);
    Reg#(Data) mdbase_csr  <- mkReg(0);
    Reg#(Data) mdbound_csr <- mkReg(0);

    // Machine Counter Setup
    Reg#(Data) mucounteren_csr = concatReg4(readOnlyReg(0), u_ir_field, u_tm_field, u_cy_field);
    Reg#(Data) mscounteren_csr = concatReg4(readOnlyReg(0), s_ir_field, s_tm_field, s_cy_field);

    function Reg#(Data) getCSR(CSR csr);
        return (case (csr)
                CSRfflags:              fflags_csr;
                CSRfrm:                 frm_csr;
                CSRfcsr:                fcsr_csr;
                CSRcycle:               cycle_csr;
                CSRtime:                time_csr;
                CSRinstreth:            instreth_csr;
                CSRcycleh:              cycleh_csr;
                CSRtimeh:               timeh_csr;
                CSRinstret:             instret_csr;
                CSRsstatus:             sstatus_csr;
                CSRsedeleg:             sedeleg_csr;
                CSRsideleg:             sideleg_csr;
                CSRsie:                 sie_csr;
                CSRstvec:               stvec_csr;
                CSRsscratch:            sscratch_csr;
                CSRsepc:                sepc_csr;
                CSRscause:              scause_csr;
                CSRsbadaddr:            sbadaddr_csr;
                CSRsip:                 sip_csr;
                CSRsptbr:               sptbr_csr;
                CSRscycle:              scycle_csr;
                CSRstime:               stime_csr;
                CSRsinstret:            sinstret_csr;
                CSRscycleh:             scycleh_csr;
                CSRstimeh:              stimeh_csr;
                CSRsinstreth:           sinstreth_csr;
                CSRmisa:                misa_csr;
                CSRmvendorid:           mvendorid_csr;
                CSRmarchid:             marchid_csr;
                CSRmimpid:              mimpid_csr;
                CSRmhartid:             mhartid_csr;
                CSRmstatus:             mstatus_csr;
                CSRmedeleg:             medeleg_csr;
                CSRmideleg:             mideleg_csr;
                CSRmie:                 mie_csr;
                CSRmtvec:               mtvec_csr;
                CSRmscratch:            mscratch_csr;
                CSRmepc:                mepc_csr;
                CSRmcause:              mcause_csr;
                CSRmbadaddr:            mbadaddr_csr;
                CSRmip:                 mip_csr;
                CSRmbase:               mbase_csr;
                CSRmbound:              mbound_csr;
                CSRmibase:              mibase_csr;
                CSRmibound:             mibound_csr;
                CSRmdbase:              mdbase_csr;
                CSRmdbound:             mdbound_csr;
                CSRmcycle:              mcycle_csr;
                CSRmtime:               mtime_csr;
                CSRminstret:            minstret_csr;
                CSRmcycleh:             mcycleh_csr;
                CSRmtimeh:              mtimeh_csr;
                CSRminstreth:           minstreth_csr;
                CSRmucounteren:         mucounteren_csr;
                CSRmscounteren:         mscounteren_csr;
                CSRmucycle_delta:       mucycle_delta_csr;
                CSRmutime_delta:        mutime_delta_csr;
                CSRmuinstret_delta:     muinstret_delta_csr;
                CSRmscycle_delta:       mscycle_delta_csr;
                CSRmstime_delta:        mstime_delta_csr;
                CSRmsinstret_delta:     msinstret_delta_csr;
                CSRmucycle_deltah:      mucycle_deltah_csr;
                CSRmutime_deltah:       mutime_deltah_csr;
                CSRmuinstret_deltah:    muinstret_deltah_csr;
                CSRmscycle_deltah:      mscycle_deltah_csr;
                CSRmstime_deltah:       mstime_deltah_csr;
                CSRmsinstret_deltah:    msinstret_deltah_csr;
                default:                (readOnlyReg(0));
            endcase);
    endfunction

    function Bool isLegalCSR(CSR csr);
        return (case (csr)
                CSRfflags:              (fs_field != 0);
                CSRfrm:                 (fs_field != 0);
                CSRfcsr:                (fs_field != 0);
                CSRcycle:               (u_cy_field == 1);
                CSRtime:                (u_tm_field == 1);
                CSRinstret:             (u_ir_field == 1);
                CSRcycleh:              ((u_cy_field == 1) && is32bit);
                CSRtimeh:               ((u_tm_field == 1) && is32bit);
                CSRinstreth:            ((u_ir_field == 1) && is32bit);
                CSRsstatus:             True;
                CSRsedeleg:             True;
                CSRsideleg:             True;
                CSRsie:                 True;
                CSRstvec:               True;
                CSRsscratch:            True;
                CSRsepc:                True;
                CSRscause:              True;
                CSRsbadaddr:            True;
                CSRsip:                 True;
                CSRsptbr:               True;
                CSRscycle:              (s_cy_field == 1);
                CSRstime:               (s_tm_field == 1);
                CSRsinstret:            (s_ir_field == 1);
                CSRscycleh:             ((s_cy_field == 1) && is32bit);
                CSRstimeh:              ((s_tm_field == 1) && is32bit);
                CSRsinstreth:           ((s_ir_field == 1) && is32bit);
                CSRmisa:                True;
                CSRmvendorid:           True;
                CSRmarchid:             True;
                CSRmimpid:              True;
                CSRmhartid:             True;
                CSRmstatus:             True;
                CSRmedeleg:             True;
                CSRmideleg:             True;
                CSRmie:                 True;
                CSRmtvec:               True;
                CSRmscratch:            True;
                CSRmepc:                True;
                CSRmcause:              True;
                CSRmbadaddr:            True;
                CSRmip:                 True;
                CSRmbase:               True;
                CSRmbound:              True;
                CSRmibase:              True;
                CSRmibound:             True;
                CSRmdbase:              True;
                CSRmdbound:             True;
                CSRmcycle:              True;
                CSRmtime:               True;
                CSRminstret:            True;
                CSRmcycleh:             is32bit;
                CSRmtimeh:              is32bit;
                CSRminstreth:           is32bit;
                CSRmucounteren:         True;
                CSRmscounteren:         True;
                CSRmucycle_delta:       True;
                CSRmutime_delta:        True;
                CSRmuinstret_delta:     True;
                CSRmscycle_delta:       True;
                CSRmstime_delta:        True;
                CSRmsinstret_delta:     True;
                CSRmucycle_deltah:      is32bit;
                CSRmutime_deltah:       is32bit;
                CSRmuinstret_deltah:    is32bit;
                CSRmscycle_deltah:      is32bit;
                CSRmstime_deltah:       is32bit;
                CSRmsinstret_deltah:    is32bit;
                default:                False;
            endcase);
    endfunction

    function Maybe#(InterruptCause) readyInterruptFunc();
        Bit#(12) ready_interrupts = truncate(mip_csr) & truncate(mie_csr);
        // machine mode
        let ready_machine_interrupts = ready_interrupts & ~truncate(mideleg_csr);
        Bool machine_interrupts_enabled = (mie_field == 1) || (prv < prvM);
        // supervisor mode
        let ready_supervisor_interrupts = ready_interrupts & truncate(mideleg_csr) & ~truncate(sideleg_csr);
        Bool supervisor_interrupts_enabled = ((sie_field == 1) && (prv == prvS)) || (prv < prvS);
        // user mode
        let ready_user_interrupts = ready_interrupts & truncate(mideleg_csr) & truncate(sideleg_csr);
        let user_interrupts_enabled = (uie_field == 1) && (prv == prvU);
        // combined
        ready_interrupts = (machine_interrupts_enabled ? ready_machine_interrupts : 0)
                            | (supervisor_interrupts_enabled ? ready_supervisor_interrupts : 0)
                            | (user_interrupts_enabled ? ready_user_interrupts : 0);
        // format pendingInterrupt value to return
        Maybe#(InterruptCause) ret = tagged Invalid;
        if (ready_interrupts != 0) begin
            // pack/unpack type conversion:
            // UInt#(TLog#(TAdd#(12,1))) == UInt#(4) -> Bit#(4) -> InterruptCause
            ret = tagged Valid unpack(pack(countZerosLSB(ready_interrupts)));
        end
        return ret;
    endfunction

    // RULES
    ////////////////////////////////////////////////////////

    rule setReadyInterruptWire;
        readyInterruptWire <= readyInterruptFunc();
    endrule

    rule incrementCycle;
        cycle_counter <= cycle_counter + 1;
    endrule

    // METHODS
    ////////////////////////////////////////////////////////

    method VMInfo#(xlen) vmI;
        Bit#(5) vm = (prv == prvM) ? vmMbare : vm_field;
        Addr base = (case (vm)
                        vmMbare: 0;
                        vmMbb: mbase_csr;
                        vmMbbid: mibase_csr;
                        // all paged virtual memory modes
`ifdef CONFIG_RV64
                        default: {0, sptbr_ppn_field, 12'd0};
`else
                        default: truncate({sptbr_ppn_field, 12'd0}); // TODO: allow Addr to be Bit#(34) for rv32
`endif
                    endcase);
        Addr bound = (case (vm)
                        vmMbb: mbound_csr;
                        vmMbbid: mibound_csr;
                        default: -1;
                    endcase);
        return VMInfo{ prv: prv, asid: asid_field, vm: vm, mxr: unpack(mxr_field), pum: unpack(pum_field), base: base, bound: bound };
    endmethod

    method VMInfo#(xlen) vmD;
        Bit#(2) vm_prv = (mprv_field == 1) ? mpp_field : prv;
        Bit#(5) vm = (vm_prv == prvM) ? vmMbare : vm_field;
        Addr base = (case (vm)
                        vmMbare: 0;
                        vmMbb: mbase_csr;
                        vmMbbid: mdbase_csr;
                        // all paged virtual memory modes
`ifdef CONFIG_RV64
                        default: {0, sptbr_ppn_field, 12'd0};
`else
                        default: truncate({sptbr_ppn_field, 12'd0}); // TODO: allow Addr to be Bit#(34) for rv32
`endif
                    endcase);
        Addr bound = (case (vm)
                        vmMbb: mbound_csr;
                        vmMbbid: mdbound_csr;
                        default: -1;
                    endcase);
        return VMInfo{ prv: vm_prv, asid: asid_field, vm: vm, mxr: unpack(mxr_field), pum: unpack(pum_field), base: base, bound: bound };
    endmethod

    method CsrState csrState = CsrState {prv: prv, frm: frm_field, f_enabled: (fs_field != 0), x_enabled: (xs_field != 0)};

    method Maybe#(InterruptCause) readyInterrupt;
        return readyInterruptWire;
    endmethod

    method Bool wakeFromWFI;
        return (mip_csr & mie_csr) != 0;
    endmethod

    method ActionValue#(CsrReturn#(xlen)) wr(
            Addr pc, // pc of current exception
            Maybe#(SystemInst) sysInst,
            CSR csr,
            Data data, // zimm or rval
            Addr addr, // badaddr
            Maybe#(TrapCause) trap, // exception or interrupt
            // indirect updates
            Bit#(5) fflags,
            Bool fpuDirty,
            Bool xDirty);

        Maybe#(TrapCause) trapToTake = trap;
        if (!isValid(trapToTake) &&& sysInst matches tagged Valid .validSysInst) begin
            case (validSysInst)
                ECall:  trapToTake = tagged Valid (case (prv)
                                                    prvU: (tagged Exception EnvCallU);
                                                    prvS: (tagged Exception EnvCallS);
                                                    prvH: (tagged Exception EnvCallH);
                                                    prvM: (tagged Exception EnvCallM);
                                                endcase);
                // URet and HRet are not supported
                URet: trapToTake = tagged Valid (tagged Exception IllegalInst);
                SRet:
                    begin
                        if (prv < prvS) begin
                            trapToTake = tagged Valid (tagged Exception IllegalInst);
                        end
                    end
                HRet: trapToTake = tagged Valid (tagged Exception IllegalInst);
                MRet:
                    begin
                        if (prv < prvM) begin
                            trapToTake = tagged Valid (tagged Exception IllegalInst);
                        end
                    end
                EBreak: trapToTake = tagged Valid (tagged Exception Breakpoint);
                CSRRW, CSRRS, CSRRC, CSRR, CSRW:
                    begin
                        Bool read = (validSysInst != CSRW);
                        Bool write = (validSysInst != CSRR);
                        if (!isLegalCSR(csr) || !hasCSRPermission(csr, prv, write)) begin
                            trapToTake = tagged Valid (tagged Exception IllegalInst);
                        end
                    end
            endcase
        end

        // Three case from this point onward:
        // 1) Trap (exception or interrupt)
        // 2) Non-trapping system instruction
        //      increment instret
        // 3) Normal instruction
        //      increment instret
        //      update fs and fflags if necessary
        if (trapToTake matches tagged Valid .validTrap) begin
            // Traps
            // delegate to S if the prv <= S and the corresponding deleg bit is set
            Bool delegToS = prv <= prvS && (case (validTrap) matches
                    tagged Exception .exceptionCause: (((medeleg_csr >> pack(exceptionCause)) & 1) != 0);
                    tagged Interrupt .interruptCause: (((mideleg_csr >> pack(interruptCause)) & 1) != 0);
                endcase);
            Addr newPC = delegToS ? stvec_csr : mtvec_csr;
            if (delegToS) begin
                // trap to prvS
                sepc_csr <= pc;
                scause_csr <= toCauseCSR(validTrap);
                case (validTrap)
                    tagged Exception InstAddrMisaligned,
                    tagged Exception InstAccessFault,
                    tagged Exception LoadAddrMisaligned,
                    tagged Exception LoadAccessFault,
                    tagged Exception StoreAddrMisaligned,
                    tagged Exception StoreAccessFault:
                        sbadaddr_csr <= addr;
                endcase
                // update mstatus fields
                spp_field <= (prv == prvU) ? 0 : 1;
                spie_field <= (prv == prvU) ? uie_field : sie_field;
                sie_field <= 0;
                // update privilege
                prv <= prvS;
            end else begin
                // trap to prvM
                mepc_csr <= pc;
                mcause_csr <= toCauseCSR(validTrap);
                case (validTrap)
                    tagged Exception InstAddrMisaligned,
                    tagged Exception InstAccessFault,
                    tagged Exception LoadAddrMisaligned,
                    tagged Exception LoadAccessFault,
                    tagged Exception StoreAddrMisaligned,
                    tagged Exception StoreAccessFault:
                        mbadaddr_csr <= addr;
                endcase
                // update mstatus fields
                mpp_field <= prv;
                mpie_field <= (case (prv)
                                prvU: uie_field;
                                prvS: sie_field;
                                prvH: hie_field;
                                prvM: mie_field;
                            endcase);
                mie_field <= 0;
                // update privilege
                prv <= prvM;
            end
            return tagged Exception {exception: validTrap, trapHandlerPC: newPC};
        end else if (sysInst matches tagged Valid .validSysInst) begin
            // Non-trapping system instructions
            instret_counter <= instret_counter + 1;
            case (validSysInst)
                SRet:
                    begin
                        let next_prv = spp_field == 1 ? prvS : prvU;
                        case (next_prv)
                            prvU: uie_field <= spie_field;
                            prvS: sie_field <= spie_field;
                        endcase
                        spie_field <= 0;
                        spp_field <= 0;
                        prv <= next_prv;
                        Addr newPC = sepc_csr;
                        return tagged RedirectPC newPC;
                    end
                MRet:
                    begin
                        let next_prv = mpp_field;
                        case (next_prv)
                            prvU: uie_field <= mpie_field;
                            prvS: sie_field <= mpie_field;
                            prvM: mie_field <= mpie_field;
                        endcase
                        mpie_field <= 0;
                        mpp_field <= prvU;
                        prv <= next_prv;
                        Addr newPC = mepc_csr;
                        return tagged RedirectPC newPC;
                    end
                CSRRW, CSRRS, CSRRC, CSRR, CSRW:
                    begin
                        // Not used at the moment, just a place holder in case
                        // any read side-effects are needed in the CSRs.
                        Bool read = (validSysInst != CSRW);
                        Bool write = (validSysInst != CSRR);
                        // CSR read/write operation
                        let oldVal = getCSR(csr)._read;
                        let newVal = (case(validSysInst)
                                CSRW, CSRR, CSRRW: data;
                                CSRRS: (oldVal | data);
                                CSRRC: (oldVal & (~data));
                            endcase);
                        if (write) begin
                            getCSR(csr)._write(newVal);
                        end
                        return tagged CsrData oldVal;
                    end
                default:
                    begin
                        return tagged None;
                    end
            endcase
        end else begin
            // Normal instruction
            // update fflags, fs, and xs if necessary
            if ((fflags | fflags_field) != fflags_field) begin
                fflags_field <= fflags_field | fflags;
                fpuDirty = True;
            end
            if (fpuDirty) begin
                if (fs_field == 0) begin
                    // fs_field shouldn't be 00
                    $fdisplay(stderr, "[ERROR] CSRFile: fpuDirty is true, but fs_field is set to 0");
                end
                fs_field <= 2'b11;
            end
            if (xDirty) begin
                xs_field <= 2'b11;
            end
            instret_counter <= instret_counter + 1;
            return tagged None;
        end
    endmethod
endmodule

