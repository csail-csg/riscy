
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
import Ehr::*;
import FIFOF::*;
import RegUtil::*;
import Vector::*;

interface RVCsrFile;
    // Read and Write ports
    // method Data rd(CSR csr);
    method ActionValue#(Tuple3#(Maybe#(Trap), Maybe#(Data), Maybe#(Addr)))
        wr( Maybe#(SystemInst) sysInst,
            CSR csr,
            Data data, // zimm or rval
            Maybe#(ExceptionCause) e,
            Bool allowInterrupt,
            Addr pc,
            Bool checkInstAlignment, // if true, addr == nextPc
            Addr addr,
            Bit#(5) fflags,
            Bool fpuDirty,
            Bool xDirty);

    // Outputs for CSRs that the rest of the processor needs to know about
    method VMInfo vmI;
    method VMInfo vmD;
    method CsrState csrState; // prv, frm, f_enabled, x_enabled

    // tohost/fromhost
    method Action hostToCsrf(Data val);
    method ActionValue#(Data) csrfToHost;
    method Bool toHostEmpty;
    method Bool fromHostZero;
    // other tohost/fromhost stuff
    method Action configure(Data miobase);

    // Interrupts
    method Action triggerExternalInterrupt;

    // performance stats is collected or not
    method Bool doPerfStats;
endinterface

interface MToHost;
    interface Reg#(Data) reg_ifc;
    interface FIFOF#(Data) fifo_ifc;
endinterface

module mkMToHost(MToHost);
    FIFOF#(Data) fifo <- mkFIFOF;

    interface Reg reg_ifc;
        method Action _write(Data x);
            fifo.enq(x);
        endmethod
        method Data _read;
            if (fifo.notEmpty) begin
                return fifo.first;
            end else begin
                return 0;
            end
        endmethod
    endinterface
    interface FIFOF fifo_ifc = fifo;
endmodule

module mkRVCsrFileWithId#(Data hartid)(RVCsrFile);
    let verbose = False;
    File fout = stdout;

    let mkCsrReg = mkReg; // can use config reg if necessary
    RiscVISASubset isa = defaultValue;
`ifdef LOOK_LIKE_A_ROCKET
    Data mimpid = {'b0, 16'h0001};
`else
    Data mimpid = {'b0, 16'h8000};
`endif

    // Storage elements for CSRs
    //---------------------------
    // User level CSRs
    Reg#(Bit#(5)) fflags_reg  <- mkCsrReg(0);
    Ehr#(2,Bit#(3)) frm_ehr     <- mkEhr(0);
    Ehr#(2,Data)  cycle_ehr   <- mkEhr(0);
    Ehr#(2,Bit#(TAdd#(64,10))) time_ehr <- mkEhr(0); // 10 extra bits so time_reg ticks once every 1024 clock cycles
    Ehr#(2,Data)  instret_ehr <- mkEhr(0);
    Reg#(Data)    cycle_reg   =  cycle_ehr[0];
    Reg#(Data)    time_reg    =  truncateRegLSB(time_ehr[0]);
    Reg#(Data)    instret_reg =  instret_ehr[0];

    // whether performance stats is collected (only need 1 bit)
    Reg#(Data)    stats_reg   <- mkConfigReg(0); 

    // Supervisor level CSRs
    // stvec
    Reg#(Bit#(62)) stvec_reg <- mkCsrReg(0);
    // sie
    // stimecmp
    Reg#(Data) stimecmp_reg <- mkCsrReg(0);
    // sscratch
    Reg#(Data) sscratch_reg <- mkCsrReg(0);
    // sepc
    Reg#(Data) sepc_reg <- mkCsrReg(0);
    // scause
    Reg#(Bit#(1)) scause_i_reg <- mkCsrReg(0);
    Reg#(Bit#(4)) scause_code_reg <- mkCsrReg(0);
    // sbadaddr
    Reg#(Data) sbadaddr_reg <- mkCsrReg(0);
    // sip
    // sptbr
    Reg#(Bit#(52)) sptbr_reg <- mkCsrReg(0);
    // sasid
    Reg#(Asid) sasid_reg <- mkCsrReg(0);

    // Machine level CSRs
    // mstatus
    Reg#(Bit#(5)) vm_reg    <- mkCsrReg(0);
    Reg#(Bit#(1)) mprv_reg  <- mkCsrReg(0);
    Ehr#(2,Bit#(2)) xs_ehr    <- isa.x ? mkEhr(0) : replicateM(mkReadOnlyReg(0));
    Ehr#(2,Bit#(2)) fs_ehr    <- (isa.f || isa.d) ? mkEhr(0) : replicateM(mkReadOnlyReg(0));
    Reg#(Bit#(1)) sd_reg    =  readOnlyReg( ((xs_ehr[0] == 2'b11) || (fs_ehr[0] == 2'b11)) ? 1 : 0 );
    Reg#(Bit#(2)) prv3_reg  <- isa.h ? mkCsrReg(0) : mkReadOnlyReg(0);
    Reg#(Bit#(1)) ie3_reg   <- isa.h ? mkCsrReg(0) : mkReadOnlyReg(0);
    Reg#(Bit#(2)) prv2_reg  <- mkCsrReg(0);
    Reg#(Bit#(1)) ie2_reg   <- mkCsrReg(0);
    Reg#(Bit#(2)) prv1_reg  <- mkCsrReg(0);
    Reg#(Bit#(1)) ie1_reg   <- mkCsrReg(0);
    Ehr#(2,Bit#(2)) prv_ehr   <- mkEhr(3);
    Reg#(Bit#(1)) ie_reg    <- mkCsrReg(0);
    // sstatus (supervisor view of sstatus
    Reg#(Bit#(1)) ps_reg    = truncateReg(prv1_reg);
    Reg#(Bit#(1)) pie_reg   = ie1_reg;
    // mtvec
    Reg#(Bit#(62)) mtvec_reg <- mkCsrReg(62'h40); // bottom two bits will be hardwired to 0
    // mtdeleg
    Reg#(Data) mtdeleg_reg <- mkCsrReg(0);
    // mip
    Ehr#(2, Bit#(1)) mtip_ehr <- mkEhr(0);
    Reg#(Bit#(1)) htip_reg =  readOnlyReg(0);
    Reg#(Bit#(1)) stip_reg <- mkCsrReg(0);
    Reg#(Bit#(1)) msip_reg <- mkCsrReg(0);
    Reg#(Bit#(1)) hsip_reg =  readOnlyReg(0);
    Reg#(Bit#(1)) ssip_reg <- mkCsrReg(0);
    // mie
    Reg#(Bit#(1)) mtie_reg <- mkCsrReg(0);
    Reg#(Bit#(1)) htie_reg =  readOnlyReg(0);
    Reg#(Bit#(1)) stie_reg <- mkCsrReg(0);
    Reg#(Bit#(1)) msie_reg <- mkCsrReg(0);
    Reg#(Bit#(1)) hsie_reg =  readOnlyReg(0);
    Reg#(Bit#(1)) ssie_reg <- mkCsrReg(0);
    // mtimecmp
    Reg#(Bit#(32)) mtimecmp_reg <- mkCsrReg(0);
    // mtime
    // mscratch
    Reg#(Data)    mscratch_reg <- mkCsrReg(0);
    // mepc
    Reg#(Data)    mepc_reg <- mkCsrReg(0); // Bottom two bits are always 0 on systems where instructions are 32-bit aligned
    // mcause
    Reg#(Bit#(1)) mcause_i_reg <- mkCsrReg(0);
    Reg#(Bit#(4)) mcause_code_reg <- mkCsrReg(0);
    // mbadaddr
    Reg#(Data)    mbadaddr_reg <- mkCsrReg(0);
    // mbase
    Reg#(Data)    mbase_reg <- mkCsrReg(0);
    // mbound
    Reg#(Data)    mbound_reg <- mkCsrReg(0);
    // mibase
    Reg#(Data)    mibase_reg <- mkCsrReg(0);
    // mibound
    Reg#(Data)    mibound_reg <- mkCsrReg(0);
    // mdbase
    Reg#(Data)    mdbase_reg <- mkCsrReg(0);
    // mdbound
    Reg#(Data)    mdbound_reg <- mkCsrReg(0);
    // tohost/fromhost
    // Reg#(Data)    mtohost_reg <- mkCsrReg(0);
    // Reg#(Data)    mfromhost_reg <- mkCsrReg(0);
    // Reg#(Data)    mtohost_reg <- mkConfigReg(0);
    MToHost       mtohost_module <- mkMToHost;
    Reg#(Data)    mtohost_reg = mtohost_module.reg_ifc;
    Reg#(Data)    mfromhost_reg <- mkConfigReg(0);
    // This should be read only (I think)
    Reg#(Data)    miobase_reg <- mkConfigReg(0);


    // Write and Read methods that make up CSRs
    //------------------------------------------
    // User level CSRs

    // not this simple -- these need to dirty the fs_ehr
    Reg#(Data) fflags_csr   = addWriteSideEffect(zeroExtendReg(fflags_reg),                           fs_ehr[0]._write(2'b11));
    Reg#(Data) frm_csr      = addWriteSideEffect(zeroExtendReg(frm_ehr[0]),                              fs_ehr[0]._write(2'b11));
    Reg#(Data) fcsr_csr     = addWriteSideEffect(concatReg3(readOnlyReg(56'h0), frm_ehr[0], fflags_reg), fs_ehr[0]._write(2'b11));

    Reg#(Data) stats_csr    = stats_reg;

    Reg#(Data) cycle_csr    = readOnlyReg(cycle_reg);
    Reg#(Data) time_csr     = readOnlyReg(time_reg);
    Reg#(Data) instret_csr  = readOnlyReg(instret_reg);

    // Supervisor level CSRs
    Reg#(Data) stvec_csr    = concatReg2(stvec_reg, readOnlyReg(2'h0));
    Reg#(Data) sstatus_csr  = concatReg10(sd_reg, readOnlyReg(46'h0), mprv_reg, xs_ehr[0], fs_ehr[0], readOnlyReg(7'h0), ps_reg, pie_reg, readOnlyReg(2'h0), ie_reg);
    Reg#(Data) sip_csr      = concatReg5(readOnlyReg(58'h0), stip_reg, readOnlyReg(3'h0), ssip_reg, readOnlyReg(1'h0));
    Reg#(Data) sie_csr      = concatReg5(readOnlyReg(58'h0), stie_reg, readOnlyReg(3'h0), ssie_reg, readOnlyReg(1'h0));
    Reg#(Data) stime_csr    = time_reg;
    Reg#(Data) stimecmp_csr = addWriteSideEffect(zeroExtendReg(stimecmp_reg), stip_reg._write(0));
    Reg#(Data) sscratch_csr = sscratch_reg;
    Reg#(Data) sepc_csr     = sepc_reg;
    Reg#(Data) scause_csr   = concatReg3(scause_i_reg, readOnlyReg(59'h0), scause_code_reg);
    Reg#(Data) sbadaddr_csr = sbadaddr_reg;
    Reg#(Data) sptbr_csr    = concatReg2(sptbr_reg, readOnlyReg(12'h0));
    Reg#(Data) sasid_csr    = zeroExtendReg(sasid_reg);
    Reg#(Data) cyclew_csr   = cycle_reg;
    Reg#(Data) timew_csr    = time_reg;
    Reg#(Data) instretw_csr = instret_reg;

    // Machine level CSRs
    Reg#(Data) mcpuid_csr   = readOnlyReg(getMCPUID(isa));
    Reg#(Data) mimpid_csr   = readOnlyReg(mimpid);
    Reg#(Data) mhartid_csr  = readOnlyReg(hartid);
    Reg#(Data) mstatus_csr  = concatReg14(sd_reg, readOnlyReg(41'h0), vm_reg, mprv_reg, xs_ehr[0], fs_ehr[0], prv3_reg, ie3_reg, prv2_reg, ie2_reg, prv1_reg, ie1_reg, prv_ehr[0], ie_reg);
    Reg#(Data) mtvec_csr    = concatReg2(mtvec_reg, readOnlyReg(2'h0));
    Reg#(Data) mtdeleg_csr  = mtdeleg_reg;
    Reg#(Data) mip_csr      = concatReg9(readOnlyReg(56'h0), mtip_ehr[0], htip_reg, stip_reg, readOnlyReg(1'h0), msip_reg, hsip_reg, ssip_reg, readOnlyReg(1'h0));
    Reg#(Data) mie_csr      = concatReg9(readOnlyReg(56'h0), mtie_reg, htie_reg, stie_reg, readOnlyReg(1'h0), msie_reg, hsie_reg, ssie_reg, readOnlyReg(1'h0));
    Reg#(Data) mtime_csr    = time_reg;
    Reg#(Data) mtimecmp_csr = addWriteSideEffect(zeroExtendReg(mtimecmp_reg), mtip_ehr[0]._write(0));
    Reg#(Data) mscratch_csr = mscratch_reg;
    Reg#(Data) mepc_csr     = mepc_reg;
    Reg#(Data) mcause_csr   = concatReg3(mcause_i_reg, readOnlyReg(59'h0), mcause_code_reg);
    Reg#(Data) mbadaddr_csr = mbadaddr_reg;
    Reg#(Data) mbase_csr    = mbase_reg;
    Reg#(Data) mbound_csr   = mbound_reg;
    Reg#(Data) mibase_csr   = mibase_reg;
    Reg#(Data) mibound_csr  = mibound_reg;
    Reg#(Data) mdbase_csr   = mdbase_reg;
    Reg#(Data) mdbound_csr  = mdbound_reg;

    // Non-standard CSRs
    Reg#(Data) mtohost_csr  = mtohost_reg;
    Reg#(Data) mfromhost_csr= mfromhost_reg;
    Reg#(Data) miobase_csr  = readOnlyReg(miobase_reg);

    // Function for getting a csr given an index
    function Reg#(Data) get_csr(CSR csr);
        return (case (csr)
                // User Floating-Point CSRs
                CSRfflags:    fflags_csr;
                CSRfrm:       frm_csr;
                CSRfcsr:      fcsr_csr;
                // User stats
                CSRstats:     stats_csr;
                // User Counter/Timers
                CSRcycle:     cycle_csr;
                CSRtime:      time_csr;
                CSRinstret:   instret_csr;

                // Supervisor Trap Setup
                CSRsstatus:   sstatus_csr;
                CSRstvec:     stvec_csr;
                CSRsie:       sie_csr;
                CSRstimecmp:  stimecmp_csr;
                // Supervisor Timer
                CSRstime:     stime_csr;
                // Supervisor Trap Handling
                CSRsscratch:  sscratch_csr;
                CSRsepc:      sepc_csr;
                CSRscause:    scause_csr;
                CSRsbadaddr:  sbadaddr_csr;
                CSRsip:       sip_csr;
                // Supervisor Protection and Translation
                CSRsptbr:     sptbr_csr;
                CSRsasid:     sasid_csr;
                // Supervisor Read/Write Shadow of User Read-Only registers
                CSRcyclew:    cyclew_csr;
                CSRtimew:     timew_csr;
                CSRinstretw:  instretw_csr;

                // Machine Information Registers
                CSRmcpuid:    mcpuid_csr;
                CSRmimpid:    mimpid_csr;
                CSRmhartid:   mhartid_csr;
                // Machine Trap Setup
                CSRmstatus:   mstatus_csr;
                CSRmtvec:     mtvec_csr;
                CSRmtdeleg:   mtdeleg_csr;
                CSRmie:       mie_csr;
                CSRmtimecmp:  mtimecmp_csr;
                // Machine Timers and Counters
                CSRmtime:     mtime_csr;
                // Machine Trap Handling
                CSRmscratch:  mscratch_csr;
                CSRmepc:      mepc_csr;
                CSRmcause:    mcause_csr;
                CSRmbadaddr:  mbadaddr_csr;
                CSRmip:       mip_csr;
                // Machine Protection and Translation
                CSRmbase:     mbase_csr;
                CSRmbound:    mbound_csr;
                CSRmibase:    mibase_csr;
                CSRmibound:   mibound_csr;
                CSRmdbase:    mdbase_csr;
                CSRmdbound:   mdbound_csr;
                // Machine Read/Write Shadow of Hypervisor Read-Only Registers
                // TODO: implement
                // Machine Host-Target Interface (Non-Standard Berkeley Extension)
                CSRmtohost:   mtohost_csr;
                CSRmfromhost: mfromhost_csr;
                CSRmiobase:   miobase_csr;

                default:      (readOnlyReg(64'h0));
            endcase);
    endfunction

    Maybe#(Interrupt) pendingInterrupt = (begin
            Maybe#(Interrupt) ret = tagged Invalid;
            Bool ie = ie_reg == 1;
            if (prv_ehr[0] < prvM || ((prv_ehr[0] == prvM) && ie)) begin
                if ((msie_reg & msip_reg) == 1) begin
                    ret = tagged Valid SoftwareInterrupt;
                end else if ((mtie_reg & mtip_ehr[0]) == 1) begin
                    ret = tagged Valid TimerInterrupt;
                end else if (mfromhost_reg != 0) begin
                    ret = tagged Valid HostInterrupt;
                end
            end
            if (!isValid(ret) && (prv_ehr[0] < prvS || ((prv_ehr[0] == prvS) && ie))) begin
                if ((ssie_reg & ssip_reg) == 1) begin
                    ret = tagged Valid SoftwareInterrupt;
                end else if ((stie_reg & stip_reg) == 1) begin
                    ret = tagged Valid TimerInterrupt;
                end
            end
            ret;
        end);


    ActionValue#(Addr) sret = (actionvalue
            // pop stack
            prv_ehr[0] <= prv1_reg;
            ie_reg <= ie1_reg;
            prv1_reg <= prv2_reg;
            ie1_reg <= ie2_reg;
            if (isa.h) begin
                prv2_reg <= prv3_reg;
                ie2_reg <= ie3_reg;
                prv3_reg <= prvU;
                ie3_reg <= 1;
            end else begin
                prv2_reg <= prvU;
                ie2_reg <= 1;
            end

            let next_pc = 0;
            if (prv_ehr[0] == prvS) begin
                next_pc = sepc_csr;
            end else if (prv_ehr[0] == prvM) begin
                next_pc = mepc_csr;
            end else begin
                $fdisplay(stderr, "[ERROR] CsrFile: sret called when processor wasn't in S or M mode");
                $finish;
            end
            return next_pc;
        endactionvalue);

    ActionValue#(Addr) mrts = (actionvalue
            prv_ehr[0] <= prvS;
            sbadaddr_reg <= mbadaddr_reg;
            scause_i_reg <= mcause_i_reg;
            scause_code_reg <= mcause_code_reg;
            sepc_reg <= mepc_reg;
            return stvec_csr;
        endactionvalue);
    
    function ActionValue#(Addr) trap(Trap t, Addr pc, Addr addr);
        return (actionvalue
                // Check mtdeleg
                Bit#(1) deleg_bit = (case (t) matches
                        tagged Exception .x: mtdeleg_csr[pack(x)];
                        tagged Interrupt .x: mtdeleg_csr[pack(x) << 4];
                    endcase);
                // Disable mprv
                mprv_reg <= 0;
                // push stack
                prv3_reg <= prv2_reg; // no action if H-mode isn't supported
                ie3_reg <= ie2_reg;     // no action if H-mode isn't supported
                prv2_reg <= prv1_reg;
                ie2_reg <= ie1_reg;
                prv1_reg <= prv_ehr[0];
                ie1_reg <= ie_reg;
                Addr next_pc = 0;
                if (deleg_bit == 1) begin
                    // trap to S-mode
                    prv_ehr[0] <= prvS;
                    ie_reg <= 0;
                    sepc_reg <= pc;
                    case (t) matches
                        tagged Exception .x:
                            begin
                                scause_i_reg <= 0;
                                scause_code_reg <= pack(x);
                                case (x)
                                    InstAddrMisaligned:
                                        sbadaddr_reg <= addr;
                                    InstAccessFault:
                                        sbadaddr_reg <= pc;
                                    LoadAddrMisaligned, LoadAccessFault, StoreAddrMisaligned, StoreAccessFault:
                                        sbadaddr_reg <= addr;
                                endcase
                            end
                        tagged Interrupt .x:
                            begin
                                scause_i_reg <= 1;
                                scause_code_reg <= pack(x);
                            end
                    endcase
                    next_pc = stvec_csr + (zeroExtend(prv_ehr[0]) << 6);
                end else begin
                    // trap to M-mode
                    prv_ehr[0] <= prvM;
                    ie_reg <= 0;
                    mepc_reg <= pc;
                    case (t) matches
                        tagged Exception .x:
                            begin
                                mcause_i_reg <= 0;
                                mcause_code_reg <= pack(x);
                                case (x)
                                    InstAddrMisaligned:
                                        mbadaddr_reg <= addr;
                                    InstAccessFault:
                                        mbadaddr_reg <= pc;
                                    LoadAddrMisaligned, LoadAccessFault, StoreAddrMisaligned, StoreAccessFault:
                                        mbadaddr_reg <= addr;
                                endcase
                            end
                        tagged Interrupt .x:
                            begin
                                mcause_i_reg <= 1;
                                mcause_code_reg <= pack(x);
                            end
                    endcase
                    next_pc = mtvec_csr + (zeroExtend(prv_ehr[0]) << 6);
                end
                // FIXME: yield load reservation
                return next_pc;
            endactionvalue);
    endfunction

    function Action wrDirect(CSR csr, Data data);
        return (action
                // increment instret
                instret_ehr[1] <= instret_ehr[1] + 1;
                get_csr(csr)._write(data);
            endaction);
    endfunction

    function Action wrIndirect(Bit#(5) fflags, Bool fpuDirty, Bool xDirty);
        return (action
                // increment instret
                instret_ehr[1] <= instret_ehr[1] + 1;

                // update fflags, fs, and xs
                if ((fflags & fflags_reg) != fflags) begin
                    fflags_reg <= fflags_reg | fflags;
                    fs_ehr[0] <= 2'b11;
                end else if (fpuDirty) begin
                    fs_ehr[0] <= 2'b11;
                end
                if (xDirty) begin
                    xs_ehr[0] <= 2'b11;
                end
            endaction);
    endfunction

    // RULES
    ////////////////////////////////////////////////////////

    rule updateMTIP((mtip_ehr[1] == 0) && (truncate(time_csr) >= mtimecmp_reg));
        mtip_ehr[1] <= 1;
    endrule

`ifndef DISABLE_STIP
    rule updateSTIP(truncate(stime_csr) >= stimecmp_reg);
        stip_reg <= 1;
    endrule
`endif

    rule incrementTimeAndCycle;
        time_ehr[1] <= time_ehr[1] + 1;
        cycle_ehr[1] <= cycle_ehr[1] + 1;
    endrule

    method VMInfo vmI;
        Bit#(2) prv = prv_ehr[0];
        Asid asid = sasid_reg;
        Bit#(5) vm = (prv == prvM) ? vmMbare : vm_reg;
        Addr base = 0;
        Addr bound = 0;
        case (vm)
            vmMbare:
                begin
                    base = 0;
                    bound = -1;
                end
            vmMbb:
                begin
                    base = mbase_csr;
                    bound = mbound_csr;
                end
            vmMbbid:
                begin
                    base = mibase_csr;
                    bound = mibound_csr;
                end
            vmSv32, vmSv39, vmSv48, vmSv57, vmSv64:
                begin
                    base = sptbr_csr;
                    bound = -1;
                end
        endcase
        return VMInfo{ prv: prv, asid: asid, vm: vm, base: base, bound: bound };
    endmethod

    method VMInfo vmD;
        Bit#(2) prv = (mprv_reg == 1) ? prv1_reg : prv_ehr[0];
        Asid asid = sasid_reg;
        Bit#(5) vm = (prv == prvM) ? vmMbare : vm_reg;
        Addr base = 0;
        Addr bound = 0;
        case (vm)
            vmMbare:
                begin
                    base = 0;
                    bound = -1;
                end
            vmMbb:
                begin
                    base = mbase_csr;
                    bound = mbound_csr;
                end
            vmMbbid:
                begin
                    base = mdbase_csr;
                    bound = mdbound_csr;
                end
            vmSv32, vmSv39, vmSv48, vmSv57, vmSv64:
                begin
                    base = sptbr_csr;
                    bound = -1;
                end
        endcase
        return VMInfo{ prv: prv, asid: asid, vm: vm, base: base, bound: bound };
    endmethod

    method CsrState csrState = CsrState {prv: prv_ehr[1], frm: frm_ehr[1], f_enabled: (fs_ehr[1] != 0), x_enabled: (xs_ehr[1] != 0)};

    // Updating CSRs

    // NEW METHODS
    // method Action wr(CSR addr, Data data);
    // method Action indirectWr(Maybe#(Exception) e, Addr pc, Addr addr, Bit#(5) fflags, Bool fpuDirty, Bool xDirty);

    // combined wr and indirectWr
    method ActionValue#(Tuple3#(Maybe#(Trap), Maybe#(Data), Maybe#(Addr)))
            wr( Maybe#(SystemInst) sysInst,
                CSR csr,
                Data data, // zimm or rval
                Maybe#(ExceptionCause) e,
                Bool allowInterrupt,
                Addr pc,
                Bool checkInstAlignment, // if true, addr == nextPc
                Addr addr,
                Bit#(5) fflags,
                Bool fpuDirty,
                Bool xDirty);
        // This method does a lot:
        // -----------------------
        // Checks for misaligned instruction address exception
        // Checks for interrupts
        // If valid exception or interrupt,
        //   change the CSR state and return valid address of exception handler
        // otherwise,
        //   Perform system instruction (maybe return pc of next instruction)
        //   Perform indirect updates

        // Collect all possible sources of pending exceptions
        // 1) external to CSRF (e.g. All memory access faults, IllegalInst from decoding, Load/store address mimsaligned)
        Maybe#(ExceptionCause) pendingException = e;
        // 2) instruction address misaligned
        if (!isValid(pendingException) && checkInstAlignment && (addr[1:0] != 0)) begin // TODO: when we support 'C', this should be addr[0] != 0
            pendingException = tagged Valid InstAddrMisaligned;
        end
        // 3) exceptions from system instructions (ecall, ebreak, illegal CSRRW's)
        if (!isValid(pendingException) &&& sysInst matches tagged Valid .validSysInst) begin
            case (validSysInst)
                ECall:      pendingException = tagged Valid (case (prv_ehr[0])
                                                                prvU: EnvCallU;
                                                                prvS: EnvCallS;
                                                                prvM: EnvCallM;
                                                            endcase);
                EBreak:     pendingException = tagged Valid Breakpoint;
                ERet:       noAction;   // All these 'noActions' will be handled later in this method
                WFI:        noAction;
                MRTS:       noAction;
                CSRRW, CSRRS, CSRRC, CSRR, CSRW:
                            begin
                                Bool read = (validSysInst != CSRW);
                                Bool write = (validSysInst != CSRR);
                                if (!isValidCSR(csr, (fs_ehr[0] != 0)) || !hasCSRPermission(csr, prv_ehr[0], write)) begin
                                    pendingException = tagged Valid IllegalInst;
                                end
                            end
                default:    pendingException = tagged Valid IllegalInst;
            endcase
        end

        // figure out if we need to handle an interrupt or an exception
        Maybe#(Trap) currTrap;
        if (allowInterrupt) begin
            currTrap = pendingInterrupt matches tagged Valid .validInt ? tagged Valid tagged Interrupt validInt :
                      (pendingException matches tagged Valid .validExc ? tagged Valid tagged Exception validExc :
                                                                         tagged Invalid);
        end else begin
            currTrap = pendingException matches tagged Valid .validExc ? tagged Valid tagged Exception validExc :
                                                                         tagged Invalid;
        end

        if (currTrap matches tagged Valid .validTrap) begin
            // Need to handle a trap
            let newPc <- trap(validTrap, pc, addr);
            // This returns currTrap for verification purposes
            // newPc is the address of the trap handler
            return tuple3(currTrap, tagged Invalid, tagged Valid newPc);
        end else if (sysInst matches tagged Valid .validSysInst) begin
            // lets do a system instruction
            if (validSysInst == ERet) begin
                let newPc <- sret;
                wrIndirect(0, False, False); // This is used to increment instret // TODO: clean this up
                return tuple3(tagged Invalid, tagged Invalid, tagged Valid newPc);
            end else if (validSysInst == MRTS) begin
                let newPc <- mrts;
                wrIndirect(0, False, False); // This is used to increment instret // TODO: clean this up
                return tuple3(tagged Invalid, tagged Invalid, tagged Valid newPc);
            end else if (validSysInst == CSRRW || validSysInst == CSRRS || validSysInst == CSRRC) begin
                // CSR read/write operation
                let oldVal = get_csr(csr)._read;
                let newVal = (case(validSysInst)
                        CSRRW: data;
                        CSRRS: (oldVal | data);
                        CSRRC: (oldVal & (~data));
                    endcase);
                wrDirect(csr, newVal); // This increments instret // TODO: clean this up
                // return oldVal
                if (verbose) $fdisplay(fout, "[RVCSRF] ", fshow(validSysInst), " :: ", fshow(csr), " - ", fshow(oldVal), " -> ", fshow(newVal));
                return tuple3(tagged Invalid, tagged Valid oldVal, tagged Invalid);
            end else if (validSysInst == CSRR) begin
                // CSR read operation
                let oldVal = get_csr(csr)._read;
                // return oldVal
                if (verbose) $fdisplay(fout, "[RVCSRF] ", fshow(validSysInst), " :: ", fshow(csr), " = ", fshow(oldVal));
                wrIndirect(0, False, False); // This is used to increment instret // TODO: clean this up
                return tuple3(tagged Invalid, tagged Valid oldVal, tagged Invalid);
            end else if (validSysInst == CSRW) begin
                // CSR write operation
                wrDirect(csr, data); // This increments instret // TODO: clean this up
                // return oldVal
                if (verbose) $fdisplay(fout, "[RVCSRF] ", fshow(validSysInst), " :: ", fshow(csr), " - ? -> ", fshow(data));
                return tuple3(tagged Invalid, tagged Invalid, tagged Invalid);
            end else begin
                // all other system instructions are NOP's
                wrIndirect(fflags, fpuDirty, xDirty);
                return tuple3(tagged Invalid, tagged Invalid, tagged Invalid);
            end
        end else begin
            wrIndirect(fflags, fpuDirty, xDirty);
            return tuple3(tagged Invalid, tagged Invalid, tagged Invalid);
        end
    endmethod

    // tohost/fromhost
    method Action hostToCsrf(Data val) if (mfromhost_reg == 0);
        mfromhost_reg <= val;
    endmethod
    method ActionValue#(Data) csrfToHost;
        mtohost_module.fifo_ifc.deq;
        return mtohost_module.fifo_ifc.first;
    endmethod
    method Bool toHostEmpty;
        return !mtohost_module.fifo_ifc.notEmpty;
    endmethod
    method Bool fromHostZero;
        return mfromhost_reg == 0;
    endmethod

    // externally configured CSRs
    method Action configure(Data miobase);
        miobase_reg <= miobase;
    endmethod

    // Interrupts
    method Action triggerExternalInterrupt;
        // XXX: make this do something
        noAction;
    endmethod

    // performance stats
    method Bool doPerfStats;
        return stats_reg != 0;
    endmethod
endmodule

// this is single core version
module mkRVCsrFile(RVCsrFile);
    let m <- mkRVCsrFileWithId(0);
    return m;
endmodule
