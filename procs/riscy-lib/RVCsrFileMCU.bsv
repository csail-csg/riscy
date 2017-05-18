
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

import RVCsrFile::*;

// From RVCsrFile
export CsrReturn(..);
export RVCsrFile(..);
// From this package
export mkRVCsrFileMCU(..);

module mkRVCsrFileMCU#(
            Data hartid,                      // Compile-time constant
            Bit#(64) time_counter, Bool mtip, // From RTC
            Bool msip,                        // From IPI
            Bool meip                         // From interrupt controller
        )(RVCsrFile);

    let verbose = False;
    File fout = stdout;

    RiscVISASubset isa = defaultValue;
    Bool is32bit       = valueOf(XLEN) == 32;
    Data mvendorid     = 0; // non-commercial
    Data marchid       = 0; // not implemented
    Data mimpid        = 0; // not implemented
    Addr default_mtvec = 'h0000_1000;

    if (isa.s || isa.u) begin
        // ERROR
        errorM("mkRVCsrFileMCU does not support S-mode or U-mode");
    end
    if (isa.f || isa.d) begin
        // ERROR
        errorM("mkRVCsrFileMCU does not support F or D ISA extensions");
    end

    // This is used to allow the readyInterruptSignal to be read after writing to the CSRF
    Wire#(Maybe#(InterruptCause)) readyInterruptWire <- mkDWire(tagged Invalid);

    Reg#(Bit#(2)) prv = readOnlyReg(prvM); // prv is always M

    // Counters
    Reg#(Bit#(64)) cycle_counter <- mkReg(0);
    Reg#(Bit#(64)) instret_counter <- mkReg(0);

    // trap delegation fields
    Reg#(Bit#(12)) medeleg_field <- mkReadOnlyReg(0);
    Reg#(Bit#(12)) mideleg_field <- mkReadOnlyReg(0);

    // trap vector fields (same as CSR without bottom 2 bits)
    Reg#(Bit#(TSub#(XLEN,2))) mtvec_field <- mkReg(truncateLSB(default_mtvec));

    // mstatus fields
    Reg#(Bit#(5)) vm_field   =  readOnlyReg(0); // WARL
    Reg#(Bit#(1)) mxr_field  =  readOnlyReg(0);
    Reg#(Bit#(1)) pum_field  =  readOnlyReg(0);
    Reg#(Bit#(1)) mprv_field =  readOnlyReg(0);
    Reg#(Bit#(2)) xs_field   =  readOnlyReg(0);
    Reg#(Bit#(2)) fs_field   =  readOnlyReg(0);
    Reg#(Bit#(2)) mpp_field  =  readOnlyReg(0);
    Reg#(Bit#(2)) hpp_field  =  readOnlyReg(0);
    Reg#(Bit#(1)) spp_field  =  readOnlyReg(0);
    Reg#(Bit#(1)) mpie_field <- mkReg(0);
    Reg#(Bit#(1)) hpie_field =  readOnlyReg(0);
    Reg#(Bit#(1)) spie_field =  readOnlyReg(0);
    Reg#(Bit#(1)) upie_field =  readOnlyReg(0);
    Reg#(Bit#(1)) mie_field  <- mkReg(0);
    Reg#(Bit#(1)) hie_field  =  readOnlyReg(0);
    Reg#(Bit#(1)) sie_field  =  readOnlyReg(0);
    Reg#(Bit#(1)) uie_field  =  readOnlyReg(0);
    Reg#(Bit#(1)) sd_field   =  readOnlyReg(pack((xs_field == 2'b11) || (fs_field == 2'b11)));

    // mie fields
    Reg#(Bit#(1)) meie_field <- mkReg(0);
    Reg#(Bit#(1)) heie_field =  readOnlyReg(0);
    Reg#(Bit#(1)) seie_field =  readOnlyReg(0);
    Reg#(Bit#(1)) ueie_field =  readOnlyReg(0);
    Reg#(Bit#(1)) mtie_field <- mkReg(0);
    Reg#(Bit#(1)) htie_field =  readOnlyReg(0);
    Reg#(Bit#(1)) stie_field =  readOnlyReg(0);
    Reg#(Bit#(1)) utie_field =  readOnlyReg(0);
    Reg#(Bit#(1)) msie_field <- mkReg(0);
    Reg#(Bit#(1)) hsie_field =  readOnlyReg(0);
    Reg#(Bit#(1)) ssie_field =  readOnlyReg(0);
    Reg#(Bit#(1)) usie_field =  readOnlyReg(0);

    // mip fields
    Reg#(Bit#(1)) meip_field =  readOnlyReg(pack(meip));
    Reg#(Bit#(1)) heip_field =  readOnlyReg(0);
    Reg#(Bit#(1)) seip_field =  readOnlyReg(0);
    Reg#(Bit#(1)) ueip_field =  readOnlyReg(0);
    Reg#(Bit#(1)) mtip_field =  readOnlyReg(pack(mtip));
    Reg#(Bit#(1)) htip_field =  readOnlyReg(0);
    Reg#(Bit#(1)) stip_field =  readOnlyReg(0);
    Reg#(Bit#(1)) utip_field =  readOnlyReg(0);
    Reg#(Bit#(1)) msip_field =  readOnlyReg(pack(msip));
    Reg#(Bit#(1)) hsip_field =  readOnlyReg(0);
    Reg#(Bit#(1)) ssip_field =  readOnlyReg(0);
    Reg#(Bit#(1)) usip_field =  readOnlyReg(0);

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

    function Reg#(Data) getCSR(CSR csr);
        return (case (csr)
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
                CSRmcycle:              mcycle_csr;
                CSRmtime:               mtime_csr;
                CSRminstret:            minstret_csr;
                CSRmcycleh:             mcycleh_csr;
                CSRmtimeh:              mtimeh_csr;
                CSRminstreth:           minstreth_csr;
                default:                (readOnlyReg(0));
            endcase);
    endfunction

    function Bool isLegalCSR(CSR csr);
        return (case (csr)
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
                CSRmcycle:              True;
                CSRmtime:               True;
                CSRminstret:            True;
                CSRmcycleh:             is32bit;
                CSRmtimeh:              is32bit;
                CSRminstreth:           is32bit;
                default:                False;
            endcase);
    endfunction

    function Maybe#(InterruptCause) readyInterruptFunc();
        Bit#(12) ready_interrupts = (mie_field == 1) ?  (truncate(mip_csr) & truncate(mie_csr)) : 0;
        // there are only three possible interrupt causes: 0x008, 0x080, and 0x800
        Maybe#(InterruptCause) ret = tagged Invalid;
        if (ready_interrupts[3] == 1) begin
            // software interrupt
            ret = tagged Valid unpack(3);
        end else if (ready_interrupts[7] == 1) begin
            // timer interrupt
            ret = tagged Valid unpack(7);
        end else if (ready_interrupts[11] == 1) begin
            // external interrupt
            ret = tagged Valid unpack(11);
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
        return VMInfo{ prv: prv, asid: 0, vm: 0, mxr: False, pum: False, base: 0, bound: '1 };
    endmethod

    method VMInfo#(xlen) vmD;
        return VMInfo{ prv: prv, asid: 0, vm: 0, mxr: False, pum: False, base: 0, bound: '1 };
    endmethod

    method CsrState csrState = CsrState {prv: prv, frm: 0, f_enabled: (fs_field != 0), x_enabled: (xs_field != 0)};

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
                ECall:  trapToTake = tagged Valid (tagged Exception EnvCallM);
                // URet and HRet are not supported
                URet: trapToTake = tagged Valid (tagged Exception IllegalInst);
                SRet: trapToTake = tagged Valid (tagged Exception IllegalInst);
                HRet: trapToTake = tagged Valid (tagged Exception IllegalInst);
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
            Addr newPC = mtvec_csr;
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
            return tagged Exception {exception: validTrap, trapHandlerPC: newPC};
        end else if (sysInst matches tagged Valid .validSysInst) begin
            // Non-trapping system instructions
            instret_counter <= instret_counter + 1;
            case (validSysInst)
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
            // Just increment the instret counter
            instret_counter <= instret_counter + 1;
            return tagged None;
        end
    endmethod
endmodule

