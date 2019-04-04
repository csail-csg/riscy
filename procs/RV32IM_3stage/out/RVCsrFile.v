Require Import Bool String List Arith.
Require Import Omega.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


Require Import RVTypes.
Require Import ConcatReg.
Require Import ConfigReg.
Require Import DefaultValue.
Require Import RegUtil.
Require Import Vector.
Definition CsrReturnFields (xlen : nat) := (STRUCT {
    "$tag" :: (Bit 8);
    "Exception$exception" :: TrapCause;
    "Exception$trapHandlerPC" :: (Bit xlen);
    "RedirectPC" :: (Bit xlen);
    "CsrData" :: (Bit xlen);
    "None" :: Void}).
Definition CsrReturn (xlen : nat) := Struct (CsrReturnFields xlen).
(* * interface RVCsrFile#(xlen) *)
Record RVCsrFile (xlen : nat) := {
    RVCsrFile'modules: Modules;
    RVCsrFile'wr : string;
    RVCsrFile'vmI : string;
    RVCsrFile'vmD : string;
    RVCsrFile'csrState : string;
    RVCsrFile'readyInterrupt : string;
    RVCsrFile'wakeFromWFI : string;
}.

Module module'mkRVCsrFile.
    Section Section'mkRVCsrFile.
    Variable xlen : Kind.
    Variable instancePrefix: string.
    Variable hartid: Data.
    Variable time_counter: string.
    Variable mtip: Bool.
    Variable msip: Bool.
    Variable meip: Bool.
    Variable XLEN: nat.
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   Let readyInterruptWire := mkDWire (instancePrefix--"readyInterruptWire").
       Let prv : string := instancePrefix--"prv".
       Let cycle_counter : string := instancePrefix--"cycle_counter".
       Let instret_counter : string := instancePrefix--"instret_counter".
       Let u_ir_field : string := instancePrefix--"u_ir_field".
       Let u_tm_field : string := instancePrefix--"u_tm_field".
       Let u_cy_field : string := instancePrefix--"u_cy_field".
       Let s_ir_field : string := instancePrefix--"s_ir_field".
       Let s_tm_field : string := instancePrefix--"s_tm_field".
       Let s_cy_field : string := instancePrefix--"s_cy_field".
       Let fflags_field : string := instancePrefix--"fflags_field".
       Let frm_field : string := instancePrefix--"frm_field".
       Let asid_field : string := instancePrefix--"asid_field".
       Let sptbr_ppn_field : string := instancePrefix--"sptbr_ppn_field".
       Let sedeleg_field : string := instancePrefix--"sedeleg_field".
       Let sideleg_field : string := instancePrefix--"sideleg_field".
       Let medeleg_field : string := instancePrefix--"medeleg_field".
       Let mideleg_field : string := instancePrefix--"mideleg_field".
       Let mtvec_field : string := instancePrefix--"mtvec_field".
       Let stvec_field : string := instancePrefix--"stvec_field".
       Let vm_field : string := instancePrefix--"vm_field".
       Let mxr_field : string := instancePrefix--"mxr_field".
       Let pum_field : string := instancePrefix--"pum_field".
       Let mprv_field : string := instancePrefix--"mprv_field".
       Let xs_field : string := instancePrefix--"xs_field".
       Let fs_field : string := instancePrefix--"fs_field".
       Let mpp_field : string := instancePrefix--"mpp_field".
       Let spp_field : string := instancePrefix--"spp_field".
       Let mpie_field : string := instancePrefix--"mpie_field".
       Let spie_field : string := instancePrefix--"spie_field".
       Let upie_field : string := instancePrefix--"upie_field".
       Let mie_field : string := instancePrefix--"mie_field".
       Let sie_field : string := instancePrefix--"sie_field".
       Let uie_field : string := instancePrefix--"uie_field".
       Let meie_field : string := instancePrefix--"meie_field".
       Let seie_field : string := instancePrefix--"seie_field".
       Let ueie_field : string := instancePrefix--"ueie_field".
       Let mtie_field : string := instancePrefix--"mtie_field".
       Let stie_field : string := instancePrefix--"stie_field".
       Let utie_field : string := instancePrefix--"utie_field".
       Let msie_field : string := instancePrefix--"msie_field".
       Let ssie_field : string := instancePrefix--"ssie_field".
       Let usie_field : string := instancePrefix--"usie_field".
       Let seip_field : string := instancePrefix--"seip_field".
       Let ueip_field : string := instancePrefix--"ueip_field".
       Let stip_field : string := instancePrefix--"stip_field".
       Let utip_field : string := instancePrefix--"utip_field".
       Let ssip_field : string := instancePrefix--"ssip_field".
       Let usip_field : string := instancePrefix--"usip_field".
       Let mucycle_delta_field : string := instancePrefix--"mucycle_delta_field".
       Let mutime_delta_field : string := instancePrefix--"mutime_delta_field".
       Let muinstret_delta_field : string := instancePrefix--"muinstret_delta_field".
       Let mscycle_delta_field : string := instancePrefix--"mscycle_delta_field".
       Let mstime_delta_field : string := instancePrefix--"mstime_delta_field".
       Let msinstret_delta_field : string := instancePrefix--"msinstret_delta_field".
       Let mucycle_delta_csr : string := instancePrefix--"mucycle_delta_csr".
       Let mutime_delta_csr : string := instancePrefix--"mutime_delta_csr".
       Let muinstret_delta_csr : string := instancePrefix--"muinstret_delta_csr".
       Let mscycle_delta_csr : string := instancePrefix--"mscycle_delta_csr".
       Let mstime_delta_csr : string := instancePrefix--"mstime_delta_csr".
       Let msinstret_delta_csr : string := instancePrefix--"msinstret_delta_csr".
       Let mucycle_deltah_csr : string := instancePrefix--"mucycle_deltah_csr".
       Let mutime_deltah_csr : string := instancePrefix--"mutime_deltah_csr".
       Let muinstret_deltah_csr : string := instancePrefix--"muinstret_deltah_csr".
       Let mscycle_deltah_csr : string := instancePrefix--"mscycle_deltah_csr".
       Let mstime_deltah_csr : string := instancePrefix--"mstime_deltah_csr".
       Let msinstret_deltah_csr : string := instancePrefix--"msinstret_deltah_csr".
       Let fflagsFieldReg : string := instancePrefix--"fflagsFieldReg".
       Let frmFieldReg : string := instancePrefix--"frmFieldReg".
       Let fflags_csr : string := instancePrefix--"fflags_csr".
       Let frm_csr : string := instancePrefix--"frm_csr".
       Let extFrmFlagsReg : string := instancePrefix--"extFrmFlagsReg".
       Let fcsr_csr : string := instancePrefix--"fcsr_csr".
       Let ucycle_counter : string := instancePrefix--"ucycle_counter".
       Let utime_counter : string := instancePrefix--"utime_counter".
       Let uinstret_counter : string := instancePrefix--"uinstret_counter".
       Let ucycleCounterLSBReg : string := instancePrefix--"ucycleCounterLSBReg".
       Let cycle_csr : string := instancePrefix--"cycle_csr".
       Let utimeCounterLSBReg : string := instancePrefix--"utimeCounterLSBReg".
       Let time_csr : string := instancePrefix--"time_csr".
       Let uinstretCounterLSBReg : string := instancePrefix--"uinstretCounterLSBReg".
       Let instret_csr : string := instancePrefix--"instret_csr".
       Let ucycleCounterMSBReg : string := instancePrefix--"ucycleCounterMSBReg".
       Let cycleh_csr : string := instancePrefix--"cycleh_csr".
       Let utimeCounterMSBReg : string := instancePrefix--"utimeCounterMSBReg".
       Let timeh_csr : string := instancePrefix--"timeh_csr".
       Let uinstregCounterMSBReg : string := instancePrefix--"uinstregCounterMSBReg".
       Let instreth_csr : string := instancePrefix--"instreth_csr".
       Let sscratch_csr : string := instancePrefix--"sscratch_csr".
       Let sepc_csr : string := instancePrefix--"sepc_csr".
       Let scause_csr : string := instancePrefix--"scause_csr".
       Let sbadaddr_csr : string := instancePrefix--"sbadaddr_csr".
       Let scycle_csr : string := instancePrefix--"scycle_csr".
       Let stime_csr : string := instancePrefix--"stime_csr".
       Let sinstret_csr : string := instancePrefix--"sinstret_csr".
       Let scycleh_csr : string := instancePrefix--"scycleh_csr".
       Let stimeh_csr : string := instancePrefix--"stimeh_csr".
       Let sinstreth_csr : string := instancePrefix--"sinstreth_csr".
       Let getMISA := mkGetMISA (instancePrefix--"getMISA").
       Let misa_csr : string := instancePrefix--"misa_csr".
       Let mvendorid_csr : string := instancePrefix--"mvendorid_csr".
       Let marchid_csr : string := instancePrefix--"marchid_csr".
       Let mimpid_csr : string := instancePrefix--"mimpid_csr".
       Let mhartid_csr : string := instancePrefix--"mhartid_csr".
       Let mscratch_csr : string := instancePrefix--"mscratch_csr".
       Let mepc_csr : string := instancePrefix--"mepc_csr".
       Let mcause_csr : string := instancePrefix--"mcause_csr".
       Let mbadaddr_csr : string := instancePrefix--"mbadaddr_csr".
       Let mbase_csr : string := instancePrefix--"mbase_csr".
       Let mbound_csr : string := instancePrefix--"mbound_csr".
       Let mibase_csr : string := instancePrefix--"mibase_csr".
       Let mibound_csr : string := instancePrefix--"mibound_csr".
       Let mdbase_csr : string := instancePrefix--"mdbase_csr".
       Let mdbound_csr : string := instancePrefix--"mdbound_csr".
       Let hasCSRPermission := mkHasCSRPermission (instancePrefix--"hasCSRPermission").
       Let toCauseCSR := mkToCauseCSR (instancePrefix--"toCauseCSR").
    Let toCauseCSRtoCauseCSR : string := (ToCauseCSR'toCauseCSR toCauseCSR).
    Definition mkRVCsrFileModule: Modules.
        refine  (BKMODULE {
                   LET verbose : Bool = False
       with         LET fout : File <- #stdout
       with         LET isa : RiscVISASubset <- #defaultValue
       with         LET is32bit : Bool <- (null == $32)
       with         LET mvendorid : Data <- $0
       with         LET marchid : Data <- $0
       with         LET mimpid : Data <- $0
       with         LET default_mtvec : Addr <- $4096
       with         LET default_stvec : Addr <- $32768
       with (BKMod (a_type'modules readyInterruptWire :: nil))
       with Register prv : Bit 2 <- $prvM
       with Register cycle_counter : Bit 64 <- $0
       with Register instret_counter : Bit 64 <- $0
       with Register u_ir_field : Bit 1 <- $0
       with Register u_tm_field : Bit 1 <- $0
       with Register u_cy_field : Bit 1 <- $0
       with Register s_ir_field : Bit 1 <- $0
       with Register s_tm_field : Bit 1 <- $0
       with Register s_cy_field : Bit 1 <- $0
       with Register fflags_field : Bit 5 <- $0
       with Register frm_field : Bit 3 <- $0
       with Register asid_field : Bit 10 <- $0
       with Register sptbr_ppn_field : Bit 22 <- $0
       with Register sedeleg_field : Bit 12 <- $0
       with Register sideleg_field : Bit 12 <- $0
       with Register medeleg_field : Bit 12 <- $0
       with Register mideleg_field : Bit 12 <- $0
       with Register mtvec_field : Bit TSub xlen 2 <- $truncateLSB(default_mtvec)
       with Register stvec_field : Bit TSub xlen 2 <- $truncateLSB(default_stvec)
       with Register vm_field : Bit 5 <- $0
       with Register mxr_field : Bit 1 <- $0
       with Register pum_field : Bit 1 <- $0
       with Register mprv_field : Bit 1 <- $0
       with Register xs_field : Bit 2 <- $0
       with Register fs_field : Bit 2 <- $0
       with Register mpp_field : Bit 2 <- $0
       with CallM hpp_field : (Reg (Bit 2)) <-  readOnlyReg($0)
       with Register spp_field : Bit 1 <- $0
       with Register mpie_field : Bit 1 <- $0
       with CallM hpie_field : (Reg (Bit 1)) <-  readOnlyReg($0)
       with Register spie_field : Bit 1 <- $0
       with Register upie_field : Bit 1 <- $0
       with Register mie_field : Bit 1 <- $0
       with CallM hie_field : (Reg (Bit 1)) <-  readOnlyReg($0)
       with Register sie_field : Bit 1 <- $0
       with Register uie_field : Bit 1 <- $0
       with CallM sd_field : (Reg (Bit 1)) <-  readOnlyReg( pack(((#xs_field_v == $3) || (#fs_field_v == $3))))
       with Register meie_field : Bit 1 <- $0
       with CallM heie_field : (Reg (Bit 1)) <-  readOnlyReg($0)
       with Register seie_field : Bit 1 <- $0
       with Register ueie_field : Bit 1 <- $0
       with Register mtie_field : Bit 1 <- $0
       with CallM htie_field : (Reg (Bit 1)) <-  readOnlyReg($0)
       with Register stie_field : Bit 1 <- $0
       with Register utie_field : Bit 1 <- $0
       with Register msie_field : Bit 1 <- $0
       with CallM hsie_field : (Reg (Bit 1)) <-  readOnlyReg($0)
       with Register ssie_field : Bit 1 <- $0
       with Register usie_field : Bit 1 <- $0
       with CallM meip_field : (Reg (Bit 1)) <-  readOnlyReg( pack(#meip))
       with CallM heip_field : (Reg (Bit 1)) <-  readOnlyReg($0)
       with Register seip_field : Bit 1 <- $0
       with Register ueip_field : Bit 1 <- $0
       with CallM mtip_field : (Reg (Bit 1)) <-  readOnlyReg( pack(#mtip))
       with CallM htip_field : (Reg (Bit 1)) <-  readOnlyReg($0)
       with Register stip_field : Bit 1 <- $0
       with Register utip_field : Bit 1 <- $0
       with CallM msip_field : (Reg (Bit 1)) <-  readOnlyReg( pack(#msip))
       with CallM hsip_field : (Reg (Bit 1)) <-  readOnlyReg($0)
       with Register ssip_field : Bit 1 <- $0
       with Register usip_field : Bit 1 <- $0
       with CallM mcycle_csr : (Reg Data) <-  readOnlyReg( truncate(#cycle_counter_v))
       with CallM mtime_csr : (Reg Data) <-  readOnlyReg( truncate(#time_counter_v))
       with CallM minstret_csr : (Reg Data) <-  readOnlyReg( truncate(#instret_counter_v))
       with CallM mcycleh_csr : (Reg Data) <-  readOnlyReg( truncateLSB(#cycle_counter_v))
       with CallM mtimeh_csr : (Reg Data) <-  readOnlyReg( truncateLSB(#time_counter_v))
       with CallM minstreth_csr : (Reg Data) <-  readOnlyReg( truncateLSB(#instret_counter_v))
       with Register mucycle_delta_field : Bit 64 <- $0
       with Register mutime_delta_field : Bit 64 <- $0
       with Register muinstret_delta_field : Bit 64 <- $0
       with Register mscycle_delta_field : Bit 64 <- $0
       with Register mstime_delta_field : Bit 64 <- $0
       with Register msinstret_delta_field : Bit 64 <- $0
       with Register mucycle_delta_csr : Data <-  truncateReg(#mucycle_delta_field_v)
       with Register mutime_delta_csr : Data <-  truncateReg(#mutime_delta_field_v)
       with Register muinstret_delta_csr : Data <-  truncateReg(#muinstret_delta_field_v)
       with Register mscycle_delta_csr : Data <-  truncateReg(#mscycle_delta_field_v)
       with Register mstime_delta_csr : Data <-  truncateReg(#mstime_delta_field_v)
       with Register msinstret_delta_csr : Data <-  truncateReg(#msinstret_delta_field_v)
       with Register mucycle_deltah_csr : Data <-  truncateRegLSB(#mucycle_delta_field_v)
       with Register mutime_deltah_csr : Data <-  truncateRegLSB(#mutime_delta_field_v)
       with Register muinstret_deltah_csr : Data <-  truncateRegLSB(#muinstret_delta_field_v)
       with Register mscycle_deltah_csr : Data <-  truncateRegLSB(#mscycle_delta_field_v)
       with Register mstime_deltah_csr : Data <-  truncateRegLSB(#mstime_delta_field_v)
       with Register msinstret_deltah_csr : Data <-  truncateRegLSB(#msinstret_delta_field_v)
       with Register fflagsFieldReg : Data <-  zeroExtendReg(#fflags_field_v)
       with Register frmFieldReg : Data <-  zeroExtendReg(#frm_field_v)
       with Register fflags_csr : Data <-  addWriteSideEffect(#fflagsFieldReg_v,  fs_field_write($3))
       with Register frm_csr : Data <-  addWriteSideEffect(#frmFieldReg_v,  fs_field_write($3))
       with CallM frmFlagsReg : (Reg (Bit 8)) <-  concatReg2(#frm_field_v, #fflags_field_v)
       with Register extFrmFlagsReg : Data <-  zeroExtendReg(#frmFlagsReg_v)
       with Register fcsr_csr : Data <-  addWriteSideEffect(#extFrmFlagsReg_v,  fs_field_write($3))
       with Register ucycle_counter : Bit 64 <-  addReg(#cycle_counter_v, #mucycle_delta_field_v)
       with Register utime_counter : Bit 64 <-  addReg(#time_counter_v, #mutime_delta_field_v)
       with Register uinstret_counter : Bit 64 <-  addReg(#instret_counter_v, #muinstret_delta_field_v)
       with Register ucycleCounterLSBReg : Data <-  truncateReg(#ucycle_counter_v)
       with Register cycle_csr : Data <-  mkReadOnlyReg(#ucycleCounterLSBReg_v)
       with Register utimeCounterLSBReg : Data <-  truncateReg(#utime_counter_v)
       with Register time_csr : Data <-  mkReadOnlyReg(#utimeCounterLSBReg_v)
       with Register uinstretCounterLSBReg : Data <-  truncateReg(#uinstret_counter_v)
       with Register instret_csr : Data <-  mkReadOnlyReg(#uinstretCounterLSBReg_v)
       with Register ucycleCounterMSBReg : Data <-  truncateRegLSB(#ucycle_counter_v)
       with Register cycleh_csr : Data <-  mkReadOnlyReg(#ucycleCounterMSBReg_v)
       with Register utimeCounterMSBReg : Data <-  truncateRegLSB(#utime_counter_v)
       with Register timeh_csr : Data <-  mkReadOnlyReg(#utimeCounterMSBReg_v)
       with Register uinstregCounterMSBReg : Data <-  truncateRegLSB(#uinstret_counter_v)
       with Register instreth_csr : Data <-  mkReadOnlyReg(#uinstregCounterMSBReg_v)
       with CallM sstatus_csr : (Reg Data) <-  concatReg20(#sd_field_v,  readOnlyReg($0), #vm_field_v,  readOnlyReg($0),  readOnlyReg($0), #pum_field_v,  readOnlyReg($0), #xs_field_v, #fs_field_v,  readOnlyReg($0),  readOnlyReg($0), #spp_field_v,  readOnlyReg($0),  readOnlyReg($0), #spie_field_v, #upie_field_v,  readOnlyReg($0),  readOnlyReg($0), #sie_field_v, #uie_field_v)
       with CallM sedeleg_csr : (Reg Data) <-  concatReg2( readOnlyReg($0), #sedeleg_field_v)
       with CallM sideleg_csr : (Reg Data) <-  concatReg2( readOnlyReg($0), #sideleg_field_v)
       with CallM sie_csr : (Reg Data) <-  concatReg13( readOnlyReg($0),  readOnlyReg($0),  readOnlyReg($0), #seie_field_v, #ueie_field_v,  readOnlyReg($0),  readOnlyReg($0), #stie_field_v, #utie_field_v,  readOnlyReg($0),  readOnlyReg($0), #ssie_field_v, #usie_field_v)
       with CallM stvec_csr : (Reg Data) <-  concatReg2(#stvec_field_v,  readOnlyReg($0))
       with Register sscratch_csr : Data <- $0
       with Register sepc_csr : Data <- $0
       with Register scause_csr : Data <- $0
       with Register sbadaddr_csr : Data <- $0
       with CallM sip_csr : (Reg Data) <-  concatReg13( readOnlyReg($0),  readOnlyReg($0),  readOnlyReg($0),  readOnlyReg(#seip_field_v),  readOnlyReg(#ueip_field_v),  readOnlyReg($0),  readOnlyReg($0),  readOnlyReg(#stip_field_v),  readOnlyReg(#utip_field_v),  readOnlyReg($0),  readOnlyReg($0), #ssip_field_v, #usip_field_v)
       with CallM sptbr_csr : (Reg Data) <-  concatReg2(#asid_field_v, #sptbr_ppn_field_v)
       with         LET scycle_counter : (Bit 64) <- (#cycle_counter_v + #mscycle_delta_field_v)
       with         LET stime_counter : (Bit 64) <- (#time_counter_v + #mstime_delta_field_v)
       with         LET sinstret_counter : (Bit 64) <- (#instret_counter_v + #msinstret_delta_field_v)
       with Register scycle_csr : Data <-  mkReadOnlyReg( truncate(#scycle_counter))
       with Register stime_csr : Data <-  mkReadOnlyReg( truncate(#stime_counter))
       with Register sinstret_csr : Data <-  mkReadOnlyReg( truncate(#sinstret_counter))
       with Register scycleh_csr : Data <-  mkReadOnlyReg( truncateLSB(#scycle_counter))
       with Register stimeh_csr : Data <-  mkReadOnlyReg( truncateLSB(#stime_counter))
       with Register sinstreth_csr : Data <-  mkReadOnlyReg( truncateLSB(#sinstret_counter))
       with (BKMod (GetMISA'modules getMISA :: nil))
       with Register misa_csr : Data <-  mkReadOnlyReg( getMISAgetMISA(#isa))
       with Register mvendorid_csr : Data <-  mkReadOnlyReg(#mvendorid)
       with Register marchid_csr : Data <-  mkReadOnlyReg(#marchid)
       with Register mimpid_csr : Data <-  mkReadOnlyReg(#mimpid)
       with Register mhartid_csr : Data <-  mkReadOnlyReg(#hartid)
       with CallM mstatus_csr : (Reg Data) <-  concatReg20(#sd_field_v,  readOnlyReg($0), #vm_field_v,  readOnlyReg($0), #mxr_field_v, #pum_field_v, #mprv_field_v, #xs_field_v, #fs_field_v, #mpp_field_v, #hpp_field_v, #spp_field_v, #mpie_field_v, #hpie_field_v, #spie_field_v, #upie_field_v, #mie_field_v, #hie_field_v, #sie_field_v, #uie_field_v)
       with CallM medeleg_csr : (Reg Data) <-  concatReg2( readOnlyReg($0), #medeleg_field_v)
       with CallM mideleg_csr : (Reg Data) <-  concatReg2( readOnlyReg($0), #mideleg_field_v)
       with CallM mie_csr : (Reg Data) <-  concatReg13( readOnlyReg($0), #meie_field_v, #heie_field_v, #seie_field_v, #ueie_field_v, #mtie_field_v, #htie_field_v, #stie_field_v, #utie_field_v, #msie_field_v, #hsie_field_v, #ssie_field_v, #usie_field_v)
       with CallM mtvec_csr : (Reg Data) <-  concatReg2(#mtvec_field_v,  readOnlyReg($0))
       with Register mscratch_csr : Data <- $0
       with Register mepc_csr : Data <- $0
       with Register mcause_csr : Data <- $0
       with Register mbadaddr_csr : Data <- $0
       with CallM mip_csr : (Reg Data) <-  concatReg13( readOnlyReg($0),  readOnlyReg(#meip_field_v),  readOnlyReg(#heip_field_v),  readOnlyReg(#seip_field_v),  readOnlyReg(#ueip_field_v),  readOnlyReg(#mtip_field_v), #htip_field_v, #stip_field_v, #utip_field_v,  readOnlyReg(#msip_field_v), #hsip_field_v, #ssip_field_v, #usip_field_v)
       with Register mbase_csr : Data <- $0
       with Register mbound_csr : Data <- $0
       with Register mibase_csr : Data <- $0
       with Register mibound_csr : Data <- $0
       with Register mdbase_csr : Data <- $0
       with Register mdbound_csr : Data <- $0
       with CallM mucounteren_csr : (Reg Data) <-  concatReg4( readOnlyReg($0), #u_ir_field_v, #u_tm_field_v, #u_cy_field_v)
       with CallM mscounteren_csr : (Reg Data) <-  concatReg4( readOnlyReg($0), #s_ir_field_v, #s_tm_field_v, #s_cy_field_v)
       with (BKMod (HasCSRPermission'modules hasCSRPermission :: nil))
       with (BKMod (ToCauseCSR'modules toCauseCSR :: nil))
       with Rule instancePrefix--"setReadyInterruptWire" :=
        Read mideleg_csr_v : Data <- mideleg_csr;
        Read mie_csr_v : Data <- mie_csr;
        Read mie_field_v : Bit 1 <- mie_field;
        Read mip_csr_v : Data <- mip_csr;
        Read prv_v : Bit 2 <- prv;
        Read sideleg_csr_v : Data <- sideleg_csr;
        Read sie_field_v : Bit 1 <- sie_field;
        Read uie_field_v : Bit 1 <- uie_field;
       LET ready_interrupts : (Bit 12) <- UniBit (Trunc 12 (32 - 12)) (castBits _ _ _ _ #mie_csr_v);
               Call ready_machine_interrupts : Bit 12 <- (#ready_interrupts & ~ truncate(#mideleg_csr_v));
               LET machine_interrupts_enabled : Bool <- ((#mie_field_v == $1) || (#prv_v < #prvM));
               Call ready_supervisor_interrupts : Bit 12 <- ((#ready_interrupts &  truncate(#mideleg_csr_v)) & ~ truncate(#sideleg_csr_v));
               LET supervisor_interrupts_enabled : Bool <- (((#sie_field_v == $1) && (#prv_v == #prvS)) || (#prv_v < #prvS));
               Call ready_user_interrupts : Bit 12 <- ((#ready_interrupts &  truncate(#mideleg_csr_v)) &  truncate(#sideleg_csr_v));
               LET user_interrupts_enabled : Bool = ((#uie_field_v == $1) && (#prv_v == #prvU));
               Assign ready_interrupts = ((#machine_interrupts_enabled#ready_machine_interrupts$0 | #supervisor_interrupts_enabled#ready_supervisor_interrupts$0) | #user_interrupts_enabled#ready_user_interrupts$0);
               LET ret : (Maybe InterruptCause) <- STRUCT {  "$tag" ::= $1; "Invalid" ::= $0; "Valid" ::= $0 };
               If (#ready_interrupts != $0)
        then                 BKSTMTS {
                Assign ret = STRUCT {  "$tag" ::= $0; "Valid" ::=  unpack( pack( FIXME$countZerosLSB(#ready_interrupts))); "Invalid" ::= $0 };
;
        Retv;
               Write readyInterruptWire : Maybe InterruptCause <- #ret;
        Retv (* rule setReadyInterruptWire *)
       with Rule instancePrefix--"incrementCycle" :=
        Read cycle_counter_v : Bit 64 <- cycle_counter;
               Write cycle_counter : Bit 64 <- (#cycle_counter_v + $1);
        Retv (* rule incrementCycle *)
       with Method instancePrefix--"vmI" () : (VMInfo xlen) :=
        Read asid_field_v : Bit 10 <- "asid_field";        Read mbase_csr_v : Data <- "mbase_csr";        Read mbound_csr_v : Data <- "mbound_csr";        Read mibase_csr_v : Data <- "mibase_csr";        Read mibound_csr_v : Data <- "mibound_csr";        Read mxr_field_v : Bit 1 <- "mxr_field";        Read prv_v : Bit 2 <- "prv";        Read pum_field_v : Bit 1 <- "pum_field";        Read sptbr_ppn_field_v : Bit 22 <- "sptbr_ppn_field";        Read vm_field_v : Bit 5 <- "vm_field";        LET vm : (Bit 5) <- (#prv_v == #prvM)#vmMbare#vm_field_v;
        LET base : Addr <- null;
        LET bound : Addr <- null;
        Ret STRUCT { "prv" ::= (#prv_v); "asid" ::= (#asid_field_v); "vm" ::= (#vm); "mxr" ::= ( unpack(#mxr_field_v)); "pum" ::= ( unpack(#pum_field_v)); "base" ::= (#base); "bound" ::= (#bound)  }

       with Method instancePrefix--"vmD" () : (VMInfo xlen) :=
        Read asid_field_v : Bit 10 <- "asid_field";        Read mbase_csr_v : Data <- "mbase_csr";        Read mbound_csr_v : Data <- "mbound_csr";        Read mdbase_csr_v : Data <- "mdbase_csr";        Read mdbound_csr_v : Data <- "mdbound_csr";        Read mpp_field_v : Bit 2 <- "mpp_field";        Read mprv_field_v : Bit 1 <- "mprv_field";        Read mxr_field_v : Bit 1 <- "mxr_field";        Read prv_v : Bit 2 <- "prv";        Read pum_field_v : Bit 1 <- "pum_field";        Read sptbr_ppn_field_v : Bit 22 <- "sptbr_ppn_field";        Read vm_field_v : Bit 5 <- "vm_field";        LET vm_prv : (Bit 2) <- (#mprv_field_v == $1)#mpp_field_v#prv_v;
        LET vm : (Bit 5) <- (#vm_prv == #prvM)#vmMbare#vm_field_v;
        LET base : Addr <- null;
        LET bound : Addr <- null;
        Ret STRUCT { "prv" ::= (#vm_prv); "asid" ::= (#asid_field_v); "vm" ::= (#vm); "mxr" ::= ( unpack(#mxr_field_v)); "pum" ::= ( unpack(#pum_field_v)); "base" ::= (#base); "bound" ::= (#bound)  }

       with Method instancePrefix--"csrState" () : CsrState :=
        Read frm_field_v : Bit 3 <- "frm_field";        Read fs_field_v : Bit 2 <- "fs_field";        Read prv_v : Bit 2 <- "prv";        Read xs_field_v : Bit 2 <- "xs_field";STRUCT { "prv" ::= (#prv_v); "frm" ::= (#frm_field_v); "f_enabled" ::= ((#fs_field_v != $0)); "x_enabled" ::= ((#xs_field_v != $0))  }

       with Method instancePrefix--"readyInterrupt" () : (Maybe InterruptCause) :=
        Ret #readyInterruptWire

       with Method instancePrefix--"wakeFromWFI" () : Bool :=
        Read mie_csr_v : Data <- "mie_csr";        Read mip_csr_v : Data <- "mip_csr";        Ret ((#mip_csr_v & #mie_csr_v) != $0)

       with Method9 instancePrefix--"wr" (pc : Addr) (sysInst : (Maybe SystemInst)) (csr : CSR) (data : Data) (addr : Addr) (trap : (Maybe TrapCause)) (fflags : (Bit 5)) (fpuDirty : Bool) (xDirty : Bool) : (ActionValue (CsrReturn xlen)) :=
        Read cycle_csr_v : Data <- "cycle_csr";        Read cycleh_csr_v : Data <- "cycleh_csr";        Read fcsr_csr_v : Data <- "fcsr_csr";        Read fflags_csr_v : Data <- "fflags_csr";        Read fflags_field_v : Bit 5 <- "fflags_field";        Read frm_csr_v : Data <- "frm_csr";        Read fs_field_v : Bit 2 <- "fs_field";        Read hie_field_v : Bit 1 <- "hie_field";        Read instret_counter_v : Bit 64 <- "instret_counter";        Read instret_csr_v : Data <- "instret_csr";        Read instreth_csr_v : Data <- "instreth_csr";        Read marchid_csr_v : Data <- "marchid_csr";        Read mbadaddr_csr_v : Data <- "mbadaddr_csr";        Read mbase_csr_v : Data <- "mbase_csr";        Read mbound_csr_v : Data <- "mbound_csr";        Read mcause_csr_v : Data <- "mcause_csr";        Read mcycle_csr_v : Data <- "mcycle_csr";        Read mcycleh_csr_v : Data <- "mcycleh_csr";        Read mdbase_csr_v : Data <- "mdbase_csr";        Read mdbound_csr_v : Data <- "mdbound_csr";        Read medeleg_csr_v : Data <- "medeleg_csr";        Read mepc_csr_v : Data <- "mepc_csr";        Read mhartid_csr_v : Data <- "mhartid_csr";        Read mibase_csr_v : Data <- "mibase_csr";        Read mibound_csr_v : Data <- "mibound_csr";        Read mideleg_csr_v : Data <- "mideleg_csr";        Read mie_csr_v : Data <- "mie_csr";        Read mie_field_v : Bit 1 <- "mie_field";        Read mimpid_csr_v : Data <- "mimpid_csr";        Read minstret_csr_v : Data <- "minstret_csr";        Read minstreth_csr_v : Data <- "minstreth_csr";        Read mip_csr_v : Data <- "mip_csr";        Read misa_csr_v : Data <- "misa_csr";        Read mpie_field_v : Bit 1 <- "mpie_field";        Read mpp_field_v : Bit 2 <- "mpp_field";        Read mscounteren_csr_v : Data <- "mscounteren_csr";        Read mscratch_csr_v : Data <- "mscratch_csr";        Read mscycle_delta_csr_v : Data <- "mscycle_delta_csr";        Read mscycle_deltah_csr_v : Data <- "mscycle_deltah_csr";        Read msinstret_delta_csr_v : Data <- "msinstret_delta_csr";        Read msinstret_deltah_csr_v : Data <- "msinstret_deltah_csr";        Read mstatus_csr_v : Data <- "mstatus_csr";        Read mstime_delta_csr_v : Data <- "mstime_delta_csr";        Read mstime_deltah_csr_v : Data <- "mstime_deltah_csr";        Read mtime_csr_v : Data <- "mtime_csr";        Read mtimeh_csr_v : Data <- "mtimeh_csr";        Read mtvec_csr_v : Data <- "mtvec_csr";        Read mucounteren_csr_v : Data <- "mucounteren_csr";        Read mucycle_delta_csr_v : Data <- "mucycle_delta_csr";        Read mucycle_deltah_csr_v : Data <- "mucycle_deltah_csr";        Read muinstret_delta_csr_v : Data <- "muinstret_delta_csr";        Read muinstret_deltah_csr_v : Data <- "muinstret_deltah_csr";        Read mutime_delta_csr_v : Data <- "mutime_delta_csr";        Read mutime_deltah_csr_v : Data <- "mutime_deltah_csr";        Read mvendorid_csr_v : Data <- "mvendorid_csr";        Read prv_v : Bit 2 <- "prv";        Read s_cy_field_v : Bit 1 <- "s_cy_field";        Read s_ir_field_v : Bit 1 <- "s_ir_field";        Read s_tm_field_v : Bit 1 <- "s_tm_field";        Read sbadaddr_csr_v : Data <- "sbadaddr_csr";        Read scause_csr_v : Data <- "scause_csr";        Read scycle_csr_v : Data <- "scycle_csr";        Read scycleh_csr_v : Data <- "scycleh_csr";        Read sedeleg_csr_v : Data <- "sedeleg_csr";        Read sepc_csr_v : Data <- "sepc_csr";        Read sideleg_csr_v : Data <- "sideleg_csr";        Read sie_csr_v : Data <- "sie_csr";        Read sie_field_v : Bit 1 <- "sie_field";        Read sinstret_csr_v : Data <- "sinstret_csr";        Read sinstreth_csr_v : Data <- "sinstreth_csr";        Read sip_csr_v : Data <- "sip_csr";        Read spie_field_v : Bit 1 <- "spie_field";        Read spp_field_v : Bit 1 <- "spp_field";        Read sptbr_csr_v : Data <- "sptbr_csr";        Read sscratch_csr_v : Data <- "sscratch_csr";        Read sstatus_csr_v : Data <- "sstatus_csr";        Read stime_csr_v : Data <- "stime_csr";        Read stimeh_csr_v : Data <- "stimeh_csr";        Read stvec_csr_v : Data <- "stvec_csr";        Read time_csr_v : Data <- "time_csr";        Read timeh_csr_v : Data <- "timeh_csr";        Read u_cy_field_v : Bit 1 <- "u_cy_field";        Read u_ir_field_v : Bit 1 <- "u_ir_field";        Read u_tm_field_v : Bit 1 <- "u_tm_field";        Read uie_field_v : Bit 1 <- "uie_field";        LET trapToTake : (Maybe TrapCause) <- #trap;
        If ! isValid(#trapToTake)#sysInst$taggedValid.validSysInst
        then                 BKSTMTS {
                Assign trapToTake = STRUCT {  "$tag" ::= $1; "Invalid" ::= $0; "Valid" ::= $0 }
;
;
        Retv;
        If #trapToTake$taggedValid.validTrap
        then                 BKSTMTS {
                LET delegToS : Bool <- ((#prv_v <= #prvS) && null);
                LET newPC : Addr <- #delegToS#stvec_csr_v#mtvec_csr_v;
                If #delegToS
        then                 BKSTMTS {
                Write sepc_csr : Data <- #pc;
                Write scause_csr : Data <-  toCauseCSRtoCauseCSR(#validTrap);
                BKSTMTS {
                Write sbadaddr_csr : Data <- #sbadaddr_csr_v;

;
                Write spp_field : Bit 1 <- (#prv_v == #prvU)$0$1;
                Write spie_field : Bit 1 <- (#prv_v == #prvU)#uie_field_v#sie_field_v;
                Write sie_field : Bit 1 <- $0;
                Write prv : Bit 2 <- #prvS;
;
        Retv
        else                 BKSTMTS {
                Write mepc_csr : Data <- #pc;
                Write mcause_csr : Data <-  toCauseCSRtoCauseCSR(#validTrap);
                Write mbadaddr_csr : Data <- #mbadaddr_csr_v
;
                Write mpp_field : Bit 2 <- #prv_v;
                Write mpie_field : Bit 1 <- null;
                Write mie_field : Bit 1 <- $0;
                Write prv : Bit 2 <- #prvM;
;
        Retv;;
                Ret STRUCT {  "$tag" ::= $0; "CsrData" ::= $0; "Exception$exception" ::= #validTrap; "Exception$trapHandlerPC" ::= #newPC; "None" ::= $0; "RedirectPC" ::= $0 };
;
        Retv
        else                 If #sysInst$taggedValid.validSysInst
        then                 BKSTMTS {
                Write instret_counter : Bit 64 <- (#instret_counter_v + $1);
                BKSTMTS {
                Ret STRUCT {  "$tag" ::= $3; "CsrData" ::= $0; "Exception$exception" ::= $0; "Exception$trapHandlerPC" ::= $0; "None" ::= $0; "RedirectPC" ::= $0 };

;
;
        Retv
        else                 BKSTMTS {
                If ((#fflags | #fflags_field_v) != #fflags_field_v)
        then                 BKSTMTS {
                Write fflags_field : Bit 5 <- (#fflags_field_v | #fflags);
                Assign fpuDirty = True;
;
        Retv;
                If #fpuDirty
        then                 BKSTMTS {
                If (#fs_field_v == $0)
        then                 BKSTMTS {
         FIXME$$fdisplay(#stderr, null);
;
        Retv;
                Write fs_field : Bit 2 <- $3;
;
        Retv;
                If #xDirty
        then                 BKSTMTS {
                Write xs_field : Bit 2 <- $3;
;
        Retv;
                Write instret_counter : Bit 64 <- (#instret_counter_v + $1);
                Ret STRUCT {  "$tag" ::= $3; "CsrData" ::= $0; "Exception$exception" ::= $0; "Exception$trapHandlerPC" ::= $0; "None" ::= $0; "RedirectPC" ::= $0 };
;
        Retv;;
        Retv;

    }); abstract omega. Qed. (* mkRVCsrFile *)

(* Module mkRVCsrFile type Data -> Reg#(Bit#(64)) -> Bool -> Bool -> Bool -> Module#(RVCsrFile#(xlen)) return type Reg#(Bit#(64)) *)
    Definition mkRVCsrFile := Build_RVCsrFile (Bit 64) mkRVCsrFileModule%kami (instancePrefix--"csrState") (instancePrefix--"readyInterrupt") (instancePrefix--"vmD") (instancePrefix--"vmI") (instancePrefix--"wakeFromWFI") (instancePrefix--"wr").
    End Section'mkRVCsrFile.
End module'mkRVCsrFile.

Definition mkRVCsrFile := module'mkRVCsrFile.mkRVCsrFile.

