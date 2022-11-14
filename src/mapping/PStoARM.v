Require Import NArith.
Require Import PArith.
Require Import ZArith.
Require Import Lia.
Require Import EquivDec.
Require Import RelationClasses.
Require Import Bool.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Basic.
From PromisingLib Require Import Axioms.
From PromisingLib Require Import Language.
From PromisingLib Require Import Event.
From PromisingLib Require Import Loc.

From PromisingIR Require Import Time.
From PromisingIR Require Import View.
From PromisingIR Require Import BoolMap.
From PromisingIR Require Import Promises.
From PromisingIR Require Import Cell.
From PromisingIR Require Import Memory.
From PromisingIR Require Import TView.
From PromisingIR Require Import Global.
From PromisingIR Require Import Local.
From PromisingIR Require Import Thread.
From PromisingIR Require Import Configuration.

Require Import PromisingArch.lib.Basic.
Require Import PromisingArch.lib.Order.
Require Import PromisingArch.lib.Time.
Require Import PromisingArch.lib.Lang.

Require Import PromisingArch.promising.Promising.
Require Import PromisingArch.mapping.RMWLang.
Require Import PromisingArch.mapping.RMWPromising.
Require Import PromisingArch.mapping.PSLang.
Require Import PromisingArch.mapping.PStoRMWUtils.
Require Import PromisingArch.mapping.PStoRMWDef.
Require Import PromisingArch.mapping.PStoRMWThread.
Require Import PromisingArch.mapping.PStoRMW.
Require Import PromisingArch.mapping.RMWtoLLSC.

Set Implicit Arguments.


Definition ps_to_arm_stmts (reg1 reg2: Id.t) (s: list Stmt.t): list stmtT :=
  rmw_to_llsc_stmts reg1 reg2 (ps_to_rmw_stmts s).

Definition ps_to_arm_program (prog_ps: ps_program) (prog_arm: program): Prop :=
  forall tid, exists reg1 reg2,
    option_rel
      (fun stmts_ps stmts_arm => stmts_arm = ps_to_arm_stmts reg1 reg2 stmts_ps)
      (IdentMap.find tid prog_ps) (IdMap.find tid prog_arm).

Variant sim_memory_final (mem_ps: PSMemory.t) (mem_arm: Memory.t): Prop :=
  | sim_memory_final_intro
      (MEM_SOUND: forall ts msg_arm
                         (GET_ARM: Memory.get_msg ts mem_arm = Some msg_arm),
        exists loc_ps from val_ps released na,
          (<<LOC: msg_arm.(Msg.loc) = Zpos loc_ps>>) /\
          (<<GET_PS: PSMemory.get loc_ps (ntt ts) mem_ps = Some (from, Message.message val_ps released na)>>) /\
          (<<VAL: PStoRMWThread.sim_val val_ps msg_arm.(Msg.val)>>) /\
          (<<TS: PSTime.lt from (ntt ts)>>))
      (MEM_COMPLETE: forall loc_ps from to msg_ps
                            (TO: PSTime.lt PSTime.bot to)
                            (GET_PS: PSMemory.get loc_ps to mem_ps = Some (from, msg_ps)),
        exists ts msg_arm,
          (<<TO: to = ntt ts>>) /\
          (<<GET_ARM: Memory.get_msg ts mem_arm = Some msg_arm>>) /\
          (<<LOC: msg_arm.(Msg.loc) = Zpos loc_ps>>))
.

Theorem ps_to_arm
        prog_ps
        prog_arm m
        (COMPILE: ps_to_arm_program prog_ps prog_arm)
        (EXEC: Machine.exec prog_arm m):
  exists c,
    (<<STEPS: rtc Configuration.all_step
                  (Configuration.init (IdentMap.map (fun s => existT _ lang_ps s) prog_ps)) c>>) /\
    (<<TERMINAL: Configuration.is_terminal c>>) /\
    (<<MEMORY: sim_memory_final c.(Configuration.global).(Global.memory) m.(Machine.mem)>>).
Proof.
Admitted.
