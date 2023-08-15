Require Import NArith.
Require Import PArith.
Require Import ZArith.
Require Import Lia.
Require Import EquivDec.
Require Import RelationClasses.
Require Import Bool.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingFlat Require Import Basic.
From PromisingFlat Require Import Axioms.
From PromisingFlat Require Import Language.
From PromisingFlat Require Import Event.
From PromisingFlat Require Import Loc.

From PromisingFlat Require Import Time.
From PromisingFlat Require Import View.
From PromisingFlat Require Import BoolMap.
From PromisingFlat Require Import Promises.
From PromisingFlat Require Import Cell.
From PromisingFlat Require Import Memory.
From PromisingFlat Require Import TView.
From PromisingFlat Require Import Global.
From PromisingFlat Require Import Local.
From PromisingFlat Require Import Thread.
From PromisingFlat Require Import Configuration.

Require Import PromisingArch.lib.Basic.
Require Import PromisingArch.lib.Order.
Require Import PromisingArch.lib.Time.
Require Import PromisingArch.lib.Lang.

Require Import PromisingArch.promising.Promising.
Require Import PromisingArch.promising.PtoPF.
Require Import PromisingArch.mapping.RMWLang.
Require Import PromisingArch.mapping.RMWPromising.
Require Import PromisingArch.mapping.PSLang.
Require Import PromisingArch.mapping.PStoRMWUtils.
Require Import PromisingArch.mapping.PStoRMWDef.
Require Import PromisingArch.mapping.PStoRMWThread.
Require Import PromisingArch.mapping.PStoRMW.
Require Import PromisingArch.mapping.RMWtoLLSC.

Set Implicit Arguments.


Definition ps_to_arm_program (prog_ps: ps_program) (prog_arm: program): Prop :=
  exists prog_rmw,
    (<<PS_TO_RMW: ps_to_rmw_program prog_ps prog_rmw>>) /\
    (<<RMW_TO_ARM: rmw_to_llsc_program prog_rmw prog_arm>>).

Variant sim_memory_final (mem_ps: PSMemory.t) (mem_arm: Memory.t): Prop :=
  | sim_memory_final_intro
      (MEM_SOUND: forall ts msg_arm
                         (GET_ARM: Memory.get_msg ts mem_arm = Some msg_arm),
        exists loc_ps from val_ps released na,
          (<<LOC: msg_arm.(Msg.loc) = loc_ps>>) /\
          (<<GET_PS: PSMemory.get loc_ps (ntt ts) mem_ps = Some (from, Message.message val_ps released na)>>) /\
          (<<VAL: PStoRMWThread.sim_val val_ps msg_arm.(Msg.val)>>) /\
          (<<TS: PSTime.lt from (ntt ts)>>))
      (MEM_COMPLETE: forall loc_ps from to msg_ps
                            (TO: PSTime.lt PSTime.bot to)
                            (GET_PS: PSMemory.get loc_ps to mem_ps = Some (from, msg_ps)),
        exists ts msg_arm,
          (<<TO: to = ntt ts>>) /\
          (<<GET_ARM: Memory.get_msg ts mem_arm = Some msg_arm>>) /\
          (<<LOC: msg_arm.(Msg.loc) = loc_ps>>))
.

Lemma ps_to_rmw_sim_sim_memory_final
      after_sc c m m_final
      (PS_NONEMPTY: exists tid lang st_ps lc_ps,
          IdentMap.find tid c.(PSConfiguration.threads) = Some (existT _ lang st_ps, lc_ps))
      (GPROMISES: c.(PSConfiguration.global).(Global.promises) = BoolMap.bot)
      (SIM: PStoRMW.sim (length m_final.(RMWMachine.mem)) after_sc c m m_final):
  sim_memory_final c.(PSConfiguration.global).(Global.memory) m_final.(RMWMachine.mem).
Proof.
  des. inv SIM.
  specialize (SIM_THREADS tid).
  rewrite PS_NONEMPTY in *.
  inv SIM_THREADS. inv REL.
  inv SIM_THREAD. inv SIM_THREAD0. ss.
  destruct c, global, m. ss. subst.
  exploit (RMWExecUnit.rtc_state_step_memory (A:=unit)); try exact STEPS1. s. i.
  exploit (RMWExecUnit.rtc_state_step_memory (A:=unit));
    try eapply rtc_mon; try exact STEPS2;
    try apply RMWExecUnit.dmbsy_over_state_step. s. i.
  rewrite x1, x0 in *. clear - SIM_MEM.
  inv SIM_MEM. econs; i; eauto.
  exploit MEM_SOUND; eauto. i. des.
  unguardH x0.
  des; subst; [|esplits; eauto].
  exploit PROMISED; [|i; des; ss].
  unfold Memory.get_msg in GET_ARM. destruct ts; ss.
  apply nth_error_some in GET_ARM. unfold le. nia.
Qed.

Lemma step_non_empty
      e tid c1 c2
      (PS_NONEMPTY: exists tid lang st_ps lc_ps,
          IdentMap.find tid c1.(PSConfiguration.threads) = Some (existT _ lang st_ps, lc_ps))
      (STEP: Configuration.step e tid c1 c2):
  exists tid lang st_ps lc_ps,
    IdentMap.find tid c2.(PSConfiguration.threads) = Some (existT _ lang st_ps, lc_ps).
Proof.
  inv STEP. ss. exists tid.
  rewrite IdentMap.gsspec. condtac; eauto.
Qed.

Lemma rtc_tau_step_non_empty
      c1 c2
      (PS_NONEMPTY: exists tid lang st_ps lc_ps,
          IdentMap.find tid c1.(PSConfiguration.threads) = Some (existT _ lang st_ps, lc_ps))
      (STEPS: rtc Configuration.tau_step c1 c2):
  exists tid lang st_ps lc_ps,
    IdentMap.find tid c2.(PSConfiguration.threads) = Some (existT _ lang st_ps, lc_ps).
Proof.
  revert PS_NONEMPTY.
  induction STEPS; i; eauto.
  apply IHSTEPS. inv H.
  eapply step_non_empty; eauto.
Qed.

Theorem ps_to_arm
        prog_ps
        prog_arm m
        (ARM: arch = armv8)
        (PS_NONEMPTY: exists tid stmts, IdentMap.find tid prog_ps = Some stmts)
        (COMPILE: ps_to_arm_program prog_ps prog_arm)
        (EXEC: Machine.exec prog_arm m)
        (TERMINAL: Machine.is_terminal m):
  exists c,
    (<<STEPS: rtc Configuration.tau_step
                  (Configuration.init (IdentMap.map (fun s => existT _ lang_ps s) prog_ps)) c>>) /\
    ((<<TERMINAL: Configuration.is_terminal c>>) /\
     (<<MEMORY: sim_memory_final c.(Configuration.global).(Global.memory) m.(Machine.mem)>>) \/
     exists tid c',
       (<<STEP: PSConfiguration.step MachineEvent.failure tid c c'>>)).
Proof.
  unfold ps_to_arm_program in *. des.
  apply promising_to_promising_pf in EXEC.
  exploit RMWtoLLSC.rmw_to_llsc; eauto. i. des.
  exploit PStoRMW.ps_to_rmw; eauto. i. des.
  - esplits; try exact STEPS. left. split; ss.
    rewrite <- MEMORY.
    eapply ps_to_rmw_sim_sim_memory_final; eauto.
    eapply rtc_tau_step_non_empty; try exact STEPS. ss.
    exists tid. unfold Threads.init.
    rewrite IdentMap.Facts.map_o.
    rewrite IdentMap.Facts.map_o.
    rewrite PS_NONEMPTY. ss.
    exists lang_ps. esplits; eauto.
  - esplits; try exact STEPS. right. eauto.
Qed.
