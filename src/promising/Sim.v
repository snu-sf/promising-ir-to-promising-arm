Require Import FunctionalExtensionality.
Require Import Relations.
Require Import EquivDec.
Require Import Equality.
Require Import List.
Require Import Bool.
Require Import Lia.
Require Import NArith.
Require Import PArith.
Require Import ZArith.
Require Import FMapPositive.
Require Import FSetPositive.
Require Import EquivDec.

From sflib Require Import sflib.
From Paco Require Import paco.

Require Import PromisingArch.lib.Basic.
Require Import PromisingArch.lib.Order.
Require Import PromisingArch.lib.Time.
Require Import PromisingArch.lib.Lang.

Require Import PromisingArch.promising.Promising.

Set Implicit Arguments.


Section SIM.
  Variable sim_machine: forall (m_src m_tgt: Machine.t), Prop.

  Definition _sim (sim: Machine.t -> Machine.t -> Prop) (m1_src m1_tgt: Machine.t): Prop :=
    forall (WF1_SRC: Machine.wf m1_src)
      (WF1_TGT: Machine.wf m1_tgt)
      (MACHINE1: sim_machine m1_src m1_tgt),
      (<<TERMINAL:
        forall (TERMINAL_TGT: Machine.is_terminal m1_tgt),
        exists m2_src,
          (<<STEPS_SRC: rtc (Machine.step ExecUnit.step) m1_src m2_src>>) /\
          (<<TERMINAL_SRC: Machine.is_terminal m2_src>>) /\
          (<<MACHINE2: sim_machine m2_src m1_tgt>>)>>) /\
      (<<STEP:
        forall m2_tgt
          (STEP_TGT: Machine.step ExecUnit.step m1_tgt m2_tgt),
        exists m2_src,
          (<<STEPS_SRC: rtc (Machine.step ExecUnit.step) m1_src m2_src>>) /\
          (<<MACHINE2: sim_machine m2_src m2_tgt>>) /\
          (<<SIM: sim m2_src m2_tgt>>)>>)
  .
  #[local] Hint Unfold _sim: paco.

  Lemma sim_monotone: monotone2 _sim.
  Proof.
    ii. exploit IN; eauto. i. des.
    esplits; eauto. i.
    exploit STEP; eauto. i. des.
    esplits; eauto.
  Qed.
  #[local] Hint Resolve sim_monotone: paco.

  Definition sim := paco2 _sim bot2.
End SIM.


Section SIM_EU.
  Variable tid: Id.t.

  Definition SIM_EU: Type := ExecUnit.t (A:=unit) -> ExecUnit.t (A:=unit) -> Prop.

  Definition _sim_eu (sim_eu: SIM_EU) (eu1_src eu1_tgt: ExecUnit.t (A:=unit)): Prop :=
      (<<TERMINAL: 
        forall (TERMINAL_TGT: ExecUnit.is_terminal eu1_tgt),
        exists eu2_src,
          (<<STEPS_SRC: rtc (ExecUnit.state_step tid) eu1_src eu2_src>>) /\
          (<<TERMINAL_SRC: ExecUnit.is_terminal eu2_src>>) /\
          (<<MEMORY2: ExecUnit.mem eu2_src = ExecUnit.mem eu1_tgt>>)>>) /\
      (<<STEP:
        forall eu2_tgt
          (STEP_TGT: ExecUnit.state_step tid eu1_tgt eu2_tgt),
        exists eu2_src,
          (<<STEP_SRC: rtc (ExecUnit.state_step tid) eu1_src eu2_src>>) /\
          (<<SIM: sim_eu eu2_src eu2_tgt>>)>>)
  .
  #[local] Hint Unfold _sim_eu: paco.

  Lemma sim_eu_monotone: monotone2 _sim_eu.
  Proof.
    ii. red in IN. des.
    red. esplits; eauto. i.
    exploit STEP; eauto. i. des.
    esplits; eauto.
  Qed.
  #[local] Hint Resolve sim_eu_monotone: paco.

  Definition sim_eu := paco2 _sim_eu bot2.
End SIM_EU.
Arguments sim_eu [_] _ _.
