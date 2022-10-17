Require Import NArith.
Require Import PArith.
Require Import ZArith.
Require Import Lia.
Require Import EquivDec.
Require Import RelationClasses.

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

Set Implicit Arguments.

Module PSLoc := PromisingLib.Loc.Loc.
Module PSTime := PromisingIR.Time.Time.
Module PSView := PromisingIR.View.View.
Module PSPromises := PromisingIR.Promises.Promises.
Module PSTView := PromisingIR.TView.TView.
Module PSLocal := PromisingIR.Local.Local.
Module PSCell := PromisingIR.Cell.Cell.
Module PSMemory := PromisingIR.Memory.Memory.
Module PSGlobal := PromisingIR.Global.Global.
Module PSThread := PromisingIR.Thread.Thread.
Module PSConfiguration := PromisingIR.Configuration.Configuration.


(* timestamp conversion between PS and ARM *)

(* Global Program Instance nat_order: orderC Nat.max 0. *)
(* Next Obligation. unfold join. lia. Qed. *)
(* Next Obligation. unfold join. lia. Qed. *)
(* Next Obligation. eauto using Max.max_assoc. Qed. *)
(* Next Obligation. eauto using Max.max_comm. Qed. *)
(* Next Obligation. unfold join. lia. Qed. *)
(* Next Obligation. unfold bot. lia. Qed. *)

Fixpoint ntt (n: Time.t): PSTime.t :=
  match n with
  | O => PSTime.bot
  | S n => PSTime.incr (ntt n)
  end.

Lemma le_ntt
  m n
  (LE: m <= n):
  PSTime.le (ntt m) (ntt n).
Proof.
  induction LE; try refl.
  etrans; eauto. ss. econs.
  apply PSTime.incr_spec.
Qed.

Lemma lt_ntt
  m n
  (LT: m < n):
  PSTime.lt (ntt m) (ntt n).
Proof.
  eapply TimeFacts.lt_le_lt; try eapply le_ntt; eauto.
  apply PSTime.incr_spec.
Qed.

Lemma ntt_le
  m n
  (LE: PSTime.le (ntt m) (ntt n)):
  m <= n.
Proof.
  destruct (Nat.le_gt_cases m n); ss.
  apply lt_ntt in H. timetac.
Qed.

Lemma ntt_lt
  m n
  (LT: PSTime.lt (ntt m) (ntt n)):
  m < n.
Proof.
  destruct (Nat.le_gt_cases n m); ss.
  apply le_ntt in H. timetac.
Qed.

Lemma ntt_inj
  m n
  (EQ: ntt m = ntt n):
  m = n.
Proof.
  apply le_antisym.
  - apply ntt_le. rewrite EQ. refl.
  - apply ntt_le. rewrite EQ. refl.
Qed.

Lemma ntt_join m n:
  ntt (join m n) = PSTime.join (ntt m) (ntt n).
Proof.
  apply TimeFacts.antisym.
  - destruct (Nat.le_ge_cases m n).
    + etrans; [|apply PSTime.join_r].
      apply le_ntt. rewrite max_r; ss.
    + etrans; [|apply PSTime.join_l].
      apply le_ntt. rewrite max_l; ss.
  - apply PSTime.join_spec; try apply le_ntt.
    + apply join_l.
    + apply join_r.
Qed.


(* SC fence with sc view le n *)

Section DMBSY.
  Context `{A: Type, _: orderC A eq}.

  Lemma dmbsy_le_cases
        n tid eu1 eu4
        (STEPS: rtc (RMWExecUnit.state_step_dmbsy_over n tid) eu1 eu4):
    (<<STEPS_DMBSY: rtc (RMWExecUnit.state_step_dmbsy_over (S n) tid) eu1 eu4>>) \/
    exists eu2 eu3,
      (<<STEPS_DMBSY1: rtc (RMWExecUnit.state_step_dmbsy_exact n tid) eu1 eu2>>) /\
      (<<STEP_DMBSY: RMWExecUnit.state_step_dmbsy n tid eu2 eu3>>) /\
      (<<STEPS_DMBSY2: rtc (RMWExecUnit.state_step_dmbsy_over (S n) tid) eu3 eu4>>).
  Proof.
    induction STEPS; eauto. des.
    - exploit RMWExecUnit.state_step_dmbsy_over_S; eauto. i. des.
      + right. esplits; try exact x1; eauto.
      + left. econs 2; eauto.
    - right. esplits; try exact STEP_DMBSY; eauto. econs 2; eauto.
      inv H1. econs; eauto. i.
      exploit DMBSY; eauto. i.
      inv x1; ss. exfalso.
      exploit RMWExecUnit.state_step0_incr; try exact STEP. i.
      exploit RMWExecUnit.rtc_state_step_incr;
        try eapply rtc_mon; try exact STEPS_DMBSY1.
      { i. inv H4. econs. eauto. }
      i. rewrite x2 in x1. inv x1. inv LC.
      inv STEP_DMBSY.
      exploit (join_le (A:=Time.t)); [apply VRO|apply VWO|].
      unfold join in H2, H3.
      rewrite <- H2. i.
      rewrite H3 in x1. nia.
  Qed.
End DMBSY.
