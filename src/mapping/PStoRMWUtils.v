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
Module PSThreads := PromisingIR.Configuration.Threads.
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

Section RMWStep.
  Context `{A: Type, _: orderC A eq}.

  Lemma dmbsy_le_cases
        n sc tid eu1 eu4
        (STEPS: rtc (RMWExecUnit.state_step_dmbsy_over n sc tid) eu1 eu4):
    (<<STEPS_DMBSY: rtc (RMWExecUnit.state_step_dmbsy_over n (S sc) tid) eu1 eu4>>) \/
    exists eu2 eu3,
      (<<STEPS_DMBSY1: rtc (RMWExecUnit.state_step_dmbsy_exact n sc tid) eu1 eu2>>) /\
      (<<STEP_DMBSY: RMWExecUnit.state_step_dmbsy n sc tid eu2 eu3>>) /\
      (<<STEPS_DMBSY2: rtc (RMWExecUnit.state_step_dmbsy_over n (S sc) tid) eu3 eu4>>).
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

  Lemma step_sc
        n sc tid eu1 eu2
        (STEP: RMWExecUnit.state_step_dmbsy_over n sc tid eu1 eu2)
        (SC: le (join eu2.(RMWExecUnit.local).(Local.vro) eu2.(RMWExecUnit.local).(Local.vwo)).(View.ts) sc):
    RMWExecUnit.state_step_dmbsy_exact n sc tid eu1 eu2.
  Proof.
    exploit RMWExecUnit.state_step_incr;
      try eapply RMWExecUnit.dmbsy_over_state_step; eauto. i.
    inv STEP. econs; eauto. i.
    apply DMBSY in H1.
    eapply le_antisym; ss.
    etrans; try apply SC.
    eapply join_le; try apply Time.order; apply x0.
  Qed.

  Lemma steps_dmbsy
        n sc tid eu1 eu2 eu3
        (STEPS: rtc (RMWExecUnit.state_step_dmbsy_over n sc tid) eu1 eu2)
        (STEP: RMWExecUnit.state_step_dmbsy n sc tid eu2 eu3):
    rtc (RMWExecUnit.state_step_dmbsy_exact n sc tid) eu1 eu2.
  Proof.
    assert (SC: le (join eu2.(RMWExecUnit.local).(Local.vro) eu2.(RMWExecUnit.local).(Local.vwo)).(View.ts) sc).
    { inv STEP. refl. }
    clear eu3 STEP. revert SC.
    induction STEPS; try refl. i.
    exploit IHSTEPS; ss. i.
    econs; try exact x1.
    eapply step_sc; ss.
    etrans; try exact SC.
    exploit RMWExecUnit.rtc_state_step_incr;
      try eapply rtc_mon; try eapply RMWExecUnit.dmbsy_over_state_step; try exact STEPS. i.
    eapply join_le; try apply Time.order; apply x2.
  Qed.

  Lemma dmbsy_vro_after
        n sc tid eu1 eu2
        (STEP: RMWExecUnit.state_step_dmbsy n sc tid eu1 eu2):
    le eu2.(RMWExecUnit.local).(Local.vro).(View.ts) sc.
  Proof.
    inv STEP. inv STEP0. inv LOCAL; ss.
    destruct eu2. inv STEP. ss. subst. ss.
    apply join_l.
  Qed.

  Lemma dmbsy_vwo_after
        n sc tid eu1 eu2
        (STEP: RMWExecUnit.state_step_dmbsy n sc tid eu1 eu2):
    le eu2.(RMWExecUnit.local).(Local.vwo).(View.ts) sc.
  Proof.
    inv STEP. inv STEP0. inv LOCAL; ss.
    destruct eu2. inv STEP. ss. subst. ss.
    apply join_r.
  Qed.

  Variant fulfill_step tid ord ts (eu1 eu2: RMWExecUnit.t): Prop :=
    | fulfill_step_fulfill
        vloc vval res view_pre
        (STATE: RMWState.step (RMWEvent.write ord vloc vval) eu1.(RMWExecUnit.state) eu2.(RMWExecUnit.state))
        (FULFILL: Local.fulfill false ord vloc vval res ts tid view_pre
                                eu1.(RMWExecUnit.local) eu1.(RMWExecUnit.mem) eu2.(RMWExecUnit.local))
        (MEM: eu2.(RMWExecUnit.mem) = eu1.(RMWExecUnit.mem))
    | fulfill_step_fadd
        ordr vloc vold vnew ts_old res lc1' view_pre lc1''
        (STATE: RMWState.step (RMWEvent.fadd ordr ord vloc vold vnew)
                              eu1.(RMWExecUnit.state) eu2.(RMWExecUnit.state))
        (STEP_READ: Local.read true ordr vloc vold ts_old
                               eu1.(RMWExecUnit.local) eu1.(RMWExecUnit.mem) lc1')
        (STEP_FULFILL: Local.fulfill true ord vloc vnew res ts tid view_pre
                                     lc1' eu1.(RMWExecUnit.mem) lc1'')
        (STEP_CONTROL: Local.control vold.(ValA.annot) lc1'' eu2.(RMWExecUnit.local))
        (MEM: eu2.(RMWExecUnit.mem) = eu1.(RMWExecUnit.mem))
  .

  Lemma steps_fulfill_cases
        n sc tid eu1 eu2
        (STEPS: rtc (RMWExecUnit.state_step_dmbsy_over (Some n) sc tid) eu1 eu2)
        (PROMISES: eu2.(RMWExecUnit.local).(Local.promises) = bot):
    (<<NON_PROMISED: Promises.lookup (S n) eu1.(RMWExecUnit.local).(Local.promises) = false>>) /\
    (<<STEPS: rtc (RMWExecUnit.state_step_dmbsy_over (Some (S n)) sc tid) eu1 eu2>>) \/
    (exists eu1' eu1'',
        (<<PROMISED: Promises.lookup (S n) eu1.(RMWExecUnit.local).(Local.promises) = true>>) /\
        (<<STEPS1: rtc (RMWExecUnit.state_step_dmbsy_over (Some (S n)) sc tid) eu1 eu1'>>) /\
        (<<FULFILL: __guard__ (exists ord, fulfill_step tid ord (S n) eu1' eu1'')>>) /\
        (<<STEPS2: rtc (RMWExecUnit.state_step_dmbsy_over (Some (S n)) sc tid) eu1'' eu2>>)).
  Proof.
    destruct (Promises.lookup (S n) eu1.(RMWExecUnit.local).(Local.promises)) eqn:PROMISED1; cycle 1.
    { left. splits; ss.
      eapply RMWExecUnit.rtc_state_step_dmbsy_over_pf_S1; eauto.
    }
    right.
    induction STEPS.
    { rewrite PROMISES in *. ss. }
    destruct (Promises.lookup (S n) (Local.promises (RMWExecUnit.local y))) eqn:Y.
    { exploit IHSTEPS; eauto. i. des.
      esplits; try exact FULFILL; eauto. econs 2; eauto.
      eapply RMWExecUnit.state_step_dmbsy_over_pf_S2; eauto.
    }
    exploit (RMWExecUnit.rtc_state_step_dmbsy_over_pf_S1 (A:=A)); try exact STEPS; ss. i.
    esplits; try exact x1; try refl; ss.
    clear - H1 PROMISED1 Y.
    inv H1. inv STEP. clear DMBSY.
    destruct x as [st1 lc1 mem1], y as [st2 lc2 mem2]. ss. subst.
    unguard. inv LOCAL; try congr.
    - inv STEP. ss. congr.
    - cut (ts = S n).
      { i. subst. esplits. econs 1; eauto. }
      inv STEP. ss.
      revert Y. erewrite Promises.unset_o. condtac; ss. congr.
    - cut (ts_new = S n).
      { i. subst. esplits. econs 2; eauto. }
      inv STEP_CONTROL. ss.
      inv STEP_FULFILL. ss.
      inv STEP_READ. ss.
      revert Y. erewrite Promises.unset_o. condtac; ss. congr.
    - inv STEP. ss. congr.
    - inv LC. ss. congr.
  Qed.
End RMWStep.


(* TODO: move to PS *)

Lemma reorder_read_cancel
      lc1 gl1 loc1 to1 val released ord lc2
      loc2 from2 to2 lc3 gl3
      (STEP1: PSLocal.read_step lc1 gl1 loc1 to1 val released ord lc2)
      (STEP2: PSLocal.cancel_step lc2 gl1 loc2 from2 to2 lc3 gl3):
  exists lc2',
    (<<STEP1: PSLocal.cancel_step lc1 gl1 loc2 from2 to2 lc2' gl3>>) /\
    (<<STEP2: PSLocal.read_step lc2' gl3 loc1 to1 val released ord lc3>>).
Proof.
  destruct lc1 as [tview1 prm1 rsv1].
  inv STEP1. inv STEP2. inv CANCEL. ss.
  exploit PSMemory.remove_get1; try exact GET; eauto. i. des; ss.
  esplits; econs; eauto.
Qed.

Lemma rtc_thread_tau_step_rtc_tau_step
      c1 tid lang st1 lc1 th2
      (FIND: IdentMap.find tid c1.(Configuration.threads) = Some (existT _ lang st1, lc1))
      (STEPS: rtc (@Thread.tau_step _) (Thread.mk _ st1 lc1 c1.(Configuration.global)) th2)
      (CONSISTENT: Thread.consistent th2):
  (<<STEPS: rtc Configuration.tau_step c1
                (Configuration.mk
                   (IdentMap.add tid (existT _ _ (Thread.state th2), (Thread.local th2)) (Configuration.threads c1))
                   (Thread.global th2))>>).
Proof.
  destruct c1, th2. ss.
  exploit rtc_tail; eauto. i. des.
  - inv x1. econs 2; try refl.
    econs. rewrite <- EVENT.
    econs; eauto.
  - inv x0. rewrite IdentMap.gsident; ss. splits. refl.
Qed.
