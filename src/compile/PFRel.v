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

Require Import PromisingArch.compile.RMWLang.
Require Import PromisingArch.compile.RMWPromising.

Set Implicit Arguments.
Set Nested Proofs Allowed.


Definition promises_eq_until (n: Time.t) (p1 p2: Promises.t): Prop :=
  forall ts (LE: ts <= n), Promises.lookup ts p1 = Promises.lookup ts p2.

#[export] Program Instance promises_eq_until_Equivalence (n: Time.t):
  Equivalence (promises_eq_until n).
Next Obligation.
  ii. ss.
Qed.
Next Obligation.
  ii. rewrite H; ss.
Qed.
Next Obligation.
  ii. rewrite H, H0; ss.
Qed.

Lemma promises_eq_until_decr
      n m p1 p2
      (LE: m <= n)
      (EQ: promises_eq_until n p1 p2):
  promises_eq_until m p1 p2.
Proof.
  ii. rewrite EQ; ss. nia.
Qed.

Definition is_release {A} `{_: orderC A} (e: RMWEvent.t (A:=A)): bool :=
  match e with
  | RMWEvent.write ordw _ _ _
  | RMWEvent.fadd _ ordw _ _ _ => OrdW.ge OrdW.release_pc ordw
  | RMWEvent.barrier (Barrier.dmb rr rw wr ww) => andb rw ww
  | _ => false
  end.


Module PFRelLocal.
  Section PFRelLocal.
    Import Local.
    Context `{A: Type, _: orderC A eq}.

    Variant step (event:RMWEvent.t (A:=View.t (A:=A))) (tid:Id.t)
              (lc1:t) (mem1:Memory.t) (lc2:t) (mem2:Memory.t): Prop :=
    | step_internal
        (EVENT: event = RMWEvent.internal)
        (LC: lc2 = lc1)
        (MEM: mem2 = mem1)
    | step_read
        ord vloc res ts
        (EVENT: event = RMWEvent.read ord vloc res)
        (STEP: read false ord vloc res ts lc1 mem1 lc2)
        (MEM: mem2 = mem1)
    | step_fulfill
        ord vloc vval res ts view_pre
        (EVENT: event = RMWEvent.write ord vloc vval res)
        (ORD: OrdW.ge ord OrdW.release_pc)
        (STEP: fulfill false ord vloc vval res ts tid view_pre lc1 mem1 lc2)
        (MEM: mem2 = mem1)
    | step_write
        lc1'
        ord vloc vval res ts view_pre
        (EVENT: event = RMWEvent.write ord vloc vval res)
        (STEP_PROMISE: promise vloc.(ValA.val) vval.(ValA.val) ts tid lc1 mem1 lc1' mem2)
        (STEP_FULFILL: fulfill false ord vloc vval res ts tid view_pre lc1' mem2 lc2)
    | step_write_failure
        ord vloc vval res
        (EVENT: event = RMWEvent.write ord vloc vval res)
        (STEP: write_failure false res lc1 lc2)
        (MEM: mem2 = mem1)
    | step_fadd_fulfill
        ordr ordw vloc vold vnew ts_old ts_new res lc1' view_pre
        (EVENT: event = RMWEvent.fadd ordr ordw vloc vold vnew)
        (ORD: OrdW.ge ordw OrdW.release_pc)
        (STEP_READ: read true ordr vloc vold ts_old lc1 mem1 lc1')
        (STEP_FULFILL: fulfill true ordw vloc vnew res ts_new tid view_pre lc1' mem1 lc2)
        (MEM: mem2 = mem1)
    | step_fadd_write
        ordr ordw vloc vold vnew ts_old ts_new res lc1' lc1'' view_pre
        (EVENT: event = RMWEvent.fadd ordr ordw vloc vold vnew)
        (STEP_READ: read true ordr vloc vold ts_old lc1 mem1 lc1')
        (STEP_PROMISE: promise vloc.(ValA.val) vnew.(ValA.val) ts_new tid lc1' mem1 lc1'' mem2)
        (STEP_FULFILL: fulfill true ordw vloc vnew res ts_new tid view_pre lc1'' mem2 lc2)
    | step_isb
        (EVENT: event = RMWEvent.barrier Barrier.isb)
        (STEP: isb lc1 lc2)
        (MEM: mem2 = mem1)
    | step_dmb
        rr rw wr ww
        (EVENT: event = RMWEvent.barrier (Barrier.dmb rr rw wr ww))
        (PROMISES: andb rw ww = true -> lc1.(Local.promises) = bot)
        (STEP: dmb rr rw wr ww lc1 lc2)
        (MEM: mem2 = mem1)
    | step_control
        ctrl
        (EVENT: event = RMWEvent.control ctrl)
        (LC: control ctrl lc1 lc2)
        (MEM: mem2 = mem1)
    .
    #[local]
     Hint Constructors step: core.

    Lemma promise_memory_incr
          loc val ts tid lc1 mem1 lc2 mem2
          (PROMISE: promise (A:=A) loc val ts tid lc1 mem1 lc2 mem2):
      mem2 = mem1 ++ [Msg.mk loc val tid].
    Proof.
      inv PROMISE. inv MEM2. ss.
    Qed.

    Lemma step_incr
          e tid lc1 mem1 lc2 mem2
          (LC: step e tid lc1 mem1 lc2 mem2):
      le lc1 lc2 /\ exists mem', mem2 = mem1 ++ mem'.
    Proof.
      inv LC; split; try refl;
        eauto using app_nil_r, promise_memory_incr.
      - eauto using read_incr.
      - eauto using fulfill_incr.
      - etrans; eauto using promise_incr, fulfill_incr.
      - eauto using write_failure_incr.
      - etrans; eauto using read_incr, fulfill_incr.
      - etrans; eauto using read_incr.
        etrans; eauto using promise_incr, fulfill_incr.
      - eauto using isb_incr.
      - eauto using dmb_incr.
      - eauto using control_incr.
    Qed.

    Lemma step_promises_le
          e tid lc1 mem1 lc2 mem2
          (STEP: step e tid lc1 mem1 lc2 mem2):
      Promises.le (promises lc2) (promises lc1).
    Proof.
      inv STEP; ss; try by (inv STEP0; ss).
      - inv STEP0. ss. apply Promises.unset_le.
      - inv STEP_PROMISE. inv STEP_FULFILL. ss.
        apply Promises.unset_set_le.
      - inv STEP_READ. inv STEP_FULFILL. ss.
        apply Promises.unset_le.
      - inv STEP_READ. inv STEP_PROMISE. ss. inv STEP_FULFILL. ss.
        apply Promises.unset_set_le.
      - inv LC. ss.
    Qed.

    Variant more_promises (n: Time.t) (lc1 lc2: t (A:=A)): Prop :=
    | more_promises_intro
        (COH: coh lc1 = coh lc2)
        (VRN: vrn lc1 = vrn lc2)
        (VWN: vwn lc1 = vwn lc2)
        (VRO: vro lc1 = vro lc2)
        (VWO: vwo lc1 = vwo lc2)
        (VCAP: vcap lc1 = vcap lc2)
        (VREL: vrel lc1 = vrel lc2)
        (FWDBANK: fwdbank lc1 = fwdbank lc2)
        (EXBANK: exbank lc1 = exbank lc2)
        (PROMISES_LE: Promises.le (promises lc1) (promises lc2))
        (PROMISES_EQ: promises_eq_until n (promises lc1) (promises lc2))
    .

    Global Program Instance more_promises_PreOrder n: PreOrder (more_promises n).
    Next Obligation.
      ii. econs; ss.
    Qed.
    Next Obligation.
      ii. inv H1. inv H2.
      econs; try congr; etrans; eauto.
    Qed.

    Lemma more_promises_decr
          m n lc1 lc2
          (MORE: more_promises n lc1 lc2)
          (MN: m <= n):
      more_promises m lc1 lc2.
    Proof.
      inv MORE. econs; eauto using promises_eq_until_decr.
    Qed.

    Lemma promise_promises_sound
          loc val ts tid lc1 mem1 lc2 mem2
          (STEP: promise (A:=A) loc val ts tid lc1 mem1 lc2 mem2)
          (SOUND: Promises.sound tid (promises lc1) mem1):
      Promises.sound tid (promises lc2) mem2.
    Proof.
      inv STEP. inv MEM2. ss.
      ii. revert LOOKUP. erewrite Promises.set_o. condtac; i.
      - inversion e. subst.
        unfold Memory.get_msg. ss.
        rewrite nth_error_app2; try refl.
        rewrite minus_diag. ss. eauto.
      - exploit SOUND; eauto. i. des.
        esplits; eauto.
        eapply Memory.get_msg_mon; eauto.
    Qed.

    Lemma step_promises_sound
          e tid lc1 mem1 lc2 mem2
          (STEP: step e tid lc1 mem1 lc2 mem2)
          (SOUND: Promises.sound tid (promises lc1) mem1):
      Promises.sound tid (promises lc2) mem2.
    Proof.
      inv STEP; eauto; try by (inv STEP0; ss; eauto).
      - inv STEP0; ss.
        eapply Promises.le_sound; eauto.
        eapply Promises.unset_le.
      - inv STEP_FULFILL; ss.
        eapply Promises.le_sound; try eapply Promises.unset_le.
        eapply promise_promises_sound; eauto.
      - inv STEP_FULFILL; ss.
        eapply Promises.le_sound; try eapply Promises.unset_le.
        inv STEP_READ. ss.
      - inv STEP_FULFILL; ss.
        eapply Promises.le_sound; try eapply Promises.unset_le.
        eapply promise_promises_sound; try exact STEP_PROMISE.
        inv STEP_READ. ss.
      - inv LC. ss.
    Qed.
  End PFRelLocal.
End PFRelLocal.


Module PFRelExecUnit.
  Section PFRelExecUnit.
    Import RMWExecUnit.
    Context `{A: Type, _: orderC A eq}.

    Variant state_step0 (tid:Id.t) (e1 e2:RMWEvent.t (A:=View.t (A:=A))) (eu1 eu2:t): Prop :=
    | state_step0_intro
        (STATE: RMWState.step e1 eu1.(state) eu2.(state))
        (LOCAL: PFRelLocal.step e2 tid eu1.(local) eu1.(mem) eu2.(local) eu2.(mem))
    .
    #[local]
     Hint Constructors state_step0: core.

    Variant state_step (tid:Id.t) (eu1 eu2:t): Prop :=
    | state_step_intro
        e
        (STEP: state_step0 tid e e eu1 eu2)
    .
    #[local]
     Hint Constructors state_step: core.

    Variant step (tid:Id.t) (eu1 eu2:t): Prop :=
    | step_state (STEP: state_step tid eu1 eu2)
    | step_promise (STEP: promise_step tid eu1 eu2)
    .
    #[local]
     Hint Constructors step: core.

    Variant non_rel_step (tid:Id.t) (eu1 eu2:t): Prop :=
    | non_rel_step_intro
        e
        (STEP: RMWExecUnit.state_step0 tid e e eu1 eu2)
        (REL: ~ is_release e)
    .
    #[local]
     Hint Constructors non_rel_step: core.

    Variant rel_step (tid:Id.t) (eu1 eu2:t): Prop :=
    | rel_step_intro
        e
        (STEP: RMWExecUnit.state_step0 tid e e eu1 eu2)
        (REL: is_release e)
    .
    #[local]
     Hint Constructors rel_step: core.

    Variant fulfilled (ts: Time.t) (eu1 eu2: t): Prop :=
    | fulfilled_intro
        (BEFORE: Promises.lookup ts eu1.(local).(Local.promises))
        (AFTER: ~ Promises.lookup ts eu2.(local).(Local.promises))
    .
    #[local]
     Hint Constructors fulfilled: core.

    Variant fulfill_step (tid:Id.t) (ts: Time.t) (e:RMWEvent.t (A:=View.t (A:=A))) (eu1 eu2:t): Prop :=
    | fulfill_step_intro
        (STEP: RMWExecUnit.state_step0 tid e e eu1 eu2)
        (FULFILL: fulfilled ts eu1 eu2)
    .
    #[local]
     Hint Constructors fulfill_step: core.

    Lemma state_step0_wf tid e1 e2 eu1 eu2
          (STEP: state_step0 tid e1 e2 eu1 eu2)
          (EVENT: eqts_rmw_event e1 e2)
          (WF: wf tid eu1):
      wf tid eu2.
    Proof.
      destruct eu1 as [state1 local1 mem1].
      destruct eu2 as [state2 local2 mem2].
      inv WF. inv STEP. ss. subst.

      assert (FWDVIEW: forall loc ts ord,
                 Memory.latest loc ts (View.ts (Local.coh local1 loc)) mem1 ->
                 ts <= length mem1 ->
                 View.ts (FwdItem.read_view (Local.fwdbank local1 loc) ts ord) <= length mem1).
      { i. rewrite Local.fwd_read_view_le; eauto. }
      generalize LOCAL. intro WF_LOCAL1.
      inv STATE0; inv LOCAL0; inv EVENT; inv LOCAL; ss.
      - econs; ss.
        eauto using ExecUnit.rmap_add_wf, ExecUnit.expr_wf.
      - inv RES. inv VIEW. inv VLOC. inv VIEW.
        econs; ss.
        + inv STEP. ss. subst.
          exploit FWDVIEW; eauto.
          { eapply ExecUnit.read_wf. eauto. }
          i. apply ExecUnit.rmap_add_wf; viewtac.
          rewrite TS, <- TS0. viewtac.
          eauto using ExecUnit.expr_wf.
        + eapply ExecUnit.read_step_wf; eauto.
          rewrite <- TS0. eapply ExecUnit.expr_wf; eauto.
      - inv RES. inv VIEW. inv VVAL. inv VIEW. inv VLOC. inv VIEW.
        econs; ss.
        + inv STEP. inv WRITABLE.
          apply ExecUnit.rmap_add_wf; viewtac.
          rewrite TS. apply bot_spec.
        + eapply ExecUnit.fulfill_step_wf; eauto.
          rewrite <- TS1. eapply ExecUnit.expr_wf; eauto.
      - inv RES. inv VIEW. inv VVAL. inv VIEW. inv VLOC. inv VIEW.
        econs; ss.
        + inv STEP_FULFILL. inv WRITABLE.
          apply ExecUnit.rmap_add_wf; viewtac.
          * inv STEP_PROMISE. inv MEM2.
            eapply ExecUnit.rmap_append_wf; eauto.
          * rewrite TS. apply bot_spec.
        + eapply ExecUnit.fulfill_step_wf; try exact STEP_FULFILL; cycle 1.
          { inv STEP_PROMISE. inv MEM2.
            rewrite List.app_length; s.
            rewrite <- TS1. erewrite ExecUnit.expr_wf; eauto. nia.
          }
          eapply ExecUnit.promise_wf; try exact PROMISE; eauto.
      - inv STEP. econs; ss.
      - inv VLOC. inv VIEW. inv VOLD. inv VIEW. inv VNEW. inv VIEW.
        econs; ss.
        + inv STEP_READ. ss. subst.
          exploit FWDVIEW; eauto.
          { eapply ExecUnit.read_wf. eauto. }
          i. apply ExecUnit.rmap_add_wf; viewtac.
          rewrite TS0, <- TS. viewtac.
          eauto using ExecUnit.expr_wf.
        + eapply ExecUnit.fulfill_step_wf; try exact STEP_FULFILL; cycle 1.
          { rewrite <- TS. eapply ExecUnit.expr_wf; eauto. }
          eapply ExecUnit.read_step_wf; eauto.
          rewrite <- TS. eapply ExecUnit.expr_wf; eauto.
      - inv VLOC. inv VIEW. inv VOLD. inv VIEW. inv VNEW. inv VIEW.
        econs; ss.
        + inv STEP_READ. ss. subst.
          exploit FWDVIEW; eauto.
          { eapply ExecUnit.read_wf. eauto. }
          i. inv STEP_PROMISE. inv MEM2.
          apply ExecUnit.rmap_add_wf; viewtac.
          * eapply ExecUnit.rmap_append_wf; eauto.
          * rewrite TS0, <- TS.
            rewrite List.app_length. s.
            etrans; [|eapply Nat.le_add_r].
            viewtac. erewrite ExecUnit.expr_wf; eauto.
        + eapply ExecUnit.fulfill_step_wf; try exact STEP_FULFILL; cycle 1.
          { inv STEP_PROMISE. inv MEM2.
            rewrite List.app_length; s.
            rewrite <- TS. erewrite ExecUnit.expr_wf; eauto. nia.
          }
          eapply ExecUnit.promise_wf; eauto.
          eapply ExecUnit.read_step_wf; eauto.
          rewrite <- TS. eapply ExecUnit.expr_wf; eauto.
      - inv STEP. econs; ss. econs; viewtac.
      - inv STEP. econs; ss. econs; viewtac.
      - inv LC. econs; ss. econs; viewtac.
        inv CTRL. rewrite <- TS. eauto using ExecUnit.expr_wf.
    Qed.

    Lemma state_step_wf tid eu1 eu2
          (STEP: state_step tid eu1 eu2)
          (WF: wf tid eu1):
      wf tid eu2.
    Proof.
      inv STEP. eapply state_step0_wf; eauto. refl.
    Qed.

    Lemma step_wf tid eu1 eu2
          (STEP: step tid eu1 eu2)
          (WF: wf tid eu1):
      wf tid eu2.
    Proof.
      inv STEP; eauto using state_step_wf, promise_step_wf.
    Qed.

    Lemma non_rel_step_wf tid eu1 eu2
          (STEP: non_rel_step tid eu1 eu2)
          (WF: wf tid eu1):
      wf tid eu2.
    Proof.
      inv STEP. eapply RMWExecUnit.state_step0_wf; eauto. refl.
    Qed.

    Lemma rel_step_wf tid eu1 eu2
          (STEP: rel_step tid eu1 eu2)
          (WF: wf tid eu1):
      wf tid eu2.
    Proof.
      inv STEP. eapply RMWExecUnit.state_step0_wf; eauto. refl.
    Qed.

    Lemma state_step0_incr
          tid e1 e2 eu1 eu2
          (STEP: state_step0 tid e1 e2 eu1 eu2):
      le eu1 eu2.
    Proof.
      inv STEP.
      exploit PFRelLocal.step_incr; eauto. i. des.
      econs; eauto.
    Qed.

    Lemma state_step_incr
          tid eu1 eu2
          (STEP: state_step tid eu1 eu2):
      le eu1 eu2.
    Proof.
      inv STEP. eauto using state_step0_incr.
    Qed.

    Lemma rtc_state_step_incr
          tid eu1 eu2
          (STEPS: rtc (state_step tid) eu1 eu2):
      le eu1 eu2.
    Proof.
      induction STEPS; try refl.
      etrans; eauto using state_step_incr.
    Qed.

    Lemma step_incr
          tid eu1 eu2
          (STEP: step tid eu1 eu2):
      le eu1 eu2.
    Proof.
      inv STEP; eauto using state_step_incr, promise_step_incr.
    Qed.

    Lemma non_rel_step_incr
          tid eu1 eu2
          (STEP: non_rel_step tid eu1 eu2):
      le eu1 eu2.
    Proof.
      inv STEP. eauto using RMWExecUnit.state_step0_incr.
    Qed.

    Lemma rel_step_incr
          tid eu1 eu2
          (STEP: rel_step tid eu1 eu2):
      le eu1 eu2.
    Proof.
      inv STEP. eauto using RMWExecUnit.state_step0_incr.
    Qed.

    Lemma state_step0_promises_le
          tid e1 e2 eu1 eu2
          (STEP: state_step0 tid e1 e2 eu1 eu2):
      Promises.le eu2.(local).(Local.promises) eu1.(local).(Local.promises).
    Proof.
      inv STEP. eauto using PFRelLocal.step_promises_le.
    Qed.

    Lemma state_step_promises_le
          tid eu1 eu2
          (STEP: state_step tid eu1 eu2):
      Promises.le eu2.(local).(Local.promises) eu1.(local).(Local.promises).
    Proof.
      inv STEP. eauto using state_step0_promises_le.
    Qed.

    Lemma rtc_state_step_promises_le
          tid eu1 eu2
          (STEPS: rtc (state_step tid) eu1 eu2):
      Promises.le eu2.(local).(Local.promises) eu1.(local).(Local.promises).
    Proof.
      induction STEPS; ss.
      etrans; eauto using state_step_promises_le.
    Qed.

    Lemma state_step0_promises_sound
          tid e1 e2 eu1 eu2
          (SOUND: Promises.sound tid (Local.promises (local eu1)) (mem eu1))
          (STEP: state_step0 tid e1 e2 eu1 eu2):
      Promises.sound tid (Local.promises (local eu2)) (mem eu2).
    Proof.
      inv STEP. eauto using PFRelLocal.step_promises_sound.
    Qed.

    Lemma state_step_promises_sound
          tid eu1 eu2
          (SOUND: Promises.sound tid (Local.promises (local eu1)) (mem eu1))
          (STEP: state_step tid eu1 eu2):
      Promises.sound tid (Local.promises (local eu2)) (mem eu2).
    Proof.
      inv STEP. eauto using state_step0_promises_sound.
    Qed.

    Lemma rtc_state_step_promises_sound
          tid eu1 eu2
          (SOUND: Promises.sound tid (Local.promises (local eu1)) (mem eu1))
          (STEP: rtc (state_step tid) eu1 eu2):
      Promises.sound tid (Local.promises (local eu2)) (mem eu2).
    Proof.
      induction STEP; ss.
      apply IHSTEP. eauto using state_step_promises_sound.
    Qed.

    Lemma promise_step_promises_sound
          tid eu1 eu2
          (SOUND: Promises.sound tid (Local.promises (local eu1)) (mem eu1))
          (STEP: promise_step tid eu1 eu2):
      Promises.sound tid (Local.promises (local eu2)) (mem eu2).
    Proof.
      inv STEP. eauto using PFRelLocal.promise_promises_sound.
    Qed.

    Lemma step_promises_sound
          tid eu1 eu2
          (SOUND: Promises.sound tid (Local.promises (local eu1)) (mem eu1))
          (STEP: step tid eu1 eu2):
      Promises.sound tid (Local.promises (local eu2)) (mem eu2).
    Proof.
      inv STEP; eauto using state_step_promises_sound, promise_step_promises_sound.
    Qed.

    Lemma non_rel_step_state_step
          tid eu1 eu2
          (STEP: non_rel_step tid eu1 eu2):
      state_step tid eu1 eu2.
    Proof.
      inv STEP. inv STEP0.
      econs. econs; eauto.
      inv LOCAL.
      - econs 1; eauto.
      - econs 2; eauto.
      - econs 3; eauto. destruct ord; ss.
      - econs 5; eauto.
      - econs 6; eauto. destruct ordw; ss.
      - econs 8; eauto.
      - econs 9; eauto. destruct rw, ww; ss.
      - econs 10; eauto.
    Qed.

    Lemma fulfill_step_state_step
          tid ts e eu1 eu2
          (STEP: fulfill_step tid ts e eu1 eu2)
          (EVENT: ~ is_release e):
      state_step tid eu1 eu2.
    Proof.
      apply non_rel_step_state_step.
      inv STEP. econs; eauto.
    Qed.

    Lemma fulfilled_dec ts eu1 eu2:
      fulfilled ts eu1 eu2 \/ ~ fulfilled ts eu1 eu2.
    Proof.
      destruct (Promises.lookup ts eu1.(local).(Local.promises)) eqn:LOOKUP1.
      - destruct (Promises.lookup ts eu2.(local).(Local.promises)) eqn:LOOKUP2.
        + right. ii. inv H1.
          rewrite LOOKUP1, LOOKUP2 in *. ss.
        + left. econs; eauto. rewrite LOOKUP2. ss.
      - right. ii. inv H1.
        rewrite LOOKUP1 in *. ss.
    Qed.

    Lemma fulfilled_or
          eu
          ts eu1 eu2
          (FULFILL: fulfilled ts eu1 eu2):
      fulfilled ts eu1 eu \/ fulfilled ts eu eu2.
    Proof.
      inv FULFILL.
      destruct (Promises.lookup ts (Local.promises (local eu))) eqn:PRM.
      - right. econs; eauto.
      - left. econs; eauto. rewrite PRM. ss.
    Qed.

    Lemma or_rtc_fulfilled
          tid eu1 eu2 eu3 ts
          (STEPS1: rtc (RMWExecUnit.state_step tid) eu1 eu2)
          (STEPS2: rtc (RMWExecUnit.state_step tid) eu2 eu3)
          (FULFILL: fulfilled ts eu1 eu2 \/ fulfilled ts eu2 eu3):
      fulfilled ts eu1 eu3.
    Proof.
      des.
      - inv FULFILL. econs; ss. ii.
        eapply RMWExecUnit.rtc_state_step_promises_le in H1; eauto.
      - inv FULFILL. econs; ss.
        eapply RMWExecUnit.rtc_state_step_promises_le in BEFORE; eauto.
    Qed.

    Lemma rtc_fulfilled_fulfill_step
          tid eu1 eu4 ts
          (STEPS: rtc (RMWExecUnit.state_step tid) eu1 eu4)
          (FULFILL: fulfilled ts eu1 eu4):
      exists e eu2 eu3,
        (<<STEPS1: rtc (RMWExecUnit.state_step tid) eu1 eu2>>) /\
        (<<FULFILL: fulfill_step tid ts e eu2 eu3>>) /\
        (<<STEPS2: rtc (RMWExecUnit.state_step tid) eu3 eu4>>).
    Proof.
      induction STEPS.
      { inv FULFILL. ss. }
      exploit (fulfilled_or y); try exact FULFILL. i. des; cycle 1.
      { exploit IHSTEPS; eauto. i. des.
        esplits; try exact FULFILL0; eauto.
      }
      inv H1. esplits; [refl|..]; eauto.
    Qed.

    Lemma rtc_last_release
          tid eu1 eu4
          (STEPS: rtc (RMWExecUnit.state_step tid) eu1 eu4):
      (exists eu2 eu3,
          (<<STEPS: rtc (RMWExecUnit.state_step tid) eu1 eu2>>) /\
          (<<REL: rel_step tid eu2 eu3>>) /\
          (<<NON_REL_STEPS: rtc (non_rel_step tid) eu3 eu4>>)) \/
      (<<NON_REL_STEPS: rtc (non_rel_step tid) eu1 eu4>>).
    Proof.
      induction STEPS; eauto. des.
      { left. esplits; [econs 2|..]; eauto. }
      inv H1. destruct (is_release e) eqn:REL.
      { left. esplits; [refl|..]; eauto. }
      { right. econs 2; eauto. econs; eauto. congr. }
    Qed.

    Variant more_promises (eu1 eu2: t): Prop :=
    | more_promises_intro
        (STATE: state eu1 = state eu2)
        (LOCAL: PFRelLocal.more_promises (length (mem eu1)) (local eu1) (local eu2))
        (MEMORY: exists mem_app, mem eu2 = mem eu1 ++ mem_app)
    .

    Global Program Instance more_promises_PreOrder: PreOrder more_promises.
    Next Obligation.
      ii. econs; eauto; try refl.
      esplits. rewrite app_nil_r. ss.
    Qed.
    Next Obligation.
      ii. inv H1. inv H2. des.
      econs; try congr.
      - etrans; eauto.
        eapply PFRelLocal.more_promises_decr; eauto.
        rewrite MEMORY, app_length. nia.
      - rewrite MEMORY0, MEMORY.
        rewrite <- app_assoc.
        esplits; eauto.
    Qed.

    Lemma more_promises_lookup
          eu1 eu2 ts
          (MORE: more_promises eu1 eu2)
          (LOOKUP1: Promises.lookup ts (Local.promises (local eu1)) = true):
      Promises.lookup ts (Local.promises (local eu2)) = true.
    Proof.
      inv MORE. inv LOCAL. apply PROMISES_LE. ss.
    Qed.

    Lemma promise_step_more_promises
          tid eu1 eu2
          (STEP: promise_step tid eu1 eu2):
      more_promises eu1 eu2.
    Proof.
      destruct eu1, eu2.
      inv STEP. inv LOCAL. inv MEM2. ss. subst.
      econs; ss; eauto.
      econs; ss.
      - apply Promises.set_le.
      - ii. rewrite Promises.set_o. condtac; ss.
        rewrite e in *. nia.
    Qed.

    Lemma rtc_promise_step_more_promises
          tid eu1 eu2
          (STEPS: rtc (promise_step tid) eu1 eu2):
      more_promises eu1 eu2.
    Proof.
      induction STEPS; try refl.
      etrans; eauto.
      eapply promise_step_more_promises; eauto.
    Qed.

    Lemma more_promises_app
          eu1 eu2 eu1'
          (MORE: more_promises eu1 eu2)
          (STATE: state eu1 = state eu1')
          (LOCAL: local eu1 = local eu1')
          (MEMORY: exists mem_app, mem eu1 = mem eu1' ++ mem_app):
      more_promises eu1' eu2.
    Proof.
      destruct eu1, eu2, eu1'. inv MORE. ss. des. subst.
      econs; ss.
      - eapply PFRelLocal.more_promises_decr; eauto.
        rewrite app_length. nia.
      - rewrite <- app_assoc. eauto.
    Qed.

    Definition unreached (ts: Time.t) (eu: t): Prop :=
      (<<UNREACHEDR: lt eu.(local).(Local.vro).(View.ts) ts>>) /\
      (<<UNREACHEDW: lt eu.(local).(Local.vwo).(View.ts) ts>>).

    Lemma more_promises_state_step
          eu1 tid meu1 meu2
          (MORE1: more_promises eu1 meu1)
          (PROMISES1: forall ts (LOOKUP: Promises.lookup ts meu1.(local).(Local.promises)), ts > length (mem eu1))
          (MSTEP: state_step tid meu1 meu2)
          (UNREACHED: unreached (length (mem eu1)) meu2):
      exists eu2,
        (<<STEP: state_step tid eu1 eu2>>) /\
        (<<MORE2: more_promises eu2 meu2>>) /\
        (<<MEM: mem eu1 = mem eu2>>).
    Proof.
      destruct eu1 as [st1 lc1 mem1],
          meu1 as [mst1 mlc1 mmem1],
          meu2 as [mst2 mlc2 mmem2].
      inv MORE1. ss. des. subst.
      inv MSTEP. inv STEP. inv LOCAL0; ss; subst.
    Admitted.
  End PFRelExecUnit.
End PFRelExecUnit.


Module PFRelMachine.
  Import RMWMachine.

  Variant exec (p:rmw_program) (m:t): Prop :=
  | exec_intro
      (STEP: rtc (step PFRelExecUnit.step) (init p) m)
      (NOPROMISE: no_promise m)
  .
  #[global]
   Hint Constructors exec: core.

  Definition promises_sound (m: t): Prop :=
    forall tid st lc
      (FIND: IdMap.find tid m.(tpool) = Some (st, lc)),
      Promises.sound tid (Local.promises lc) m.(mem).

  Lemma state_step_incr
        m1 m2
        (STEP: step PFRelExecUnit.state_step m1 m2):
    exists mem', mem m2 = mem m1 ++ mem'.
  Proof.
    inv STEP.
    exploit (PFRelExecUnit.state_step_incr (A:=unit)); eauto. i.
    inv x0. eauto.
  Qed.

  Lemma promise_step_incr
        m1 m2
        (STEP: step RMWExecUnit.promise_step m1 m2):
    exists mem', mem m2 = mem m1 ++ mem'.
  Proof.
    inv STEP.
    exploit (RMWExecUnit.promise_step_incr (A:=unit)); eauto. i.
    inv x0. eauto.
  Qed.

  Lemma step_incr
        m1 m2
        (STEP: step PFRelExecUnit.step m1 m2):
    exists mem', mem m2 = mem m1 ++ mem'.
  Proof.
    inv STEP.
    exploit (PFRelExecUnit.step_incr (A:=unit)); eauto. i.
    inv x0. eauto.
  Qed.

  Lemma rtc_state_step_incr
        m1 m2
        (STEP: rtc (step PFRelExecUnit.state_step) m1 m2):
    exists mem', mem m2 = mem m1 ++ mem'.
  Proof.
    induction STEP.
    - esplits. rewrite app_nil_r. ss.
    - exploit state_step_incr; eauto. i. des.
      rewrite IHSTEP, x1.
      rewrite <- app_assoc. eauto.
  Qed.

  Lemma rtc_promise_step_incr
        m1 m2
        (STEP: rtc (step RMWExecUnit.promise_step) m1 m2):
    exists mem', mem m2 = mem m1 ++ mem'.
  Proof.
    induction STEP.
    - esplits. rewrite app_nil_r. ss.
    - exploit promise_step_incr; eauto. i. des.
      rewrite IHSTEP, x1.
      rewrite <- app_assoc. eauto.
  Qed.

  Lemma rtc_step_incr
        m1 m2
        (STEP: rtc (step PFRelExecUnit.step) m1 m2):
    exists mem', mem m2 = mem m1 ++ mem'.
  Proof.
    induction STEP.
    - esplits. rewrite app_nil_r. ss.
    - exploit step_incr; eauto. i. des.
      rewrite IHSTEP, x1.
      rewrite <- app_assoc. eauto.
  Qed.

  Lemma state_step_promises_sound
        m1 m2
        (SOUND: promises_sound m1)
        (STEP: step PFRelExecUnit.state_step m1 m2):
    promises_sound m2.
  Proof.
    inv STEP.
    apply SOUND in FIND.
    hexploit (PFRelExecUnit.state_step_promises_sound (A:=unit)); try exact STEP0; ss. i.
    ii. revert FIND0. rewrite TPOOL.
    rewrite IdMap.add_spec. condtac.
    - inversion e. subst. i. inv FIND0. eauto.
    - i. apply SOUND in FIND0.
      exploit (PFRelExecUnit.state_step_incr (A:=unit)); eauto. i.
      exploit FIND0; eauto. i. des.
      inv x0. ss. rewrite MEM.
      esplits; eauto.
      eapply Memory.get_msg_mon; eauto.
  Qed.

  Lemma promise_step_promises_sound
        m1 m2
        (SOUND: promises_sound m1)
        (STEP: step RMWExecUnit.promise_step m1 m2):
    promises_sound m2.
  Proof.
    inv STEP.
    apply SOUND in FIND.
    hexploit (PFRelExecUnit.promise_step_promises_sound (A:=unit)); try exact STEP0; ss. i.
    ii. revert FIND0. rewrite TPOOL.
    rewrite IdMap.add_spec. condtac.
    - inversion e. subst. i. inv FIND0. eauto.
    - i. apply SOUND in FIND0.
      exploit (RMWExecUnit.promise_step_incr (A:=unit)); eauto. i.
      exploit FIND0; eauto. i. des.
      inv x0. ss. rewrite MEM.
      esplits; eauto.
      eapply Memory.get_msg_mon; eauto.
  Qed.

  Lemma step_promises_sound
        m1 m2
        (SOUND: promises_sound m1)
        (STEP: step PFRelExecUnit.step m1 m2):
    promises_sound m2.
  Proof.
    inv STEP.
    apply SOUND in FIND.
    hexploit (PFRelExecUnit.step_promises_sound (A:=unit)); try exact STEP0; ss. i.
    ii. revert FIND0. rewrite TPOOL.
    rewrite IdMap.add_spec. condtac.
    - inversion e. subst. i. inv FIND0. eauto.
    - i. apply SOUND in FIND0.
      exploit (PFRelExecUnit.step_incr (A:=unit)); eauto. i.
      exploit FIND0; eauto. i. des.
      inv x0. ss. rewrite MEM.
      esplits; eauto.
      eapply Memory.get_msg_mon; eauto.
  Qed.

  Lemma rtc_state_step_promises_sound
        m1 m2
        (SOUND: promises_sound m1)
        (STEP: rtc (step PFRelExecUnit.state_step) m1 m2):
    promises_sound m2.
  Proof.
    induction STEP; eauto using state_step_promises_sound.
  Qed.

  Lemma rtc_promise_step_promises_sound
        m1 m2
        (SOUND: promises_sound m1)
        (STEP: rtc (step RMWExecUnit.promise_step) m1 m2):
    promises_sound m2.
  Proof.
    induction STEP; eauto using promise_step_promises_sound.
  Qed.

  Lemma rtc_step_promises_sound
        m1 m2
        (SOUND: promises_sound m1)
        (STEP: rtc (step PFRelExecUnit.step) m1 m2):
    promises_sound m2.
  Proof.
    induction STEP; eauto using step_promises_sound.
  Qed.

  Lemma rtc_promise_step_more_promises
        m1 m2
        (STEPS: rtc (step RMWExecUnit.promise_step) m1 m2):
    IdMap.Forall2
      (fun tid sl1 sl2 =>
         PFRelExecUnit.more_promises
           (RMWExecUnit.mk (fst sl1) (snd sl1) m1.(mem))
           (RMWExecUnit.mk (fst sl2) (snd sl2) m2.(mem)))
      m1.(tpool) m2.(tpool).
  Proof.
    induction STEPS; ii.
    { destruct (IdMap.find id (tpool x)); ss. econs. refl. }
    inv H.
    specialize (IHSTEPS id). revert IHSTEPS.
    destruct (IdMap.find id (tpool x)) eqn:FINDx.
    { rewrite TPOOL, IdMap.add_spec. condtac.
      - inversion e. subst.
        rewrite FIND in *. inv FINDx.
        exploit (@PFRelExecUnit.promise_step_more_promises unit); eauto. i.
        inv IHSTEPS. ss.
        econs. etrans; eauto.
      - rewrite FINDx. i. inv IHSTEPS.
        econs. ss.
        eapply PFRelExecUnit.more_promises_app; try exact REL; eauto.
        inv STEP. inv LOCAL. inv MEM2. ss. eauto.
    }
    { rewrite TPOOL, IdMap.add_spec. condtac.
      { inversion e. subst. congr. }
      rewrite FINDx. i. inv IHSTEPS. econs.
    }
  Qed.

  Variant pf_rel_until_eu (tid: Id.t) (n: nat) (eu1 eu2: RMWExecUnit.t (A:=unit)): Prop :=
  | pf_re_until_eu_intro
      eu
      (STEPS1: rtc (PFRelExecUnit.state_step tid) eu1 eu)
      (PROMISES: forall ts (LOOKUP: Promises.lookup ts eu.(RMWExecUnit.local).(Local.promises)), ts > n)
      (STEPS2: rtc (RMWExecUnit.state_step tid) eu eu2)
  .
  #[global]
   Hint Constructors pf_rel_until_eu: core.

  Variant pf_rel_until (n: nat) (m_init m_final: t): Prop :=
  | pf_rel_until_intro
      m1 m2
      (PF_REL_STEPS: rtc (step PFRelExecUnit.step) m_init m1)
      (LENGTH: length m1.(mem) = n)
      (PROMISES: rtc (step RMWExecUnit.promise_step) m1 m2)
      (STATE_EXEC: IdMap.Forall2
                     (fun tid sl1 sl2 =>
                        pf_rel_until_eu
                          tid n
                          (RMWExecUnit.mk (fst sl1) (snd sl1) m2.(mem))
                          (RMWExecUnit.mk (fst sl2) (snd sl2) m2.(mem)))
                     m2.(tpool) m_final.(tpool))
      (MEMORY: m2.(mem) = m_final.(mem))
      (NOPROMISE: no_promise m_final)
  .
  #[global]
   Hint Constructors pf_rel_until: core.

  Lemma pf_exec_pf_rel_until
        p m
        (PF_EXEC: RMWMachine.pf_exec p m):
    pf_rel_until 0 (RMWMachine.init p) m.
  Proof.
    inv PF_EXEC. econs.
    - refl.
    - ss.
    - eauto.
    - inv STEP2. ii.
      specialize (TPOOL id). inv TPOOL; eauto.
      econs. econs; eauto. s.
      hexploit rtc_promise_step_more_promises; eauto. i.
      specialize (H1 id).
      rewrite <- H0 in *. inv H1.
      revert H3. rewrite IdMap.map_spec.
      destruct (IdMap.find id p); ss. i. inv H3. ss.
      inv REL0. ss. inv LOCAL.
      destruct ts; try nia.
      exploit PROMISES_EQ; try refl. ss.
    - inv STEP2. ss.
    - ss.
  Qed.

  Lemma promise_step_inv
        tid (eu1 eu2: RMWExecUnit.t (A:=unit))
        (STEP: RMWExecUnit.promise_step tid eu1 eu2):
    (<<PROMISE: Promises.lookup
                  (S (length (RMWExecUnit.mem eu1)))
                  (Local.promises (RMWExecUnit.local eu2)) = true>>) /\
    (<<MEM: exists loc val,
        Memory.get_msg (S (length (RMWExecUnit.mem eu1))) (RMWExecUnit.mem eu2) =
        Some (Msg.mk loc val tid)>>).
  Proof.
    destruct eu1, eu2. ss.
    inv STEP. inv LOCAL. inv MEM2. ss. subst. ss.
    splits.
    - erewrite Promises.set_o. condtac; ss. congr.
    - unfold Memory.get_msg. ss.
      rewrite nth_error_app2; try nia.
      rewrite Nat.sub_diag. s. eauto.
  Qed.

  Lemma pf_rel_until_step
        n m_init m_final
        (SOUND: promises_sound m_init)
        (LENGTH: n < length m_final.(mem))
        (UNTIL: pf_rel_until n m_init m_final):
    pf_rel_until (S n) m_init m_final.
  Proof.
    inv UNTIL.
    hexploit rtc_step_promises_sound; try exact PF_REL_STEPS; eauto. intro SOUND1.
    hexploit rtc_promise_step_promises_sound; try exact PROMISES; eauto. intro SOUND2.
    inv PROMISES.
    { rewrite MEMORY in *. nia. }
    rename y into m. inv H.
    exploit promise_step_inv; try exact STEP. s. i. des.
    hexploit rtc_promise_step_more_promises; try exact H0. intro MORE.
    generalize (MORE tid).
    rewrite TPOOL. rewrite IdMap.add_spec. condtac; try congr.
    i. inv H. clear e X.
    destruct b as [st3 lc3]. ss.
    eapply PFRelExecUnit.more_promises_lookup in REL; eauto. ss.
    dup STATE_EXEC. specialize (STATE_EXEC0 tid).
    rewrite <- H3 in *. inv STATE_EXEC0.
    destruct b as [st4 lc4]. ss. inv REL0. ss.
    exploit (PFRelExecUnit.fulfilled_or eu).
    { instantiate (1:=RMWExecUnit.mk st4 lc4 (mem m2)).
      instantiate (1:=RMWExecUnit.mk st3 lc3 (mem m2)).
      instantiate (1:=S (length (mem m1))).
      econs; ss.
      inv NOPROMISE. exploit PROMISES0; eauto.
      i. rewrite x0. ss.
    }
    i. des.

    { (* fulfilled by PFRel steps *)
      econs.
      - etrans; [exact PF_REL_STEPS|]. econs 2; try refl.
        econs; eauto. econs 2. ss.
      - inv STEP. inv LOCAL. inv MEM2. ss.
        rewrite app_length. s.
        rewrite plus_comm. refl.
      - eauto.
      - ii. destruct (Id.eq_dec id tid).
        { subst. rewrite <- H3, <- H. econs. s. econs; eauto. i.
          exploit PROMISES; eauto. i.
          destruct (Nat.eq_dec ts (S (length (mem m1)))); try nia.
          subst. inv x0. ss.
        }
        { specialize (STATE_EXEC id).
          inv STATE_EXEC; econs.
          destruct a as [st'1 lc'1], b as [st'2 lc'2]. ss.
          inv REL0. econs; eauto. i.
          exploit PROMISES0; eauto. i.
          destruct (Nat.eq_dec ts (S (length (mem m1)))); try nia. subst.
          exploit (PFRelExecUnit.rtc_state_step_promises_sound (A:=unit));
            try exact STEPS0; s; eauto.
          i. des.
          exploit rtc_promise_step_incr; try exact H0. i. des.
          exploit (PFRelExecUnit.rtc_state_step_incr (A:=unit)); try exact STEPS0. i. inv x3. ss.
          revert GET. rewrite MEM0, x2. rewrite <- app_assoc.
          erewrite Memory.get_msg_mon; eauto. i. inv GET. ss.
        }
      - ss.
      - ss.
    }

    (* fulfilled after PFRel steps *)
    exploit (PFRelExecUnit.rtc_fulfilled_fulfill_step (A:=unit)); try exact STEPS2; eauto.
    clear STEPS2. i. des.
    destruct (is_release e) eqn:EVENT.
    { (* fulfilled by a release write *)
      admit.
    }

    (* fulfilled by a non-release write *)
    exploit (PFRelExecUnit.rtc_last_release (A:=unit)); try exact STEPS0.
    clear STEPS0. i. des; cycle 1.
    { (* no release step until the fulfillment *)
      econs; [..|eauto|eauto].
      { etrans; [eauto|].
        econs 2; try refl. econs; eauto.
        econs 2. ss.
      }
      { inv STEP. inv LOCAL. inv MEM2. ss.
        rewrite app_length. s. nia.
      }
      { ss. }
      ii. destruct (Id.eq_dec id tid).
      { subst. rewrite <- H3, <- H. econs. s.
        exploit rtc_mon; try eapply (PFRelExecUnit.non_rel_step_state_step (A:=unit));
          try exact NON_REL_STEPS. i.
        exploit (PFRelExecUnit.fulfill_step_state_step (A:=unit)); eauto; try congr. i.
        econs.
        - etrans; [eauto|]. etrans; [eauto|]. econs 2; eauto.
        - hexploit (PFRelExecUnit.rtc_state_step_promises_le (A:=unit)).
          { etrans; [exact x1|]. econs 2; eauto. }
          i. exploit H1; eauto.
          i. exploit PROMISES; eauto. i.
          destruct (Nat.eq_dec ts (S (length (mem m1)))); try nia. subst.
          inv FULFILL. inv FULFILL0. congr.
        - ss.
      }
      { specialize (STATE_EXEC id).
        inv STATE_EXEC; econs.
        destruct a as [st'1 lc'1], b as [st'2 lc'2]. ss.
        inv REL0. econs; eauto. i.
        exploit PROMISES0; eauto. i.
        destruct (Nat.eq_dec ts (S (length (mem m1)))); try nia. subst.
        exploit (PFRelExecUnit.rtc_state_step_promises_sound (A:=unit));
          try exact STEPS0; s; eauto.
        i. des.
        exploit rtc_promise_step_incr; try exact H0. i. des.
        exploit (PFRelExecUnit.rtc_state_step_incr (A:=unit)); try exact STEPS0. i. inv x3. ss.
        revert GET. rewrite MEM0, x2. rewrite <- app_assoc.
        erewrite Memory.get_msg_mon; eauto. i. inv GET. ss.
      }
    }

    (* release step before the fulfillment *)
  Admitted.

  Lemma pf_rel_until_pf_rel_exec
        n p m
        (UNTIL: pf_rel_until n (RMWMachine.init p) m)
        (LENGTH: length m.(mem) <= n):
    PFRelMachine.exec p m.
  Proof.
    inv UNTIL.
  Admitted.
End PFRelMachine.


Lemma promising_to_pf_release
      p m
      (EXEC: RMWMachine.pf_exec p m):
  PFRelMachine.exec p m.
Proof.
Admitted.
