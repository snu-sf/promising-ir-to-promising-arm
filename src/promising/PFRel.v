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
Require Import PromisingArch.promising.Sim.

Set Implicit Arguments.
Set Nested Proofs Allowed.


Definition promises_eq_until (n: Time.t) (p1 p2: Promises.t): Prop :=
  forall ts (LE: ts <= n), Promises.lookup ts p1 = Promises.lookup ts p2.

Program Instance promises_eq_until_Equivalence (n: Time.t): Equivalence (promises_eq_until n).
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

Definition promises_sound (tid: Id.t) (prm: Promises.t) (mem: Memory.t): Prop :=
  forall ts (LOOKUP: Promises.lookup ts prm),
  exists msg,
    (<<GET: Memory.get_msg ts mem = Some msg>>) /\
    (<<TID: msg.(Msg.tid) = tid>>).

Lemma le_promises_sound
      tid prm1 prm2 mem
      (SOUND: promises_sound tid prm1 mem)
      (LE: Promises.le prm2 prm1):
  promises_sound tid prm2 mem.
Proof.
  ii. eauto.
Qed.

Definition is_release {A} `{_: orderC A} (e: Event.t (A:=A)): bool :=
  match e with
  | Event.write _ ordw _ _ _
  | Event.fadd _ ordw _ _ _ => OrdW.ge OrdW.release_pc ordw
  | Event.barrier (Barrier.dmb rr rw wr ww) => andb rw ww
  | _ => false
  end.


Module PFRelLocal.
  Section PFRelLocal.
    Import Local.
    Context `{A: Type, _: orderC A eq}.

    Variant step (event:Event.t (A:=View.t (A:=A))) (tid:Id.t)
              (lc1:t) (mem1:Memory.t) (lc2:t) (mem2:Memory.t): Prop :=
    | step_internal
        (EVENT: event = Event.internal)
        (LC: lc2 = lc1)
        (MEM: mem2 = mem1)
    | step_read
        ex ord vloc res ts
        (EVENT: event = Event.read ex ord vloc res)
        (STEP: read ex ord vloc res ts lc1 mem1 lc2)
        (MEM: mem2 = mem1)
    | step_fulfill
        ex ord vloc vval res ts view_pre
        (EVENT: event = Event.write ex ord vloc vval res)
        (ORD: OrdW.ge ord OrdW.release_pc)
        (STEP: fulfill ex ord vloc vval res ts tid view_pre lc1 mem1 lc2)
        (MEM: mem2 = mem1)
    | step_write
        lc1'
        ex ord vloc vval res ts view_pre
        (EVENT: event = Event.write ex ord vloc vval res)
        (STEP_PROMISE: promise vloc.(ValA.val) vval.(ValA.val) ts tid lc1 mem1 lc1' mem2)
        (STEP_FULFILL: fulfill ex ord vloc vval res ts tid view_pre lc1' mem2 lc2)
    | step_write_failure
        ex ord vloc vval res
        (EVENT: event = Event.write ex ord vloc vval res)
        (STEP: write_failure ex res lc1 lc2)
        (MEM: mem2 = mem1)
    | step_fadd_fulfill
        ordr ordw vloc vold vnew ts_old ts_new res lc1' view_pre
        (EVENT: event = Event.fadd ordr ordw vloc vold vnew)
        (ORD: OrdW.ge ordw OrdW.release_pc)
        (STEP_READ: read true ordr vloc vold ts_old lc1 mem1 lc1')
        (STEP_FULFILL: fulfill true ordw vloc vnew res ts_new tid view_pre lc1' mem1 lc2)
        (MEM: mem2 = mem1)
    | step_fadd_write
        ordr ordw vloc vold vnew ts_old ts_new res lc1' lc1'' view_pre
        (EVENT: event = Event.fadd ordr ordw vloc vold vnew)
        (STEP_READ: read true ordr vloc vold ts_old lc1 mem1 lc1')
        (STEP_PROMISE: promise vloc.(ValA.val) vnew.(ValA.val) ts_new tid lc1' mem1 lc1'' mem2)
        (STEP_FULFILL: fulfill true ordw vloc vnew res ts_new tid view_pre lc1'' mem2 lc2)
    | step_isb
        (EVENT: event = Event.barrier Barrier.isb)
        (STEP: isb lc1 lc2)
        (MEM: mem2 = mem1)
    | step_dmb
        rr rw wr ww
        (EVENT: event = Event.barrier (Barrier.dmb rr rw wr ww))
        (PROMISES: andb rw ww = true -> lc1.(Local.promises) = bot)
        (STEP: dmb rr rw wr ww lc1 lc2)
        (MEM: mem2 = mem1)
    | step_control
        ctrl
        (EVENT: event = Event.control ctrl)
        (LC: control ctrl lc1 lc2)
        (MEM: mem2 = mem1)
    .
    #[local]
     Hint Constructors step: core.

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
  End PFRelLocal.
End PFRelLocal.


Module PFRelExecUnit.
  Section PFRelExecUnit.
    Import ExecUnit.
    Context `{A: Type, _: orderC A eq}.

    Variant state_step0 (tid:Id.t) (e1 e2:Event.t (A:=View.t (A:=A))) (eu1 eu2:t): Prop :=
    | state_step0_intro
        (STATE: State.step e1 eu1.(state) eu2.(state))
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
        (STEP: ExecUnit.state_step0 tid e e eu1 eu2)
        (REL: ~ is_release e)
    .
    #[local]
     Hint Constructors non_rel_step: core.

    Variant rel_step (tid:Id.t) (eu1 eu2:t): Prop :=
    | rel_step_intro
        e
        (STEP: ExecUnit.state_step0 tid e e eu1 eu2)
        (REL: is_release e)
    .
    #[local]
     Hint Constructors rel_step: core.

    Variant fulfilled (ts: Time.t) (eu1 eu2: t): Prop :=
    | fulfilled_intro
        (BEFORE: Promises.lookup ts eu1.(ExecUnit.local).(Local.promises))
        (AFTER: ~ Promises.lookup ts eu2.(ExecUnit.local).(Local.promises))
    .
    #[local]
     Hint Constructors fulfilled: core.

    Variant fulfill_step (tid:Id.t) (ts: Time.t) (e:Event.t (A:=View.t (A:=A))) (eu1 eu2:t): Prop :=
    | fulfill_step_intro
        (STEP: ExecUnit.state_step0 tid e e eu1 eu2)
        (FULFILL: fulfilled ts eu1 eu2)
    .
    #[local]
     Hint Constructors fulfill_step: core.

    Lemma state_step0_wf tid e1 e2 eu1 eu2
          (STEP: state_step0 tid e1 e2 eu1 eu2)
          (EVENT: eqts_event e1 e2)
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
        eauto using rmap_add_wf, expr_wf.
      - inv RES. inv VIEW. inv VLOC. inv VIEW.
        econs; ss.
        + inv STEP. ss. subst.
          exploit FWDVIEW; eauto.
          { eapply read_wf. eauto. }
          i. apply rmap_add_wf; viewtac.
          rewrite TS, <- TS0. viewtac.
          eauto using expr_wf.
        + eapply read_step_wf; eauto.
          rewrite <- TS0. eapply expr_wf; eauto.
      - inv RES. inv VIEW. inv VVAL. inv VIEW. inv VLOC. inv VIEW.
        econs; ss.
        + inv STEP. inv WRITABLE.
          apply rmap_add_wf; viewtac.
          rewrite TS. unfold ifc. condtac; [|by apply bot_spec]. eapply get_msg_wf. eauto.
        + eapply fulfill_step_wf; eauto.
          rewrite <- TS1. eapply expr_wf; eauto.
      - inv RES. inv VIEW. inv VVAL. inv VIEW. inv VLOC. inv VIEW.
        econs; ss.
        + inv STEP_FULFILL. inv WRITABLE.
          apply rmap_add_wf; viewtac.
          * inv STEP_PROMISE. inv MEM2.
            eapply rmap_append_wf; eauto.
          * rewrite TS. unfold ifc. condtac; [|by apply bot_spec]. eapply get_msg_wf. eauto.
        + eapply fulfill_step_wf; try exact STEP_FULFILL; cycle 1.
          { inv STEP_PROMISE. inv MEM2.
            rewrite List.app_length; s.
            rewrite <- TS1. erewrite expr_wf; eauto. nia.
          }
          eapply promise_wf; try exact PROMISE; eauto.
      - inv STEP. econs; ss. apply rmap_add_wf; viewtac.
        inv RES. inv VIEW. rewrite TS. s. apply bot_spec.
      - inv VLOC. inv VIEW. inv VOLD. inv VIEW. inv VNEW. inv VIEW.
        econs; ss.
        + inv STEP_READ. ss. subst.
          exploit FWDVIEW; eauto.
          { eapply read_wf. eauto. }
          i. apply rmap_add_wf; viewtac.
          rewrite TS0, <- TS. viewtac.
          eauto using expr_wf.
        + eapply fulfill_step_wf; try exact STEP_FULFILL; cycle 1.
          { rewrite <- TS. eapply expr_wf; eauto. }
          eapply read_step_wf; eauto.
          rewrite <- TS. eapply expr_wf; eauto.
      - inv VLOC. inv VIEW. inv VOLD. inv VIEW. inv VNEW. inv VIEW.
        econs; ss.
        + inv STEP_READ. ss. subst.
          exploit FWDVIEW; eauto.
          { eapply read_wf. eauto. }
          i. inv STEP_PROMISE. inv MEM2.
          apply rmap_add_wf; viewtac.
          * eapply rmap_append_wf; eauto.
          * rewrite TS0, <- TS.
            rewrite List.app_length. s.
            etrans; [|eapply Nat.le_add_r].
            viewtac. erewrite expr_wf; eauto.
        + eapply fulfill_step_wf; try exact STEP_FULFILL; cycle 1.
          { inv STEP_PROMISE. inv MEM2.
            rewrite List.app_length; s.
            rewrite <- TS. erewrite expr_wf; eauto. nia.
          }
          eapply promise_wf; eauto.
          eapply read_step_wf; eauto.
          rewrite <- TS. eapply expr_wf; eauto.
      - inv STEP. econs; ss. econs; viewtac.
      - inv STEP. econs; ss. econs; viewtac.
      - inv LC. econs; ss. econs; viewtac.
        inv CTRL. rewrite <- TS. eauto using expr_wf.
    Qed.

    Lemma state_step_wf tid eu1 eu2
          (STEP: state_step tid eu1 eu2)
          (WF: wf tid eu1):
      wf tid eu2.
    Proof.
      inv STEP. eapply state_step0_wf; eauto. refl.
    Qed.

    Lemma non_rel_step_wf tid eu1 eu2
          (STEP: non_rel_step tid eu1 eu2)
          (WF: wf tid eu1):
      wf tid eu2.
    Proof.
      inv STEP. eapply ExecUnit.state_step0_wf; eauto. refl.
    Qed.

    Lemma rel_step_wf tid eu1 eu2
          (STEP: rel_step tid eu1 eu2)
          (WF: wf tid eu1):
      wf tid eu2.
    Proof.
      inv STEP. eapply ExecUnit.state_step0_wf; eauto. refl.
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

    Lemma non_rel_step_state_step
          tid eu1 eu2
          (STEP: non_rel_step tid eu1 eu2):
      state_step tid eu1 eu2.
    Proof.
      inv STEP. inv STEP0.
      econs. econs; eauto.
      inv LOCAL; ss.
      - econs 1; eauto.
      - econs 2; eauto.
      - econs 3; eauto.
        destruct ord; ss.
      - econs 5; eauto.
      - econs 6; eauto.
        destruct ordw; ss.
      - econs 8; eauto.
      - econs 9; eauto.
        destruct rw, ww; ss.
      - econs 10; eauto.
    Qed.

    Lemma fulfilled_dec ts eu1 eu2:
      fulfilled ts eu1 eu2 \/ ~ fulfilled ts eu1 eu2.
    Proof.
      destruct (Promises.lookup ts eu1.(ExecUnit.local).(Local.promises)) eqn:LOOKUP1.
      - destruct (Promises.lookup ts eu2.(ExecUnit.local).(Local.promises)) eqn:LOOKUP2.
        + right. ii. inv H1.
          rewrite LOOKUP1, LOOKUP2 in *. ss.
        + left. econs; eauto. rewrite LOOKUP2. ss.
      - right. ii. inv H1.
        rewrite LOOKUP1 in *. ss.
    Qed.

    Lemma rtc_fulfilled_or
          tid eu1 eu2 eu3 ts
          (STEPS1: rtc (ExecUnit.state_step tid) eu1 eu2)
          (STEPS2: rtc (ExecUnit.state_step tid) eu2 eu3)
          (FULFILL: fulfilled ts eu1 eu3):
      fulfilled ts eu1 eu2 \/ fulfilled ts eu2 eu3.
    Proof.
      revert eu3 STEPS2 FULFILL.
      induction STEPS1; i; auto.
      specialize (fulfilled_dec ts x y). i. des.
      { left.
        hexploit ExecUnit.rtc_state_step_promises_le; try exact STEPS1. i.
        inv H2. econs; ss. ii.
        apply H3 in H2. ss.
      }
      exploit IHSTEPS1; eauto.
      { inv FULFILL. econs; ss.
        destruct (Promises.lookup ts y.(local).(Local.promises)) eqn:LOOKUP; ss.
        exfalso. apply H2. econs; ss.
        rewrite LOOKUP. ss.
      }
      i. des; auto. left.
      inv x1. econs; ss.
      hexploit ExecUnit.state_step_promises_le; try exact H1. auto.
    Qed.

    Lemma or_rtc_fulfilled
          tid eu1 eu2 eu3 ts
          (STEPS1: rtc (ExecUnit.state_step tid) eu1 eu2)
          (STEPS2: rtc (ExecUnit.state_step tid) eu2 eu3)
          (FULFILL: fulfilled ts eu1 eu2 \/ fulfilled ts eu2 eu3):
      fulfilled ts eu1 eu3.
    Proof.
      des.
      - inv FULFILL. econs; ss. ii.
        eapply ExecUnit.rtc_state_step_promises_le in H1; eauto.
      - inv FULFILL. econs; ss.
        eapply ExecUnit.rtc_state_step_promises_le in BEFORE; eauto.
    Qed.

    Lemma rtc_fulfilled_fulfill_step
          tid eu1 eu4 ts
          (STEPS: rtc (ExecUnit.state_step tid) eu1 eu4)
          (FULFILL: fulfilled ts eu1 eu4):
      exists e eu2 eu3,
        (<<STEPS1: rtc (ExecUnit.state_step tid) eu1 eu2>>) /\
        (<<FULFILL: fulfill_step tid ts e eu2 eu3>>) /\
        (<<STEPS2: rtc (ExecUnit.state_step tid) eu3 eu4>>).
    Proof.
      induction STEPS.
      { inv FULFILL. ss. }
      exploit rtc_fulfilled_or; try exact FULFILL.
      { econs 2; try refl. eauto. }
      { ss. }
      i. des; cycle 1.
      { exploit IHSTEPS; eauto. i. des.
        esplits; try exact FULFILL0; eauto.
      }
      inv H1. esplits; [refl|..]; eauto.
    Qed.

    Lemma rtc_last_release
          tid eu1 eu4
          (STEPS: rtc (ExecUnit.state_step tid) eu1 eu4):
      (exists eu2 eu3,
          (<<STEPS: rtc (ExecUnit.state_step tid) eu1 eu2>>) /\
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
      ii. econs; ss; try refl.
      exists []. rewrite List.app_nil_r. ss.
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
  End PFRelExecUnit.
End PFRelExecUnit.


Module PFRelMachine.
  Import Machine.

  Variant exec (p:program) (m:t): Prop :=
  | exec_intro
      (STEP: rtc (step PFRelExecUnit.step) (init p) m)
      (NOPROMISE: no_promise m)
  .
  #[global]
   Hint Constructors exec: core.

  Definition promises_sound (m:t): Prop :=
    forall tid st lc
      (FIND: IdMap.find tid m.(tpool) = Some (st, lc)),
      promises_sound tid (Local.promises lc) m.(mem).

  Lemma rtc_promise_step_more_promises
        m1 m2
        (STEPS: rtc (step ExecUnit.promise_step) m1 m2):
    IdMap.Forall2
      (fun tid sl1 sl2 =>
         PFRelExecUnit.more_promises
           (ExecUnit.mk (fst sl1) (snd sl1) m1.(mem))
           (ExecUnit.mk (fst sl2) (snd sl2) m2.(mem)))
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

  Variant pf_rel_until_eu (tid: Id.t) (n: nat) (eu1 eu2: ExecUnit.t (A:=unit)): Prop :=
  | pf_re_until_eu_intro
      eu
      (STEPS1: rtc (PFRelExecUnit.state_step tid) eu1 eu)
      (PROMISES: forall ts (LOOKUP: Promises.lookup ts eu.(ExecUnit.local).(Local.promises)), ts > n)
      (STEPS2: rtc (ExecUnit.state_step tid) eu eu2)
      (MEMORY: eu1.(ExecUnit.mem) = eu2.(ExecUnit.mem))
  .
  #[global]
   Hint Constructors pf_rel_until_eu: core.

  Variant pf_rel_until (n: nat) (m_init m_final: t): Prop :=
  | pf_rel_until_intro
      m1 m2
      (PF_REL_STEPS: rtc (step PFRelExecUnit.step) m_init m1)
      (LENGTH: length m1.(mem) = n)
      (PROMISES: rtc (step ExecUnit.promise_step) m1 m2)
      (STATE_EXEC: IdMap.Forall2
                     (fun tid sl1 sl2 =>
                        pf_rel_until_eu
                          tid n
                          (ExecUnit.mk (fst sl1) (snd sl1) m2.(mem))
                          (ExecUnit.mk (fst sl2) (snd sl2) m2.(mem)))
                     m2.(tpool) m_final.(tpool))
      (MEMORY: m2.(mem) = m_final.(mem))
      (NOPROMISE: no_promise m_final)
  .
  #[global]
   Hint Constructors pf_rel_until: core.

  Lemma pf_exec_pf_rel_until
        p m
        (PF_EXEC: Machine.pf_exec p m):
    pf_rel_until 0 (Machine.init p) m.
  Proof.
    inv PF_EXEC. econs.
    - refl.
    - ss.
    - eauto.
    - inv STEP2. ii.
      specialize (TPOOL id). inv TPOOL; eauto.
      econs. econs; eauto. ss.
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

  Lemma pf_rel_until_step
        n m_init m_final
        (SOUND: promises_sound m_init)
        (LENGTH: n < length m_final.(mem))
        (UNTIL: pf_rel_until n m_init m_final):
    pf_rel_until (S n) m_init m_final.
  Proof.
    inv UNTIL. inv PROMISES.
    { rewrite MEMORY in *. nia. }
    rename y into m. inv H.
    dup STATE_EXEC.
  Admitted.

  Lemma pf_rel_until_pf_rel_exec
        n p m
        (UNTIL: pf_rel_until n (Machine.init p) m)
        (LENGTH: length m.(mem) <= n):
    PFRelMachine.exec p m.
  Proof.
    inv UNTIL.
  Admitted.
End PFRelMachine.


Lemma promising_to_pf_release
      p m
      (EXEC: Machine.pf_exec p m):
  PFRelMachine.exec p m.
Proof.
Admitted.
