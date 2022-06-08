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


Module RelPFLocal.
  Section RelPFLocal.
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
  End RelPFLocal.
End RelPFLocal.


Module RelPFExecUnit.
  Section RelPFExecUnit.
    Import ExecUnit.
    Context `{A: Type, _: orderC A eq}.

    Variant state_step0 (tid:Id.t) (e1 e2:Event.t (A:=View.t (A:=A))) (eu1 eu2:t): Prop :=
    | state_step0_intro
        (STATE: State.step e1 eu1.(state) eu2.(state))
        (LOCAL: RelPFLocal.step e2 tid eu1.(local) eu1.(mem) eu2.(local)  eu2.(mem))
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
            rewrite <- TS1. erewrite expr_wf; eauto. lia.
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
  End RelPFExecUnit.
End RelPFExecUnit.


Module RelPFMachine.
  Import Machine.

  Variant exec (p:program) (m:t): Prop :=
  | exec_intro
      (STEP: rtc (step RelPFExecUnit.step) (init p) m)
      (NOPROMISE: no_promise m)
  .
  #[global]
   Hint Constructors exec: core.
End RelPFMachine.
