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

Require Import PromisingArch.mapping.RMWLang.

Set Implicit Arguments.


Ltac etl := etrans; [|apply join_l].
Ltac etr := etrans; [|apply join_r].
Ltac ets :=
  s;
  (try refl);
  (try eassumption);
  (try by (etl; ets));
  (try by (etr; ets)).


Section Eqts.
  Context `{A: Type, B: Type, _: orderC A eq, _: orderC B eq}.

  Variant eqts_rmw_event: forall (e1:RMWEvent.t (A:=View.t (A:=A))) (e2:RMWEvent.t (A:=View.t (A:=B))), Prop :=
  | eqts_rmw_event_internal:
      eqts_rmw_event RMWEvent.internal RMWEvent.internal
  | eqts_rmw_event_read
      ord vloc1 vloc2 res1 res2
      (VLOC: eqts_val vloc1 vloc2)
      (RES: eqts_val res1 res2):
      eqts_rmw_event (RMWEvent.read ord vloc1 res1) (RMWEvent.read ord vloc2 res2)
  | eqts_rmw_event_write
      ord vloc1 vloc2 vval1 vval2
      (VLOC: eqts_val vloc1 vloc2)
      (VVAL: eqts_val vval1 vval2):
      eqts_rmw_event (RMWEvent.write ord vloc1 vval1) (RMWEvent.write ord vloc2 vval2)
  | eqts_rmw_event_fadd
      ordr ordw vloc1 vloc2 vold1 vold2 vnew1 vnew2
      (VLOC: eqts_val vloc1 vloc2)
      (VOLD: eqts_val vold1 vold2)
      (VNEW: eqts_val vnew1 vnew2):
      eqts_rmw_event (RMWEvent.fadd ordr ordw vloc1 vold1 vnew1) (RMWEvent.fadd ordr ordw vloc2 vold2 vnew2)
  | eqts_rmw_event_barrier
      rr rw wr ww:
      eqts_rmw_event (RMWEvent.dmb rr rw wr ww) (RMWEvent.dmb rr rw wr ww)
  | eqts_rmw_event_control
      ctrl1 ctrl2
      (CTRL: eqts_view ctrl1 ctrl2):
      eqts_rmw_event (RMWEvent.control ctrl1) (RMWEvent.control ctrl2)
  .
  #[local]
  Hint Constructors eqts_event: core.
End Eqts.

Section EqtsEquiv.
  Context `{A: Type, _: orderC A eq}.

  Global Program Instance eqts_rmw_event_equiv: Equivalence eqts_rmw_event.
  Next Obligation. ii. destruct x; econs; ss. Qed.
  Next Obligation.
    ii. inv H1; econs; ss.
    all: symmetry; ss.
  Qed.
  Next Obligation.
    ii. inv H1; inv H2; econs; ss.
    all: etrans; eauto.
  Qed.
End EqtsEquiv.


Module RMWLocal.
Section RMWLocal.
  Context `{A: Type, _: orderC A eq}.

  Variant step (n:option Time.t) (event:RMWEvent.t (A:=View.t (A:=A))) (tid:Id.t) (mem:Memory.t) (lc1 lc2:Local.t (A:=A)): Prop :=
  | step_internal
      (EVENT: event = RMWEvent.internal)
      (LC: lc2 = lc1)
  | step_read
      ord vloc res ts
      (EVENT: event = RMWEvent.read ord vloc res)
      (STEP: Local.read false ord vloc res ts lc1 mem lc2)
  | step_fulfill
      ord vloc vval res ts view_pre
      (EVENT: event = RMWEvent.write ord vloc vval)
      (STEP: Local.fulfill false ord vloc vval res ts tid view_pre lc1 mem lc2)
      (PF: match n with
           | None => True
           | Some n => le ts n -> OrdW.ge OrdW.pln ord
           end)
  | step_fadd
      ordr ordw vloc vold vnew ts_old ts_new res lc1' view_pre lc1''
      (EVENT: event = RMWEvent.fadd ordr ordw vloc vold vnew)
      (STEP_READ: Local.read true ordr vloc vold ts_old lc1 mem lc1')
      (STEP_FULFILL: Local.fulfill true ordw vloc vnew res ts_new tid view_pre lc1' mem lc1'')
      (STEP_CONTROL: Local.control vold.(ValA.annot) lc1'' lc2)
      (PF: match n with
           | None => True
           | Some n => le ts_new n -> OrdW.ge OrdW.pln ordw
           end)
  | step_dmb
      rr rw wr ww
      (EVENT: event = RMWEvent.dmb rr rw wr ww)
      (STEP: Local.dmb rr rw wr ww lc1 lc2)
  | step_control
      ctrl
      (EVENT: event = RMWEvent.control ctrl)
      (LC: Local.control ctrl lc1 lc2)
  .
  #[local]
  Hint Constructors step: core.

  Lemma step_pf_none n:
    step n <5= step None.
  Proof.
    i. inv PR; eauto.
  Qed.

  Lemma step_pf_mon
        m n
        (PF_LE: m <= n):
    step (Some n) <5= step (Some m).
  Proof.
    i. inv PR; eauto.
    - econs 3; eauto. i. apply PF. etrans; eauto.
    - econs 4; eauto. i. apply PF. etrans; eauto.
  Qed.

  Lemma step_incr
        n e tid mem lc1 lc2
        (LC: step n e tid mem lc1 lc2):
    Local.le lc1 lc2.
  Proof.
    inv LC; try refl.
    - eapply Local.read_incr. eauto.
    - eapply Local.fulfill_incr. eauto.
    - hexploit Local.read_incr; eauto. i.
      hexploit Local.fulfill_incr; eauto. i.
      hexploit Local.control_incr; eauto. i.
      do 2 (etrans; eauto).
    (* - eapply Local.isb_incr. eauto. *)
    - eapply Local.dmb_incr. eauto.
    - eapply Local.control_incr. eauto.
  Qed.

  Lemma step_promises_le
        n e tid mem lc1 lc2
        (STEP: step n e tid mem lc1 lc2):
    Promises.le (Local.promises lc2) (Local.promises lc1).
  Proof.
    inv STEP; ss; try by (inv STEP0; ss).
    - inv STEP0. ss. apply Promises.unset_le.
    - inv STEP_READ. inv STEP_FULFILL. inv STEP_CONTROL. ss.
      apply Promises.unset_le.
    - inv LC. ss.
  Qed.

  Lemma promise_promises_sound
        loc val ts tid lc1 mem1 lc2 mem2
        (STEP: Local.promise (A:=A) loc val ts tid lc1 mem1 lc2 mem2)
        (SOUND: Promises.sound tid (Local.promises lc1) mem1):
    Promises.sound tid (Local.promises lc2) mem2.
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

  Lemma fulfill_promises_sound
        ex ord vloc vval res ts tid view_pre lc1 mem lc2
        (FULFILL: Local.fulfill ex ord vloc vval res ts tid view_pre lc1 mem lc2)
        (SOUND: Promises.sound tid (Local.promises lc1) mem):
    Promises.sound tid (Local.promises lc2) mem.
  Proof.
    inv FULFILL; ss.
    eapply Promises.le_sound; eauto.
    eapply Promises.unset_le.
  Qed.

  Lemma step_promises_sound
        n e tid mem lc1 lc2
        (STEP: step n e tid mem lc1 lc2)
        (SOUND: Promises.sound tid (Local.promises lc1) mem):
    Promises.sound tid (Local.promises lc2) mem.
  Proof.
    inv STEP; eauto; try by (inv STEP0; ss; eauto).
    - eapply fulfill_promises_sound; eauto.
    - inv STEP_READ. inv STEP_CONTROL. ss.
      eapply fulfill_promises_sound; eauto.
    - inv LC. ss.
  Qed.

  Variant wf (tid: Id.t) (lc: Local.t (A:=A)) (mem: Memory.t): Prop :=
    | view_wf_intro
        (COH: forall loc, le (lc.(Local.coh) loc) (join lc.(Local.vro) lc.(Local.vwo)))
        (VRN: le lc.(Local.vrn) (join lc.(Local.vro) lc.(Local.vwo)))
        (VWN: le lc.(Local.vwn) (join lc.(Local.vro) lc.(Local.vwo)))
        (FWD: forall loc,
            le (lc.(Local.fwdbank) loc).(FwdItem.ts) (View.ts (lc.(Local.coh) loc)))
        (FWD_VIEW: forall loc,
            le (lc.(Local.fwdbank) loc).(FwdItem.view).(View.ts)
               (lc.(Local.fwdbank) loc).(FwdItem.ts))
        (PRM: Promises.sound tid (Local.promises lc) mem)
        (PRM_COH: forall ts msg
                         (MSG: Memory.get_msg ts mem = Some msg)
                         (TID: msg.(Msg.tid) = tid)
                         (TS: (lc.(Local.coh) msg.(Msg.loc)).(View.ts) < ts),
            Promises.lookup ts lc.(Local.promises))
  .

  Lemma init_wf tid:
    wf tid Local.init Memory.empty.
  Proof.
    econs; ss; i; try refl; try apply join_l.
    - ii. rewrite Promises.lookup_bot in *. ss.
    - unfold Memory.get_msg in *. destruct ts; ss.
      apply nth_error_some in MSG. ss. nia.
  Qed.

  Lemma read_wf
        tid
        ex ord vloc res ts lc1 mem lc2
        (READ: Local.read ex ord vloc res ts lc1 mem lc2)
        (WF: wf tid lc1 mem):
    wf tid lc2 mem.
  Proof.
    inv WF. inv READ. econs; ss; i.
    - unfold fun_add. condtac.
      + inversion e. subst. apply join_spec.
        * etrans; [apply COH|].
          eapply join_le; try apply View.order. refl.
        * etrans; [|apply join_l]. apply join_r.
      + etrans; [apply COH|].
        eapply join_le; try apply View.order. refl.
    - apply join_spec.
      + etrans; eauto.
        eapply join_le; try apply View.order. refl.
      + unfold ifc. condtac; ss; try apply bot_spec.
        etrans; [|apply join_l]. apply join_r.
    - apply join_spec.
      + etrans; eauto.
        eapply join_le; try apply View.order. refl.
      + unfold ifc. condtac; ss; try apply bot_spec.
        etrans; [|apply join_l]. apply join_r.
    - etrans; eauto.
      unfold fun_add. condtac; ss.
      rewrite e. apply join_l.
    - eapply PRM_COH; eauto.
      eapply le_lt_trans; try exact TS.
      unfold fun_add. condtac; ss.
      rewrite e. ets.
  Qed.

  Lemma fulfill_wf
        ex ord vloc vval res ts tid view_pre lc1 mem lc2
        (FULFILL: Local.fulfill ex ord vloc vval res ts tid view_pre lc1 mem lc2)
        (WF: wf tid lc1 mem):
    wf tid lc2 mem.
  Proof.
    hexploit fulfill_promises_sound; try apply WF; eauto. i.
    inv WF. inv FULFILL. econs; ss; i.
    - unfold fun_add. condtac.
      + inversion e. subst.
        etrans; [|apply join_r]. apply join_r.
      + etrans; [apply COH|].
        eapply join_le; try apply View.order. refl.
    - etrans; eauto.
      eapply join_le; try apply View.order. refl.
    - etrans; eauto.
      eapply join_le; try apply View.order. refl.
    - unfold fun_add. condtac; ss.
    - unfold fun_add. condtac; ss.
      inv WRITABLE. apply Nat.lt_le_incl.
      eapply Nat.le_lt_trans; try exact EXT. ss.
      eapply join_le; [apply Time.order|..]; try refl.
      apply join_l.
    - rewrite Promises.unset_o. condtac; ss.
      + r in e. subst.
        destruct msg. rewrite MSG in *. inv MSG0. ss.
        revert TS. unfold fun_add. condtac; try congr. s. nia.
      + eapply PRM_COH; eauto.
        eapply le_lt_trans; try exact TS.
        unfold fun_add. condtac; ss.
        rewrite e. inv WRITABLE. nia.
  Qed.

  Lemma dmb_wf
        tid mem
        rr rw wr ww lc1 lc2
        (DMB: Local.dmb rr rw wr ww lc1 lc2)
        (WF: wf tid lc1 mem):
    wf tid lc2 mem.
  Proof.
    inv WF. inv DMB. econs; ss; i.
    - apply join_spec; ss.
      apply join_spec.
      + destruct rr; s; try apply bot_spec. apply join_l.
      + apply join_spec; try apply bot_spec.
        destruct wr; s; try apply bot_spec. apply join_r.
    - apply join_spec; ss.
      apply join_spec.
      + destruct rw; s; try apply bot_spec. apply join_l.
      + apply join_spec; try apply bot_spec.
        destruct ww; s; try apply bot_spec. apply join_r.
  Qed.

  Lemma control_wf
        tid mem
        ctrl lc1 lc2
        (CONTROL: Local.control ctrl lc1 lc2)
        (WF: wf tid lc1 mem):
    wf tid lc2 mem.
  Proof.
    inv WF. inv CONTROL. econs; ss.
  Qed.

  Lemma step_wf
        n e tid mem lc1 lc2
        (STEP: step n e tid mem lc1 lc2)
        (WF: wf tid lc1 mem):
    wf tid lc2 mem.
  Proof.
    inv STEP; ss.
    - eauto using read_wf.
    - eauto using fulfill_wf.
    - eapply control_wf; try exact STEP_CONTROL.
      eapply fulfill_wf; try exact STEP_FULFILL.
      eapply read_wf; eauto.
    - eauto using dmb_wf.
    - eauto using control_wf.
  Qed.

  Lemma interference_wf
        tid lc mem mem'
        (INTERFERENCE: Forall (fun msg => msg.(Msg.tid) <> tid) mem')
        (WF: wf tid lc mem):
    wf tid lc (mem ++ mem').
  Proof.
    inv WF. econs; ss.
    - ii. exploit PRM; eauto. i. des.
      esplits; eauto.
      unfold Memory.get_msg in *. destruct ts; ss.
      eapply nth_error_app_mon; eauto.
    - i. unfold Memory.get_msg in MSG. destruct ts; ss.
      apply nth_error_app_inv in MSG. des; eauto.
      apply nth_error_In in MSG0.
      rewrite Forall_forall in INTERFERENCE.
      exploit INTERFERENCE; eauto.
      rewrite TID. i. r in x0.
      unfold proj_sumbool in x0. des_ifs. congr.
  Qed.

  Variant fulfillable_ts (ts: Time.t) (lc: Local.t (A:=A)): Prop :=
    | fulfillable_ts_intro
        (LT_VWN: lt lc.(Local.vwn).(View.ts) ts)
        (LT_VCAP: lt lc.(Local.vcap).(View.ts) ts)
  .

  Lemma fulfillable_ts_le
        ts lc1 lc2
        (LC_LE: Local.le lc1 lc2)
        (FULFILLABLE: fulfillable_ts ts lc2):
    fulfillable_ts ts lc1.
  Proof.
    inv FULFILLABLE. econs.
    - eapply Nat.le_lt_trans; [|exact LT_VWN]. apply LC_LE.
    - eapply Nat.le_lt_trans; [|exact LT_VCAP]. apply LC_LE.
  Qed.

  Definition fulfillable (lc: Local.t (A:=A)) (mem: Memory.t): Prop :=
    forall ts (PROMISED: Promises.lookup ts lc.(Local.promises) = true),
      (<<LT_VWN: lt lc.(Local.vwn).(View.ts) ts>>) /\
      (<<LT_VCAP: lt lc.(Local.vcap).(View.ts) ts>>) /\
      (<<LT_COH: forall msg (GET: Memory.get_msg ts mem = Some msg),
          lt (lc.(Local.coh) msg.(Msg.loc)).(View.ts) ts>>).

  Lemma read_fulfillable
        ex ord vloc res ts lc1 mem lc2
        (READ: Local.read ex ord vloc res ts lc1 mem lc2)
        (FULFILLABLE: fulfillable lc2 mem):
    fulfillable lc1 mem.
  Proof.
    ii. exploit (FULFILLABLE ts0).
    { inv READ. ss. }
    i. des.
    exploit Local.read_incr; eauto. i.
    splits; i.
    - eapply le_lt_trans; try exact LT_VWN. apply x0.
    - eapply le_lt_trans; try exact LT_VCAP. apply x0.
    - exploit LT_COH; eauto. i.
      eapply le_lt_trans; try exact x1. apply x0.
  Qed.

  Lemma fulfill_fulfillable
        ex ord vloc vval res ts tid view_pre lc1 mem lc2
        (FULFILL: Local.fulfill ex ord vloc vval res ts tid view_pre lc1 mem lc2)
        (FULFILLABLE: fulfillable lc2 mem):
    fulfillable lc1 mem.
  Proof.
    ii. destruct (Promises.lookup ts0 (Local.promises lc2)) eqn:PROMISED2.
    - exploit FULFILLABLE; eauto. i. des.
      exploit Local.fulfill_incr; eauto. i.
      splits; i.
      + eapply le_lt_trans; try exact LT_VWN. apply x0.
      + eapply le_lt_trans; try exact LT_VCAP. apply x0.
      + exploit LT_COH; eauto. i.
        eapply le_lt_trans; try exact x1. apply x0.
    - inv FULFILL. inv WRITABLE. ss.
      revert PROMISED2. rewrite Promises.unset_o. condtac; try congr.
      r in e. i. subst. clear X PROMISED2 EX.
      splits; i.
      + eapply le_lt_trans; try exact EXT. ets.
      + eapply le_lt_trans; try exact EXT. ets.
      + destruct msg. rewrite GET in *. inv MSG. ss.
  Qed.

  Lemma dmb_fulfillable
        mem
        rr rw wr ww lc1 lc2
        (DMB: Local.dmb rr rw wr ww lc1 lc2)
        (FULFILLABLE: fulfillable lc2 mem):
    fulfillable lc1 mem.
  Proof.
    ii. exploit (FULFILLABLE ts).
    { inv DMB. ss. }
    i. des.
    exploit Local.dmb_incr; eauto. i.
    splits; i.
    - eapply le_lt_trans; try exact LT_VWN. apply x0.
    - eapply le_lt_trans; try exact LT_VCAP. apply x0.
    - exploit LT_COH; eauto. i.
      eapply le_lt_trans; try exact x1. apply x0.
  Qed.

  Lemma control_fulfillable
        mem
        ctrl lc1 lc2
        (CONTROL: Local.control ctrl lc1 lc2)
        (FULFILLABLE: fulfillable lc2 mem):
    fulfillable lc1 mem.
  Proof.
    inv CONTROL. ii.
    exploit FULFILLABLE; eauto. s. i. des.
    splits; ss.
    eapply le_lt_trans; try exact LT_VCAP. apply join_l.
  Qed.

  Lemma step_fulfillable
        n e tid mem lc1 lc2
        (STEP: step n e tid mem lc1 lc2)
        (FULFILLABLE: fulfillable lc2 mem):
    fulfillable lc1 mem.
  Proof.
    inv STEP; ss.
    - eauto using read_fulfillable.
    - eauto using fulfill_fulfillable.
    - eapply read_fulfillable; try exact STEP_READ.
      eapply fulfill_fulfillable; try exact STEP_FULFILL.
      eapply control_fulfillable; eauto.
    - eauto using dmb_fulfillable.
    - eauto using control_fulfillable.
  Qed.

  Lemma step_pf_S1
        n e tid mem lc1 lc2
        (STEP: step (Some n) e tid mem lc1 lc2)
        (NON_PROMISED: Promises.lookup (S n) lc1.(Local.promises) = false):
    step (Some (S n)) e tid mem lc1 lc2.
  Proof.
    inv STEP; eauto.
    - econs 3; eauto. i. inv H1; auto.
      inv STEP0. congr.
    - econs 4; eauto. i. inv H1; auto.
      inv STEP_READ. inv STEP_FULFILL. ss. congr.
  Qed.

  Lemma step_pf_S2
        n e tid mem lc1 lc2
        (STEP: step (Some n) e tid mem lc1 lc2)
        (PROMISED: Promises.lookup (S n) lc2.(Local.promises) = true):
    step (Some (S n)) e tid mem lc1 lc2.
  Proof.
    inv STEP; eauto.
    - econs 3; eauto. i. inv H1; auto.
      inv STEP0. ss.
      revert PROMISED. erewrite Promises.unset_o.
      condtac; ss. congr.
    - econs 4; eauto. i. inv H1; auto.
      inv STEP_CONTROL. ss.
      inv STEP_FULFILL. ss.
      inv STEP_READ. ss.
      revert PROMISED. erewrite Promises.unset_o.
      condtac; ss. congr.
  Qed.
End RMWLocal.
End RMWLocal.


Module RMWExecUnit.
Section RMWExecUnit.
  Context `{A: Type, _: orderC A eq}.

  Record t := mk {
    state: RMWState.t (A:=View.t (A:=A));
    local: Local.t (A:=A);
    mem: Memory.t;
  }.
  #[local]
  Hint Constructors t: core.

  Variant state_step0 (n: option Time.t) (tid:Id.t) (e1 e2:RMWEvent.t (A:=View.t (A:=A))) (eu1 eu2:t): Prop :=
  | state_step0_intro
      (STATE: RMWState.step e1 eu1.(state) eu2.(state))
      (LOCAL: RMWLocal.step n e2 tid eu1.(mem) eu1.(local) eu2.(local))
      (MEM: eu2.(mem) = eu1.(mem))
  .
  #[local]
  Hint Constructors state_step0: core.

  Variant state_step (n: option Time.t) (tid:Id.t) (eu1 eu2:t): Prop :=
  | state_step_intro
      e
      (STEP: state_step0 n tid e e eu1 eu2)
  .
  #[local]
    Hint Constructors state_step: core.

  Definition is_dmbsy (e: RMWEvent.t (A:=View.t (A:=A))): bool :=
    match e with
    | RMWEvent.dmb true true true true => true
    | _ => false
    end.

  Variant state_step_dmbsy (n: option Time.t) (sc: Time.t) (tid:Id.t) (eu1 eu2:t): Prop :=
  | state_step_dmbsy_intro
      e
      (STEP: state_step0 n tid e e eu1 eu2)
      (DMBSY: is_dmbsy e)
      (VIEW: (join eu1.(local).(Local.vro) eu1.(local).(Local.vwo)).(View.ts) = sc)
  .
  #[local]
  Hint Constructors state_step_dmbsy: core.

  Variant state_step_dmbsy_exact (n: option Time.t) (sc: Time.t) (tid:Id.t) (eu1 eu2:t): Prop :=
  | state_step_dmbsy_exact_intro
      e
      (STEP: state_step0 n tid e e eu1 eu2)
      (DMBSY: is_dmbsy e ->
              (join eu1.(local).(Local.vro) eu1.(local).(Local.vwo)).(View.ts) = sc)
  .
  #[local]
  Hint Constructors state_step_dmbsy_exact: core.

  Variant state_step_dmbsy_under (n: option Time.t) (sc: Time.t) (tid:Id.t) (eu1 eu2:t): Prop :=
  | state_step_dmbsy_under_intro
      e
      (STEP: state_step0 n tid e e eu1 eu2)
      (DMBSY: is_dmbsy e ->
              le (join eu1.(local).(Local.vro) eu1.(local).(Local.vwo)).(View.ts) sc)
  .
  #[local]
  Hint Constructors state_step_dmbsy_under: core.

  Variant state_step_dmbsy_over (n: option Time.t) (sc: Time.t) (tid:Id.t) (eu1 eu2:t): Prop :=
  | state_step_dmbsy_over_intro
      e
      (STEP: state_step0 n tid e e eu1 eu2)
      (DMBSY: is_dmbsy e ->
              le sc (join eu1.(local).(Local.vro) eu1.(local).(Local.vwo)).(View.ts))
  .
  #[local]
  Hint Constructors state_step_dmbsy_over: core.

  Lemma state_step0_pf_none n:
    state_step0 n <5= state_step0 None.
  Proof.
    i. inv PR.
    econs; eauto using RMWLocal.step_pf_none.
  Qed.

  Lemma state_step_pf_none n:
    state_step n <3= state_step None.
  Proof.
    i. inv PR. econs.
    eauto using state_step0_pf_none.
  Qed.

  Lemma state_step_dmbsy_exact_pf_none n:
    state_step_dmbsy_exact n <4= state_step_dmbsy_exact None.
  Proof.
    i. inv PR.
    econs; eauto using state_step0_pf_none.
  Qed.

  Lemma state_step_dmbsy_over_pf_none n:
    state_step_dmbsy_over n <4= state_step_dmbsy_over None.
  Proof.
    i. inv PR.
    econs; eauto using state_step0_pf_none.
  Qed.

  Lemma state_step0_pf_mon
        m n
        (PF_LE: m <= n):
    state_step0 (Some n) <5= state_step0 (Some m).
  Proof.
    i. inv PR.
    econs; eauto using RMWLocal.step_pf_mon.
  Qed.

  Lemma state_step_pf_mon
        m n
        (PF_LE: m <= n):
    state_step (Some n) <3= state_step (Some m).
  Proof.
    i. inv PR. econs.
    eauto using state_step0_pf_mon.
  Qed.

  Lemma state_step_dmbsy_exact_pf_mon
        m n
        (PF_LE: m <= n):
    state_step_dmbsy_exact (Some n) <4= state_step_dmbsy_exact (Some m).
  Proof.
    i. inv PR.
    econs; eauto using state_step0_pf_mon.
  Qed.

  Lemma state_step_dmbsy_over_pf_mon
        m n
        (PF_LE: m <= n):
    state_step_dmbsy_over (Some n) <4= state_step_dmbsy_over (Some m).
  Proof.
    i. inv PR.
    econs; eauto using state_step0_pf_mon.
  Qed.

  Lemma dmbsy_state_step n sc:
    state_step_dmbsy n sc <3= state_step n.
  Proof.
    i. inv PR. econs. eauto.
  Qed.

  Lemma dmbsy_exact_state_step n sc:
    state_step_dmbsy_exact n sc <3= state_step n.
  Proof.
    i. inv PR. econs. eauto.
  Qed.

  Lemma dmbsy_under_state_step n sc:
    state_step_dmbsy_under n sc <3= state_step n.
  Proof.
    i. inv PR. econs. eauto.
  Qed.

  Lemma dmbsy_over_state_step n sc:
    state_step_dmbsy_over n sc <3= state_step n.
  Proof.
    i. inv PR. econs. eauto.
  Qed.

  Lemma dmbsy_dmbsy_exact:
    state_step_dmbsy <5= state_step_dmbsy_exact.
  Proof.
    i. inv PR. econs; eauto.
  Qed.

  Lemma dmbsy_exact_dmbsy_over:
    state_step_dmbsy_exact <5= state_step_dmbsy_over.
  Proof.
    i. inv PR. econs; eauto.
    i. apply DMBSY in H1. subst. refl.
  Qed.

  Lemma dmbsy_over_sc_mon
        n sc1 sc2
        (SC_LE: sc1 <= sc2):
    state_step_dmbsy_over n sc2 <3= state_step_dmbsy_over n sc1.
  Proof.
    i. inv PR. econs; eauto. i. etrans; eauto.
  Qed.

  Lemma state_step_dmbsy_over_S
        n sc tid eu1 eu2
        (STEP: state_step_dmbsy_over n sc tid eu1 eu2):
    state_step_dmbsy n sc tid eu1 eu2 \/
    state_step_dmbsy_over n (S sc) tid eu1 eu2.
  Proof.
    inv STEP. destruct (is_dmbsy e) eqn:X.
    - exploit DMBSY; eauto. i. inv x0.
      + left. econs; eauto.
      + right. econs; eauto. i. ss.
        rewrite <- H1. unfold le. nia.
    - right. econs; eauto. i. congr.
  Qed.

  Variant promise_step (tid:Id.t) (eu1 eu2:t): Prop :=
  | promise_step_intro
      loc val ts
      (STATE: eu1.(state) = eu2.(state))
      (LOCAL: Local.promise loc val ts tid eu1.(local) eu1.(mem) eu2.(local) eu2.(mem))
  .
  #[local]
  Hint Constructors promise_step: core.

  Variant step (tid:Id.t) (eu1 eu2:t): Prop :=
  | step_state (STEP: state_step None tid eu1 eu2)
  | step_promise (STEP: promise_step tid eu1 eu2)
  .
  #[local]
  Hint Constructors step: core.

  Variant wf (tid:Id.t) (eu:t): Prop :=
  | wf_intro
      (STATE: ExecUnit.rmap_wf eu.(mem) eu.(state).(RMWState.rmap))
      (LOCAL: Local.wf tid eu.(mem) eu.(local))
  .
  #[local]
  Hint Constructors wf: core.

  Lemma state_step0_wf
        n tid e1 e2 eu1 eu2
        (STEP: state_step0 n tid e1 e2 eu1 eu2)
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
    - inv VVAL. inv VIEW. inv VLOC. inv VIEW.
      econs; ss.
      eapply ExecUnit.fulfill_step_wf; eauto.
      rewrite <- TS0. eapply ExecUnit.expr_wf; eauto.
    - inv VLOC. inv VIEW. inv VOLD. inv VIEW. inv VNEW. inv VIEW.
      assert (VOLD: View.ts (ValA.annot vold) <= length mem1).
      { inv STEP_READ. ss. subst.
        exploit FWDVIEW; eauto.
        { eapply ExecUnit.read_wf. eauto. }
        i. rewrite TS0, <- TS. viewtac.
        eauto using ExecUnit.expr_wf.
      }
      econs; ss.
      + apply ExecUnit.rmap_add_wf; viewtac.
      + eapply ExecUnit.control_step_wf; try exact STEP_CONTROL; try nia.
        eapply ExecUnit.fulfill_step_wf; try exact STEP_FULFILL; cycle 1.
        { rewrite <- TS. eapply ExecUnit.expr_wf; eauto. }
        eapply ExecUnit.read_step_wf; eauto.
        rewrite <- TS. eapply ExecUnit.expr_wf; eauto.
    - inv STEP. econs; ss. econs; viewtac.
    (* - inv STEP. econs; ss. econs; viewtac. *)
    - inv LC. econs; ss. econs; viewtac.
      inv CTRL. rewrite <- TS. eauto using ExecUnit.expr_wf.
  Qed.

  Lemma state_step_wf 
        n tid eu1 eu2
        (STEP: state_step n tid eu1 eu2)
        (WF: wf tid eu1):
    wf tid eu2.
  Proof.
    inv STEP. eapply state_step0_wf; eauto. refl.
  Qed.

  Lemma state_step_dmbsy_wf
        n sc tid eu1 eu2
        (STEP: state_step_dmbsy n sc tid eu1 eu2)
        (WF: wf tid eu1):
    wf tid eu2.
  Proof.
    inv STEP. eapply state_step0_wf; eauto. refl.
  Qed.

  Lemma promise_step_wf
        tid eu1 eu2
        (STEP: promise_step tid eu1 eu2)
        (WF: wf tid eu1):
    wf tid eu2.
  Proof.
    destruct eu1 as [state1 local1 mem1].
    destruct eu2 as [state2 local2 mem2].
    inv WF. inv STEP. ss. subst. econs; ss.
    - inv LOCAL0. inv MEM2.
      apply ExecUnit.rmap_append_wf. ss.
    - eapply ExecUnit.promise_wf; eauto.
  Qed.

  Lemma step_wf
        tid eu1 eu2
        (STEP: step tid eu1 eu2)
        (WF: wf tid eu1):
    wf tid eu2.
  Proof.
    inv STEP.
    - eapply state_step_wf; eauto.
    - eapply promise_step_wf; eauto.
  Qed.

  Variant le (eu1 eu2:t): Prop :=
  | le_intro
      mem'
      (LC: Local.le eu1.(local) eu2.(local))
      (MEM: eu2.(mem) = eu1.(mem) ++ mem')
  .

  Global Program Instance le_partial_order: PreOrder le.
  Next Obligation.
    econs.
    - refl.
    - rewrite app_nil_r. ss.
  Qed.
  Next Obligation.
    ii. inv H1. inv H2. econs; etrans; eauto.
    rewrite MEM, app_assoc. eauto.
  Qed.

  Lemma state_step0_incr
        n tid e1 e2 eu1 eu2
        (STEP: state_step0 n tid e1 e2 eu1 eu2):
    le eu1 eu2.
  Proof.
    inv STEP. econs.
    - eauto using RMWLocal.step_incr.
    - rewrite app_nil_r. ss.
  Qed.

  Lemma state_step_incr
        n tid eu1 eu2
        (STEP: state_step n tid eu1 eu2):
    le eu1 eu2.
  Proof.
    inv STEP. inv STEP0. econs.
    - eapply RMWLocal.step_incr. eauto.
    - rewrite MEM, app_nil_r. ss.
  Qed.

  Lemma state_step_dmbsy_incr
        n sc tid eu1 eu2
        (STEP: state_step_dmbsy n sc tid eu1 eu2):
    le eu1 eu2.
  Proof.
    inv STEP. inv STEP0. econs.
    - eapply RMWLocal.step_incr. eauto.
    - rewrite MEM, app_nil_r. ss.
  Qed.

  Lemma promise_step_incr
        tid eu1 eu2
        (STEP: promise_step tid eu1 eu2):
    le eu1 eu2.
  Proof.
    inv STEP. econs.
    - eapply Local.promise_incr. eauto.
    - inv LOCAL. inv MEM2. ss.
  Qed.

  Lemma step_incr
        tid eu1 eu2
        (STEP: step tid eu1 eu2):
    le eu1 eu2.
  Proof.
    inv STEP.
    - eapply state_step_incr. eauto.
    - eapply promise_step_incr. eauto.
  Qed.

  Lemma rtc_state_step_incr
        n tid eu1 eu2
        (STEPS: rtc (state_step n tid) eu1 eu2):
    le eu1 eu2.
  Proof.
    induction STEPS; try refl.
    etrans; eauto using state_step_incr.
  Qed.

  Lemma rtc_step_incr
        tid eu1 eu2
        (STEPS: rtc (step tid) eu1 eu2):
    le eu1 eu2.
  Proof.
    induction STEPS; try refl.
    etrans; eauto using step_incr.
  Qed.

  Definition is_terminal (eu: t): Prop :=
    RMWState.is_terminal (state eu) /\ Local.promises (local eu) = bot.

  Lemma state_step0_promises_le
        n tid e1 e2 eu1 eu2
        (STEP: state_step0 n tid e1 e2 eu1 eu2):
    Promises.le eu2.(local).(Local.promises) eu1.(local).(Local.promises).
  Proof.
    inv STEP. eauto using RMWLocal.step_promises_le.
  Qed.

  Lemma state_step_promises_le
        n tid eu1 eu2
        (STEP: state_step n tid eu1 eu2):
    Promises.le eu2.(local).(Local.promises) eu1.(local).(Local.promises).
  Proof.
    inv STEP. eauto using state_step0_promises_le.
  Qed.

  Lemma state_step_dmbsy_promises_le
        n sc tid eu1 eu2
        (STEP: state_step_dmbsy n sc tid eu1 eu2):
    Promises.le eu2.(local).(Local.promises) eu1.(local).(Local.promises).
  Proof.
    inv STEP. eauto using state_step0_promises_le.
  Qed.

  Lemma rtc_state_step_promises_le
        n tid eu1 eu2
        (STEPS: rtc (state_step n tid) eu1 eu2):
    Promises.le eu2.(local).(Local.promises) eu1.(local).(Local.promises).
  Proof.
    induction STEPS; ss.
    etrans; eauto using state_step_promises_le.
  Qed.

  Lemma state_step_rmw_wf
        n tid eu1 eu2
        (STEP: state_step n tid eu1 eu2)
        (WF: RMWLocal.wf tid eu1.(local) eu1.(mem)):
    RMWLocal.wf tid eu2.(local) eu2.(mem).
  Proof.
    inv STEP. inv STEP0.
    rewrite MEM in *.
    eapply RMWLocal.step_wf; eauto.
  Qed.

  Lemma rtc_state_step_rmw_wf
        n tid eu1 eu2
        (STEPS: rtc (state_step n tid) eu1 eu2)
        (WF: RMWLocal.wf tid eu1.(local) eu1.(mem)):
    RMWLocal.wf tid eu2.(local) eu2.(mem).
  Proof.
    induction STEPS;
      eauto using state_step_rmw_wf.
  Qed.

  Lemma promise_step_rmw_wf
        tid eu1 eu2
        (STEP: promise_step tid eu1 eu2)
        (WF: RMWLocal.wf tid eu1.(local) eu1.(mem)):
    RMWLocal.wf tid eu2.(local) eu2.(mem).
  Proof.
    destruct eu1, eu2.
    inv STEP. inv LOCAL. inv MEM2. ss. subst.
    inv WF. econs; ss.
    - ii. revert LOOKUP.
      rewrite Promises.set_o. condtac; ss; i.
      + r in e. subst.
        unfold Memory.get_msg. ss.
        rewrite nth_error_app2; try refl.
        rewrite Nat.sub_diag. ss. esplits; eauto.
      + exploit PRM; eauto. i. des. esplits; eauto.
        unfold Memory.get_msg in *. destruct ts; ss.
        eapply nth_error_app_mon; eauto.
    - i. unfold Memory.get_msg in MSG. destruct ts; ss.
      apply nth_error_app_inv in MSG. des.
      + rewrite Promises.set_o.
        condtac; ss; try nia. eauto.
      + rewrite Promises.set_o.
        condtac; ss; eauto.
        apply nth_error_some in MSG0. ss.
        cut (ts = length mem0); try nia. i. subst. congr.
  Qed.

  Lemma rtc_promise_step_rmw_wf
        tid eu1 eu2
        (STEPS: rtc (promise_step tid) eu1 eu2)
        (WF: RMWLocal.wf tid eu1.(local) eu1.(mem)):
    RMWLocal.wf tid eu2.(local) eu2.(mem).
  Proof.
    induction STEPS;
      eauto using promise_step_rmw_wf.
  Qed.

  Lemma state_step_fulfillable
        n tid eu1 eu2
        (STEP: state_step n tid eu1 eu2)
        (FULFILLABLE: RMWLocal.fulfillable eu2.(local) eu2.(mem)):
    RMWLocal.fulfillable eu1.(local) eu1.(mem).
  Proof.
    inv STEP. inv STEP0.
    rewrite <- MEM in *.
    eapply RMWLocal.step_fulfillable; eauto.
  Qed.

  Lemma rtc_state_step_fulfillable
        n tid eu1 eu2
        (STEPS: rtc (state_step n tid) eu1 eu2)
        (FULFILLABLE: RMWLocal.fulfillable eu2.(local) eu2.(mem)):
    RMWLocal.fulfillable eu1.(local) eu1.(mem).
  Proof.
    induction STEPS;
      eauto using state_step_fulfillable.
  Qed.

  Lemma rtc_state_step_memory
        n tid eu1 eu2
        (STEPS: rtc (state_step n tid) eu1 eu2):
    eu2.(mem) = eu1.(mem).
  Proof.
    induction STEPS; ss.
    inv H1. inv STEP. congr.
  Qed.

  Lemma state_step0_pf_S1
        n tid e1 e2 eu1 eu2
        (STEP: state_step0 (Some n) tid e1 e2 eu1 eu2)
        (NON_PROMISED: Promises.lookup (S n) eu1.(local).(Local.promises) = false):
    state_step0 (Some (S n)) tid e1 e2 eu1 eu2.
  Proof.
    inv STEP. econs; eauto using RMWLocal.step_pf_S1.
  Qed.

  Lemma state_step_pf_S1
        n tid eu1 eu2
        (STEP: state_step (Some n) tid eu1 eu2)
        (NON_PROMISED: Promises.lookup (S n) eu1.(local).(Local.promises) = false):
    state_step (Some (S n)) tid eu1 eu2.
  Proof.
    inv STEP. econs. eauto using state_step0_pf_S1.
  Qed.

  Lemma state_step_dmbsy_over_pf_S1
        n sc tid eu1 eu2
        (STEP: state_step_dmbsy_over (Some n) sc tid eu1 eu2)
        (NON_PROMISED: Promises.lookup (S n) eu1.(local).(Local.promises) = false):
    state_step_dmbsy_over (Some (S n)) sc tid eu1 eu2.
  Proof.
    inv STEP. econs; eauto using state_step0_pf_S1.
  Qed.

  Lemma state_step_dmbsy_exact_pf_S1
        n sc tid eu1 eu2
        (STEP: state_step_dmbsy_exact (Some n) sc tid eu1 eu2)
        (NON_PROMISED: Promises.lookup (S n) eu1.(local).(Local.promises) = false):
    state_step_dmbsy_exact (Some (S n)) sc tid eu1 eu2.
  Proof.
    inv STEP. econs; eauto using state_step0_pf_S1.
  Qed.

  Lemma rtc_state_step_dmbsy_over_pf_S1
        n sc tid eu1 eu2
        (STEPS: rtc (state_step_dmbsy_over (Some n) sc tid) eu1 eu2)
        (NON_PROMISED: Promises.lookup (S n) eu1.(local).(Local.promises) = false):
    rtc (state_step_dmbsy_over (Some (S n)) sc tid) eu1 eu2.
  Proof.
    induction STEPS; try refl.
    exploit state_step_dmbsy_over_pf_S1; eauto. i.
    econs 2; eauto. apply IHSTEPS.
    inv H1. hexploit state_step0_promises_le; try eassumption. i.
    destruct (Promises.lookup (S n) (Local.promises (local y))) eqn:Y; ss.
    exploit H1; eauto.
  Qed.

  Lemma state_step0_pf_S2
        n tid e1 e2 eu1 eu2
        (STEP: state_step0 (Some n) tid e1 e2 eu1 eu2)
        (PROMISED: Promises.lookup (S n) eu2.(local).(Local.promises) = true):
    state_step0 (Some (S n)) tid e1 e2 eu1 eu2.
  Proof.
    inv STEP. econs; eauto using RMWLocal.step_pf_S2.
  Qed.

  Lemma state_step_pf_S2
        n tid eu1 eu2
        (STEP: state_step (Some n) tid eu1 eu2)
        (NON_PROMISED: Promises.lookup (S n) eu2.(local).(Local.promises) = true):
    state_step (Some (S n)) tid eu1 eu2.
  Proof.
    inv STEP. econs. eauto using state_step0_pf_S2.
  Qed.

  Lemma state_step_dmbsy_over_pf_S2
        n sc tid eu1 eu2
        (STEP: state_step_dmbsy_over (Some n) sc tid eu1 eu2)
        (NON_PROMISED: Promises.lookup (S n) eu2.(local).(Local.promises) = true):
    state_step_dmbsy_over (Some (S n)) sc tid eu1 eu2.
  Proof.
    inv STEP. econs; eauto using state_step0_pf_S2.
  Qed.

  Lemma state_step_dmbsy_exact_pf_S2
        n sc tid eu1 eu2
        (STEP: state_step_dmbsy_exact (Some n) sc tid eu1 eu2)
        (NON_PROMISED: Promises.lookup (S n) eu2.(local).(Local.promises) = true):
    state_step_dmbsy_exact (Some (S n)) sc tid eu1 eu2.
  Proof.
    inv STEP. econs; eauto using state_step0_pf_S2.
  Qed.

  Lemma rtc_state_step_dmbsy_over_pf_S2
        n sc tid eu1 eu2
        (STEPS: rtc (state_step_dmbsy_over (Some n) sc tid) eu1 eu2)
        (NON_PROMISED: Promises.lookup (S n) eu2.(local).(Local.promises) = true):
    rtc (state_step_dmbsy_over (Some (S n)) sc tid) eu1 eu2.
  Proof.
    induction STEPS; try refl.
    exploit IHSTEPS; eauto. i.
    econs 2; eauto.
    eapply state_step_dmbsy_over_pf_S2; eauto.
    eapply rtc_state_step_promises_le; try exact NON_PROMISED.
    eapply rtc_mon; try exact STEPS.
    apply dmbsy_over_state_step.
  Qed.
End RMWExecUnit.
End RMWExecUnit.

Module RMWMachine.
  Record t := mk {
    tpool: IdMap.t (RMWState.t (A:=View.t (A:=unit)) * Local.t (A:=unit));
    mem: Memory.t;
  }.
  #[global]
  Hint Constructors t: core.

  Definition init (p:rmw_program): t :=
    mk
      (IdMap.map (fun stmts => (RMWState.init stmts, Local.init)) p)
      Memory.empty.

  Variant is_terminal (m:t): Prop :=
  | is_terminal_intro
      (TERMINAL:
         forall tid st lc
           (FIND: IdMap.find tid m.(tpool) = Some (st, lc)),
           RMWState.is_terminal st /\ lc.(Local.promises) = bot)
  .
  #[global]
  Hint Constructors is_terminal: core.

  Variant no_promise (m:t): Prop :=
  | no_promise_intro
      (PROMISES:
         forall tid st lc
           (FIND: IdMap.find tid m.(tpool) = Some (st, lc)),
           lc.(Local.promises) = bot)
  .
  #[global]
  Hint Constructors no_promise: core.

  Lemma is_terminal_no_promise
        m
        (TERMINAL: is_terminal m):
    no_promise m.
  Proof.
    econs. i. eapply TERMINAL. eauto.
  Qed.

  Variant step (eustep: forall (tid:Id.t) (eu1 eu2:RMWExecUnit.t (A:=unit)), Prop) (m1 m2:t): Prop :=
  | step_intro
      tid st1 lc1 st2 lc2
      (FIND: IdMap.find tid m1.(tpool) = Some (st1, lc1))
      (STEP: eustep tid (RMWExecUnit.mk st1 lc1 m1.(mem)) (RMWExecUnit.mk st2 lc2 m2.(mem)))
      (TPOOL: m2.(tpool) = IdMap.add tid (st2, lc2) m1.(tpool))
  .
  #[global]
  Hint Constructors step: core.

  Lemma rtc_eu_step_step
        eustep tid m st1 lc1 mem1 st2 lc2 mem2
        (FIND: IdMap.find tid m.(tpool) = Some (st1, lc1))
        (MEM: m.(mem) = mem1)
        (EX: rtc (eustep tid)
                 (RMWExecUnit.mk st1 lc1 mem1)
                 (RMWExecUnit.mk st2 lc2 mem2)):
    rtc (step eustep)
        m
        (mk
           (IdMap.add tid (st2, lc2) m.(tpool))
           mem2).
  Proof.
    revert m FIND MEM.
    depind EX.
    { i. subst. destruct m. s. rewrite PositiveMapAdditionalFacts.gsident; ss. refl. }
    destruct y. i. subst. econs.
    - instantiate (1 := mk _ _). econs; ss; eauto.
    - exploit IHEX; eauto.
      + instantiate (1 := mk _ _). s.
        rewrite IdMap.add_spec. condtac; eauto. exfalso. apply c. ss.
      + ss.
      + s. rewrite (IdMap.add_add tid (st2, lc2)). eauto.
  Qed.

  Variant wf (m:t): Prop :=
  | wf_intro
      (WF: forall tid st lc
             (FIND: IdMap.find tid m.(tpool) = Some (st, lc)),
          RMWExecUnit.wf tid (RMWExecUnit.mk st lc m.(mem)))
  .
  #[global]
  Hint Constructors wf: core.

  Lemma init_wf p:
    wf (init p).
  Proof.
    econs. i. ss.
    rewrite IdMap.map_spec in FIND. destruct (IdMap.find tid p); inv FIND.
    econs; ss.
    - econs. i. unfold RMap.find, RMap.init. rewrite IdMap.gempty. ss.
    - apply Local.init_wf.
  Qed.

  Lemma init_no_promise p:
    no_promise (init p).
  Proof.
    econs. s. i.
    revert FIND. rewrite IdMap.map_spec. destruct (IdMap.find tid p); ss. i. inv FIND.
    ss.
  Qed.

  Lemma step_state_step_wf
        n m1 m2
        (STEP: step (RMWExecUnit.state_step n) m1 m2)
        (WF: wf m1):
    wf m2.
  Proof.
    destruct m1 as [tpool1 mem1].
    destruct m2 as [tpool2 mem2].
    inv STEP. inv STEP0. inv WF. econs. ss. subst.
    i. revert FIND0. rewrite IdMap.add_spec. condtac.
    - inversion e0. i. inv FIND0.
      eapply RMWExecUnit.state_step_wf; eauto. econs; eauto.
    - inv STEP. ss. i. subst. exploit WF0; eauto.
  Qed.

  Lemma step_promise_step_wf
        m1 m2
        (STEP: step RMWExecUnit.promise_step m1 m2)
        (WF: wf m1):
    wf m2.
  Proof.
    destruct m1 as [tpool1 mem1].
    destruct m2 as [tpool2 mem2].
    inv STEP. inv STEP0. inv LOCAL. inv MEM2. inv WF. econs. ss. subst.
    i. revert FIND0. rewrite IdMap.add_spec. condtac.
    - inversion e. i. inv FIND0.
      eapply RMWExecUnit.promise_step_wf; eauto. econs; eauto. econs; eauto.
      + econs; eauto.
      + refl.
    - i. exploit WF0; eauto. intro x. inv x. ss. econs; ss.
      + apply ExecUnit.rmap_append_wf. ss.
      + inv LOCAL. econs; eauto.
        all: try rewrite List.app_length; s; try lia.
        * i. rewrite COH. lia.
        * i. destruct (FWDBANK loc0). des. econs; esplits; ss.
          { rewrite TS. apply Memory.latest_ts_append. }
          { apply Memory.read_mon; eauto. }
        * i. exploit EXBANK; eauto. intro Y. inv Y. des.
          econs; esplits; ss.
          { rewrite TS. apply Memory.latest_ts_append. }
          { apply Memory.read_mon. eauto. }
        * i. exploit PROMISES; eauto. lia.
        * i. apply Memory.get_msg_snoc_inv in MSG. des.
          { eapply PROMISES0; eauto. }
          { subst. ss. congr. }
  Qed.

  Lemma rtc_step_promise_step_wf
        m1 m2
        (STEP: rtc (step RMWExecUnit.promise_step) m1 m2)
        (WF: wf m1):
    wf m2.
  Proof.
    revert WF. induction STEP; ss. i. apply IHSTEP.
    eapply step_promise_step_wf; eauto.
  Qed.

  Lemma step_step_wf
        m1 m2
        (STEP: step RMWExecUnit.step m1 m2)
        (WF: wf m1):
    wf m2.
  Proof.
    inv STEP. inv STEP0.
    - eapply step_state_step_wf; eauto.
    - eapply step_promise_step_wf; eauto.
  Qed.

  Lemma rtc_step_step_wf
        m1 m2
        (STEP: rtc (step RMWExecUnit.step) m1 m2)
        (WF: wf m1):
    wf m2.
  Proof.
    revert WF. induction STEP; ss. i. apply IHSTEP.
    eapply step_step_wf; eauto.
  Qed.

  Variant rmw_wf (m:t): Prop :=
  | rmw_wf_intro
      (WF: forall tid st lc
             (FIND: IdMap.find tid m.(tpool) = Some (st, lc)),
          RMWLocal.wf tid lc m.(mem))
  .
  #[global]
  Hint Constructors rmw_wf: core.

  Lemma init_rmw_wf p:
    rmw_wf (init p).
  Proof.
    econs. i. ss.
    rewrite IdMap.map_spec in FIND. destruct (IdMap.find tid p); inv FIND.
    apply RMWLocal.init_wf.
  Qed.

  Lemma step_state_step_rmw_wf
        n m1 m2
        (STEP: step (RMWExecUnit.state_step n) m1 m2)
        (WF: rmw_wf m1):
    rmw_wf m2.
  Proof.
    destruct m1 as [tpool1 mem1].
    destruct m2 as [tpool2 mem2].
    inv STEP. inv WF. econs. ss. subst.
    i. revert FIND0. rewrite IdMap.add_spec. condtac.
    - r in e. i. inv FIND0.
      exploit (RMWExecUnit.state_step_rmw_wf (A:=unit)); eauto.
    - inv STEP0. inv STEP. ss. subst. eauto.
  Qed.

  Lemma step_promise_step_rmw_wf
        m1 m2
        (STEP: step RMWExecUnit.promise_step m1 m2)
        (WF: rmw_wf m1):
    rmw_wf m2.
  Proof.
    destruct m1 as [tpool1 mem1].
    destruct m2 as [tpool2 mem2].
    inv STEP. inv WF. econs. ss. subst.
    i. revert FIND0. rewrite IdMap.add_spec. condtac.
    - r in e. i. inv FIND0.
      exploit (RMWExecUnit.promise_step_rmw_wf (A:=unit)); eauto.
    - i. apply WF0 in FIND0.
      inv STEP0. inv LOCAL. inv MEM2. ss. subst.
      eapply RMWLocal.interference_wf; eauto.
      econs; ss. unfold proj_sumbool. condtac; ss. congr.
  Qed.

  Lemma rtc_step_promise_step_rmw_wf
        m1 m2
        (STEP: rtc (step RMWExecUnit.promise_step) m1 m2)
        (WF: rmw_wf m1):
    rmw_wf m2.
  Proof.
    revert WF. induction STEP; ss. i. apply IHSTEP.
    eapply step_promise_step_rmw_wf; eauto.
  Qed.

  Lemma step_step_rmw_wf
        m1 m2
        (STEP: step RMWExecUnit.step m1 m2)
        (WF: rmw_wf m1):
    rmw_wf m2.
  Proof.
    inv STEP. inv STEP0.
    - eapply step_state_step_rmw_wf; eauto.
    - eapply step_promise_step_rmw_wf; eauto.
  Qed.

  Lemma rtc_step_step_rmw_wf
        m1 m2
        (STEP: rtc (step RMWExecUnit.step) m1 m2)
        (WF: rmw_wf m1):
    rmw_wf m2.
  Proof.
    revert WF. induction STEP; ss. i. apply IHSTEP.
    eapply step_step_rmw_wf; eauto.
  Qed.

  Lemma step_mon
        (eustep1 eustep2: _ -> _ -> _ -> Prop)
        (EUSTEP: forall tid m1 m2, eustep1 tid m1 m2 -> eustep2 tid m1 m2):
    forall m1 m2, step eustep1 m1 m2 -> step eustep2 m1 m2.
  Proof.
    i. inv H. econs; eauto.
  Qed.

  Lemma rtc_step_mon
        (eustep1 eustep2: _ -> _ -> _ -> Prop)
        (EUSTEP: forall tid m1 m2, eustep1 tid m1 m2 -> eustep2 tid m1 m2):
    forall m1 m2, rtc (step eustep1) m1 m2 -> rtc (step eustep2) m1 m2.
  Proof.
    i. induction H; eauto. econs; eauto. eapply step_mon; eauto.
  Qed.

  Variant exec (p:rmw_program) (m:t): Prop :=
  | exec_intro
      (STEP: rtc (step RMWExecUnit.step) (init p) m)
      (NOPROMISE: no_promise m)
  .
  #[global]
  Hint Constructors exec: core.

  Variant state_exec (m1 m2:t): Prop :=
  | state_exec_intro
      (TPOOL: IdMap.Forall2
                (fun tid sl1 sl2 =>
                   rtc (RMWExecUnit.state_step None tid)
                       (RMWExecUnit.mk (fst sl1) (snd sl1) m1.(mem))
                       (RMWExecUnit.mk (fst sl2) (snd sl2) m1.(mem)))
                m1.(tpool) m2.(tpool))
      (MEM: m1.(mem) = m2.(mem))
  .

  Variant pf_exec (p:rmw_program) (m:t): Prop :=
  | pf_exec_intro
      m1
      (STEP1: rtc (step RMWExecUnit.promise_step) (init p) m1)
      (STEP2: state_exec m1 m)
      (NOPROMISE: no_promise m)
  .
  #[global]
  Hint Constructors pf_exec: core.

  Variant equiv (m1 m2:t): Prop :=
  | equiv_intro
      (TPOOL: IdMap.Equal m1.(tpool) m2.(tpool))
      (MEM: m1.(mem) = m2.(mem))
  .

  Lemma equiv_no_promise
        m1 m2
        (EQUIV: equiv m1 m2)
        (NOPROMISE: no_promise m1):
    no_promise m2.
  Proof.
    inv EQUIV. inv NOPROMISE. econs. i.
    specialize (TPOOL tid). rewrite FIND in TPOOL.
    eapply PROMISES. eauto.
  Qed.

  Lemma unlift_step_state_step
        n m1 m2 tid st1 lc1
        (STEPS: rtc (step (RMWExecUnit.state_step n)) m1 m2)
        (TPOOL: IdMap.find tid m1.(tpool) = Some (st1, lc1)):
    exists st2 lc2,
      <<TPOOL: IdMap.find tid m2.(tpool) = Some (st2, lc2)>> /\
      <<STEPS: rtc (RMWExecUnit.state_step n tid)
                   (RMWExecUnit.mk st1 lc1 m1.(mem))
                   (RMWExecUnit.mk st2 lc2 m2.(mem))>>.
  Proof.
    revert st1 lc1 TPOOL. induction STEPS; eauto. i.
    destruct x as [tpool1 mem1].
    destruct y as [tpool2 mem2].
    destruct z as [tpool3 mem3].
    inv H. ss.
    assert (mem2 = mem1).
    { inv STEP. inv STEP0. ss. }
    subst. exploit IHSTEPS.
    { rewrite IdMap.add_spec, TPOOL.
      instantiate (1 := if equiv_dec tid tid0 then lc2 else lc1).
      instantiate (1 := if equiv_dec tid tid0 then st2 else st1).
      condtac; ss.
    }
    i. des.
    esplits; eauto. rewrite <- STEPS0. condtac; eauto.
    inversion e. subst. rewrite TPOOL in FIND. inv FIND. econs; eauto.
  Qed.

  Lemma step_get_msg_tpool
        p m ts msg
        (STEPS: rtc (step RMWExecUnit.step) (init p) m)
        (MSG: Memory.get_msg ts m.(mem) = Some msg):
    exists sl, IdMap.find msg.(Msg.tid) m.(tpool) = Some sl.
  Proof.
    apply clos_rt_rt1n_iff in STEPS.
    apply clos_rt_rtn1_iff in STEPS.
    revert ts msg MSG. induction STEPS; ss.
    { destruct ts; ss. destruct ts; ss. }
    destruct y as [tpool1 mem1].
    destruct z as [tpool2 mem2].
    ss. inv H. ss. i. inv STEP.
    - rewrite IdMap.add_spec. condtac; eauto.
      inv STEP0. inv STEP. ss. subst. eauto.
    - rewrite IdMap.add_spec. condtac; eauto.
      inv STEP0. ss. subst. inv LOCAL. inv MEM2.
      apply Memory.get_msg_snoc_inv in MSG. des; eauto. subst.
      ss. congr.
  Qed.

  Definition promises_from_mem
             (tid:Id.t) (mem: Memory.t): Promises.t.
  Proof.
    induction mem using list_rev_rect.
    - exact bot.
    - destruct x.
      apply (if tid0 == tid
             then Promises.set (S (List.length (List.rev mem0))) IHmem
             else IHmem).
  Defined.

  Lemma promises_from_mem_nil tid:
    promises_from_mem tid Memory.empty = bot.
  Proof.
    unfold promises_from_mem, list_rev_rect, eq_rect. ss.
    match goal with
    | [|- context[match ?c with | eq_refl => _ end]] => destruct c
    end; ss.
  Qed.

  Lemma promises_from_mem_snoc tid mem msg:
    promises_from_mem tid (mem ++ [msg]) =
    if msg.(Msg.tid) == tid
    then Promises.set (S (List.length mem)) (promises_from_mem tid mem)
    else promises_from_mem tid mem.
  Proof.
    unfold promises_from_mem at 1, list_rev_rect, eq_rect.
    match goal with
    | [|- context[match ?c with | eq_refl => _ end]] => destruct c
    end; ss.
    rewrite List.rev_involutive, List.rev_app_distr. ss.
    destruct msg. s. condtac.
    - inversion e. subst. rewrite ? List.rev_length.
      f_equal.
      unfold promises_from_mem, list_rev_rect, eq_rect.
      match goal with
      | [|- context[match ?c with | eq_refl => _ end]] => destruct c
      end; ss.
    - unfold promises_from_mem, list_rev_rect, eq_rect.
      match goal with
      | [|- context[match ?c with | eq_refl => _ end]] => destruct c
      end; ss.
  Qed.

  Lemma promises_from_mem_inv
        ts tid mem
        (LOOKUP: Promises.lookup (S ts) (promises_from_mem tid mem)):
    exists loc val, List.nth_error mem ts = Some (Msg.mk loc val tid).
  Proof.
    revert LOOKUP. induction mem using List.rev_ind.
    { rewrite promises_from_mem_nil, Promises.lookup_bot. ss. }
    rewrite promises_from_mem_snoc. condtac.
    { rewrite Promises.set_o. condtac.
      - inversion e. inversion e0. subst.
        rewrite List.nth_error_app2; [|lia].
        rewrite Nat.sub_diag. ss.
        destruct x. esplits; eauto.
      - i. exploit IHmem; eauto.  i. des.
        rewrite List.nth_error_app1; eauto.
        apply List.nth_error_Some. congr.
    }
    i. exploit IHmem; eauto.  i. des.
    rewrite List.nth_error_app1; eauto.
    apply List.nth_error_Some. congr.
  Qed.

  Lemma promises_from_mem_lookup
        mem ts loc val tid
        (GET: List.nth_error mem ts = Some (Msg.mk loc val tid)):
    Promises.lookup (S ts) (promises_from_mem tid mem).
  Proof.
    revert GET. induction mem using List.rev_ind.
    { i. apply List.nth_error_In in GET. inv GET. }
    rewrite promises_from_mem_snoc. condtac.
    - rewrite Promises.set_o. condtac.
      + inversion e. inversion e0. subst.
        rewrite List.nth_error_app2; [|lia].
        rewrite Nat.sub_diag. ss.
      + i. apply IHmem.
        erewrite <- List.nth_error_app1; eauto.
        assert (H: ts < List.length (mem0 ++ [x])).
        { rewrite <- List.nth_error_Some. ii. congr. }
        rewrite List.app_length in H.
        rewrite Nat.add_1_r in H. inv H; try lia.
        exfalso. apply c. ss.
    - i. apply IHmem.
      destruct (Nat.eq_dec ts (List.length mem0)) eqn:Heq.
      + inv Heq. rewrite List.nth_error_app2 in GET; try lia.
        rewrite Nat.sub_diag in GET. ss. inv GET. ss.
        exfalso. apply c. ss.
      + rewrite List.nth_error_app1 in GET; auto.
        assert (H: ts < List.length (mem0 ++ [x])).
        { rewrite <- List.nth_error_Some. ii. congr. }
        rewrite List.app_length in H.
        rewrite Nat.add_1_r in H. inv H; try lia; congr.
  Qed.

  Lemma promises_from_mem_spec
        ts tid mem:
    Promises.lookup (S ts) (promises_from_mem tid mem) <->
    exists loc val, List.nth_error mem ts = Some (Msg.mk loc val tid).
  Proof.
    induction mem using List.rev_ind.
    { econs.
      - rewrite promises_from_mem_nil, Promises.lookup_bot. ss.
      - i. des. destruct ts; ss.
    }
    rewrite promises_from_mem_snoc. econs.
    - condtac.
      + inversion e. subst. rewrite Promises.set_o. condtac.
        * inversion e0. subst. i.
          rewrite List.nth_error_app2, Nat.sub_diag; [|lia]. ss.
          destruct x. ss. eauto.
        * intro Y. apply IHmem in Y. des.
          esplits; eauto. apply nth_error_app_mon. eauto.
      + intro Y. apply IHmem in Y. des.
        esplits; eauto. apply nth_error_app_mon. eauto.
    - i. des. apply nth_error_snoc_inv in H. des; ss.
      { condtac; eauto. rewrite Promises.set_o. condtac; eauto. }
      subst. condtac; ss; [|congr]. rewrite Promises.set_o. condtac; [|congr]. ss.
  Qed.

  Definition init_with_promises (p:rmw_program) (mem:Memory.t): t :=
    mk
      (IdMap.mapi (fun tid stmts =>
                     (RMWState.init stmts,
                      Local.init_with_promises (promises_from_mem tid mem)))
                  p)
      mem.

  Lemma pf_init_with_promises
        p promises
        (MEM: forall msg (MSG: List.In msg promises), IdMap.find msg.(Msg.tid) p <> None):
    exists m,
      <<STEP: rtc (step RMWExecUnit.promise_step) (init p) m>> /\
      <<TPOOL: IdMap.Equal m.(tpool) (init_with_promises p promises).(tpool)>> /\
      <<MEM: m.(mem) = promises>>.
  Proof.
    revert MEM. induction promises using List.rev_ind; i.
    { esplits; eauto. ii. s. rewrite IdMap.map_spec, IdMap.mapi_spec.
      destruct (IdMap.find y p); ss.
      unfold Local.init, Local.init_with_promises. repeat f_equal.
      rewrite promises_from_mem_nil. ss.
    }
    exploit IHpromises; eauto.
    { i. apply MEM. apply List.in_app_iff. intuition. }
    i. des. subst. destruct x.
    hexploit MEM.
    { apply List.in_app_iff. right. left. eauto. }
    match goal with
    | [|- context[(?f <> None) -> _]] => destruct f eqn:FIND
    end; ss.
    intro X. clear X.
    eexists (mk _ _). esplits.
    - etrans; [eauto|]. econs 2; [|refl].
      econs.
      + rewrite TPOOL, IdMap.mapi_spec, FIND. ss.
      + econs; ss.
      + ss.
    - s. ii. rewrite IdMap.add_spec. condtac; ss.
      + inversion e. subst. rewrite IdMap.mapi_spec, FIND. s.
        unfold Local.init_with_promises. repeat f_equal.
        rewrite promises_from_mem_snoc. condtac; ss.
      + rewrite TPOOL, ? IdMap.mapi_spec. destruct (IdMap.find y p); ss.
        unfold Local.init_with_promises. rewrite promises_from_mem_snoc. s.
        condtac; ss. congr.
    - ss.
  Qed.

  Lemma rtc_promise_step_spec
        p m
        (STEP: rtc (step RMWExecUnit.promise_step) (init p) m):
    IdMap.Equal m.(tpool) (init_with_promises p m.(mem)).(tpool).
  Proof.
    apply clos_rt_rt1n_iff in STEP.
    apply clos_rt_rtn1_iff in STEP.
    induction STEP.
    { s. ii. rewrite IdMap.map_spec, IdMap.mapi_spec.
      destruct (IdMap.find y p); ss. f_equal. f_equal.
      rewrite promises_from_mem_nil. ss.
    }
    destruct y as [tpool2 mem2].
    destruct z as [tpool3 mem3].
    ss. inv H. inv STEP0. inv LOCAL. ss. subst. inv MEM2.
    ii. generalize (IHSTEP y). rewrite IdMap.add_spec, ? IdMap.mapi_spec.
    rewrite promises_from_mem_snoc. s.
    repeat condtac; try congr.
    inversion e. subst. rewrite FIND. destruct (IdMap.find tid p); ss. i. inv H. ss.
  Qed.

  Definition promised_memory (m: t): Prop :=
    forall ts msg (GET: Memory.get_msg ts m.(mem) = Some msg),
    exists st lc,
      (<<FIND: IdMap.find msg.(Msg.tid) m.(tpool) = Some (st, lc)>>) /\
      (<<PROMISED: Promises.lookup ts lc.(Local.promises) = true>>).

  Lemma init_promised_memory p: promised_memory (init p).
  Proof.
    ii. ss.
    unfold Memory.get_msg in *. des_ifs.
    exploit nth_error_None. i. des.
    rewrite x1 in GET; ss. nia.
  Qed.

  Lemma promise_step_promised_memory
        m1 m2
        (PROMISED: promised_memory m1)
        (STEP: step RMWExecUnit.promise_step m1 m2):
    promised_memory m2.
  Proof.
    destruct m1 as [tpool1 mem1], m2 as [tpool2 mem2].
    inv STEP. inv STEP0. inv LOCAL. inv MEM2. ss. subst. ii. ss.
    unfold Memory.get_msg in *. destruct ts; ss.
    apply nth_error_app_inv in GET. des.
    - exploit (PROMISED (S ts)); eauto. s. i. des.
      erewrite IdMap.add_spec. condtac; eauto.
      r in e. subst.
      rewrite FIND in *. inv FIND0.
      esplits; eauto. s.
      rewrite Promises.set_o. condtac; ss.
    - exploit nth_error_some; eauto. s. i.
      assert (ts = length mem1) by nia. subst.
      rewrite Nat.sub_diag in *. ss. inv GET0. ss.
      rewrite IdMap.gss. esplits; eauto. s.
      rewrite Promises.set_o. condtac; ss. congr.
  Qed.

  Lemma rtc_promise_step_promised_memory
        m1 m2
        (PROMISED: promised_memory m1)
        (STEP: rtc (step RMWExecUnit.promise_step) m1 m2):
    promised_memory m2.
  Proof.
    induction STEP; ss.
    eauto using promise_step_promised_memory.
  Qed.
End RMWMachine.
