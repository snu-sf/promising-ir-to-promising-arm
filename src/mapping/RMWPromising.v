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

Require Import PromisingArch.lib.Basic.
Require Import PromisingArch.lib.Order.
Require Import PromisingArch.lib.Time.
Require Import PromisingArch.lib.Lang.

Require Import PromisingArch.promising.Promising.

Require Import PromisingArch.mapping.RMWLang.

Set Implicit Arguments.


Section Eqts.
  Context `{A: Type, B: Type, _: orderC A eq, _: orderC B eq}.

  Inductive eqts_rmw_event: forall (e1:RMWEvent.t (A:=View.t (A:=A))) (e2:RMWEvent.t (A:=View.t (A:=B))), Prop :=
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
      b:
      eqts_rmw_event (RMWEvent.barrier b) (RMWEvent.barrier b)
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

  Inductive step (event:RMWEvent.t (A:=View.t (A:=A))) (tid:Id.t) (mem:Memory.t) (lc1 lc2:Local.t (A:=A)): Prop :=
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
  | step_fadd
      ordr ordw vloc vold vnew ts_old ts_new res lc1' view_pre lc1''
      (EVENT: event = RMWEvent.fadd ordr ordw vloc vold vnew)
      (STEP_READ: Local.read true ordr vloc vold ts_old lc1 mem lc1')
      (STEP_FULFILL: Local.fulfill true ordw vloc vnew res ts_new tid view_pre lc1' mem lc1'')
      (STEP_CONTROL: Local.control vold.(ValA.annot) lc1'' lc2)
  | step_isb
      (EVENT: event = RMWEvent.barrier Barrier.isb)
      (STEP: Local.isb lc1 lc2)
  | step_dmb
      rr rw wr ww
      (EVENT: event = RMWEvent.barrier (Barrier.dmb rr rw wr ww))
      (STEP: Local.dmb rr rw wr ww lc1 lc2)
  | step_control
      ctrl
      (EVENT: event = RMWEvent.control ctrl)
      (LC: Local.control ctrl lc1 lc2)
  .
  #[local]
  Hint Constructors step: core.

  Lemma step_incr
        e tid mem lc1 lc2
        (LC: step e tid mem lc1 lc2):
    Local.le lc1 lc2.
  Proof.
    inv LC; try refl.
    - eapply Local.read_incr. eauto.
    - eapply Local.fulfill_incr. eauto.
    - hexploit Local.read_incr; eauto. i.
      hexploit Local.fulfill_incr; eauto. i.
      hexploit Local.control_incr; eauto. i.
      do 2 (etrans; eauto).
    - eapply Local.isb_incr. eauto.
    - eapply Local.dmb_incr. eauto.
    - eapply Local.control_incr. eauto.
  Qed.

  Lemma step_promises_le
        e tid mem lc1 lc2
        (STEP: step e tid mem lc1 lc2):
    Promises.le (Local.promises lc2) (Local.promises lc1).
  Proof.
    inv STEP; ss; try by (inv STEP0; ss).
    - inv STEP0. ss. apply Promises.unset_le.
    - inv STEP_READ. inv STEP_FULFILL. inv STEP_CONTROL. ss.
      apply Promises.unset_le.
    - inv LC. ss.
  Qed.
End RMWLocal.
End RMWLocal.


Module RMWExecUnit.
Section RMWExecUnit.
  Context `{A: Type, _: orderC A eq}.

  Inductive t := mk {
    state: RMWState.t (A:=View.t (A:=A));
    local: Local.t (A:=A);
    mem: Memory.t;
  }.
  #[local]
  Hint Constructors t: core.

  Inductive state_step0 (tid:Id.t) (e1 e2:RMWEvent.t (A:=View.t (A:=A))) (eu1 eu2:t): Prop :=
  | state_step0_intro
      (STATE: RMWState.step e1 eu1.(state) eu2.(state))
      (LOCAL: RMWLocal.step e2 tid eu1.(mem) eu1.(local) eu2.(local))
      (MEM: eu2.(mem) = eu1.(mem))
  .
  #[local]
  Hint Constructors state_step0: core.

  Inductive state_step (tid:Id.t) (eu1 eu2:t): Prop :=
  | state_step_intro
      e
      (STEP: state_step0 tid e e eu1 eu2)
  .
  #[local]
  Hint Constructors state_step: core.

  Definition is_dmbsy (e: RMWEvent.t (A:=View.t (A:=A))): bool :=
    match e with
    | RMWEvent.barrier (Barrier.dmb true true true true) => true
    | _ => false
    end.

  Inductive state_step_dmbsy (n: Time.t) (tid:Id.t) (eu1 eu2:t): Prop :=
  | state_step_dmbsy_intro
      e
      (STEP: state_step0 tid e e eu1 eu2)
      (DMBSY: is_dmbsy e -> le n eu1.(local).(Local.vro).(View.ts) /\
                            le n eu1.(local).(Local.vwo).(View.ts))
  .
  #[local]
  Hint Constructors state_step_dmbsy: core.

  Inductive promise_step (tid:Id.t) (eu1 eu2:t): Prop :=
  | promise_step_intro
      loc val ts
      (STATE: eu1.(state) = eu2.(state))
      (LOCAL: Local.promise loc val ts tid eu1.(local) eu1.(mem) eu2.(local) eu2.(mem))
  .
  #[local]
  Hint Constructors promise_step: core.

  Inductive step (tid:Id.t) (eu1 eu2:t): Prop :=
  | step_state (STEP: state_step tid eu1 eu2)
  | step_promise (STEP: promise_step tid eu1 eu2)
  .
  #[local]
  Hint Constructors step: core.

  Inductive wf (tid:Id.t) (eu:t): Prop :=
  | wf_intro
      (STATE: ExecUnit.rmap_wf eu.(mem) eu.(state).(RMWState.rmap))
      (LOCAL: Local.wf tid eu.(mem) eu.(local))
  .
  #[local]
  Hint Constructors wf: core.

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

  Lemma state_step_dmbsy_wf n tid eu1 eu2
        (STEP: state_step_dmbsy n tid eu1 eu2)
        (WF: wf tid eu1):
    wf tid eu2.
  Proof.
    inv STEP. eapply state_step0_wf; eauto. refl.
  Qed.

  Lemma promise_step_wf tid eu1 eu2
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

  Lemma step_wf tid eu1 eu2
        (STEP: step tid eu1 eu2)
        (WF: wf tid eu1):
    wf tid eu2.
  Proof.
    inv STEP.
    - eapply state_step_wf; eauto.
    - eapply promise_step_wf; eauto.
  Qed.

  Inductive le (eu1 eu2:t): Prop :=
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
        tid e1 e2 eu1 eu2
        (STEP: state_step0 tid e1 e2 eu1 eu2):
    le eu1 eu2.
  Proof.
    inv STEP. econs.
    - eauto using RMWLocal.step_incr.
    - rewrite app_nil_r. ss.
  Qed.

  Lemma state_step_incr tid eu1 eu2
        (STEP: state_step tid eu1 eu2):
    le eu1 eu2.
  Proof.
    inv STEP. inv STEP0. econs.
    - eapply RMWLocal.step_incr. eauto.
    - rewrite MEM, app_nil_r. ss.
  Qed.

  Lemma state_step_dmbsy_incr n tid eu1 eu2
        (STEP: state_step_dmbsy n tid eu1 eu2):
    le eu1 eu2.
  Proof.
    inv STEP. inv STEP0. econs.
    - eapply RMWLocal.step_incr. eauto.
    - rewrite MEM, app_nil_r. ss.
  Qed.

  Lemma promise_step_incr tid eu1 eu2
        (STEP: promise_step tid eu1 eu2):
    le eu1 eu2.
  Proof.
    inv STEP. econs.
    - eapply Local.promise_incr. eauto.
    - inv LOCAL. inv MEM2. ss.
  Qed.

  Lemma step_incr tid eu1 eu2
        (STEP: step tid eu1 eu2):
    le eu1 eu2.
  Proof.
    inv STEP.
    - eapply state_step_incr. eauto.
    - eapply promise_step_incr. eauto.
  Qed.

  Definition is_terminal (eu: t): Prop :=
    RMWState.is_terminal (state eu) /\ Local.promises (local eu) = bot.

  Lemma state_step0_promises_le
        tid e1 e2 eu1 eu2
        (STEP: state_step0 tid e1 e2 eu1 eu2):
    Promises.le eu2.(local).(Local.promises) eu1.(local).(Local.promises).
  Proof.
    inv STEP. eauto using RMWLocal.step_promises_le.
  Qed.

  Lemma state_step_promises_le
        tid eu1 eu2
        (STEP: state_step tid eu1 eu2):
    Promises.le eu2.(local).(Local.promises) eu1.(local).(Local.promises).
  Proof.
    inv STEP. eauto using state_step0_promises_le.
  Qed.

  Lemma state_step_dmbsy_promises_le
        n tid eu1 eu2
        (STEP: state_step_dmbsy n tid eu1 eu2):
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
End RMWExecUnit.
End RMWExecUnit.

Module RMWMachine.
  Inductive t := mk {
    tpool: IdMap.t (RMWState.t (A:=View.t (A:=unit)) * Local.t (A:=unit));
    mem: Memory.t;
  }.
  #[global]
  Hint Constructors t: core.

  Definition init (p:rmw_program): t :=
    mk
      (IdMap.map (fun stmts => (RMWState.init stmts, Local.init)) p)
      Memory.empty.

  Inductive is_terminal (m:t): Prop :=
  | is_terminal_intro
      (TERMINAL:
         forall tid st lc
           (FIND: IdMap.find tid m.(tpool) = Some (st, lc)),
           RMWState.is_terminal st /\ lc.(Local.promises) = bot)
  .
  #[global]
  Hint Constructors is_terminal: core.

  Inductive no_promise (m:t): Prop :=
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

  Inductive step (eustep: forall (tid:Id.t) (eu1 eu2:RMWExecUnit.t (A:=unit)), Prop) (m1 m2:t): Prop :=
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

  Inductive wf (m:t): Prop :=
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
        m1 m2
        (STEP: step RMWExecUnit.state_step m1 m2)
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

  Inductive exec (p:rmw_program) (m:t): Prop :=
  | exec_intro
      (STEP: rtc (step RMWExecUnit.step) (init p) m)
      (NOPROMISE: no_promise m)
  .
  #[global]
  Hint Constructors exec: core.

  Inductive state_exec (m1 m2:t): Prop :=
  | state_exec_intro
      (TPOOL: IdMap.Forall2
                (fun tid sl1 sl2 =>
                   rtc (RMWExecUnit.state_step tid)
                       (RMWExecUnit.mk (fst sl1) (snd sl1) m1.(mem))
                       (RMWExecUnit.mk (fst sl2) (snd sl2) m1.(mem)))
                m1.(tpool) m2.(tpool))
      (MEM: m1.(mem) = m2.(mem))
  .

  Inductive pf_exec (p:rmw_program) (m:t): Prop :=
  | pf_exec_intro
      m1
      (STEP1: rtc (step RMWExecUnit.promise_step) (init p) m1)
      (STEP2: state_exec m1 m)
      (NOPROMISE: no_promise m)
  .
  #[global]
  Hint Constructors pf_exec: core.

  Inductive equiv (m1 m2:t): Prop :=
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
        m1 m2 tid st1 lc1
        (STEPS: rtc (step RMWExecUnit.state_step) m1 m2)
        (TPOOL: IdMap.find tid m1.(tpool) = Some (st1, lc1)):
    exists st2 lc2,
      <<TPOOL: IdMap.find tid m2.(tpool) = Some (st2, lc2)>> /\
      <<STEPS: rtc (RMWExecUnit.state_step tid)
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
End RMWMachine.
