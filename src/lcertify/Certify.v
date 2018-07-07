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
Require Import sflib.
Require Import HahnSets.

Require Import PromisingArch.lib.Basic.
Require Import PromisingArch.lib.Order.
Require Import PromisingArch.lib.Time.
Require Import PromisingArch.lib.Lang.
Require Import PromisingArch.promising.Promising.

Set Implicit Arguments.


Inductive write_step (tid:Id.t) (eu1 eu2:ExecUnit.t (A:=unit)): Prop :=
| write_step_intro
    ex ord vloc vval res e lc
    (EVENT: e = Event.write ex ord vloc vval res)
    (STATE: State.step e eu1.(ExecUnit.state) eu2.(ExecUnit.state))
    (PROMISE: Local.promise vloc.(ValA.val) vval.(ValA.val) tid eu1.(ExecUnit.local) eu1.(ExecUnit.mem) lc eu2.(ExecUnit.mem))
    (FULFILL: Local.fulfill ex ord vloc vval res tid lc eu2.(ExecUnit.mem) eu2.(ExecUnit.local))
.
Hint Constructors write_step.

Inductive certify_step (tid:Id.t) (eu1 eu2:ExecUnit.t (A:=unit)): Prop :=
| certify_step_state
    (STEP: ExecUnit.state_step tid eu1 eu2)
| certify_step_write
    (STEP: write_step tid eu1 eu2)
.
Hint Constructors certify_step.

Inductive certify (tid:Id.t) (eu1:ExecUnit.t (A:=unit)): Prop :=
| certify_intro
    eu2
    (STEPS: rtc (certify_step tid) eu1 eu2)
    (NOPROMISE: eu2.(ExecUnit.local).(Local.promises) = bot)
.
Hint Constructors certify.


Lemma write_step_wf
      tid eu1 eu2
      (STEP: write_step tid eu1 eu2)
      (WF: ExecUnit.wf tid eu1):
  ExecUnit.wf tid eu2.
Proof.
  inv STEP.
  exploit (ExecUnit.promise_step_wf (A:=unit)); [|by eauto|].
  { instantiate (1 := ExecUnit.mk (A:=unit) eu1.(ExecUnit.state) lc eu2.(ExecUnit.mem)).
    econs; ss. eauto.
  }
  i. exploit (ExecUnit.state_step_wf (A:=unit)); eauto. econs. econs; eauto. s.
  econs 3; eauto.
Qed.
Hint Resolve write_step_wf.

Lemma certify_step_wf
      tid eu1 eu2
      (STEP: certify_step tid eu1 eu2)
      (WF: ExecUnit.wf tid eu1):
  ExecUnit.wf tid eu2.
Proof.
  inv STEP.
  - eapply ExecUnit.state_step_wf; eauto.
  - eapply write_step_wf; eauto.
Qed.

Lemma rtc_certify_step_wf
      tid eu1 eu2
      (STEP: rtc (certify_step tid) eu1 eu2)
      (WF: ExecUnit.wf tid eu1):
  ExecUnit.wf tid eu2.
Proof.
  revert WF. induction STEP; ss.
  i. apply IHSTEP. eapply certify_step_wf; eauto.
Qed.


Inductive sim_time (ts:Time.t) (v1 v2:Time.t): Prop :=
| sim_time_intro
    (TS: v2 <= ts -> v1 = v2)
.
Hint Constructors sim_time.

Inductive sim_view (ts:Time.t) (v1 v2:View.t (A:=unit)): Prop :=
| sim_view_intro
    (TS: v2.(View.ts) <= ts -> v1 = v2)
.
Hint Constructors sim_view.

Inductive sim_val (ts:Time.t) (v1 v2:ValA.t (A:=View.t (A:=unit))): Prop :=
| sim_val_intro
    (TS: v2.(ValA.annot).(View.ts) <= ts -> v1 = v2)
.
Hint Constructors sim_val.

Inductive sim_rmap (ts:Time.t) (rmap1 rmap2:RMap.t (A:=View.t (A:=unit))): Prop :=
| sim_rmap_intro
    (RMAP: IdMap.Forall2 (fun _ => sim_val ts) rmap1 rmap2)
.
Hint Constructors sim_rmap.

Inductive sim_state (ts:Time.t) (st1 st2:State.t (A:=View.t (A:=unit))): Prop :=
| sim_state_intro
    (STMTS: st1.(State.stmts) = st2.(State.stmts))
    (RMAP: sim_rmap ts st1.(State.rmap) st2.(State.rmap))
.
Hint Constructors sim_state.

Inductive sim_exbank (tid:Id.t) (ts:Time.t) (mem1 mem2:Memory.t) (eb1 eb2:Exbank.t (A:=unit)): Prop :=
| sim_exbank_intro
    (LOC: eb1.(Exbank.loc) = eb2.(Exbank.loc))
    (TS: sim_time ts eb1.(Exbank.ts) eb2.(Exbank.ts))
    (EBVIEW: sim_view ts eb1.(Exbank.view) eb2.(Exbank.view))
.

Inductive sim_lc (tid:Id.t) (ts:Time.t) (lc1 lc2:Local.t (A:=unit)) (mem1 mem2:Memory.t): Prop :=
| sim_lc_intro
    (COH: forall loc, sim_time ts (lc1.(Local.coh) loc) (lc2.(Local.coh) loc))
    (VRP: sim_view ts lc1.(Local.vrp) lc2.(Local.vrp))
    (VWP: sim_view ts lc1.(Local.vwp) lc2.(Local.vwp))
    (VRM: sim_view ts lc1.(Local.vrm) lc2.(Local.vrm))
    (VWM: sim_view ts lc1.(Local.vwm) lc2.(Local.vwm))
    (VCAP: sim_view ts lc1.(Local.vcap) lc2.(Local.vcap))
    (VREL: sim_view ts lc1.(Local.vrel) lc2.(Local.vrel))
    (FWDBANK: forall loc,
        opt_rel
          (fun fwd1 fwd2 =>
             fwd2.(FwdItem.view).(View.ts) <= ts ->
             Memory.read loc fwd1.(FwdItem.ts) mem1 = Memory.read loc fwd2.(FwdItem.ts) mem2 /\
             sim_view ts fwd1.(FwdItem.view) fwd2.(FwdItem.view) /\
             fwd1.(FwdItem.ex) = fwd2.(FwdItem.ex))
          (lc1.(Local.fwdbank) loc) (lc2.(Local.fwdbank) loc))
    (EXBANK: opt_rel (sim_exbank tid ts mem1 mem2) lc1.(Local.exbank) lc2.(Local.exbank))
    (PROMISES: lc1.(Local.promises) = lc2.(Local.promises))
    (PROMISES_TS: forall mid (FIND: Promises.lookup mid lc2.(Local.promises)), mid <= ts)
.
Hint Constructors sim_lc.

Inductive sim_mem (tid:Id.t) (ts:Time.t) (mem1 mem2:Memory.t): Prop :=
| sim_mem_intro
    (EQUIV: forall tsx (TSX: tsx <= ts), Memory.get_msg tsx mem1 = Memory.get_msg tsx mem2)
.
Hint Constructors sim_mem.

Inductive sim_eu (tid:Id.t) (ts:Time.t) (eu1 eu2:ExecUnit.t (A:=unit)): Prop :=
| sim_eu_intro
    (STATE: sim_state ts eu1.(ExecUnit.state) eu2.(ExecUnit.state))
    (LOCAL: sim_lc tid ts eu1.(ExecUnit.local) eu2.(ExecUnit.local) eu1.(ExecUnit.mem) eu2.(ExecUnit.mem))
    (MEM: sim_mem tid ts eu1.(ExecUnit.mem) eu2.(ExecUnit.mem))
.
Hint Constructors sim_eu.

Lemma sim_time_join
      ts l1 l2 r1 r2
      (VIEW1: sim_time ts l1 r1)
      (VIEW2: sim_time ts l2 r2):
  sim_time ts (join l1 l2) (join r1 r2).
Proof.
  inv VIEW1. inv VIEW2.
  econs. intro X. unfold join, Time.join in X. apply Time.max_lub_iff in X. des.
  eauto.
Qed.

Lemma sim_val_const
      ts c:
  sim_val ts (ValA.mk _ c bot) (ValA.mk _ c bot).
Proof.
  econs. ss.
Qed.

Lemma sim_view_bot
      ts:
  sim_view ts bot bot.
Proof.
  econs. ss.
Qed.

Lemma sim_view_const
      ts c:
  sim_view ts (View.mk c bot) (View.mk c bot).
Proof.
  econs. ss.
Qed.

Lemma sim_view_join
      ts l1 l2 r1 r2
      (VIEW1: sim_view ts l1 r1)
      (VIEW2: sim_view ts l2 r2):
  sim_view ts (join l1 l2) (join r1 r2).
Proof.
  destruct l1 as [lt1 lv1].
  destruct l2 as [lt2 lv2].
  destruct r1 as [rt1 rv1].
  destruct r2 as [rt2 rv2].
  inv VIEW1. inv VIEW2. ss.
  econs. s. intro X. unfold join, Time.join in X. apply Time.max_lub_iff in X. des.
  specialize (TS X). specialize (TS0 X0). des. inv TS. inv TS0. ss.
Qed.

Lemma sim_view_ifc
      ts c l1 r1
      (VIEW1: sim_view ts l1 r1):
  sim_view ts (ifc c l1) (ifc c r1).
Proof.
  destruct c; ss.
Qed.

Lemma sim_val_view ts v1 v2
      (VAL: sim_val ts v1 v2):
  sim_view ts v1.(ValA.annot) v2.(ValA.annot).
Proof.
  inv VAL. econs. i. specialize (TS H). des. subst. ss.
Qed.

Lemma sim_rmap_expr
      ts rmap1 rmap2 e
      (RMAP: sim_rmap ts rmap1 rmap2):
  sim_val ts (sem_expr rmap1 e) (sem_expr rmap2 e).
Proof.
  induction e; s.
  - apply sim_val_const.
  - unfold RMap.find. inv RMAP. specialize (RMAP0 reg). inv RMAP0; ss.
  - econs. s. i. inv IHe. specialize (TS H). des. congr.
  - econs. s. i. unfold join, Time.join in H. apply Time.max_lub_iff in H. des.
    inv IHe1. inv IHe2.
    specialize (TS H). specialize (TS0 H0). des. congr.
Qed.

Lemma sim_rmap_add
      ts rmap1 rmap2 v1 v2 r
      (RMAP: sim_rmap ts rmap1 rmap2)
      (VAL: sim_val ts v1 v2):
  sim_rmap ts (RMap.add r v1 rmap1) (RMap.add r v2 rmap2).
Proof.
  inv RMAP. econs. ii. unfold RMap.add. rewrite ? IdMap.add_spec.
  condtac; ss. inversion e. subst. econs. ss.
Qed.

(* TODO: move *)
Lemma internal_bot_inv
      A `{orderC A eq}
      lc1 lc2
      (LC: Local.internal (A:=A) bot lc1 lc2):
  lc2 = lc1.
Proof.
  inv LC. destruct lc1. s. f_equal.
  rewrite bot_join; ss. apply View.order.
Qed.

Lemma sim_eu_step
      tid ts eu1 eu2 eu2'
      (SIM: sim_eu tid ts eu1 eu2)
      (STEP: certify_step tid eu2 eu2')
      (WF1: ExecUnit.wf tid eu1)
      (WF2: ExecUnit.wf tid eu2):
      (* TODO: remove *)
      (* (VWP: eu2'.(ExecUnit.local).(Local.vwp).(View.ts) <= ts) *)
      (* (VCAP: eu2'.(ExecUnit.local).(Local.vcap).(View.ts) <= ts): *)
  exists eu1',
    <<STEP: certify_step tid eu1 eu1'>> /\
    <<SIM: sim_eu tid ts eu1' eu2'>>.
Proof.
  exploit certify_step_wf; eauto. i.
  destruct eu1 as [[stmts1 rmap1] lc1 mem1].
  destruct eu2 as [[stmts2 rmap2] lc2 mem2].
  destruct eu2' as [[stmts2' rmap2'] lc2' mem2'].
  inv SIM. inv STATE. ss. subst. inv STEP; cycle 1.
  { (* write step *)
    admit.
  }
  { (* state step *)
    inv STEP0. inv STEP. ss. subst. inv STATE; inv LOCAL0; inv EVENT.
    - (* skip *)
      apply internal_bot_inv in LC. subst.
      eexists (ExecUnit.mk _ _ _). esplits.
      + econs 1. econs. econs; ss; cycle 1.
        * econs 1; eauto. econs; eauto.
        * s. econs 1.
      + econs; ss. econs; ss; try by apply LOCAL.
        rewrite bot_join; [|by apply View.order]. apply LOCAL.
    - (* assign *)
      apply internal_bot_inv in LC. subst.
      eexists (ExecUnit.mk _ _ _). esplits.
      + econs 1. econs. econs; ss; cycle 1.
        * econs 1; eauto. econs; eauto.
        * s. econs 2. ss.
      + econs; ss. econs; ss; try by apply LOCAL.
        * apply sim_rmap_add; ss. apply sim_rmap_expr. ss.
        * rewrite bot_join; [|by apply View.order]. destruct lc1. ss.
    - (* read *)



              (* TODO: move *)
              Lemma sim_view_eq
                    ts v1 v2
                    (SIM: sim_view ts v1 v2)
                    (V2: v2.(View.ts) <= ts):
                v1 = v2.
              Proof.
                apply SIM. ss.
              Qed.
              Lemma sim_time_eq
                    ts v1 v2
                    (SIM: sim_time ts v1 v2)
                    (V2: v2 <= ts):
                v1 = v2.
              Proof.
                apply SIM. ss.
              Qed.

              
      inv STEP.
      match goal with
      | [|- context[join (joins ?l) ?f]] =>
        remember (join (joins l) f) as post eqn:POST
      end.
      destruct (le_dec post.(View.ts) ts).
      { (* read's post-view <= ts. *)
        rename l into TS0.
        exploit sim_rmap_expr; eauto. i. inv x1. exploit TS.
        { rewrite <- TS0. s. rewrite <- join_l, <- join_l. eauto. }
        intro ELOC. clear TS.
        


        eexists (ExecUnit.mk _ _ _). esplits.
        + econs 1. econs. econs; ss; cycle 1.
          * econs 2; eauto. econs.
            4: instantiate (1 :=
                              match Local.fwdbank lc2 (ValA.val (sem_expr rmap2 eloc)) with
                              | Some fwd => 
                              ts0).
            1: instantiate (1 := (sem_expr rmap1 eloc)).
            all: ss.
            { rewrite ELOC. exploit sim_time_eq.
              { inv LOCAL. eapply COH0. }
              { rewrite <- TS0. admit. }
              intro COH'. rewrite COH'. ss.
            }
            { admit. (* latest *) }
            {
              (* TODO: move *)
              Lemma sim_mem_read
                    tid ts mem1 mem2 loc ts0
                    (SIM: sim_mem tid ts mem1 mem2)
                    (TS0: ts0 <= ts):
                Memory.read loc ts0 mem1 = Memory.read loc ts0 mem2.
              Proof.
                inv SIM. generalize (EQUIV _ TS0). unfold Memory.get_msg, Memory.read. destruct ts0; ss.
                intro X. rewrite X. ss.
              Qed.

              rewrite ELOC,  <- MSG. revert TS0.
              destruct (Local.fwdbank lc2 (ValA.val (sem_expr rmap2 eloc))) as [[]|] eqn:FWD; cycle 1.
              { i. eapply sim_mem_read; eauto. rewrite <- TS0, <- join_r. ss. }
              unfold FwdItem.read_view. s. condtac; cycle 1.
              { i. eapply sim_mem_read; eauto. rewrite <- TS0, <- join_r. ss. }
              i. destruct (equiv_dec ts1 ts0); ss. inv e.
              inv LOCAL. specialize (FWDBANK (ValA.val (sem_expr rmap2 eloc))). inv FWDBANK; [congr|].
              rewrite FWD in H. inv H. ss. exploit REL.
              { rewrite <- TS0, <- join_r. ss. }
              i. des.
              unfold FwdItem.read_view. ss. 
              
              ; s; cycle 1.
              { rewrite <- TS0, <- join_r. ss. }
              
              { rewrite <- TS0, <- join_r. ss. }
              inv e. 

inv WF2. inv LOCAL0. ss. exploit FWDBANK; eauto. s. i. des.
              rewrite x. inv LOCAL. apply COH1. 
                

  FWD : Local.fwdbank lc2 (ValA.val (sem_expr rmap2 eloc)) =
        Some {| FwdItem.ts := ts1; FwdItem.view := view; FwdItem.ex := ex |}
                
              - rewrite <- join_r. ss.
            }
              inv MEM. specialize (MEM (S ts0).
              admit. }
          * econs 3; ss.
        + econs; ss.
          * admit.
          * admit.
      }
      { (* read's post-view > ts. *)
        admit.
      }
      (*       1, 2, 3: eauto. *)
      (*       econs; eauto. *)
      (*     * s. econs 2. ss. *)
      (*   + econs; ss. econs; ss; try by apply LOCAL. *)
      (*     * apply sim_rmap_add; ss. apply sim_rmap_expr. ss. *)
      (*     * rewrite bot_join; [|by apply View.order]. destruct lc1. ss. *)

      (*   eexists (ExecUnit.mk _ _ _). esplits; [econs 2; [|econs 1]|]. *)
      (*   - left. econs; ss. *)
      (*     assert (ELOC: sem_expr rmap1 eloc = sem_expr rmap2 eloc). *)
      (*     { eapply sim_rmap_expr; eauto. rewrite <- VCAP, <- join_r. refl. } *)
      (*     econs; ss; cycle 1. *)
      (*     + econs 2; eauto. econs. *)
      (*       4: instantiate (1 := ts0). *)
      (*       1: instantiate (1 := (sem_expr rmap1 eloc)). *)
      (*       all: ss. *)
      (*       all: rewrite ELOC. *)
      (*       * inv LOCAL0. specialize (COH0 (ValA.val (sem_expr rmap2 eloc))). inv COH0. *)
      (*         rewrite TS; ss. etrans; eauto. *)
      (*       * admit. (* hard: coh <= ts0, so no additional messages *) *)
      (*       * rewrite <- MSG. inv MEM. unfold Memory.read. destruct ts0; ss. *)
      (*         rewrite ? nth_error_app1; ss. *)
      (*     + econs 3; ss. *)
      (*   - econs; ss. econs; ss. *)
      (*     + admit. (* sim_state *) *)
      (*     + admit. (* sim_lc *) *)
      (* } *)
      (* { (* read from new msg. *) *)
      (*   admit. *)
      (* } *)
    - (* fulfill *)
      inv STEP.
      assert (TS0: ts0 <= ts).
      { inv WRITABLE. inv LOCAL. exploit PROMISES_TS; eauto. }
      exploit sim_rmap_expr; eauto. i. inv x1. exploit TS.
      { rewrite <- TS0. inv WRITABLE. etrans; [|by apply Time.lt_le_incl; eauto].
        s. rewrite <- join_l. eauto.
      }
      intro ELOC. clear TS.
      exploit sim_rmap_expr; eauto. i. inv x1. exploit TS.
      { rewrite <- TS0. inv WRITABLE. etrans; [|by apply Time.lt_le_incl; eauto].
        s. rewrite <- join_r, <- join_l. eauto.
      }
      intro EVAL. clear TS.
      eexists (ExecUnit.mk _ _ _). esplits.
      + econs 1. econs. econs; ss; cycle 1.
        * econs 3; eauto. econs; eauto; cycle 1.
          { rewrite <- MSG. apply MEM. ss. }
          { inv LOCAL. rewrite PROMISES. eauto. }
          { instantiate (1 := view_ext).
            instantiate (1 := ord).
            instantiate (1 := ex0).
            inv WRITABLE. econs; eauto.
            - symmetry. eapply sim_view_eq; cycle 1.
              { etrans; [by apply Time.lt_le_incl; eauto|]. eauto. }
              s. repeat apply sim_view_join; ss.
              all: try apply sim_view_ifc.
              all: try by apply LOCAL.
              inv LOCAL. inv EXBANK; ss. inv REL. ss.
            - exploit sim_time_eq.
              { inv LOCAL. eapply COH0. }
              { etrans; [by apply Time.lt_le_incl; eauto|]. eauto. }
              i. congr.
            - admit. (* exclusive on old message *)
          }
        * econs 4; ss.
      + econs; ss; eauto using sim_rmap_add, sim_val_const.
        inv LOCAL. econs; ss; i.
        all: repeat rewrite fun_add_spec.
        all: repeat apply sim_view_join; ss.
        * condtac; ss.
        * condtac; ss. econs. s. splits; ss.
        * destruct ex0; ss.
        * congr.
        * revert FIND. rewrite Promises.unset_o. condtac; ss. eauto.
    - (* write_failure *)
      inv STEP. eexists (ExecUnit.mk _ _ _). esplits.
      + econs 1. econs. econs; ss; cycle 1.
        * econs 4; eauto. econs; eauto.
        * econs 4; ss.
      + econs; ss. econs; ss; eauto using sim_rmap_add, sim_val_const.
        inv LOCAL. econs; ss.
    - (* isb *)
      inv STEP. eexists (ExecUnit.mk _ _ _). esplits.
      + econs 1. econs. econs; ss; cycle 1.
        * econs 5; eauto. econs; eauto.
        * econs 5.
      + econs; ss. inv LOCAL. econs; eauto using sim_view_join.
    - (* dmb *)
      inv STEP. eexists (ExecUnit.mk _ _ _). esplits.
      + econs 1. econs. econs; ss; cycle 1.
        * econs 6; eauto. econs; eauto.
        * econs 5.
      + econs; ss. inv LOCAL. econs; eauto 10 using sim_view_join, sim_view_ifc.
    - (* if *)
      inv LC. eexists (ExecUnit.mk _ _ _). esplits.
      + econs 1. econs. econs; ss; cycle 1.
        * econs 1; eauto. econs; eauto.
        * econs 6; ss.
      + exploit sim_rmap_expr; eauto. i. inv x1. exploit TS.
        { rewrite <- VCAP. apply join_r. }
        intro ELOC. econs; ss.
        { econs; ss. rewrite ELOC. ss. }
        econs; ss; try by apply LOCAL.
        apply sim_view_join; try by apply LOCAL.
        rewrite x. ss.
    - (* dowhile *)
      apply internal_bot_inv in LC. subst.
      eexists (ExecUnit.mk _ _ _). esplits.
      + econs 1. econs. econs; ss; cycle 1.
        * econs 1; eauto. econs; eauto.
        * econs 7. ss.
      + econs; ss. econs; ss; try by apply LOCAL.
        rewrite bot_join; [|by apply View.order]. apply LOCAL.
  }
Admitted.
      


Lemma sim_certify
      tid eu1 eu2
      (STATE: True)
      (CERTIFY: certify tid eu1):
  certify tid eu2.
Proof.
Admitted.