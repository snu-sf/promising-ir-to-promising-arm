Require Import NArith.
Require Import PArith.
Require Import ZArith.
Require Import Lia.
Require Import EquivDec.
Require Import RelationClasses.
Require Import Bool.

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
Require Import PromisingArch.mapping.PStoRMWUtils.
Require Import PromisingArch.mapping.PStoRMWDef.
Require Import PromisingArch.mapping.PStoRMWThread.

Set Implicit Arguments.
Set Nested Proofs Allowed.


Module PStoRMWConsistent.
  Import PStoRMWThread.

  Definition sim_val_cons (n: Time.t) (val_ps: Const.t) (val_arm: ValA.t (A:=View.t (A:=unit))): Prop :=
    le val_arm.(ValA.annot).(View.ts) n -> sim_val val_ps val_arm.(ValA.val).

  Definition sim_regs_cons (n: Time.t) (regs_ps: RegFile.t) (regs_arm: RMap.t (A:=View.t (A:=unit))): Prop :=
    forall r, sim_val_cons n (IdentFun.find r regs_ps) (RMap.find r regs_arm).

  Variant sim_state_cons (n: Time.t) (st_ps: State.t) (st_arm: RMWState.t (A:=View.t (A:=unit))): Prop :=
    | sim_state_cons_intro
        (STMTS: RMWState.stmts st_arm = ps_to_rmw_stmts (State.stmts st_ps))
        (REGS: sim_regs_cons n st_ps.(State.regs) st_arm.(RMWState.rmap))
  .
  #[export] Hint Constructors sim_state: core.

  Definition read_ts (fwd: FwdItem.t (A:=unit)) (ts: Time.t): Time.t :=
    if fwd.(FwdItem.ts) == ts
    then fwd.(FwdItem.view).(View.ts)
    else ts.

  Variant sim_memory_cons (tid: Ident.t) (n: Time.t)
    (lc_ps: PSLocal.t) (gprm_ps: BoolMap.t) (mem_ps: PSMemory.t)
    (lc_arm: Local.t (A:=unit)) (mem_arm: Memory.t): Prop :=
    | sim_memory_intro
        (PRM_SOUND: forall ts (PROMISED_ARM: Promises.lookup ts lc_arm.(Local.promises)),
          exists msg_arm loc_ps from,
            (<<GET_ARM: Memory.get_msg ts mem_arm = Some msg_arm>>) /\
            (<<TID: msg_arm.(Msg.tid) = tid>>) /\
            (<<LOC: msg_arm.(Msg.loc) = Zpos loc_ps>>) /\
            (<<RESERVED: Memory.get loc_ps (ntt ts) (PSLocal.reserves lc_ps) = Some (from, Message.reserve)>>) /\
            (<<PROMISED_PS: le ts n -> lc_ps.(PSLocal.promises) loc_ps = true>>))
        (PRM_COMPLETE: forall loc (PROMISED_PS: lc_ps.(PSLocal.promises) loc = true),
          exists ts msg_arm,
            (<<LE: le ts n>>) /\
            (<<PROMISED_ARM: Promises.lookup ts lc_arm.(Local.promises)>>) /\
            (<<GET_ARM: Memory.get_msg ts mem_arm = Some msg_arm>>) /\
            (<<LOC: msg_arm.(Msg.loc) = Zpos loc>>))
        (MEM_SOUND: forall ts msg_arm
                           (GET_ARM: Memory.get_msg ts mem_arm = Some msg_arm),
          exists loc_ps from msg_ps,
            (<<LOC: msg_arm.(Msg.loc) = Zpos loc_ps>>) /\
            (<<GET_PS: PSMemory.get loc_ps (ntt ts) mem_ps = Some (from, msg_ps)>>) /\
            (<<TS: PSTime.lt from (ntt ts)>>) /\
            (__guard__ (
               (<<FROM: from = PSTime.bot>>) \/
               exists fts fval ftid,
                 (<<FROM: from = ntt fts>>) /\
                 (<<GET_FROM_ARM: Memory.get_msg fts mem_arm = Some (Msg.mk msg_arm.(Msg.loc) fval ftid)>>) /\
                 (<<EMPTY: empty_loc msg_arm.(Msg.loc) fts ts mem_arm>>))) /\
            (__guard__ (
               (<<MSG: msg_ps = Message.reserve>>) /\
               (<<PROMISED_ARM: Promises.lookup ts lc_arm.(Local.promises) <-> msg_arm.(Msg.tid) = tid>>) /\
               (<<PROMISED: le ts n ->
                            (<<GPROMISED: gprm_ps loc_ps = true>>) /\
                            (<<PROMISED_PS: lc_ps.(PSLocal.promises) loc_ps <-> msg_arm.(Msg.tid) = tid>>)>>) \/
               exists val_ps released na,
                 (<<MSG: msg_ps = Message.message val_ps released na>>) /\
                 (<<VAL: le (read_ts (lc_arm.(Local.fwdbank) msg_arm.(Msg.loc)) ts) n ->
                         sim_val val_ps msg_arm.(Msg.val)>>) /\
                 (<<PROMISED_ARM: Promises.lookup ts lc_arm.(Local.promises) = false>>))))
        (MEM_COMPLETE: forall loc_ps from to msg_ps
                              (TO: PSTime.lt PSTime.bot to)
                              (GET_PS: PSMemory.get loc_ps to mem_ps = Some (from, msg_ps)),
          (exists tts,
              (<<TO: to = ntt tts>>) /\
              (<<MSG_PS: msg_ps = Message.reserve>>) /\
              (<<OUT: forall ts msg_arm
                        (LE: le tts ts)
                        (GET_ARM: Memory.get_msg ts mem_arm = Some msg_arm),
                  msg_arm.(Msg.loc) <> Zpos loc_ps>>)) \/
          exists ts msg_arm,
            (<<TO: to = ntt ts>>) /\
            (<<GET_ARM: Memory.get_msg ts mem_arm = Some msg_arm>>) /\
            (<<LOC: msg_arm.(Msg.loc) = Zpos loc_ps>>))
        (FWD: forall loc loc_ps ts
                (LOC: loc = Zpos loc_ps)
                (FWD: (lc_arm.(Local.fwdbank) loc).(FwdItem.ts) = ts),
            exists from val released na,
              (<<CUR: PSTime.le (ntt ts) (lc_ps.(Local.tview).(TView.cur).(View.rlx) loc_ps)>>) /\
              (<<GET_PS: PSMemory.get loc_ps (ntt ts) mem_ps = Some (from, Message.message val released na)>>) /\
              (<<REL_FWD: if (lc_arm.(Local.fwdbank) loc).(FwdItem.ex)
                          then forall loc, PSTime.le
                                        ((PSView.unwrap released).(View.rlx) loc)
                                        (ntt (View.ts (join (join lc_arm.(Local.vrn) lc_arm.(Local.vro))
                                                            (lc_arm.(Local.coh) (Zpos loc)))))
                          else PSView.le (View.unwrap released) (lc_ps.(PSLocal.tview).(PSTView.rel) loc_ps)>>))
        (RELEASED: forall loc from to val released na
                          (GET: PSMemory.get loc to mem_ps = Some (from, Message.message val released na)),
          forall loc', PSTime.le ((View.unwrap released).(View.rlx) loc') to)
  .

  Variant sim_thread_cons (tid: Ident.t) (n: Time.t)
    (th_ps: PSThread.t lang_ps) (eu: RMWExecUnit.t (A:=unit)): Prop :=
    | sim_thread_cons_intro
        (SIM_STATE: sim_state_cons n (PSThread.state th_ps) (RMWExecUnit.state eu))
        (SIM_TVIEW: sim_tview (PSLocal.tview (PSThread.local th_ps)) (RMWExecUnit.local eu))
        (SIM_MEM: sim_memory_cons tid n
                                  (PSThread.local th_ps)
                                  (PSGlobal.promises (PSThread.global th_ps))
                                  (PSGlobal.memory (PSThread.global th_ps))
                                  (RMWExecUnit.local eu) (RMWExecUnit.mem eu))
  .

  Lemma sim_regs_cons_eval_expr
        n regs_ps regs_arm e
        (SIM: sim_regs_cons n regs_ps regs_arm):
    sim_val_cons n (RegFile.eval_expr regs_ps e) (sem_expr regs_arm (ps_to_rmw_expr e)).
  Proof.
    induction e; ss.
    - ii. exploit IHe; eauto. i.
      destruct op. ss. inv x0; ss.
      condtac; econs.
    - ii. ss.
      exploit IHe1; [etrans; eauto; apply join_l|]. i.
      exploit IHe2; [etrans; eauto; apply join_r|]. i.
      destruct op; inv x0; inv x1; ss.
  Qed.

  Lemma sim_regs_cons_add
        n regs_ps regs_arm
        r val_ps (val_arm: ValA.t (A:=View.t (A:=unit)))
        (SIM: sim_regs_cons n regs_ps regs_arm)
        (VAL: sim_val_cons n val_ps val_arm):
    sim_regs_cons n (IdentFun.add r val_ps regs_ps)
                  (RMap.add r val_arm regs_arm).
  Proof.
    ii. rewrite IdentFun.add_spec, RMap.add_o.
    condtac; ss; subst.
    - condtac; try congr.
      revert H. rewrite RMap.add_o. condtac; ss.
    - condtac; ss. apply SIM.
      revert H. rewrite RMap.add_o. condtac; ss.
  Qed.

  (* Lemma sim_state_step *)
  (*       st1_ps st1_arm e_arm st2_arm *)
  (*       (SIM1: sim_state st1_ps st1_arm) *)
  (*       (STEP: RMWState.step e_arm st1_arm st2_arm): *)
  (*   exists e_ps st2_ps, *)
  (*     (<<STEP_PS: State.step e_ps st1_ps st2_ps>>) /\ *)
  (*     (<<EVENT: sim_program_event e_ps e_arm>>) /\ *)
  (*     (<<SIM2: sim_state st2_ps st2_arm>>). *)
  (* Proof. *)
  (*   destruct st1_ps as [regs1_ps stmts1_ps]. *)
  (*   destruct st1_arm as [stmts1_arm regs1_arm]. *)
  (*   destruct st2_arm as [stmts2_arm regs2_arm]. *)
  (*   inv SIM1. ss. *)
  (*   destruct stmts1_ps; ss; subst; [inv STEP|]. *)
  (*   destruct t; ss; cycle 1. *)
  (*   { (* ite *) *)
  (*     inv STEP. condtac. *)
  (*     - esplits; [econs 2|..]; ss. *)
  (*       + des_ifs. *)
  (*         exploit sim_regs_eval_expr; eauto. *)
  (*         rewrite Heq. ii. inv x0. congr. *)
  (*       + econs; ss. rewrite <- List.map_app. ss. *)
  (*     - esplits; [econs 3|..]; ss. *)
  (*       + des_ifs. *)
  (*         exploit sim_regs_eval_expr; eauto. *)
  (*         rewrite Heq. ii. inv x0. congr. *)
  (*       + econs; ss. rewrite <- List.map_app. ss. *)
  (*   } *)
  (*   { (* dowhile *) *)
  (*     inv STEP. esplits; [econs 4|..]; ss. *)
  (*     econs; ss. unfold ps_to_rmw_stmts. *)
  (*     rewrite List.map_app. ss. *)
  (*   } *)

  (*   destruct i; ss; inv STEP. *)
  (*   { (* skip *) *)
  (*     esplits; [econs 1; econs 1|..]; ss. *)
  (*   } *)
  (*   { (* assign *) *)
  (*     esplits; [econs 1; econs 2|..]; ss. *)
  (*     econs; ss. *)
  (*     apply sim_regs_add; ss. *)
  (*     apply sim_regs_eval_expr; ss. *)
  (*   } *)
  (*   { (* load *) *)
  (*     esplits; [econs 1; econs 3|..]; eauto. *)
  (*     econs; ss. *)
  (*     apply sim_regs_add; ss. *)
  (*   } *)
  (*   { (* store *) *)
  (*     esplits; [econs 1; econs 4|..]; eauto. *)
  (*     econs; ss. *)
  (*     apply sim_regs_eval_expr; ss. *)
  (*   } *)
  (*   { (* fadd *) *)
  (*     esplits; [econs 1; econs 5|..]; eauto. *)
  (*     - econs; ss. s. *)
  (*       exploit sim_regs_eval_expr; eauto. i. *)
  (*       inv x0. rewrite <- H0. ss. *)
  (*     - econs; ss. *)
  (*       apply sim_regs_add; ss. *)
  (*   } *)
  (*   { (* dmb *) *)
  (*     esplits; [econs 1; econs 6|..]; eauto. *)
  (*   } *)
  (* Qed. *)

  Lemma sim_memory_cons_latest_le
        tid n lc_ps gprm_ps mem_ps prm_ps mem_arm
        ts loc loc_ps view val ts_ps
        (SIM: sim_memory_cons tid n lc_ps gprm_ps mem_ps prm_ps mem_arm)
        (LOC: loc = Zpos loc_ps)
        (LATEST: Memory.latest loc ts view mem_arm)
        (READ: Memory.read loc ts mem_arm = Some val)
        (LE: PSTime.le ts_ps (ntt view))
        (CLOSED: exists from val released na,
            PSMemory.get loc_ps ts_ps mem_ps = Some (from, Message.message val released na)):
    PSTime.le ts_ps (ntt ts).
  Proof.
    des. destruct (TimeFacts.le_lt_dec ts_ps PSTime.bot).
    { etrans; eauto. apply PSTime.bot_spec. }
    destruct (TimeFacts.le_lt_dec ts_ps (ntt ts)); ss.
    inv SIM. exploit MEM_COMPLETE; eauto. i. des; ss. subst.
    clear PRM_SOUND PRM_COMPLETE MEM_SOUND MEM_COMPLETE RELEASED.
    unfold Memory.get_msg in *. destruct ts0; ss.
    exploit LATEST; try exact GET_ARM; ss.
    - apply ntt_lt. ss.
    - apply ntt_le. ss.
  Qed.

  Lemma sim_tview_cons_readable
        tid n lc_ps gprm_ps mem_ps lc_arm mem_arm
        loc loc_ps ts view_pre val
        ord
        (TVIEW: sim_tview lc_ps.(PSLocal.tview) lc_arm)
        (MEM: sim_memory_cons tid n lc_ps gprm_ps mem_ps lc_arm mem_arm)
        (TVIEW_WF: TView.wf lc_ps.(PSLocal.tview))
        (TVIEW_CLOSED: TView.closed lc_ps.(PSLocal.tview) mem_ps)
        (LOC: loc = Zpos loc_ps)
        (VIEW_PRE: le lc_arm.(Local.vrn) view_pre)
        (LATEST_COH: Memory.latest loc ts (lc_arm.(Local.coh) loc).(View.ts) mem_arm)
        (LATEST_PRE: Memory.latest loc ts view_pre.(View.ts) mem_arm)
        (READ: Memory.read loc ts mem_arm = Some val):
    PSTView.readable (PSTView.cur lc_ps.(PSLocal.tview)) loc_ps (ntt ts) ord.
  Proof.
    cut (PSTime.le (View.rlx (PSTView.cur (PSLocal.tview lc_ps)) loc_ps) (ntt ts)).
    { i. econs; ss. etrans; eauto. apply TVIEW_WF. }
    inv TVIEW. clear REL ACQ.
    specialize (CUR loc_ps). ss.
    eapply sim_memory_cons_latest_le; try exact CUR; eauto.
    - apply Memory.latest_join; ss.
      eapply Memory.latest_mon2; try exact LATEST_PRE. apply VIEW_PRE.
    - inv TVIEW_CLOSED. inv CUR0. specialize (RLX loc_ps). des. eauto.
  Qed.

  Lemma sim_memory_cons_read
        tid n lc_ps gprm_ps mem_ps lc_arm mem_arm
        loc loc_ps ts ord val_arm
        (MEM: sim_memory_cons tid n lc_ps gprm_ps mem_ps lc_arm mem_arm)
        (INHABITED: PSMemory.inhabited mem_ps)
        (LE: le (FwdItem.read_view (Local.fwdbank lc_arm loc) ts ord).(View.ts) n)
        (LOC: loc = Zpos loc_ps)
        (READ: Memory.read loc ts mem_arm = Some val_arm):
    (<<PROMISED_ARM: Promises.lookup ts lc_arm.(Local.promises)>>) \/
    (<<GPROMISED: gprm_ps loc_ps = true>>) /\
    (<<PROMISED: lc_ps.(PSLocal.promises) loc_ps = false>>) \/
    exists from val released na,
      (<<GET_PS: PSMemory.get loc_ps (ntt ts) mem_ps = Some (from, Message.message val released na)>>) /\
      (<<VAL: le (read_ts (lc_arm.(Local.fwdbank) loc) ts) n ->
              sim_val val val_arm>>) /\
      (<<REL_FWD: (lc_arm.(Local.fwdbank) loc).(FwdItem.ts) = ts ->
                  if (lc_arm.(Local.fwdbank) loc).(FwdItem.ex)
                  then forall loc, PSTime.le
                                     ((PSView.unwrap released).(View.rlx) loc)
                                     (ntt (View.ts (join (join lc_arm.(Local.vrn) lc_arm.(Local.vro))
                                                      (lc_arm.(Local.coh) (Zpos loc)))))
                  else PSView.le (View.unwrap released) (lc_ps.(PSLocal.tview).(PSTView.rel) loc_ps)>>).
  Proof.
    unfold Memory.read in *. destruct ts; ss.
    { inv READ. right. right. esplits; eauto.
      condtac; ss; i.
      - apply PSTime.bot_spec.
      - apply PSView.bot_spec.
    }
    revert READ.
    destruct (List.nth_error mem_arm ts) eqn:Heq; ss.
    condtac; ss. destruct t. ss. r in e. i. inv READ. clear X.
    inv MEM. exploit MEM_SOUND; eauto.
    { instantiate (2:=S ts). eauto. }
    s. i. des. inv LOC.
    revert LE. unfold FwdItem.read_view. condtac; ss; i.
    - right. right.
      apply andb_prop in X. des.
      revert X. unfold proj_sumbool.
      condtac; ss. i. r in e.
      exploit FWD; try exact e; eauto. i. des. ss.
      rewrite GET_PS in *. inv GET_PS0.
      esplits; try exact GET_PS0; ss.
      unguardH x0. des; ss. inv MSG. ss.
    - unguardH x0. des; subst.
      + exploit PROMISED; ss. i. des.
        destruct (Id.eq_dec tid0 tid); subst; auto.
        right. left. splits; ss.
        destruct (PSLocal.promises lc_ps loc_ps0) eqn:Y; ss.
        exploit PROMISED_PS; ss.
      + right. right. esplits; eauto. i.
        exploit FWD; eauto. s. i. des.
        rewrite GET_PS0 in *. inv GET_PS. ss.
  Qed.

  Lemma sim_cons_read
        tid n
        lc1_ps gl1_ps
        ord loc
        ex ord_arm (vloc: ValA.t (A:=View.t (A:=unit))) res ts lc1_arm mem_arm lc2_arm
        (TVIEW1: sim_tview (PSLocal.tview lc1_ps) lc1_arm)
        (MEM1: sim_memory_cons tid n lc1_ps (Global.promises gl1_ps) (Global.memory gl1_ps) lc1_arm mem_arm)
        (LC_WF1_PS: PSLocal.wf lc1_ps gl1_ps)
        (GL_WF1_PS: PSGlobal.wf gl1_ps)
        (WF1_ARM: RMWLocal.wf tid lc1_arm mem_arm)
        (ORD: ord_arm = ps_to_rmw_ordr ord)
        (LOC: vloc.(ValA.val) = Zpos loc)
        (READ_VIEW: le (FwdItem.read_view (Local.fwdbank lc1_arm vloc.(ValA.val)) ts ord_arm).(View.ts) n)
        (STEP: Local.read ex ord_arm vloc res ts lc1_arm mem_arm lc2_arm):
    (<<PROMISED_ARM: Promises.lookup ts (Local.promises lc1_arm)>>) \/
    (exists val released lc2_ps,
        (<<STEP_PS: PSLocal.read_step lc1_ps gl1_ps loc (ntt ts) val released ord lc2_ps>>) /\
        (<<VAL: sim_val_cons n val res>>) /\
        (<<TVIEW2: sim_tview (PSLocal.tview lc2_ps) lc2_arm>>) /\
        (<<MEM2: sim_memory_cons tid n lc2_ps (Global.promises gl1_ps) (Global.memory gl1_ps) lc2_arm mem_arm>>)) \/
    (exists val,
        (<<STEP_PS: PSLocal.racy_read_step lc1_ps gl1_ps loc None val ord>>) /\
        (<<VAL: sim_val val res.(ValA.val)>>) /\
        (<<TVIEW2: sim_tview (PSLocal.tview lc1_ps) lc2_arm>>) /\
        (<<MEM2: sim_memory_cons tid n lc1_ps (Global.promises gl1_ps) (Global.memory gl1_ps) lc2_arm mem_arm>>)).
  Proof.
    exploit (Local.read_incr (A:=unit)); eauto. i.
    inv STEP.
    exploit sim_memory_cons_read; eauto; try apply GL_WF1_PS. i. des; auto.
    { (* race with a promise *)
      ss. right. right.
      esplits; eauto.
      - eapply sim_tview_le; try exact TVIEW1; ss; i.
        eapply join_le; try apply View.order; try refl. apply TVIEW1.
      - econs; s; try apply MEM1. i.
        guardH FWD.
        dup MEM1. inv MEM0.
        exploit FWD0; try exact FWD; eauto.
        clear PRM_SOUND PRM_COMPLETE MEM_SOUND MEM_COMPLETE FWD0 RELEASED.
        unguardH FWD. i. des.
        esplits; eauto. condtac; ss. i.
        etrans; [apply REL_FWD|]. apply le_ntt.
        eapply join_le; [apply Time.order|..].
        + eapply join_le; try apply Time.order.
        + unfold fun_add. condtac; ets. ss.
          rewrite e. ss. ets.
    }

    { (* normal read *)
      exploit sim_tview_cons_readable; try exact LATEST; eauto; try apply LC_WF1_PS.
      { apply joins_le. right. left. ss. }
      ss. i. des.
      right. left. esplits.
      { econs; eauto; try refl. }
      { ii. ss. apply VAL.
        etrans; try exact H. etr.
        unfold read_ts, FwdItem.read_view. condtac; ss.
        condtac; try refl. s.
        rewrite <- e. apply WF1_ARM.
      }
      { econs; s; i.
        { (* rel view *)
          etrans; [apply TVIEW1|]. apply le_ntt. ss.
          eapply join_le; try apply Time.order. apply x0.
        }

        { (* cur view *)
          repeat apply PSTime.join_spec.
          { etrans; [apply TVIEW1|]. apply le_ntt. ss.
            eapply join_le; try apply Time.order. apply x0.
          }
          { replace (View.rlx (View.singleton_ur_if (Ordering.le Ordering.relaxed ord) loc (ntt ts)) loc0)
              with (TimeMap.singleton loc (ntt ts) loc0); cycle 1.
            { unfold View.singleton_ur_if. condtac; ss. }
            unfold TimeMap.singleton, LocFun.add, LocFun.init, LocFun.find.
            unfold fun_add. condtac; ss; try apply PSTime.bot_spec.
            subst. rewrite LOC. condtac; ss; try congr. apply le_ntt.
            etrans; [|apply join_r].
            exploit (wf_arm_fwd ts); eauto. i. des; ets.
          }
          { condtac; ss; try apply PSTime.bot_spec.
            unfold FwdItem.read_view. condtac; ss.
            - apply andb_prop in X0. des.
              revert X0. unfold proj_sumbool. condtac; ss. r in e. i. clear X2.
              rewrite negb_true_iff in X1.
              exploit REL_FWD; ss. condtac; i.
              + rewrite andb_true_l in X1.
                apply orb_false_elim in X1. des.
                destruct ord; ss.
              + etrans; [apply x2|].
                etrans; [apply LC_WF1_PS|].
                etrans; [apply TVIEW1|].
                apply le_ntt. ss.
                eapply join_le; try apply Time.order.
                unfold fun_add. condtac; ss.
                rewrite e0. apply join_l.
            - unfold ifc. repeat (condtac; try by destruct ord; ss).
              inv MEM1. exploit RELEASED; eauto. i.
              clear PRM_SOUND PRM_COMPLETE MEM_SOUND MEM_COMPLETE FWD RELEASED.
              etrans; try apply x2. apply le_ntt. ets.
          }
        }

        { (* acq view *)
          repeat apply PSTime.join_spec.
          { etrans; [apply TVIEW1|]. apply le_ntt. ss.
            eapply join_le; [apply Time.order|..]; try apply x0.
            eapply join_le; try apply Time.order.
          }
          { replace (View.rlx (View.singleton_ur_if (Ordering.le Ordering.relaxed ord) loc (ntt ts)) loc0)
              with (TimeMap.singleton loc (ntt ts) loc0); cycle 1.
            { unfold View.singleton_ur_if. condtac; ss. }
            unfold TimeMap.singleton, LocFun.add, LocFun.init, LocFun.find.
            unfold fun_add. condtac; ss; try apply PSTime.bot_spec.
            subst. rewrite LOC. condtac; ss; try congr. apply le_ntt.
            etrans; [|apply join_r].
            exploit (wf_arm_fwd ts); eauto. i. des.
            - etrans; [|apply join_l]. apply x2.
            - etrans; [|apply join_r]. etrans; [|apply join_r]. apply x2.
          }
          { condtac; ss; try apply PSTime.bot_spec.
            unfold FwdItem.read_view. condtac; ss.
            - apply andb_prop in X0. des.
              revert X0. unfold proj_sumbool. condtac; ss. r in e. i. clear X2.
              rewrite negb_true_iff in X1.
              exploit REL_FWD; ss. condtac; i.
              + etrans; [apply x2|]. apply le_ntt.
                eapply join_le; [apply Time.order|..].
                * eapply join_le; try apply Time.order.
                * unfold fun_add. condtac; ss.
                  rewrite e0. apply join_l.
              + etrans; [apply x2|].
                etrans; [apply LC_WF1_PS|].
                etrans; [apply LC_WF1_PS|].
                etrans; [apply TVIEW1|].
                apply le_ntt. ss.
                eapply join_le; [apply Time.order|..].
                * eapply join_le; apply Time.order.
                * unfold fun_add. condtac; ss.
                  rewrite e0. apply join_l.
            - unfold ifc. repeat (condtac; try by destruct ord; ss).
              + inv MEM1. exploit RELEASED; eauto. i.
                clear PRM_SOUND PRM_COMPLETE MEM_SOUND MEM_COMPLETE FWD RELEASED.
                etrans; try apply x2. apply le_ntt. ets.
              + inv MEM1. exploit RELEASED; eauto. i.
                clear PRM_SOUND PRM_COMPLETE MEM_SOUND MEM_COMPLETE FWD RELEASED.
                etrans; try apply x2. apply le_ntt. ets.
          }
        }

        { (* VNEW *)
          eapply join_le; try apply View.order; try refl. apply TVIEW1.
        }
      }

      { inv MEM1. econs; s; eauto. i.
        exploit FWD; eauto. i. des.
        esplits; eauto.
        - etrans; try exact CUR.
          unfold TimeMap.join.
          etrans; [|apply PSTime.join_l].
          apply PSTime.join_l.
        - condtac; ss. i.
          etrans; eauto. i. apply le_ntt.
          eapply join_le; [apply Time.order|..].
          + eapply join_le; try apply Time.order.
          + unfold fun_add. condtac; ss. rewrite e. ets.
      }
    }
  Qed.

  Lemma sim_cons_read_cur
        tid n
        lc1_ps gl1_ps
        ord loc
        ex ord_arm (vloc: ValA.t (A:=View.t (A:=unit))) res ts lc1_arm mem_arm lc2_arm
        (TVIEW1: sim_tview (PSLocal.tview lc1_ps) lc1_arm)
        (MEM1: sim_memory_cons tid n lc1_ps (Global.promises gl1_ps) (Global.memory gl1_ps) lc1_arm mem_arm)
        (LC_WF1_PS: PSLocal.wf lc1_ps gl1_ps)
        (GL_WF1_PS: PSGlobal.wf gl1_ps)
        (WF1_ARM: RMWLocal.wf tid lc1_arm mem_arm)
        (ORD: ord_arm = ps_to_rmw_ordr ord)
        (LOC: vloc.(ValA.val) = Zpos loc)
        (STEP: Local.read ex ord_arm vloc res ts lc1_arm mem_arm lc2_arm):
    exists ts val released lc2_ps,
      (<<CUR: ts = lc1_ps.(PSLocal.tview).(TView.cur).(View.rlx) loc>>) /\
      (<<READ_CUR: PSLocal.read_step lc1_ps gl1_ps loc ts val released ord lc2_ps>>) /\
      (<<TVIEW2: sim_tview (PSLocal.tview lc2_ps) lc2_arm>>) /\
      (<<MEM2: sim_memory_cons tid n lc2_ps (Global.promises gl1_ps) (Global.memory gl1_ps) lc2_arm mem_arm>>).
  Proof.
    dup LC_WF1_PS. inv LC_WF1_PS0. inv TVIEW_CLOSED. inv CUR.
    specialize (RLX loc). des.
    clear TVIEW_WF PROMISES PROMISES_FINITE RESERVES RESERVES_ONLY RESERVES_FINITE REL ACQ PLN.
    assert (TS: PSTime.le (lc1_ps.(PSLocal.tview).(TView.cur).(View.rlx) loc) (ntt ts)).
    { dup MEM1. inv MEM0.
      destruct (TimeFacts.le_lt_dec (lc1_ps.(PSLocal.tview).(TView.cur).(View.rlx) loc) PSTime.bot).
      { etrans; eauto. apply PSTime.bot_spec. }
      exploit MEM_COMPLETE; eauto. i. des; ss.
      clear PRM_SOUND PRM_COMPLETE MEM_SOUND MEM_COMPLETE FWD RELEASED.
      rewrite TO. apply le_ntt.
      inv STEP.
      hexploit Memory.latest_join; [exact LATEST|exact COH|]. i.
      clear LATEST COH.
      exploit Memory.latest_latest_ts; eauto. i.
      etrans; [|apply x0].
      unfold Memory.get_msg in GET_ARM. destruct ts0; ss.
      eapply Memory.latest_ts_read_le.
      - unfold Memory.read. s. rewrite GET_ARM.
        condtac; ss. congr.
      - apply ntt_le. ss. rewrite <- TO.
        etrans; [apply TVIEW1|]. apply le_ntt. s.
        rewrite LOC. apply join_spec; ets.
    }
    exploit (Local.read_incr (A:=unit)); eauto. i.
    esplits; try refl.
    { econs; eauto; try refl.
      econs; try refl. apply LC_WF1_PS.
    }

    { (* tview *)
      inv STEP. ss. econs; s; i.
      { (* rel view *)
        etrans; [apply TVIEW1|]. apply le_ntt. ss.
        eapply join_le; try apply Time.order. apply x0.
      }

      { (* cur view *)
        repeat apply PSTime.join_spec.
        { etrans; [apply TVIEW1|]. apply le_ntt. ss.
          eapply join_le; try apply Time.order. apply x0.
        }
        { replace (View.rlx (View.singleton_ur_if (Ordering.le Ordering.relaxed ord) loc
                               (View.rlx (TView.cur (PSLocal.tview lc1_ps)) loc)) loc0)
            with (TimeMap.singleton loc (View.rlx (TView.cur (PSLocal.tview lc1_ps)) loc) loc0); cycle 1.
          { unfold View.singleton_ur_if. condtac; ss. }
          unfold TimeMap.singleton, LocFun.add, LocFun.init, LocFun.find.
          unfold fun_add. condtac; ss; try apply PSTime.bot_spec.
          subst. rewrite LOC. condtac; ss; try congr.
          etrans; [apply TVIEW1|]. apply le_ntt. ss.
          eapply join_le; try apply join_l. apply Time.order.
        }
        { condtac; ss; try apply PSTime.bot_spec.
          inv MEM1. clear PRM_SOUND PRM_COMPLETE MEM_SOUND MEM_COMPLETE.
          unfold FwdItem.read_view. condtac; ss.
          - apply andb_prop in X0. des.
            revert X0. unfold proj_sumbool. condtac; ss. r in e. i. clear X2.
            rewrite negb_true_iff in X1.
            exploit FWD; try exact e; eauto. i. des. subst.
            assert (TS_EQ: ntt (FwdItem.ts (Local.fwdbank lc1_arm (ValA.val vloc))) =
                           View.rlx (TView.cur (Local.tview lc1_ps)) loc).
            { apply TimeFacts.antisym; ss. }
            rewrite TS_EQ in GET_PS.
            rewrite GET_PS in *. inv RLX.
            revert REL_FWD. condtac; i.
            + rewrite andb_true_l in X1.
              apply orb_false_elim in X1. des.
              destruct ord; ss.
            + etrans; [apply REL_FWD|].
              etrans; [apply LC_WF1_PS|].
              etrans; [apply TVIEW1|].
              apply le_ntt. ss.
              eapply join_le; try apply Time.order.
              unfold fun_add. condtac; ss.
              rewrite e. apply join_l.
          - unfold ifc. repeat (condtac; try by destruct ord; ss).
            exploit RELEASED; eauto. i.
            etrans; [apply x1|].
            etrans; [apply TS|].
            apply le_ntt. ss. ets.
        }
      }

      { (* acq view *)
        repeat apply PSTime.join_spec.
        { etrans; [apply TVIEW1|]. apply le_ntt. ss.
          eapply join_le; [apply Time.order|..]; try apply x0.
          eapply join_le; try apply Time.order.
        }
        { replace (View.rlx (View.singleton_ur_if (Ordering.le Ordering.relaxed ord) loc
                               (View.rlx (TView.cur (PSLocal.tview lc1_ps)) loc)) loc0)
            with (TimeMap.singleton loc (View.rlx (TView.cur (PSLocal.tview lc1_ps)) loc) loc0); cycle 1.
          { unfold View.singleton_ur_if. condtac; ss. }
          unfold TimeMap.singleton, LocFun.add, LocFun.init, LocFun.find.
          unfold fun_add. condtac; ss; try apply PSTime.bot_spec.
          subst. rewrite LOC. condtac; ss; try congr.
          etrans; [exact TS|]. apply le_ntt.
          etrans; [|apply join_r].
          exploit (wf_arm_fwd ts); eauto. i. des.
          - etrans; [|apply join_l]. apply x1.
          - etrans; [|apply join_r]. etrans; [|apply join_r]. apply x1.
        }
        { condtac; ss; try apply PSTime.bot_spec.
          inv MEM1. clear PRM_SOUND PRM_COMPLETE MEM_SOUND MEM_COMPLETE.
          unfold FwdItem.read_view. condtac; ss.
          - apply andb_prop in X0. des.
            revert X0. unfold proj_sumbool. condtac; ss. r in e. i. clear X2.
            rewrite negb_true_iff in X1.
            exploit FWD; try exact e; eauto. i. des. subst.
            assert (TS_EQ: ntt (FwdItem.ts (Local.fwdbank lc1_arm (ValA.val vloc))) =
                           View.rlx (TView.cur (Local.tview lc1_ps)) loc).
            { apply TimeFacts.antisym; ss. }
            rewrite TS_EQ in GET_PS.
            rewrite GET_PS in *. inv RLX.
            revert REL_FWD. condtac; i.
            + etrans; [apply REL_FWD|]. apply le_ntt.
              eapply join_le; [apply Time.order|..].
              * eapply join_le; try apply Time.order.
              * unfold fun_add. condtac; ss.
                rewrite e. apply join_l.
            + etrans; [apply REL_FWD|].
              etrans; [apply LC_WF1_PS|].
              etrans; [apply LC_WF1_PS|].
              etrans; [apply TVIEW1|].
              apply le_ntt. ss.
              eapply join_le; [apply Time.order|..].
              * eapply join_le; apply Time.order.
              * unfold fun_add. condtac; ss.
                rewrite e. apply join_l.
          - exploit RELEASED; eauto. i.
            etrans; [apply x1|].
            etrans; [apply TS|].
            apply le_ntt. unfold ifc.
            repeat (condtac; try by destruct ord; ss); ets.
        }
      }

      { (* vnew *)
        eapply join_le; try apply View.order; try refl. apply TVIEW1.
      }
    }

    { (* memory *)
      inv STEP. ss.
      inv MEM1. econs; s; eauto. i.
      exploit FWD; eauto. i. des.
      esplits; eauto.
      - etrans; try exact CUR.
        unfold TimeMap.join.
        etrans; [|apply PSTime.join_l].
        apply PSTime.join_l.
      - condtac; ss. i.
        etrans; eauto. i. apply le_ntt.
        eapply join_le; [apply Time.order|..].
        + eapply join_le; try apply Time.order.
        + unfold fun_add. condtac; ss. rewrite e. ets.
    }
  Qed.

  Lemma sim_cons_fulfill
        tid n
        lc1_ps gl1_ps
        ord loc val_ps
        (ex: bool) ord_arm (vloc: ValA.t (A:=View.t (A:=unit))) vval res ts view_pre lc1_arm mem_arm lc2_arm
        releasedm
        (TVIEW1: sim_tview (PSLocal.tview lc1_ps) lc1_arm)
        (MEM1: sim_memory_cons tid n lc1_ps (Global.promises gl1_ps) (Global.memory gl1_ps) lc1_arm mem_arm)
        (LC_WF1_PS: PSLocal.wf lc1_ps gl1_ps)
        (GL_WF1_PS: PSGlobal.wf gl1_ps)
        (WF1_ARM: RMWLocal.wf tid lc1_arm mem_arm)
        (ORD: ord_arm = ps_to_rmw_ordw ord)
        (ORD_NA: le ts n -> Ordering.le ord Ordering.na)
        (LOC: vloc.(ValA.val) = Zpos loc)
        (RELEASEDM_WF: View.opt_wf releasedm)
        (RELEASEDM1: if ex
                     then forall loc, PSTime.le
                                        ((PSView.unwrap releasedm).(View.rlx) loc)
                                        (ntt (View.ts (join (join lc1_arm.(Local.vrn) lc1_arm.(Local.vro))
                                                         (lc1_arm.(Local.coh) (Zpos loc)))))
                     else releasedm = None)
        (RELEASEDM2: forall loc', PSTime.le ((View.unwrap releasedm).(View.rlx) loc') (ntt ts))
        (VAL: sim_val_cons n val_ps vval)
        (STEP: Local.fulfill ex ord_arm vloc vval res ts tid view_pre lc1_arm mem_arm lc2_arm):
    exists from lc2_ps gl2_ps,
      (<<CANCEL_PS: PSLocal.cancel_step lc1_ps gl1_ps loc from (ntt ts) lc2_ps gl2_ps>>) /\
      exists released lc3_ps gl3_ps,
        (<<STEP_PS: PSLocal.write_step lc2_ps gl2_ps loc from (ntt ts) val_ps releasedm released ord lc3_ps gl3_ps>>) /\
        (<<TVIEW2: sim_tview (PSLocal.tview lc3_ps) lc2_arm>>) /\
        (<<MEM2: sim_memory_cons tid n lc3_ps (Global.promises gl3_ps) (Global.memory gl3_ps) lc2_arm mem_arm>>).
  Proof.
    exploit (Local.fulfill_incr (A:=unit)); eauto. intro INCR.
    inv STEP. dup MEM1. inv MEM0.
    exploit MEM_SOUND; eauto. s. i. des.
    rewrite LOC in LOC0. symmetry in LOC0. inv LOC0.
    unguardH x0. des; try congr. subst.
    exploit PRM_SOUND; eauto. s. i. des.
    clear PRM_SOUND PRM_COMPLETE MEM_SOUND MEM_COMPLETE FWD RELEASED TID.
    rewrite MSG in *. inv GET_ARM. ss.
    rewrite LOC in LOC0. symmetry in LOC0. inv LOC0.
    dup LC_WF1_PS. inv LC_WF1_PS0.
    exploit RESERVES; eauto. i.
    rewrite GET_PS in x0. symmetry in x0. inv x0.
    clear TVIEW_WF TVIEW_CLOSED PROMISES PROMISES_FINITE RESERVES RESERVES_ONLY RESERVES_FINITE.
    exploit PSMemory.remove_exists; try exact RESERVED. i. des.
    rename mem2 into rsv2.
    exploit PSMemory.remove_exists; try exact GET_PS. i. des.
    destruct lc1_ps as [tview1 prm1 rsv1].
    destruct gl1_ps as [sc1 gprm1 mem1]. ss.
    do 3 eexists. split; [eauto|]. s.

    exploit (@PSMemory.add_exists
               mem2 loc from (ntt ts)
               (Message.message val_ps (TView.write_released tview1 loc (ntt ts) releasedm ord) (Ordering.le ord Ordering.na))); ss.
    { i. revert GET2. erewrite Memory.remove_o; eauto.
      condtac; ss. guardH o. i.
      exploit PSMemory.remove_get0; try exact x2. i. des.
      exploit PSMemory.get_disjoint; [exact GET|exact GET2|]. i. des; ss.
      subst. unguard. des; ss.
    }
    { econs.
      exploit TViewFacts.write_future0; try apply LC_WF1_PS; try exact RELEASEDM_WF. s. i. des.
      apply WF_RELEASED.
    }
    i. des.

    assert (exists prm2 gprm2,
               (<<FULFILL: Promises.fulfill prm1 gprm1 loc ord prm2 gprm2>>) /\
               (<<PROMISED:
                 __guard__ (prm2 loc = true <->
                            exists ts' msg_arm,
                              (<<LE: le ts' n>>) /\
                              (<<PROMISED_ARM: Promises.lookup ts' (Promises.unset ts (Local.promises lc1_arm))>>) /\
                              (<<GET_ARM: Memory.get_msg ts' mem_arm = Some msg_arm>>) /\
                              (<<LOC: msg_arm.(Msg.loc) = Zpos loc>>))>>)).
    { destruct (prm1 loc) eqn:GETP; cycle 1.
      { esplits; [econs 1; eauto|].
        split; i; try congr. des.
        apply Promises.unset_le in H0.
        inv MEM1. exploit PRM_SOUND; try exact H0; try eassumption. s. i. des.
        clear PRM_SOUND PRM_COMPLETE MEM_SOUND MEM_COMPLETE RELEASED.
        rewrite GET_ARM in *. inv H1.
        rewrite LOC0 in *. inv H2. auto.
      }
      destruct (classic (
                    exists ts' msg_arm,
                      le ts' n /\
                      Promises.lookup ts' (Promises.unset ts (Local.promises lc1_arm)) /\
                      Memory.get_msg ts' mem_arm = Some msg_arm /\
                      msg_arm.(Msg.loc) = Zpos loc)).
      - des. esplits; [econs 1; eauto|].
        split; i; ss. esplits; eauto.
      - exploit BoolMap.remove_exists; try exact GETP. i. des.
        exploit BoolMap.remove_exists; try eapply LC_WF1_PS; try exact GETP. s. i. des.
        esplits; [econs 2; eauto|].
        + apply ORD_NA. destruct (le_lt_dec ts n); ss. exfalso.
          inv MEM1. exploit PRM_COMPLETE; eauto. i. des.
          apply H. esplits; try exact LE; eauto.
          rewrite Promises.unset_o. condtac; ss.
          inversion e. subst.
          exploit Nat.le_lt_trans; try apply LE; try exact l. nia.
        + split; i; try congr.
          exploit BoolMap.remove_get0; try exact x4. i. des. congr.
    }
    des.

    esplits.
    { (* step *)
      econs; try exact FULFILL; eauto.
      inv WRITABLE.
      eapply sim_tview_writable; [..|exact COH|exact EXT]; eauto.
      apply joins_le. right. right. right. left. ss.
    }

    { (* sim_tview *)
      s. clear x1 PROMISED PROMISED_PS rsv2 x0 mem2 x2 mem0 x3 prm2 gprm2 FULFILL PROMISED0.
      inv WRITABLE. econs; s; try apply TVIEW1; i.
      { unfold LocFun.add. condtac; ss; cycle 1.
        { etrans; [apply TVIEW1|]. apply le_ntt. ss.
          eapply join_le; try apply Time.order; try refl. apply INCR.
        }
        subst. unfold fun_add. rewrite LOC.
        do 2 (condtac; ss; try congr).
        - rewrite ntt_join. etrans; [|eapply PSTime.join_r].
          apply PSTime.join_spec.
          + etrans; [apply TVIEW1|].
            apply le_ntt. ss. apply join_spec.
            * etrans; try apply TVIEW1.
              etrans; [|apply Nat.lt_le_incl; exact EXT].
              do 3 (etrans; [|apply join_r]). apply join_l.
            * etrans; [apply WF1_ARM|].
              etrans; [|apply Nat.lt_le_incl; exact EXT].
              unfold ifc. do 2 (condtac; try by (destruct ord; ss)).
              do 4 (etrans; [|apply join_r]). ss.
              eapply join_le; try apply Time.order. refl.
          + unfold TimeMap.singleton, LocFun.add.
            condtac; try refl. apply PSTime.bot_spec.
        - apply PSTime.join_spec.
          + etrans; [apply TVIEW1|]. apply le_ntt. ss.
            apply join_spec; try apply join_l.
            rewrite LOC in *.
            etrans; [apply Nat.lt_le_incl; apply COH|].
            apply join_r.
          + rewrite ntt_join. etrans; [|apply PSTime.join_r].
            unfold TimeMap.singleton, LocFun.add.
            condtac; try refl. apply PSTime.bot_spec.
      }

      { rewrite ntt_join. apply PSTime.join_spec.
        - etrans; [apply TVIEW1|]. s. rewrite ntt_join.
          apply PSTime.join_spec; [apply PSTime.join_l|].
          rewrite <- ntt_join. apply le_ntt.
          etrans; [|apply join_r]. apply INCR.
        - unfold TimeMap.singleton, LocFun.add.
          condtac; try apply PSTime.bot_spec.
          subst. unfold fun_add. rewrite LOC. condtac; try congr. s.
          apply PSTime.join_r.
      }
      { rewrite ntt_join. apply PSTime.join_spec.
        - etrans; [apply TVIEW1|]. s. rewrite ntt_join.
          apply PSTime.join_spec; [apply PSTime.join_l|].
          rewrite <- ntt_join. apply le_ntt.
          etrans; [|apply join_r]. apply INCR.
        - unfold TimeMap.singleton, LocFun.add.
          condtac; try apply PSTime.bot_spec.
          subst. unfold fun_add. rewrite LOC. condtac; try congr. s.
          apply PSTime.join_r.
      }
    }

    { (* sim_memory *)
      s. clear INCR. inv MEM1. econs; s; i.
      { (* PRM_SOUND *)
        revert PROMISED_ARM1.
        rewrite Promises.unset_o. condtac; ss. i.
        exploit PRM_SOUND; try exact PROMISED_ARM1. i. des.
        esplits; try eassumption.
        - erewrite Memory.remove_o; eauto. condtac; ss; eauto.
          des. clear X0. apply ntt_inj in a0. subst. congr.
        - i. exploit PROMISED_PS0; try eassumption. i.
          inv FULFILL; ss.
          erewrite BoolMap.remove_o; try eassumption. condtac; ss. subst.
          inv PROMISED0. exploit H1.
          { esplits; try exact H; eauto.
            rewrite Promises.unset_o. condtac; ss.
          }
          i. exploit BoolMap.remove_get0; try exact REMOVE. i. des. congr.
      }
      { (* PRM_COMPLETE *)
        destruct (PSLoc.eq_dec loc0 loc).
        { subst. inv PROMISED0. eauto. }
        exploit (PRM_COMPLETE loc0).
        { inv FULFILL; ss. revert PROMISED_PS0.
          erewrite BoolMap.remove_o; eauto. condtac; ss.
        }
        i. des. esplits; eauto.
        erewrite Promises.unset_o. condtac; ss. inversion e. subst.
        rewrite GET_ARM in *. inv MSG. ss.
        rewrite LOC in *. inv LOC0. ss.
      }

      { (* MEM_SOUND *)
        destruct (Nat.eq_dec ts0 ts); subst.
        - rewrite GET_ARM in *. inv MSG.
          exploit PSMemory.add_get0; try exact x3. i. des.
          esplits; try exact GET0; ss.
          right. esplits; ss.
          { i. apply VAL. etrans; try exact H.
            unfold fun_add. condtac; try congr.
            unfold read_ts; s. condtac; try congr.
            apply join_r.
          }
          { rewrite Promises.unset_o. condtac; ss. congr. }
        - exploit MEM_SOUND; eauto. i. des.
          exploit Memory.remove_get1; try exact GET_PS0; eauto. i. des.
          { apply ntt_inj in x8. congr. }
          exploit Memory.add_get1; try exact x6; eauto. i.
          esplits; eauto. unguardH x4. des; subst.
          + left. splits; ss.
            { erewrite Promises.unset_o. condtac; ss. }
            i. exploit PROMISED1; eauto. i. des.
            inv FULFILL; auto.
            erewrite (@BoolMap.remove_o prm2); try eassumption.
            erewrite (@BoolMap.remove_o gprm2); try eassumption.
            condtac; subst.
            { exploit BoolMap.remove_get0; try exact REMOVE. i. des.
              move PROMISED0 at bottom. inv PROMISED0.
              exploit H1; try congr.
              esplits; try exact H; eauto.
              rewrite Promises.unset_o. condtac; ss. auto.
            }
            splits; auto.
          + right. esplits; eauto.
            { i. apply VAL0. etrans; try exact H.
              unfold fun_add. condtac; ss.
              unfold read_ts at 2. s. condtac; try congr.
              unfold read_ts. condtac; try refl.
              rewrite <- e0.
              apply WF1_ARM.
            }
            { rewrite Promises.unset_o. condtac; ss. }
      }

      { (* MEM_COMPLETE *)
        revert GET_PS0.
        erewrite PSMemory.add_o; eauto. condtac; ss.
        - i. des. inv GET_PS0. right. esplits; eauto.
        - erewrite Memory.remove_o; eauto. condtac; ss. eauto.
      }

      { (* FWD *)
        revert FWD0. unfold fun_add. condtac; ss.
        - i. r in e. clear X. subst.
          rewrite LOC in e. inv e.
          exploit PSMemory.add_get0; try exact x3. i. des.
          esplits; try exact GET0; ss.
          { unfold TimeMap.join, TimeMap.singleton, LocFun.add.
            condtac; ss. apply PSTime.join_r.
          }
          condtac.
          + i. unfold TView.write_released.
            condtac; try apply PSTime.bot_spec. ss.
            apply PSTime.join_spec.
            * etrans; try apply RELEASEDM1. apply le_ntt.
              eapply join_le; [apply Time.order|..]; try refl.
              condtac; ss. rewrite e. inv WRITABLE. nia.
            * unfold LocFun.add. condtac; ss.
              condtac; ss; apply PSTime.join_spec.
              { etrans; [apply LC_WF1_PS|].
                etrans; [apply TVIEW1|].
                apply le_ntt. s.
                eapply join_le; [apply Time.order|..]; try refl.
                condtac; ss. rewrite e0. inv WRITABLE. nia.
              }
              { unfold TimeMap.singleton, LocFun.add, LocFun.init.
                condtac; try apply PSTime.bot_spec. subst.
                rewrite LOC. condtac; ss; try congr.
                apply le_ntt. ets.
              }
              { etrans; [apply LC_WF1_PS|]. s.
                etrans; [apply LC_WF1_PS|]. s.
                etrans; [apply TVIEW1|]. apply le_ntt. s.
                eapply join_le; [apply Time.order|..]; try refl.
                condtac; ss. rewrite e0. inv WRITABLE. nia.
              }
              { unfold TimeMap.singleton, LocFun.add, LocFun.init.
                condtac; try apply PSTime.bot_spec. subst.
                rewrite LOC. condtac; ss; try congr.
                apply le_ntt. ets.
              }
          + subst.
            unfold TView.write_released.
            condtac; ss; try apply View.bot_spec.
            unfold LocFun.add. condtac; ss.
            condtac; ss; apply PSView.join_spec; try apply PSView.bot_spec; try refl.
        - i. exploit FWD; eauto. i. des.
          exploit PSMemory.remove_get1; try exact GET_PS0; eauto. i. des; ss.
          exploit PSMemory.add_get1; try exact x4; eauto. i.
          esplits; try exact x5; ss.
          { etrans; try exact CUR. apply PSTime.join_l. }
          condtac.
          + etrans; try apply REL_FWD. apply le_ntt.
            eapply join_le; [apply Time.order|..]; try refl.
            condtac; ss. rewrite e. inv WRITABLE. nia.
          + etrans; try apply REL_FWD. condtac.
            * unfold LocFun.add. condtac; try refl.
              etrans; [|apply PSView.join_l]. apply LC_WF1_PS.
            * unfold LocFun.add. condtac; try refl.
              subst. apply PSView.join_l.
      }

      { (* RELEASED *)
        revert GET.
        erewrite PSMemory.add_o; eauto. condtac; ss.
        - i. des. inv GET.
          unfold TView.write_released.
          condtac; ss; try apply PSTime.bot_spec.
          apply PSTime.join_spec; ss.
          unfold LocFun.add. condtac; ss.
          condtac; ss; apply PSTime.join_spec.
          + etrans; [apply TVIEW1|]. apply le_ntt. s.
            inv WRITABLE. apply join_spec.
            * etrans; [apply TVIEW1|].
              etrans; [|apply Nat.lt_le_incl; apply EXT]. s.
              do 3 (etrans; [|apply join_r]). apply join_l.
            * etrans; [apply WF1_ARM|].
              etrans; [|apply Nat.lt_le_incl; apply EXT]. s.
              do 4 (etrans; [|apply join_r]).
              unfold ifc. do 2 (condtac; try by (destruct ord; ss)).
              eapply join_le; try apply Time.order. refl.
          + unfold TimeMap.singleton. unfold LocFun.add.
            condtac; try refl. apply PSTime.bot_spec.
          + etrans; [apply TVIEW1|]. apply le_ntt. s.
            inv WRITABLE. apply join_spec.
            * etrans; [|apply Nat.lt_le_incl; apply EXT]. s.
              do 3 (etrans; [|apply join_r]). apply join_l.
            * rewrite LOC in *. apply Nat.lt_le_incl. ss.
          + unfold TimeMap.singleton. unfold LocFun.add.
            condtac; try refl. apply PSTime.bot_spec.
        - erewrite Memory.remove_o; eauto. condtac; ss. eauto.
      }
    }
  Qed.

  Lemma sim_cons_dmb
        tid n
        lc1_ps gl1_ps lc1_arm mem_arm
        ordr ordw
        rr rw wr ww lc2_arm
        (TVIEW1: sim_tview (PSLocal.tview lc1_ps) lc1_arm)
        (SC1: forall loc, PSTime.le (gl1_ps.(PSGlobal.sc) loc) (ntt n))
        (MEM1: sim_memory_cons tid n lc1_ps (Global.promises gl1_ps) (Global.memory gl1_ps) lc1_arm mem_arm)
        (LC_WF1_PS: PSLocal.wf lc1_ps gl1_ps)
        (GL_WF1_PS: PSGlobal.wf gl1_ps)
        (WF1_ARM: RMWLocal.wf tid lc1_arm mem_arm)
        (RR: rr = (Ordering.le Ordering.acqrel ordr: bool) || Ordering.le Ordering.seqcst ordw)
        (RW: rw = Ordering.le Ordering.acqrel ordr || Ordering.le Ordering.acqrel ordw)
        (WR: wr = Ordering.le Ordering.seqcst ordw)
        (WW: ww = Ordering.le Ordering.acqrel ordw)
        (DMBSY: Ordering.le Ordering.seqcst ordw ->
                (join lc1_arm.(Local.vro) lc1_arm.(Local.vwo)).(View.ts) = n)
        (FULFILLABLE: RMWLocal.fulfillable lc2_arm mem_arm)
        (STEP: Local.dmb rr rw wr ww lc1_arm lc2_arm):
    exists lc2_ps gl2_ps,
      (<<STEP_PS: PSLocal.fence_step lc1_ps gl1_ps ordr ordw lc2_ps gl2_ps>>) /\
      (<<TVIEW2: sim_tview (PSLocal.tview lc2_ps) lc2_arm>>) /\
      (<<SC2: forall loc, PSTime.le (gl2_ps.(PSGlobal.sc) loc) (ntt n)>>) /\
      (<<MEM2: sim_memory_cons tid n lc2_ps (Global.promises gl2_ps) (Global.memory gl2_ps) lc2_arm mem_arm>>).
  Proof.
    exploit (Local.dmb_incr (A:=unit)); eauto. i.
    destruct lc1_ps as [tview1 prm1 rsv1].
    destruct gl1_ps as [sc1 gprm1 mem1]. ss.
    inv STEP. esplits.
    { econs; eauto. s. i.
      extensionality loc.
      destruct (prm1 loc) eqn:PRM; ss.
      inv MEM1. exploit PRM_COMPLETE; try eassumption. s. i. des.
      exploit FULFILLABLE; try eassumption. s. i. des.
      clear PRM_SOUND PRM_COMPLETE MEM_SOUND MEM_COMPLETE RELEASED LT_VCAP LT_COH.
      replace (Ordering.le Ordering.acqrel ordw)
        with true in * by (destruct ordw; ss).
      rewrite orb_true_r in LT_VWN. ss.
      cut (ts < ts); try by nia.
      eapply le_lt_trans; try apply LT_VWN.
      etrans; try apply LE.
      rewrite <- DMBSY; ss.
      etrans; [|apply join_r].
      eapply join_le; try apply Time.order. refl.
    }

    { econs; ss; i.
      { (* rel view *)
        repeat condtac; s.
        - unfold TView.write_fence_sc.
          rewrite X0, orb_true_r. ss.
          apply PSTime.join_spec.
          + etrans; try apply SC1. rewrite <- DMBSY; ss. apply le_ntt.
            etrans; [|apply join_l].
            etrans; [|apply join_r].
            eapply join_le; try apply Time.order. refl.
          + condtac.
            * etrans; [apply TVIEW1|]. apply le_ntt. s.
              repeat apply join_spec.
              { etrans; [|apply join_l].
                etrans; [|apply join_l].
                apply TVIEW1.
              }
              { etrans; [|apply join_l].
                etrans; [|apply join_r].
                apply join_l.
              }
              { etrans; [apply WF1_ARM|].
                etrans; [|apply join_l].
                etrans; [|apply join_r]. s.
                eapply join_le; try apply Time.order. refl.
              }
            * etrans; [apply TVIEW1|]. apply le_ntt. s. apply join_spec.
              { etrans; [apply TVIEW1|].
                repeat (etrans; [|apply join_l]; try refl).
              }
              { etrans; [apply WF1_ARM|].
                etrans; [|apply join_l].
                etrans; [|apply join_r]. s.
                eapply join_le; try apply Time.order. refl.
              }
        - etrans; [apply TVIEW1|]. apply le_ntt. s.
          repeat apply join_spec.
          + etrans; [|apply join_l].
            etrans; [|apply join_l].
            apply TVIEW1.
          + etrans; [|apply join_l].
            etrans; [|apply join_r].
            apply join_l.
          + etrans; [apply WF1_ARM|]. s.
            etrans; [|apply join_l].
            etrans; [|apply join_r].
            eapply join_le; try apply Time.order. refl.
        - etrans; [apply TVIEW1|]. apply le_ntt. s. apply join_spec.
          + etrans; [apply WF1_ARM|].
            etrans; [|apply join_l].
            etrans; [|apply join_r]. s.
            eapply join_le; try apply Time.order. refl.
          + etrans; [apply WF1_ARM|]. s.
            etrans; [|apply join_l].
            etrans; [|apply join_r].
            eapply join_le; try apply Time.order. refl.
        - etrans; [apply TVIEW1|]. apply le_ntt. s. apply join_spec.
          + etrans; [|apply join_l]. apply join_l.
          + apply join_r.
      }

      { (* cur *)
        repeat condtac; s.
        - unfold TView.write_fence_sc.
          rewrite X, orb_true_r. ss.
          apply PSTime.join_spec.
          + etrans; try apply SC1. rewrite <- DMBSY; ss. apply le_ntt.
            etrans; [|apply join_l].
            etrans; [|apply join_r].
            eapply join_le; try apply Time.order. refl.
          + condtac.
            * etrans; [apply TVIEW1|]. apply le_ntt. s.
              repeat apply join_spec.
              { etrans; [|apply join_l]. apply join_l. }
              { etrans; [|apply join_l].
                etrans; [|apply join_r].
                apply join_l.
              }
              { etrans; [apply WF1_ARM|].
                etrans; [|apply join_l].
                etrans; [|apply join_r]. s.
                eapply join_le; try apply Time.order. refl.
              }
            * etrans; [apply TVIEW1|]. apply le_ntt. s. apply join_spec.
              { etrans; [|apply join_l]. apply join_l. }
              { etrans; [apply WF1_ARM|].
                etrans; [|apply join_l].
                etrans; [|apply join_r]. s.
                eapply join_le; try apply Time.order. refl.
              }
        - etrans; [apply TVIEW1|]. apply le_ntt. s.
          repeat apply join_spec.
          + etrans; [|apply join_l]. apply join_l.
          + etrans; [|apply join_l].
            etrans; [|apply join_r].
            apply join_l.
          + apply join_r.
        - etrans; [apply TVIEW1|]. apply le_ntt. s. apply join_spec.
          + etrans; [|apply join_l]. apply join_l.
          + apply join_r.
      }

      { (* acq *)
        apply PSTime.join_spec.
        { etrans; [apply TVIEW1|]. apply le_ntt. s.
          eapply join_le; [apply Time.order|..]; try refl.
          eapply join_le; try apply Time.order. refl.
        }
        condtac; try apply PSTime.bot_spec. s.
        unfold TView.write_fence_sc.
        rewrite X, orb_true_r. ss.
        apply PSTime.join_spec.
        - etrans; try apply SC1. rewrite <- DMBSY; ss. apply le_ntt.
          etrans; [|apply join_l].
          etrans; [|apply join_l].
          etrans; [|apply join_r].
          eapply join_le; try apply Time.order. refl.
        - condtac.
          + etrans; [apply TVIEW1|]. apply le_ntt. s.
            repeat apply join_spec.
            { do 2 (etrans; [|apply join_l]). apply join_l. }
            { etrans; [|apply join_l].
              etrans; [|apply join_r].
              refl.
            }
            { etrans; [apply WF1_ARM|].
              etrans; [|apply join_l].
              etrans; [|apply join_l].
              etrans; [|apply join_r]. s.
              eapply join_le; try apply Time.order. refl.
            }
          + etrans; [apply TVIEW1|]. apply le_ntt. s. apply join_spec.
            { do 2 (etrans; [|apply join_l]). apply join_l. }
            { etrans; [apply WF1_ARM|].
              etrans; [|apply join_l].
              etrans; [|apply join_l].
              etrans; [|apply join_r]. s.
              eapply join_le; try apply Time.order. refl.
            }
      }

      { (* vnew *)
        apply join_spec.
        - etrans; [|apply join_l]. apply TVIEW1.
        - etrans; [|apply join_r]. apply join_spec.
          + etrans; [|apply join_l]. unfold ifc.
            condtac; try apply bot_spec. condtac; try refl.
            destruct ordr, ordw; ss.
          + etrans; [|apply join_r]. unfold ifc.
            condtac; try apply bot_spec. condtac; try refl.
            destruct ordr, ordw; ss.
      }
    }

    { (* sc *)
      s. i. unfold TView.write_fence_sc. condtac; ss.
      apply PSTime.join_spec; ss.
      exploit DMBSY; ss. i. rewrite <- x1.
      condtac.
      - etrans; [apply TVIEW1|]. apply le_ntt. ss.
        (repeat apply join_spec); try apply WF1_ARM. apply join_l.
      - etrans; [apply TVIEW1|]. apply le_ntt. ss.
        repeat apply join_spec; apply WF1_ARM.
    }

    { (* mem *)
      inv MEM1. ss. econs; s; eauto. i.
      exploit FWD; eauto. i. des.
      esplits; eauto.
      { etrans; try exact CUR.
        repeat condtac; ss; try refl; try apply LC_WF1_PS.
        unfold TView.write_fence_sc. unfold TimeMap.join.
        repeat (condtac; ss); try apply PSTime.join_r.
        etrans; [|apply PSTime.join_r]. apply LC_WF1_PS.
      }
      condtac; ss.
      - i. etrans; eauto. apply le_ntt.
        eapply join_le; [apply Time.order|..]; try refl.
        apply join_spec; ets.
      - etrans; eauto. condtac; ss; try refl.
        repeat (condtac; ss); cycle 1.
        { etrans; [apply LC_WF1_PS|]. apply LC_WF1_PS. }
        { apply LC_WF1_PS. }
        unfold TView.write_fence_sc.
        condtac; try by (destruct ordw; ss). s.
        econs; s.
        + etrans; [|apply TimeMap.join_r]. condtac; ss.
          * etrans; [apply LC_WF1_PS|]. s.
            etrans; [apply LC_WF1_PS|]. s.
            apply LC_WF1_PS.
          * etrans; [apply LC_WF1_PS|]. s.
            apply LC_WF1_PS.
        + etrans; [|apply TimeMap.join_r]. condtac; ss.
          * etrans; [apply LC_WF1_PS|]. s.
            apply LC_WF1_PS.
          * apply LC_WF1_PS.
    }
  Qed.

  Lemma sim_cons_control
        tid n
        lc1_ps gl1_ps lc1_arm mem_arm
        ctrl lc2_arm
        (TVIEW1: sim_tview (PSLocal.tview lc1_ps) lc1_arm)
        (MEM1: sim_memory_cons tid n lc1_ps (Global.promises gl1_ps) (Global.memory gl1_ps) lc1_arm mem_arm)
        (STEP: Local.control ctrl lc1_arm lc2_arm):
    (<<TVIEW2: sim_tview (PSLocal.tview lc1_ps) lc2_arm>>) /\
    (<<MEM2: sim_memory_cons tid n lc1_ps (Global.promises gl1_ps) (Global.memory gl1_ps) lc2_arm mem_arm>>).
  Proof.
    exploit (Local.control_incr (A:=unit)); eauto. i.
    inv STEP. split.
    - eapply sim_tview_le; eauto. s. apply TVIEW1.
    - inv MEM1. ss.
  Qed.

  Lemma sim_memory_cons_exclusive
        told tnew
        tid n lc_ps gprm_ps mem_ps lc_arm mem_arm
        loc vold msg loc_ps
        from
        (SIM: sim_memory_cons tid n lc_ps gprm_ps mem_ps lc_arm mem_arm)
        (TS: told < tnew)
        (OLD: Memory.read loc told mem_arm = Some vold)
        (NEW: Memory.get_msg tnew mem_arm = Some msg)
        (EX: empty_loc loc told tnew mem_arm)
        (LOC1: msg.(Msg.loc) = loc)
        (LOC2: loc = Zpos loc_ps)
        (RESERVED: PSMemory.get loc_ps (ntt tnew) mem_ps = Some (from, Message.reserve)):
    from = ntt told.
  Proof.
    dup SIM. inv SIM0.
    exploit MEM_SOUND; eauto. i. des.
    clear PRM_SOUND PRM_COMPLETE MEM_SOUND MEM_COMPLETE FWD RELEASED x0.
    rewrite LOC in *. inv LOC2.
    rewrite GET_PS in *. inv RESERVED.
    unguard. des; subst.
    { destruct told; ss.
      unfold Memory.read in OLD. ss. des_ifs.
      inv SIM. exploit (MEM_SOUND (S told)); eauto. i. des.
      clear PRM_SOUND PRM_COMPLETE MEM_SOUND MEM_COMPLETE FWD RELEASED x0.
      rewrite e in LOC0. inv LOC0.
      exploit PSMemory.get_disjoint; [exact GET_PS|exact GET_PS0|]. i. des.
      { apply ntt_inj in x0. subst. nia. }
      exfalso. apply (x0 (ntt (S told))); econs; ss; try refl.
      - eapply TimeFacts.le_lt_lt; try apply PSTime.bot_spec.
        apply PSTime.incr_spec.
      - exploit lt_ntt; try exact TS. s. i. timetac.
    }
    { apply ntt_lt in TS0.
      destruct (le_lt_dec fts told); cycle 1.
      { unfold Memory.get_msg in GET_FROM_ARM.
        destruct fts; ss.
        exploit EX; try apply GET_FROM_ARM; ss; try nia.
      }
      inv l; ss. exfalso.
      unfold Memory.read in OLD. ss. des_ifs.
      exploit EMPTY; try exact Heq; ss; try nia.
    }
  Qed.

  Lemma sim_state_cons_internal
        n st1_ps st1_arm e_arm st2_arm
        (SIM1: sim_state_cons n st1_ps st1_arm)
        (STEP: RMWState.step e_arm st1_arm st2_arm)
        (EVENT: e_arm = RMWEvent.internal):
    exists st2_ps,
      (<<STEP_PS: State.step ProgramEvent.silent st1_ps st2_ps>>) /\
      (<<SIM2: sim_state_cons n st2_ps st2_arm>>).
  Proof.
    destruct st1_ps as [regs1_ps stmts1_ps].
    destruct st1_arm as [stmts1_arm regs1_arm].
    destruct st2_arm as [stmts2_arm regs2_arm].
    inv SIM1. ss.
    destruct stmts1_ps; ss; subst; [inv STEP|].
    destruct t; ss; (try by inv STEP); cycle 1.
    { (* dowhile *)
      inv STEP. esplits; [econs 4|]; ss.
      econs; ss. unfold ps_to_rmw_stmts.
      rewrite List.map_app. ss.
    }

    destruct i; ss; inv STEP.
    { (* skip *)
      esplits; [econs 1; econs 1|..]; ss.
    }
    { (* assign *)
      esplits; [econs 1; econs 2|..]; ss.
      econs; ss.
      apply sim_regs_cons_add; ss.
      apply sim_regs_cons_eval_expr; ss.
    }
  Qed.

  Lemma sim_state_cons_control
        n st1_ps st1_arm e_arm st2_arm
        ctrl
        (SIM1: sim_state_cons n st1_ps st1_arm)
        (STEP: RMWState.step e_arm st1_arm st2_arm)
        (EVENT: e_arm = RMWEvent.control ctrl)
        (CTRL: le ctrl.(View.ts) n):
    exists st2_ps,
      (<<STEP_PS: State.step ProgramEvent.silent st1_ps st2_ps>>) /\
      (<<SIM2: sim_state_cons n st2_ps st2_arm>>).
  Proof.
    destruct st1_ps as [regs1_ps stmts1_ps].
    destruct st1_arm as [stmts1_arm regs1_arm].
    destruct st2_arm as [stmts2_arm regs2_arm].
    inv SIM1. ss.
    destruct stmts1_ps; ss; subst; [inv STEP|].
    destruct t; ss; inv STEP.
    condtac.
    - esplits; [econs 2|..]; ss.
      + des_ifs.
        exploit sim_regs_cons_eval_expr; eauto.
        rewrite Heq. ii. inv x0. congr.
      + econs; ss. rewrite <- List.map_app. ss.
    - esplits; [econs 3|..]; ss.
      + des_ifs.
        exploit sim_regs_cons_eval_expr; eauto.
        rewrite Heq. ii. inv x0. congr.
      + econs; ss. rewrite <- List.map_app. ss.
  Qed.

  Lemma sim_state_cons_read_aux
        n st1_ps st1_arm e_arm st2_arm
        loc_arm val_arm ord_arm
        (SIM1: sim_state_cons n st1_ps st1_arm)
        (STEP: RMWState.step e_arm st1_arm st2_arm)
        (EVENT: e_arm = RMWEvent.read ord_arm loc_arm val_arm):
    exists loc_ps ord_ps,
      (<<LOC: loc_arm.(ValA.annot).(View.ts) <= n -> loc_arm.(ValA.val) = Zpos loc_ps>>) /\
      (<<ORD: ord_arm = ps_to_rmw_ordr ord_ps>>).
  Proof.
    destruct st1_ps as [regs1_ps stmts1_ps].
    destruct st1_arm as [stmts1_arm regs1_arm].
    destruct st2_arm as [stmts2_arm regs2_arm].
    inv SIM1. ss.
    destruct stmts1_ps; ss; subst; [inv STEP|].
    destruct t; ss; try by inv STEP.
    destruct i; inv STEP.
    esplits; eauto. ss.
  Qed.

  Lemma sim_state_cons_read
        n st1_ps st1_arm e_arm st2_arm
        loc_arm val_arm ord_arm
        (SIM1: sim_state_cons n st1_ps st1_arm)
        (STEP: RMWState.step e_arm st1_arm st2_arm)
        (EVENT: e_arm = RMWEvent.read ord_arm loc_arm val_arm):
    exists loc_ps ord_ps,
      (<<LOC: loc_arm.(ValA.annot).(View.ts) <= n -> loc_arm.(ValA.val) = Zpos loc_ps>>) /\
      (<<ORD: ord_arm = ps_to_rmw_ordr ord_ps>>) /\
      forall val_ps (VAL: sim_val_cons n val_ps val_arm),
      exists st2_ps,
        (<<STEP_PS: State.step (ProgramEvent.read loc_ps val_ps ord_ps) st1_ps st2_ps>>) /\
        (<<SIM2: sim_state_cons n st2_ps st2_arm>>).
  Proof.
    destruct st1_ps as [regs1_ps stmts1_ps].
    destruct st1_arm as [stmts1_arm regs1_arm].
    destruct st2_arm as [stmts2_arm regs2_arm].
    inv SIM1. ss.
    destruct stmts1_ps; ss; subst; [inv STEP|].
    destruct t; ss; try by inv STEP.
    destruct i; inv STEP.
    esplits; ss. i.
    esplits; [econs 1; econs 3|..]; eauto.
    econs; ss.
    apply sim_regs_cons_add; ss.
  Qed.

  Lemma sim_state_cons_write
        n st1_ps st1_arm e_arm st2_arm
        loc_arm val_arm ord_arm
        (SIM1: sim_state_cons n st1_ps st1_arm)
        (STEP: RMWState.step e_arm st1_arm st2_arm)
        (EVENT: e_arm = RMWEvent.write ord_arm loc_arm val_arm):
    exists loc_ps val_ps ord_ps st2_ps,
      (<<STEP_PS: State.step (ProgramEvent.write loc_ps val_ps ord_ps) st1_ps st2_ps>>) /\
      (<<LOC: loc_arm.(ValA.annot).(View.ts) <= n -> loc_arm.(ValA.val) = Zpos loc_ps>>) /\
      (<<VAL: sim_val_cons n val_ps val_arm>>) /\
      (<<ORD: ord_arm = ps_to_rmw_ordw ord_ps>>) /\
      (<<SIM2: sim_state_cons n st2_ps st2_arm>>).
  Proof.
    destruct st1_ps as [regs1_ps stmts1_ps].
    destruct st1_arm as [stmts1_arm regs1_arm].
    destruct st2_arm as [stmts2_arm regs2_arm].
    inv SIM1. ss.
    destruct stmts1_ps; ss; subst; [inv STEP|].
    destruct t; ss; try by inv STEP.
    destruct i; inv STEP.
    esplits; [econs 1; econs 4|..]; eauto.
    - apply sim_regs_cons_eval_expr; ss.
    - econs; ss.
  Qed.

  Lemma sim_state_cons_fadd
        n st1_ps st1_arm e_arm st2_arm
        ordr_arm ordw_arm loc_arm vold_arm vnew_arm
        (SIM1: sim_state_cons n st1_ps st1_arm)
        (STEP: RMWState.step e_arm st1_arm st2_arm)
        (EVENT: e_arm = RMWEvent.fadd ordr_arm ordw_arm loc_arm vold_arm vnew_arm):
    exists loc_ps ordr_ps ordw_ps,
      (<<LOC: loc_arm.(ValA.annot).(View.ts) <= n -> loc_arm.(ValA.val) = Zpos loc_ps>>) /\
      (<<ORDR: ordr_arm = ps_to_rmw_ordr ordr_ps>>) /\
      (<<ORDW: ordw_arm = ps_to_rmw_ordw ordw_ps>>) /\
      forall vold_ps (VOLD: sim_val_cons n vold_ps vold_arm),
      exists vnew_ps st2_ps,
        (<<STEP_PS: State.step (ProgramEvent.update loc_ps vold_ps vnew_ps ordr_ps ordw_ps) st1_ps st2_ps>>) /\
        (<<VNEW: sim_val_cons n vnew_ps vnew_arm>>) /\
        (<<SIM2: sim_state_cons n st2_ps st2_arm>>).
  Proof.
    destruct st1_ps as [regs1_ps stmts1_ps].
    destruct st1_arm as [stmts1_arm regs1_arm].
    destruct st2_arm as [stmts2_arm regs2_arm].
    inv SIM1. ss.
    destruct stmts1_ps; ss; subst; [inv STEP|].
    destruct t; ss; try by inv STEP.
    destruct i; inv STEP.
    esplits; ss. i.
    esplits; [econs 1; econs 5|..]; eauto.
    - ii. ss.
      exploit VOLD.
      { etrans; eauto. apply join_l. }
      i. inv x0.
      exploit sim_regs_cons_eval_expr; try exact REGS.
      { etrans; [|exact H]. apply join_r. }
      i. inv x0. ss.
    - econs; ss.
      apply sim_regs_cons_add; ss.
  Qed.

  Lemma sim_state_cons_fadd_weak
        n st1_ps st1_arm e_arm st2_arm
        ordr_arm ordw_arm loc_arm vold_arm vnew_arm
        (SIM1: sim_state_cons n st1_ps st1_arm)
        (STEP: RMWState.step e_arm st1_arm st2_arm)
        (EVENT: e_arm = RMWEvent.fadd ordr_arm ordw_arm loc_arm vold_arm vnew_arm):
    exists loc_ps ordr_ps ordw_ps,
      (<<LOC: loc_arm.(ValA.annot).(View.ts) <= n -> loc_arm.(ValA.val) = Zpos loc_ps>>) /\
      (<<ORDR: ordr_arm = ps_to_rmw_ordr ordr_ps>>) /\
      (<<ORDW: ordw_arm = ps_to_rmw_ordw ordw_ps>>) /\
      forall vold_ps,
      exists vnew_ps st2_ps,
        (<<STEP_PS: State.step (ProgramEvent.update loc_ps vold_ps vnew_ps ordr_ps ordw_ps) st1_ps st2_ps>>).
  Proof.
    destruct st1_ps as [regs1_ps stmts1_ps].
    destruct st1_arm as [stmts1_arm regs1_arm].
    destruct st2_arm as [stmts2_arm regs2_arm].
    inv SIM1. ss.
    destruct stmts1_ps; ss; subst; [inv STEP|].
    destruct t; ss; try by inv STEP.
    destruct i; inv STEP.
    esplits; ss. i.
    esplits; [econs 1; econs 5|..]; eauto.
  Qed.

  Lemma sim_state_cons_dmb
        n st1_ps st1_arm e_arm st2_arm
        rr rw wr ww
        (SIM1: sim_state_cons n st1_ps st1_arm)
        (STEP: RMWState.step e_arm st1_arm st2_arm)
        (EVENT: e_arm = RMWEvent.dmb rr rw wr ww):
    exists ordr_ps ordw_ps st2_ps,
      (<<STEP_PS: State.step (ProgramEvent.fence ordr_ps ordw_ps) st1_ps st2_ps>>) /\
      (<<RR: rr = Ordering.le Ordering.acqrel ordr_ps || Ordering.le Ordering.seqcst ordw_ps>>) /\
      (<<RW: rw = Ordering.le Ordering.acqrel ordr_ps || Ordering.le Ordering.acqrel ordw_ps>>) /\
      (<<WR: wr = Ordering.le Ordering.seqcst ordw_ps>>) /\
      (<<WW: ww = Ordering.le Ordering.acqrel ordw_ps>>) /\
      (<<SIM2: sim_state_cons n st2_ps st2_arm>>).
  Proof.
    destruct st1_ps as [regs1_ps stmts1_ps].
    destruct st1_arm as [stmts1_arm regs1_arm].
    destruct st2_arm as [stmts2_arm regs2_arm].
    inv SIM1. ss.
    destruct stmts1_ps; ss; subst; [inv STEP|].
    destruct t; ss; try by inv STEP.
    destruct i; inv STEP.
    esplits; [econs 1; econs 6|..]; eauto.
    econs; ss.
  Qed.

  Lemma sim_thread_cons_step
        tid n th1_ps eu1 eu2
        (SIM1: sim_thread_cons tid n th1_ps eu1)
        (SC1: forall loc, PSTime.le (th1_ps.(PSThread.global).(PSGlobal.sc) loc) (ntt n))
        (LC_WF1_PS: PSLocal.wf (PSThread.local th1_ps) (PSThread.global th1_ps))
        (GL_WF1_PS: PSGlobal.wf (PSThread.global th1_ps))
        (WF1_ARM: RMWLocal.wf tid eu1.(RMWExecUnit.local) eu1.(RMWExecUnit.mem))
        (STEP_ARM: RMWExecUnit.state_step_dmbsy_exact (Some n) n tid eu1 eu2)
        (FULFILLABLE: RMWLocal.fulfillable eu2.(RMWExecUnit.local) eu2.(RMWExecUnit.mem))
        (VCAP: eu2.(RMWExecUnit.local).(Local.vcap).(View.ts) <= n):
    exists th2_ps,
      (<<STEPS_PS: rtc (@PSThread.tau_step _) th1_ps th2_ps>>) /\
      ((<<SIM2: sim_thread_cons tid n th2_ps eu2>>) /\
       (<<SC2: forall loc, PSTime.le (th2_ps.(PSThread.global).(PSGlobal.sc) loc) (ntt n)>>) \/
       exists e_ps th3_ps,
         (<<STEP_PS: PSThread.step e_ps th2_ps th3_ps>>) /\
         (<<FAILURE: ThreadEvent.get_machine_event e_ps = MachineEvent.failure>>)).
  Proof.
    destruct th1_ps as [st1_ps lc1_ps gl1_ps].
    destruct eu1 as [st1_arm lc1_arm mem1_arm].
    destruct eu2 as [st2_arm lc2_arm mem2_arm].
    inv SIM1. inv STEP_ARM. inv STEP. ss. subst.
    inv LOCAL.
    { (* internal *)
      exploit sim_state_cons_internal; eauto. i. des.
      esplits.
      - econs 2; try refl.
        econs 1; [econs 2; [|econs 1]|]; eauto.
      - left. ss.
    }

    { (* read *)
      exploit sim_state_cons_read; eauto. i. des. subst.
      exploit LOC.
      { etrans; [|exact VCAP]. inv STEP. ss. ets. }
      clear LOC. intro LOC.
      destruct (le_lt_dec
                  (FwdItem.read_view (Local.fwdbank lc1_arm vloc.(ValA.val)) ts (ps_to_rmw_ordr ord_ps)).(View.ts) n);
         rename l into READ_VIEW.
      { (* read view <= n *)
        exploit sim_cons_read; try exact STEP; eauto. i. des.
        - exfalso.
          exploit (FULFILLABLE ts); try by (inv STEP; ss). i. des.
          dup WF1_ARM. inv WF1_ARM0.
          exploit PRM; eauto. i. des.
          clear COH VRN VWN FWD PRM.
          exploit LT_COH; eauto. i.
          exploit (read_ts_coh (A:=unit)); eauto. i.
          clear - STEP GET x1 x2.
          inv STEP. ss.
          unfold Memory.get_msg in *. destruct ts; ss.
          revert MSG. unfold Memory.read. ss.
          rewrite GET. condtac; ss. i.
          rewrite e in *.
          eapply Nat.lt_strorder.
          eapply Nat.lt_le_trans; [exact x1|]. apply x2.
        - exploit x0; eauto. i. des.
          esplits.
          + econs 2; try refl.
            econs 1; [econs 2; [|econs 2]|]; eauto.
          + left. ss.
        - exploit x0; ii; eauto. i. des.
          esplits.
          + econs 2; try refl.
            econs 1; [econs 2; [|econs 8]|]; eauto.
          + left. ss.
      }

      { (* read view > n *)
        exploit sim_cons_read_cur; try exact STEP; eauto. i. des.
        exploit (x0 val).
        { ii. exfalso.
          inv STEP. ss. move READ_VIEW at bottom.
          cut (n < n); try nia.
          eapply Nat.lt_le_trans; [exact READ_VIEW|].
          etrans; try exact H.
          apply join_r.
        }
        i. des.
        esplits.
        - econs 2; try refl.
          econs 1; [econs 2; [|econs 2]|]; eauto.
        - left. ss.
      }
    }

    { (* fulfill *)
      exploit sim_state_cons_write; eauto. i. des.
      exploit LOC.
      { etrans; [|exact VCAP]. inv STEP. ss. ets. }
      clear LOC. intro LOC.
      exploit sim_cons_fulfill; try exact STEP; eauto; ss.
      { Transparent Ordering.le.
        i. subst. apply PF in H. destruct ord_ps; ss.
      }
      { i. apply PSTime.bot_spec. }
      i. des.
      esplits.
      - econs 2.
        { econs 1; [econs 1; econs 3|]; eauto. }
        econs 2; try refl.
        econs 1; [econs 2; [|econs 3]|]; eauto.
      - left. splits; ss. i.
        inv CANCEL_PS. inv STEP_PS0. ss.
    }

    { (* fadd *)
      exploit sim_state_cons_fadd; eauto. i. des. subst.
      exploit LOC.
      { etrans; [|exact VCAP].
        clear - STEP_FULFILL STEP_CONTROL.
        inv STEP_CONTROL. ss.
        inv STEP_FULFILL. ss.
        ets.
      }
      clear LOC. intro LOC.
      exploit (update_ts (A:=unit)); eauto. intro TS.
      destruct (le_lt_dec
                  (FwdItem.read_view (Local.fwdbank lc1_arm vloc.(ValA.val)) ts_old (ps_to_rmw_ordr ordr_ps)).(View.ts) n);
        rename l into READ_VIEW.
      { (* read view <= n *)
        exploit sim_cons_read; try exact STEP_READ; eauto. i. des.
        { (* read message is a promise *)
          exfalso.
          exploit (FULFILLABLE ts_old).
          { inv STEP_CONTROL; ss.
            inv STEP_FULFILL; ss.
            rewrite Promises.unset_o.
            condtac; try by (inv STEP_READ; ss); ss.
            r in e. subst. nia.
          }
          i. des.
          dup WF1_ARM. inv WF1_ARM0.
          exploit PRM; eauto. i. des.
          clear COH VRN VWN FWD PRM.
          exploit LT_COH; eauto. i.
          eapply Nat.lt_strorder.
          etrans; try exact x0.
          eapply Nat.lt_le_trans; try exact TS.
          exploit (Local.control_incr (A:=unit)); eauto. i.
          etrans; [|apply x2].
          replace (Msg.loc msg) with (ValA.val vloc); cycle 1.
          { clear - STEP_READ GET.
            inv STEP_READ. ss.
            revert GET. unfold Memory.get_msg. destruct ts_old; ss. i.
            revert MSG. unfold Memory.read. s. rewrite GET. condtac; ss.
          }
          clear - STEP_FULFILL.
          inv STEP_FULFILL. ss.
          unfold fun_add. condtac; ss. congr.
        }

        { (* normal read *)
          exploit x1; eauto. i. des. clear x1.
          exploit PSLocal.read_step_future; try exact STEP_PS0; eauto. i. des.
          exploit (RMWLocal.read_wf (A:=unit)); eauto. i.
          exploit sim_cons_fulfill; try exact STEP_FULFILL; eauto; ss.
          { Transparent Ordering.le.
            i. subst. apply PF in H. destruct ordw_ps; ss.
          }
          { clear - LOC SIM_TVIEW SIM_MEM LC_WF1_PS STEP_READ STEP_PS TVIEW2 MEM2.
            i. inv STEP_READ. ss.
            unfold FwdItem.read_view. condtac; s.
            - apply andb_prop in X. des.
              revert X. unfold proj_sumbool. condtac; ss. r in e. i. clear X0 X X1.
              inv SIM_MEM. clear PRM_SOUND PRM_COMPLETE MEM_SOUND MEM_COMPLETE RELEASED.
              exploit (FWD (Zpos loc_ps)); eauto. i. des.
              rewrite LOC in *.
              inv STEP_PS. rewrite GET_PS in *. inv GET.
              revert REL_FWD. condtac; i.
              + etrans; try apply REL_FWD. apply le_ntt. s.
                eapply join_le; [apply Time.order|..].
                * eapply join_le; [apply Time.order|..]; ets.
                * unfold fun_add. condtac; ss. rewrite e. ets.
              + etrans; try apply REL_FWD.
                etrans; [apply LC_WF1_PS|].
                etrans; [apply LC_WF1_PS|].
                etrans; [apply SIM_TVIEW|].
                apply le_ntt. s.
                eapply join_le; [apply Time.order|..].
                * eapply join_le; [apply Time.order|..]; ets.
                * unfold fun_add. condtac; ss. rewrite e. ets.
            - inv STEP_PS. ss.
              inv MEM2. exploit RELEASED; eauto. i.
              etrans; eauto. apply le_ntt. ets.
          }
          { i. inv STEP_PS. ss.
            inv SIM_MEM. exploit RELEASED; eauto.
            etrans; try apply x1. econs.
            apply lt_ntt. ss.
          }
          i. des.
          exploit reorder_read_cancel; eauto. i. des.
          exploit (@sim_memory_cons_exclusive ts_old ts_new); try exact SIM_MEM.
          { clear - WF1_ARM STEP_READ STEP_FULFILL.
            eapply le_lt_trans; cycle 1.
            { inv STEP_FULFILL. inv WRITABLE. apply COH. }
            clear STEP_FULFILL. inv STEP_READ. ss.
            unfold FwdItem.read_view. condtac.
            - apply andb_prop in X. des.
              revert X. unfold proj_sumbool. condtac; ss.
              r in e. i. clear X X0 X1. subst.
              inv WF1_ARM. etrans; try apply FWD.
              unfold fun_add. condtac; try congr. s.
              apply join_l.
            - unfold fun_add. condtac; ss; try congr. ets.
          }
          { instantiate (1:=vold.(ValA.val)).
            instantiate (1:=vloc.(ValA.val)).
            inv STEP_READ. ss.
          }
          { instantiate (1:=Msg.mk vloc.(ValA.val) vnew.(ValA.val) tid).
            inv STEP_FULFILL. ss.
          }
          { hexploit update_empty_loc; try exact STEP_READ; try exact STEP_FULFILL; ss.
            eapply RMWLocal.control_fulfillable; eauto.
          }
          { ss. }
          { eauto. }
          { instantiate (1:=from).
            inv CANCEL_PS. inv CANCEL.
            exploit PSMemory.remove_get0; try exact MEM. i. des. ss.
          }
          i. subst. esplits.
          + econs 2.
            { econs; [econs 1; econs 3|]; eauto. }
            econs 2; try refl.
            econs; [econs 2; [|econs 4]|]; eauto.
          + left. splits.
            * econs; ss.
              { exploit (Local.control_incr (A:=unit)); eauto. i.
                eapply sim_tview_le; eauto.
                inv STEP_CONTROL. ss. apply TVIEW0.
              }
              { inv STEP_CONTROL. inv MEM0. econs; ss. }
            * i. inv STEP_PS0. inv CANCEL_PS. inv STEP_PS1. ss.
        }

        { (* racy read *)
          exploit (x1 val); ii; ss. des.
          inv STEP_PS. esplits; try refl.
          right. esplits.
          - econs 2; [|econs 10]; eauto.
          - ss.
        }
      }

      { (* read view > n *)
        cut (n < n); try nia.
        eapply Nat.lt_le_trans; [exact READ_VIEW|].
        etrans; [|exact VCAP].
        clear - STEP_READ STEP_FULFILL STEP_CONTROL.
        inv STEP_CONTROL. ss.
        inv STEP_FULFILL. ss.
        inv STEP_READ. ss. ets.
      }
    }

    { (* dmb *)
      exploit sim_state_cons_dmb; eauto. i. des.
      exploit sim_cons_dmb; try exact STEP; eauto.
      { i. apply DMBSY.
        destruct ordr_ps, ordw_ps; subst; ss.
      }
      i. des. esplits.
      - econs 2; try refl.
        econs; [econs 2; [|econs 5]|]; eauto.
      - left. ss.
    }

    { (* control *)
      exploit sim_state_cons_control; eauto.
      { etrans; [|exact VCAP]. inv LC. ss. apply join_r. }
      exploit sim_cons_control; try exact LC; eauto. i. des.
      esplits.
      - econs 2; try refl.
        econs; [econs 2; [|econs 1]|]; eauto.
      - left. ss.
    }
  Qed.

  Lemma sim_thread_cons_rtc_step
        tid n th1_ps eu1 eu2
        (SIM1: sim_thread_cons tid n th1_ps eu1)
        (SC1: forall loc, PSTime.le (th1_ps.(PSThread.global).(PSGlobal.sc) loc) (ntt n))
        (LC_WF1_PS: PSLocal.wf (PSThread.local th1_ps) (PSThread.global th1_ps))
        (GL_WF1_PS: PSGlobal.wf (PSThread.global th1_ps))
        (WF1_ARM: RMWLocal.wf tid eu1.(RMWExecUnit.local) eu1.(RMWExecUnit.mem))
        (STEPS_ARM: rtc (RMWExecUnit.state_step_dmbsy_exact (Some n) n tid) eu1 eu2)
        (FULFILLABLE: RMWLocal.fulfillable eu2.(RMWExecUnit.local) eu2.(RMWExecUnit.mem))
        (VCAP: eu2.(RMWExecUnit.local).(Local.vcap).(View.ts) <= n):
    exists th2_ps,
      (<<STEPS_PS: rtc (@PSThread.tau_step _) th1_ps th2_ps>>) /\
      ((<<SIM2: sim_thread_cons tid n th2_ps eu2>>) /\
       (<<SC2: forall loc, PSTime.le (th2_ps.(PSThread.global).(PSGlobal.sc) loc) (ntt n)>>) \/
       exists e_ps th3_ps,
         (<<STEP_PS: PSThread.step e_ps th2_ps th3_ps>>) /\
         (<<FAILURE: ThreadEvent.get_machine_event e_ps = MachineEvent.failure>>)).
  Proof.
    revert th1_ps SIM1 SC1 LC_WF1_PS GL_WF1_PS.
    induction STEPS_ARM; i.
    { esplits; eauto. }
    hexploit (RMWExecUnit.rtc_state_step_fulfillable (A:=unit)); try exact FULFILLABLE;
      try eapply rtc_mon; try exact STEPS_ARM; i.
    { inv H0. econs. eauto. }
    exploit (RMWExecUnit.rtc_state_step_incr (A:=unit));
      try eapply rtc_mon; try exact STEPS_ARM; i.
    { inv H1. econs. eauto. }
    exploit sim_thread_cons_step; eauto.
    { etrans; [apply x1|]. ss. }
    i. des; cycle 1.
    { esplits; eauto. }
    exploit PSThread.rtc_tau_step_future; try exact STEPS_PS; eauto. i. des.
    exploit (RMWExecUnit.state_step_rmw_wf (A:=unit)); i.
    { inv H. econs. eauto. }
    { ss. }
    exploit IHSTEPS_ARM; eauto. i. des.
    - esplits; [|eauto]. etrans; eauto.
    - esplits; [|eauto]. etrans; eauto.
  Qed.

  Lemma sim_thread_sim_thread_cons
        tid n th_ps eu
        (SIM: sim_thread tid n th_ps eu):
    sim_thread_cons tid n th_ps eu.
  Proof.
    inv SIM. econs; ss.
    - inv SIM_STATE. econs; ss. ii. auto.
    - inv SIM_MEM. econs; eauto; i.
      exploit MEM_SOUND; eauto. i. des.
      esplits; eauto. clear x1.
      unguard. des.
      + left. splits; ss.
      + right. esplits; eauto.
  Qed.

  Lemma sim_thread_cap_sim_thread_cons
        tid n th_ps eu
        (INHABITED: PSMemory.inhabited th_ps.(PSThread.global).(Global.memory))
        (SIM: sim_thread tid n th_ps eu):
    sim_thread_cons tid n (PSThread.cap_of th_ps) eu.
  Proof.
    destruct th_ps as [st_ps lc_ps [sc gprm mem_ps]].
    destruct eu as [st_arm lc_arm mem_arm].
    inv SIM. econs; ss.
    { inv SIM_STATE. econs; ss. ii. auto. }
    clear - INHABITED SIM_MEM.
    specialize (PSMemory.cap_of_cap mem_ps). intro CAP.
    hexploit PSMemory.cap_le; eauto. intro CAP_LE.
    inv SIM_MEM. econs; eauto; i.
    { exploit MEM_SOUND; eauto. i. des.
      exploit CAP_LE; eauto. i.
      esplits; try exact x2; eauto.
      clear x1. unguard. des.
      - left. splits; ss.
      - right. esplits; eauto.
    }
    { exploit PSMemory.cap_inv; eauto. i. des; eauto.
      { subst. exfalso.
        clear PRM_SOUND PRM_COMPLETE FWD RELEASED.
        inv x1.
        exploit MEM_COMPLETE; try exact GET2.
        { eapply TimeFacts.le_lt_lt; try exact TS. apply Time.bot_spec. }
        i. des. subst.
        exploit MEM_SOUND; try exact GET_ARM. i. des. clear x1.
        rewrite LOC0 in *. inv LOC.
        rewrite GET_PS0 in *. inv GET2.
        unguardH x3. des; subst.
        { inv x2. }
        exploit MEM_SOUND; try exact GET_FROM_ARM. s. i. des.
        clear x3 x1. inv LOC.
        exploit (EMPTY (ntt fts)); ss; try congr.
      }
      { subst. left.
        exploit (@PSMemory.max_ts_spec loc_ps); try eapply INHABITED. i. des.
        destruct (TimeFacts.le_lt_dec (PSMemory.max_ts loc_ps mem_ps) PSTime.bot).
        { exploit TimeFacts.antisym; try exact l; try apply PSTime.bot_spec. i.
          rewrite x1. exists 1. splits; ss. i.
          ii. exploit MEM_SOUND; try exact GET_ARM. i. des.
          rewrite LOC in *. inv H.
          exploit PSMemory.max_ts_spec; try exact GET_PS0. i. des.
          rewrite l in MAX0.
          replace PSTime.bot with (ntt 0) in MAX0 by ss.
          apply ntt_le in MAX0. unfold le in LE. nia.
        }
        exploit MEM_COMPLETE; try exact GET; ss. i. des.
        exists (S ts). splits; ss.
        - rewrite TO0. ss.
        - ii. exploit MEM_SOUND; try exact GET_ARM0. i. des.
          rewrite LOC0 in *. inv H.
          exploit PSMemory.max_ts_spec; try exact GET_PS0. i. des.
          rewrite TO0 in MAX0. apply ntt_le in MAX0.
          unfold le in LE. nia.
      }
    }
    { exploit FWD; eauto. i. des.
      exploit CAP_LE; eauto. i.
      esplits; eauto.
    }
    { exploit PSMemory.cap_inv; eauto. i. des; ss. eauto. }
  Qed.

  Lemma sim_thread_cons_no_promises
        tid n th_ps eu
        (SIM: sim_thread_cons tid n th_ps eu)
        (PROMISES: forall ts
                     (PROMISED: Promises.lookup ts eu.(RMWExecUnit.local).(Local.promises) = true),
            ts > n):
    th_ps.(PSThread.local).(PSLocal.promises) = BoolMap.bot.
  Proof.
    apply BoolMap.antisym; try apply BoolMap.bot_spec.
    ii. exfalso.
    inv SIM. inv SIM_MEM.
    exploit PRM_COMPLETE; eauto. i. des.
    exploit PROMISES; eauto. i.
    unfold le in LE. nia.
  Qed.

  Lemma sim_thread_exec_consistent
        tid n after_sc th1_ps eu
        (SIM1: sim_thread_exec tid n after_sc th1_ps eu)
        (SC1: forall loc, PSTime.le (th1_ps.(PSThread.global).(PSGlobal.sc) loc) (ntt n))
        (LC_WF1_PS: PSLocal.wf (PSThread.local th1_ps) (PSThread.global th1_ps))
        (GL_WF1_PS: PSGlobal.wf (PSThread.global th1_ps))
        (WF_ARM: RMWLocal.wf tid (RMWExecUnit.local eu) (RMWExecUnit.mem eu)):
    PSThread.consistent th1_ps.
  Proof.
    inv SIM1.
    exploit sim_thread_cap_sim_thread_cons; eauto; try apply GL_WF1_PS. intro SIM_CONS.
    exploit PSThread.cap_wf; eauto. i. des.
    exploit (certify_cases (A:=unit)); try exact STEPS2; auto. i. des.
    { econs 2; try refl.
      exploit sim_thread_cons_no_promises; eauto.
    }
    unguard. des.
    exploit (fulfill_step_state_step0_pln (A:=unit)); eauto. i. des.
    exploit (RMWExecUnit.rtc_state_step_rmw_wf (A:=unit)); try exact STEPS1; eauto. i.
    exploit (RMWExecUnit.rtc_state_step_rmw_wf (A:=unit));
      try eapply rtc_mon; try exact STEPS0;
      try apply RMWExecUnit.dmbsy_over_state_step; eauto. i.
    exploit (fulfill_step_vwn (A:=unit)); eauto. i. des.
    exploit (fulfill_step_vcap (A:=unit)); eauto. i. des.
    hexploit (RMWExecUnit.rtc_state_step_fulfillable (A:=unit));
      try eapply rtc_mon; try exact STEPS3;
      try apply RMWExecUnit.dmbsy_over_state_step.
    { ii. rewrite PROMISES, Promises.lookup_bot in *. ss. }
    intro FULFILLABLE.
    assert (CERTIFY_STEPS: rtc (RMWExecUnit.state_step_dmbsy_exact (Some n) n tid) eu1 eu1'').
    { exploit rtc_n1; try exact STEPS0.
      { econs; eauto. ss. }
      i. clear - FULFILL_TS x2 VWN2.
      induction x2; i; try refl.
      econs 2; [|apply IHx2; auto].
      inv H. econs; eauto. i.
      exploit DMBSY; eauto. i.
      destruct (le_lt_dec (View.ts (join (Local.vro (RMWExecUnit.local x)) (Local.vwo (RMWExecUnit.local x)))) n).
      { apply le_antisym; ss.
        destruct after_sc; ss. unfold le in x1. nia.
      }
      exfalso. clear IHx2 l.
      exploit (RMWExecUnit.rtc_state_step_incr (A:=unit));
        try eapply rtc_mon; try exact x2;
        try apply RMWExecUnit.dmbsy_over_state_step. i.
      inv STEP. inv LOCAL; ss. destruct rr, rw, wr, ww; ss.
      cut (n < n); try nia.
      eapply lt_le_trans; [|exact FULFILL_TS].
      eapply le_lt_trans; [|exact VWN2].
      etrans; [|apply x3].
      clear - x1 STEP.
      destruct y as []. s.
      inv STEP; ss. subst. ss.
      etrans; [etrans; [|exact x1]|].
      - destruct after_sc; nia.
      - apply join_spec; ets.
    }
    exploit sim_thread_cons_rtc_step; try exact SIM_CONS;
      try eapply rtc_mon; try exact CERTIFY_STEPS; eauto; try nia.
    i. des.
    - econs 2; try exact STEPS_PS.
      eapply sim_thread_cons_no_promises; eauto.
    - econs 1. econs; eauto.
  Qed.
End PStoRMWConsistent.
