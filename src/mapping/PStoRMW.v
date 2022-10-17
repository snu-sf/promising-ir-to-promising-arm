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
Require Import PromisingArch.mapping.PStoRMWUtils.

Set Implicit Arguments.
Set Nested Proofs Allowed.


Definition const_to_val (c: Const.t): Val.t :=
  match c with
  | Const.num n => n
  | Const.undef => 0%Z
  end.

Fixpoint ps_to_rmw_expr (e: Expr.t): exprT :=
  match e with
  | Expr.const c => const_to_val c
  | Expr.reg r => expr_reg r
  | Expr.op1 op e => expr_op1 op (ps_to_rmw_expr e)
  | Expr.op2 op e1 e2 => expr_op2 op (ps_to_rmw_expr e1) (ps_to_rmw_expr e2)
  end.

Definition ps_to_rmw_ordr (ord: Ordering.t): OrdR.t :=
  if Ordering.le Ordering.acqrel ord
  then OrdR.acquire_pc
  else OrdR.pln.

Definition ps_to_rmw_ordw (ord: Ordering.t): OrdW.t :=
  if Ordering.le Ordering.acqrel ord
  then OrdW.release_pc
  else
    if Ordering.le Ordering.plain ord
    then OrdW.srlx
    else OrdW.pln.

Definition ps_to_rmw_instr (i: Instr.t): rmw_instrT :=
  match i with
  | Instr.skip =>
      rmw_instr_skip
  | Instr.assign reg e =>
      rmw_instr_assign reg (ps_to_rmw_expr e)
  | Instr.load reg loc ord =>
      rmw_instr_load (ps_to_rmw_ordr ord) reg (expr_const (Zpos loc))
  | Instr.store loc e ord =>
      rmw_instr_store (ps_to_rmw_ordw ord) (expr_const (Zpos loc)) (ps_to_rmw_expr e)
  | Instr.fadd reg loc e ordr ordw =>
      rmw_instr_fadd
        (ps_to_rmw_ordr ordr) (ps_to_rmw_ordw ordw)
        reg (expr_const (Zpos loc)) (ps_to_rmw_expr e)
  | Instr.fence ordr ordw =>
      rmw_instr_barrier
        (Barrier.dmb
           (Ordering.le Ordering.acqrel ordr || Ordering.le Ordering.seqcst ordw)
           (Ordering.le Ordering.acqrel ordr || Ordering.le Ordering.acqrel ordw)
           (Ordering.le Ordering.seqcst ordw)
           (Ordering.le Ordering.acqrel ordw))
  end.

Fixpoint ps_to_rmw_stmt (stmt: Stmt.t): rmw_stmtT :=
  match stmt with
  | Stmt.instr i =>
      rmw_stmt_instr (ps_to_rmw_instr i)
  | Stmt.ite cond s1 s2 =>
      rmw_stmt_if
        (ps_to_rmw_expr cond)
        (List.map ps_to_rmw_stmt s1)
        (List.map ps_to_rmw_stmt s2)
  | Stmt.dowhile s cond =>
      rmw_stmt_dowhile (List.map ps_to_rmw_stmt s) (ps_to_rmw_expr cond)
  end.

Definition ps_to_rmw_stmts (s: list Stmt.t): list rmw_stmtT :=
  List.map ps_to_rmw_stmt s.


Module PStoRMW.
  Variant sim_val: forall (val_ps: Const.t) (val_arm: Val.t), Prop :=
    | sim_val_num
        v:
      sim_val (Const.num v) v
    (* | sim_val_undef *)
    (*     v: *)
    (*   sim_val Const.undef v *)
  .
  #[export] Hint Constructors sim_val: core.

  Variant sim_state (st_ps: State.t) (st_arm: RMWState.t (A:=View.t (A:=unit))): Prop :=
    | sim_state_intro
        (STMTS: RMWState.stmts st_arm = ps_to_rmw_stmts (State.stmts st_ps))
        (REGS: forall r, sim_val (IdentFun.find r st_ps.(State.regs))
                                 (RMap.find r st_arm.(RMWState.rmap)).(ValA.val))
  .
  #[export] Hint Constructors sim_state: core.

  Variant sim_tview (tview: PSTView.t) (lc_arm: Local.t (A:=unit)): Prop :=
    | sim_tview_intro
        (REL: forall loc loc',
            PSTime.le
              ((tview.(PSTView.rel) loc).(View.rlx) loc')
              (ntt (View.ts (join lc_arm.(Local.vwn) (lc_arm.(Local.coh) (Zpos loc))))))
        (CUR: forall loc,
            PSTime.le
              (tview.(PSTView.cur).(View.rlx) loc)
              (ntt (View.ts (join lc_arm.(Local.vrn) (lc_arm.(Local.coh) (Zpos loc))))))
        (ACQ: forall loc,
            PSTime.le
              (tview.(PSTView.acq).(View.rlx) loc)
              (ntt (View.ts (join lc_arm.(Local.vro) (lc_arm.(Local.coh) (Zpos loc))))))
        (VNEW: le lc_arm.(Local.vrn) lc_arm.(Local.vwn))
        (VOLD: forall loc, le (lc_arm.(Local.coh) loc) (join lc_arm.(Local.vro) lc_arm.(Local.vwo)))
        (FWD: forall loc,
            le (lc_arm.(Local.fwdbank) loc).(FwdItem.ts) (View.ts (lc_arm.(Local.coh) loc)))
  .
  #[export] Hint Constructors sim_tview: core.

  Variant sim_memory (tid: Ident.t) (n: Time.t)
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
                 (<<LATEST: Memory.latest msg_arm.(Msg.loc) fts ts mem_arm>>))) /\
            (__guard__ (
               (<<MSG: msg_ps = Message.reserve>>) /\
               (<<PROMISED: le ts n ->
                            (<<GPROMISED: gprm_ps loc_ps = true>>) /\
                            (<<PROMISED_PS: lc_ps.(PSLocal.promises) loc_ps <-> msg_arm.(Msg.tid) = tid>>) /\
                            (<<PROMISED_ARM: Promises.lookup ts lc_arm.(Local.promises) <-> msg_arm.(Msg.tid) = tid>>)>>) \/
               exists val_ps released na,
                 (<<MSG: msg_ps = Message.message val_ps released na>>) /\
                 (<<VAL: sim_val val_ps msg_arm.(Msg.val)>>) /\
                 (<<REL_FWD: (lc_arm.(Local.fwdbank) msg_arm.(Msg.loc)).(FwdItem.ts) = ts ->
                             if (lc_arm.(Local.fwdbank) msg_arm.(Msg.loc)).(FwdItem.ex)
                             then PSView.opt_le released (Some lc_ps.(PSLocal.tview).(PSTView.acq))
                             else PSView.opt_le released (Some (lc_ps.(PSLocal.tview).(PSTView.rel) loc_ps))>>) /\
                 (<<PROMISED_ARM: Promises.lookup ts lc_arm.(Local.promises) = false>>))))
        (MEM_COMPLETE: forall loc_ps from to msg_ps
                              (TO: PSTime.lt PSTime.bot to)
                              (GET_PS: PSMemory.get loc_ps to mem_ps = Some (from, msg_ps)),
          exists ts msg_arm,
            (<<TO: to = ntt ts>>) /\
            (<<GET_ARM: Memory.get_msg ts mem_arm = Some msg_arm>>) /\
            (<<LOC: msg_arm.(Msg.loc) = Zpos loc_ps>>))
        (RELEASED: forall loc from to val released na
                          (GET: PSMemory.get loc to mem_ps = Some (from, Message.message val released na)),
          forall loc', PSTime.le ((View.unwrap released).(View.rlx) loc') to)
  .

  Variant sim_thread (tid: Ident.t) (n: Time.t) (after_sc: bool)
    (th_ps: PSThread.t lang_ps) (eu: RMWExecUnit.t (A:=unit)): Prop :=
    | sim_thread_intro
        eu1 eu2
        (STEPS1: rtc (RMWExecUnit.state_step tid) eu eu1)
        (SIM_STATE: sim_state (PSThread.state th_ps) (RMWExecUnit.state eu1))
        (SIM_TVIEW: sim_tview (PSLocal.tview (PSThread.local th_ps)) (RMWExecUnit.local eu1))
        (SIM_MEM: sim_memory tid n
                             (PSThread.local th_ps)
                             (PSGlobal.promises (PSThread.global th_ps))
                             (PSGlobal.memory (PSThread.global th_ps))
                             (RMWExecUnit.local eu1) (RMWExecUnit.mem eu1))
        (STEPS2: if after_sc
                 then rtc (RMWExecUnit.state_step_dmbsy_over (S n) tid) eu1 eu2
                 else rtc (RMWExecUnit.state_step_dmbsy_over n tid) eu1 eu2)
        (PROMISES: eu2.(RMWExecUnit.local).(Local.promises) = bot)
  .

  (** TODO
        - only non-atomic writes are promised: add to the thread relation
   *)
  Variant sim_thread_sl (tid: Ident.t) (n: Time.t) (after_sc: bool)
    (gl_ps: PSGlobal.t) (mem_arm: Memory.t):
    forall (sl_ps: {lang: language & Language.state lang} * PSLocal.t)
           (sl_arm: RMWState.t (A:=View.t (A:=unit)) * Local.t (A:=unit)), Prop :=
    | sim_thread_sl_intro
        st_ps lc_ps st_arm lc_arm
        (SIM_THREAD: sim_thread tid n after_sc
                       (PSThread.mk _ st_ps lc_ps gl_ps) (RMWExecUnit.mk st_arm lc_arm mem_arm)):
      sim_thread_sl tid n after_sc gl_ps mem_arm
        (existT _ lang_ps st_ps, lc_ps) (st_arm, lc_arm)
  .

  Variant sim (n: Time.t) (c: PSConfiguration.t) (m: RMWMachine.t): Prop :=
    | sim_intro
        m1
        (PROMISE_STEPS: rtc (RMWMachine.step RMWExecUnit.promise_step) m m1)
        (SIM_THREADS:
          forall tid,
            opt_rel
              (sim_thread_sl tid n true c.(PSConfiguration.global) m.(RMWMachine.mem))
              (IdentMap.find tid c.(PSConfiguration.threads))
              (IdMap.find tid m.(RMWMachine.tpool)))
        (SIM_SC: forall loc,
            PSTime.le (c.(PSConfiguration.global).(PSGlobal.sc) loc) (ntt n))
  .

  Lemma sim_tview_le
        tview lc1_arm lc2_arm
        (SIM: sim_tview tview lc1_arm)
        (LE: Local.le lc1_arm lc2_arm)
        (VNEW2: le lc2_arm.(Local.vrn) lc2_arm.(Local.vwn))
        (OLD2: forall loc,
            le (lc2_arm.(Local.coh) loc) (join lc2_arm.(Local.vro) lc2_arm.(Local.vwo)))
        (FWD2: forall loc,
            le (lc2_arm.(Local.fwdbank) loc).(FwdItem.ts) (View.ts (lc2_arm.(Local.coh) loc))):
    sim_tview tview lc2_arm.
  Proof.
    inv SIM. econs; ss; i.
    - etrans; eauto. apply le_ntt.
      eapply join_le; try apply Time.order; try apply LE.
    - etrans; eauto. apply le_ntt.
      eapply join_le; try apply Time.order; try apply LE.
    - etrans; eauto. apply le_ntt.
      eapply join_le; try apply Time.order; try apply LE.
  Qed.

  Lemma sim_memory_latest_le
        tid n lc_ps gprm_ps mem_ps prm_ps mem_arm
        ts loc loc_ps view val ts_ps
        (SIM: sim_memory tid n lc_ps gprm_ps mem_ps prm_ps mem_arm)
        (LOC: loc = Zpos loc_ps)
        (LATEST: Memory.latest loc ts view mem_arm)
        (READ: Memory.read loc ts mem_arm = Some val)
        (LE: PSTime.le ts_ps (ntt view))
        (CLOSED: exists from msg,
            PSMemory.get loc_ps ts_ps mem_ps = Some (from, msg)):
    PSTime.le ts_ps (ntt ts).
  Proof.
    des. destruct (TimeFacts.le_lt_dec ts_ps PSTime.bot).
    { etrans; eauto. apply PSTime.bot_spec. }
    destruct (TimeFacts.le_lt_dec ts_ps (ntt ts)); ss.
    inv SIM. exploit MEM_COMPLETE; eauto. i. des. subst.
    clear PRM_SOUND PRM_COMPLETE MEM_SOUND MEM_COMPLETE RELEASED.
    unfold Memory.get_msg in *. destruct ts0; ss.
    exploit LATEST; try exact GET_ARM; ss.
    - apply ntt_lt. ss.
    - apply ntt_le. ss.
  Qed.

  Lemma sim_tview_readable
        tid n lc_ps gprm_ps mem_ps lc_arm mem_arm
        loc loc_ps ts view_pre val
        ord
        (TVIEW: sim_tview lc_ps.(PSLocal.tview) lc_arm)
        (MEM: sim_memory tid n lc_ps gprm_ps mem_ps lc_arm mem_arm)
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
    inv TVIEW. clear REL ACQ VOLD FWD.
    specialize (CUR loc_ps). ss.
    eapply sim_memory_latest_le; try exact CUR; eauto.
    - apply Memory.latest_join; ss.
      eapply Memory.latest_mon2; try exact LATEST_PRE. apply VIEW_PRE.
    - inv TVIEW_CLOSED. inv CUR0. specialize (RLX loc_ps). des. eauto.
  Qed.

  Lemma sim_memory_read_arm
        tid n lc_ps gprm_ps mem_ps lc_arm mem_arm
        loc loc_ps ts val_arm
        (MEM: sim_memory tid n lc_ps gprm_ps mem_ps lc_arm mem_arm)
        (INHABITED: PSMemory.inhabited mem_ps)
        (LE: le ts n)
        (LOC: loc = Zpos loc_ps)
        (READ: Memory.read loc ts mem_arm = Some val_arm):
    (<<PROMISED_ARM: Promises.lookup ts lc_arm.(Local.promises)>>) \/
    (<<GPROMISED: gprm_ps loc_ps = true>>) /\
    (<<PROMISED: lc_ps.(PSLocal.promises) loc_ps = false>>) \/
    exists from val released na,
      (<<GET_PS: PSMemory.get loc_ps (ntt ts) mem_ps = Some (from, Message.message val released na)>>) /\
      (<<VAL: sim_val val val_arm>>) /\
      (<<PROMISED_ARM: Promises.lookup ts lc_arm.(Local.promises) = false>>) /\
      (<<REL_FWD: (lc_arm.(Local.fwdbank) loc).(FwdItem.ts) = ts ->
                  if (lc_arm.(Local.fwdbank) loc).(FwdItem.ex)
                  then PSView.opt_le released (Some lc_ps.(PSLocal.tview).(PSTView.acq))
                  else PSView.opt_le released (Some (lc_ps.(PSLocal.tview).(PSTView.rel) loc_ps))>>).
  Proof.
    unfold Memory.read in *. destruct ts; ss.
    - inv READ. right. right. esplits; eauto. condtac; ss.
    - revert READ.
      destruct (List.nth_error mem_arm ts) eqn:Heq; ss.
      condtac; ss. destruct t. ss. inversion e. i. inv READ.
      inv MEM. exploit MEM_SOUND; eauto.
      { instantiate (2:=S ts). eauto. }
      s. i. des. inv LOC.
      unguardH x0. des; subst.
      + exploit PROMISED; ss. i. des.
        destruct (Id.eq_dec tid0 tid); subst; auto.
        right. left. splits; ss.
        destruct (PSLocal.promises lc_ps loc_ps0) eqn:Y; ss.
        exploit PROMISED_PS; ss.
      + right. right. esplits; eauto.
  Qed.

  Lemma sim_tview_fwd
        ts loc ord
        tview lc_arm
        (SIM: sim_tview tview lc_arm):
    ts <= View.ts (Local.coh lc_arm loc) \/
    ts <= View.ts (FwdItem.read_view (Local.fwdbank lc_arm loc) ts ord).
  Proof.
    inv SIM. clear - FWD.
    unfold FwdItem.read_view. condtac; ss.
    - left. apply andb_prop in X. des.
      destruct (FwdItem.ts (Local.fwdbank lc_arm loc) == ts); ss.
      etrans; [|apply FWD].
      rewrite e. ss.
    - right. ss.
  Qed.

  Lemma sim_read_step
        tid n
        lc1_ps gl1_ps
        ord loc
        ex ord_arm (vloc: ValA.t (A:=View.t (A:=unit))) res ts lc1_arm mem_arm lc2_arm
        (TVIEW1: sim_tview (PSLocal.tview lc1_ps) lc1_arm)
        (MEM1: sim_memory tid n lc1_ps (Global.promises gl1_ps) (Global.memory gl1_ps) lc1_arm mem_arm)
        (LC_WF1_PS: PSLocal.wf lc1_ps gl1_ps)
        (GL_WF1_PS: PSGlobal.wf gl1_ps)
        (ORD: ord_arm = ps_to_rmw_ordr ord)
        (LOC: vloc.(ValA.val) = Zpos loc)
        (LE: le ts n)
        (STEP: Local.read ex ord_arm vloc res ts lc1_arm mem_arm lc2_arm):
    (<<PROMISED_ARM: Promises.lookup ts (Local.promises lc1_arm)>>) \/
    (exists val released lc2_ps,
        (<<STEP_PS: PSLocal.read_step lc1_ps gl1_ps loc (ntt ts) val released ord lc2_ps>>) /\
        (<<VAL: sim_val val res.(ValA.val)>>) /\
        (<<TVIEW2: sim_tview (PSLocal.tview lc2_ps) lc2_arm>>) /\
        (<<MEM2: sim_memory tid n lc2_ps (Global.promises gl1_ps) (Global.memory gl1_ps) lc2_arm mem_arm>>)) \/
    (exists val,
        (<<STEP_PS: PSLocal.racy_read_step lc1_ps gl1_ps loc None val ord>>) /\
        (<<VAL: sim_val val res.(ValA.val)>>) /\
        (<<TVIEW2: sim_tview (PSLocal.tview lc1_ps) lc2_arm>>) /\
        (<<MEM2: sim_memory tid n lc1_ps (Global.promises gl1_ps) (Global.memory gl1_ps) lc2_arm mem_arm>>)).
  Proof.
    exploit (Local.read_incr (A:=unit)); eauto. i.
    inv STEP.
    exploit sim_memory_read_arm; eauto; try apply GL_WF1_PS. i. des; auto.
    { (* race with a promise *)
      ss. right. right.
      esplits; eauto; [|econs; ss; apply MEM1].
      eapply sim_tview_le; try exact TVIEW1; ss; i.
      - eapply join_le; try apply View.order; try refl. apply TVIEW1.
      - unfold fun_add. condtac.
        + apply join_spec.
          * etrans; [apply TVIEW1|].
            apply join_spec; try apply join_r.
            etrans; [|apply join_l]. apply join_l.
          * etrans; [|apply join_l]. apply join_r.
        + etrans; [apply TVIEW1|].
          eapply join_le; try apply View.order. refl.
      - etrans; [apply TVIEW1|]. apply x0.
    }

    { (* normal read *)
      exploit sim_tview_readable; try exact LATEST; eauto; try apply LC_WF1_PS.
      { apply joins_le. right. left. ss. }
      ss. i. des.
      right. left. esplits.
      { econs; eauto; try refl. }
      { ss. }

      { econs; s; i.
        { etrans; [apply TVIEW1|]. apply le_ntt. ss.
          eapply join_le; try apply Time.order. apply x0.
        }
        { repeat apply PSTime.join_spec.
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
            exploit (sim_tview_fwd ts); try exact TVIEW1. i. des.
            - etrans; [|apply join_l]. apply x2.
            - etrans; [|apply join_r]. etrans; [|apply join_r]. apply x2.
          }
          { condtac; ss; try apply PSTime.bot_spec.
            destruct released; s; try apply PSTime.bot_spec.
            unfold FwdItem.read_view. condtac; ss.
            - apply andb_prop in X0. des.
              rewrite Bool.negb_true_iff in X1.
              exploit REL_FWD.
              { destruct (FwdItem.ts (Local.fwdbank lc1_arm (ValA.val vloc)) == ts); ss. }
              condtac.
              + i. inv x2.
                rewrite Bool.andb_true_l in X1.
                apply Bool.orb_false_elim in X1. des.
                destruct ord; ss.
              + i. inv x2.
                etrans; [apply LE0|].
                etrans; [apply LC_WF1_PS|].
                etrans; [apply TVIEW1|].
                apply le_ntt. ss.
                eapply join_le; try apply Time.order.
                unfold fun_add. condtac; ss.
                rewrite e. apply join_l.
            - unfold ifc. repeat (condtac; try by destruct ord; ss).
              inv MEM1. exploit RELEASED; eauto. i.
              clear PRM_SOUND PRM_COMPLETE MEM_SOUND MEM_COMPLETE RELEASED.
              etrans; try apply x2. apply le_ntt.
              etrans; [|apply join_l].
              etrans; apply join_r.
          }
        }

        { repeat apply PSTime.join_spec.
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
            exploit (sim_tview_fwd ts); try exact TVIEW1. i. des.
            - etrans; [|apply join_l]. apply x2.
            - etrans; [|apply join_r]. etrans; [|apply join_r]. apply x2.
          }
          { condtac; ss; try apply PSTime.bot_spec.
            destruct released; s; try apply PSTime.bot_spec.
            unfold FwdItem.read_view. condtac; ss.
            - apply andb_prop in X0. des.
              rewrite Bool.negb_true_iff in X1.
              exploit REL_FWD.
              { destruct (FwdItem.ts (Local.fwdbank lc1_arm (ValA.val vloc)) == ts); ss. }
              condtac.
              + i. inv x2.
                etrans; [apply LE0|].
                etrans; [apply TVIEW1|].
                apply le_ntt. ss.
                eapply join_le; try apply Time.order.
                unfold fun_add. condtac; ss.
                rewrite e. apply join_l.
              + i. inv x2.
                etrans; [apply LE0|].
                etrans; [apply LC_WF1_PS|].
                etrans; [apply LC_WF1_PS|].
                etrans; [apply TVIEW1|].
                apply le_ntt. ss.
                eapply join_le; try apply Time.order.
                unfold fun_add. condtac; ss.
                rewrite e. apply join_l.
            - unfold ifc. repeat (condtac; try by destruct ord; ss).
              inv MEM1. exploit RELEASED; eauto. i.
              clear PRM_SOUND PRM_COMPLETE MEM_SOUND MEM_COMPLETE RELEASED.
              etrans; try apply x2. apply le_ntt.
              etrans; [|apply join_l].
              etrans; apply join_r.
          }
        }

        { eapply join_le; try apply View.order; try refl. apply TVIEW1. }
        { unfold fun_add. condtac; ss.
          - apply join_spec.
            + etrans; [apply TVIEW1|].
              eapply join_le; try apply View.order. refl.
            + etrans; [|apply join_l]. apply join_r.
          - etrans; [apply TVIEW1|].
            eapply join_le; try apply View.order. refl.
        }
        { etrans; [apply TVIEW1|]. apply x0. }
      }

      { inv MEM1. econs; s; eauto. i.
        exploit MEM_SOUND; eauto. i. des.
        esplits; eauto. unguardH x2. des; subst.
        - left. auto.
        - right. esplits; eauto. i.
          apply REL_FWD0 in H. condtac; ss.
          etrans; [exact H|]. econs.
          do 2 (etrans; [|apply View.join_l]). refl.
      }
    }
  Qed.

  Lemma sim_tview_writable
        tview lc_arm
        loc loc_ps ts view_pre
        ord
        (TVIEW: sim_tview tview lc_arm)
        (LOC: loc = Zpos loc_ps)
        (VIEW_PRE: le lc_arm.(Local.vwn) view_pre)
        (COH: lt (lc_arm.(Local.coh) loc).(View.ts) ts)
        (EXT: lt view_pre.(View.ts) ts):
    PSTView.writable (PSTView.cur tview) loc_ps (ntt ts) ord.
  Proof.
    subst. econs.
    eapply TimeFacts.le_lt_lt; [apply TVIEW|].
    apply lt_ntt. ss.
    apply Time.max_lub_lt; ss.
    eapply Time.le_lt_trans; try exact EXT.
    etrans; [|apply VIEW_PRE].
    apply TVIEW.
  Qed.

  Lemma sim_memory_S
        tid n lc_ps gprm_ps mem_ps lc_arm mem_arm
        loc from msg
        (MEM: sim_memory tid n lc_ps gprm_ps mem_ps lc_arm mem_arm)
        (RSV_LE: Memory.le (PSLocal.reserves lc_ps) mem_ps)
        (GET: PSMemory.get loc (ntt (S n)) mem_ps = Some (from, msg))
        (MSG: msg <> Message.reserve):
    sim_memory tid (S n) lc_ps gprm_ps mem_ps lc_arm mem_arm.
  Proof.
    inv MEM. move GET at bottom.
    exploit MEM_COMPLETE; eauto.
    { ss. eapply TimeFacts.le_lt_lt; try apply PSTime.bot_spec.
      apply PSTime.incr_spec.
    }
    i. des.
    apply ntt_inj in TO. subst.
    econs; i; eauto.
    - exploit PRM_SOUND; eauto. i. des. esplits; eauto. i.
      inv H; eauto.
      rewrite GET_ARM0 in *. inv GET_ARM.
      rewrite LOC0 in *. inv LOC.
      exploit RSV_LE; try eassumption. i. congr.
    - exploit PRM_COMPLETE; eauto. i. des.
      esplits; eauto. etrans; eauto. apply le_S. refl.
    - exploit MEM_SOUND; eauto. i. des.
      esplits; eauto. unguardH x0. des; subst.
      + left. split; ss. i. inv H; eauto. ss. congr.
      + right. esplits; eauto.
  Qed.

  Lemma sim_fulfill_step
        tid n
        lc1_ps gl1_ps
        ord loc
        (ex: bool) ord_arm (vloc: ValA.t (A:=View.t (A:=unit))) vval res ts view_pre lc1_arm mem_arm lc2_arm
        releasedm
        (TVIEW1: sim_tview (PSLocal.tview lc1_ps) lc1_arm)
        (MEM1: sim_memory tid n lc1_ps (Global.promises gl1_ps) (Global.memory gl1_ps) lc1_arm mem_arm)
        (LC_WF1_PS: PSLocal.wf lc1_ps gl1_ps)
        (GL_WF1_PS: PSGlobal.wf gl1_ps)
        (ORD: ord_arm = ps_to_rmw_ordw ord)
        (ORD_NA: le ts n -> Ordering.le ord Ordering.na)
        (LOC: vloc.(ValA.val) = Zpos loc)
        (RELEASEDM_WF: View.opt_wf releasedm)
        (RELEASEDM1: if ex
                     then View.opt_le releasedm (Some lc1_ps.(PSLocal.tview).(PSTView.acq))
                     else releasedm = None)
        (RELEASEDM2: forall loc', PSTime.le ((View.unwrap releasedm).(View.rlx) loc') (ntt ts))
        (STEP: Local.fulfill ex ord_arm vloc vval res ts tid view_pre lc1_arm mem_arm lc2_arm):
    exists from lc2_ps gl2_ps,
      (<<CANCEL_PS: PSLocal.cancel_step lc1_ps gl1_ps loc from (ntt ts) lc2_ps gl2_ps>>) /\
      exists released lc3_ps gl3_ps,
        (<<STEP_PS: PSLocal.write_step lc2_ps gl2_ps loc from (ntt ts) vval.(ValA.val) releasedm released ord lc3_ps gl3_ps>>) /\
        (<<TVIEW2: sim_tview (PSLocal.tview lc3_ps) lc2_arm>>) /\
        (<<MEM2: sim_memory tid n lc3_ps (Global.promises gl3_ps) (Global.memory gl3_ps) lc2_arm mem_arm>>).
  Proof.
    exploit (Local.fulfill_incr (A:=unit)); eauto. intro INCR.
    inv STEP. dup MEM1. inv MEM0.
    exploit MEM_SOUND; eauto. s. i. des.
    rewrite LOC in LOC0. symmetry in LOC0. inv LOC0.
    unguardH x0. des; try congr. subst.
    exploit PRM_SOUND; eauto. s. i. des.
    clear PRM_SOUND PRM_COMPLETE MEM_SOUND MEM_COMPLETE RELEASED TID.
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
               (Message.message (ValA.val vval) (TView.write_released tview1 loc (ntt ts) releasedm ord) (Ordering.le ord Ordering.na))); ss.
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
    { econs; try exact FULFILL; eauto.
      inv WRITABLE.
      eapply sim_tview_writable; [..|exact COH|exact EXT]; eauto.
      apply joins_le. right. right. right. left. ss.
    }

    { s. clear x1 PROMISED PROMISED_PS rsv2 x0 mem2 x2 mem0 x3 prm2 gprm2 FULFILL PROMISED0.
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
            * etrans; [apply TVIEW1|].
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
      { unfold fun_add. condtac.
        - etrans; [|apply join_r]. apply join_r.
        - etrans; [apply TVIEW1|].
          eapply join_le; try apply View.order. refl.
      }
      { unfold fun_add. condtac; try refl. apply TVIEW1. }
    }

    { s. clear INCR. inv MEM1. econs; s; i.
      { revert PROMISED_ARM.
        rewrite Promises.unset_o. condtac; ss. i.
        exploit PRM_SOUND; try exact PROMISED_ARM. i. des.
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
      { destruct (PSLoc.eq_dec loc0 loc).
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

      { destruct (Nat.eq_dec ts0 ts); subst.
        - rewrite GET_ARM in *. inv MSG.
          exploit PSMemory.add_get0; try exact x3. i. des.
          esplits; try exact GET0; ss.
          right. esplits; ss.
          + i. clear H. condtac; ss.
            { revert X. unfold fun_add. condtac; ss; try congr. i. subst.
              unfold TView.write_released. condtac; econs.
              apply PSView.join_spec.
              - inv RELEASEDM1; ss; try apply PSView.bot_spec.
                etrans; try exact LE. apply PSView.join_l.
              - ss. unfold LocFun.add. condtac; ss.
                condtac; ss; apply PSView.join_spec.
                + etrans; [apply LC_WF1_PS|]. apply PSView.join_l.
                + apply PSView.join_r.
                + etrans; [apply LC_WF1_PS|]. s.
                  etrans; [apply LC_WF1_PS|]. apply PSView.join_l.
                + apply PSView.join_r.
            }
            { revert X. unfold fun_add. condtac; ss; try congr. i. subst. subst.
              unfold TView.write_released. condtac; econs. ss.
              unfold LocFun.add. condtac; ss.
              condtac; ss; apply PSView.join_spec; try apply PSView.bot_spec; refl.
            }
          + rewrite Promises.unset_o. condtac; ss. congr.
        - exploit MEM_SOUND; eauto. i. des.
          exploit Memory.remove_get1; try exact GET_PS0; eauto. i. des.
          { apply ntt_inj in x8. congr. }
          exploit Memory.add_get1; try exact x6; eauto. i.
          esplits; eauto. unguardH x4. des; subst.
          + left. split; ss. i.
            exploit PROMISED1; eauto. i. des.
            inv FULFILL.
            { splits; ss. rewrite Promises.unset_o. condtac; ss. }
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
            rewrite Promises.unset_o. condtac; ss.
          + right. esplits; eauto; cycle 1.
            { rewrite Promises.unset_o. condtac; ss. }
            unfold fun_add. condtac; ss; try congr. i.
            exploit REL_FWD; eauto. condtac; ss; i.
            * etrans; eauto. econs. apply View.join_l.
            * etrans; eauto. econs.
              unfold LocFun.add. condtac; ss; try refl. subst.
              condtac; try apply View.join_l.
              etrans; [apply LC_WF1_PS|]. apply View.join_l.
      }

      { revert GET_PS0.
        erewrite PSMemory.add_o; eauto. condtac; ss.
        - i. des. inv GET_PS0. esplits; eauto.
        - erewrite Memory.remove_o; eauto. condtac; ss. eauto.
      }
      { revert GET.
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
            * etrans; [apply TVIEW1|].
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
End PStoRMW.
