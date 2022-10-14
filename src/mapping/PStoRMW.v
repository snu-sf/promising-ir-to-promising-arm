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
    | sim_val_undef
        v:
      sim_val Const.undef v
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
        (VNEW: le lc_arm.(Local.vrn) lc_arm.(Local.vwn))
        (REL: forall loc loc',
            PSTime.le
              ((tview.(PSTView.rel) loc).(View.rlx) loc')
              (ntt (View.ts (join lc_arm.(Local.vwn) (ifc (PSLoc.eq_dec loc' loc) (lc_arm.(Local.coh) (Zpos loc)))))))
        (CUR: forall loc,
            PSTime.le
              (tview.(PSTView.cur).(View.rlx) loc)
              (ntt (View.ts (join lc_arm.(Local.vrn) (lc_arm.(Local.coh) (Zpos loc))))))
        (ACQ: forall loc,
            PSTime.le
              (tview.(PSTView.acq).(View.rlx) loc)
              (ntt (View.ts (join lc_arm.(Local.vrn) (lc_arm.(Local.coh) (Zpos loc))))))
        (OLD: forall loc, le (lc_arm.(Local.coh) loc) (join lc_arm.(Local.vro) lc_arm.(Local.vwo)))
        (FWD: forall loc,
            le (lc_arm.(Local.fwdbank) loc).(FwdItem.ts) (View.ts (lc_arm.(Local.coh) loc)))
  .
  #[export] Hint Constructors sim_tview: core.

  Variant sim_memory (tid: Ident.t) (n: Time.t)
    (lc_ps: PSLocal.t) (gprm_ps: BoolMap.t) (mem_ps: PSMemory.t)
    (prm_arm: Promises.t) (mem_arm: Memory.t): Prop :=
    | sim_memory_intro
        (PRM_SOUND: forall ts (LE: le ts n) (PROMISED_ARM: Promises.lookup ts prm_arm),
          exists msg_arm loc_ps from,
            (<<GET_ARM: Memory.get_msg ts mem_arm = Some msg_arm>>) /\
            (<<TID: msg_arm.(Msg.tid) = tid>>) /\
            (<<LOC: msg_arm.(Msg.loc) = Zpos loc_ps>>) /\
            (<<PROMISED_PS: lc_ps.(PSLocal.promises) loc_ps = true>>) /\
            (<<RESERVED: Memory.get loc_ps (ntt ts) (PSLocal.reserves lc_ps) = Some (from, Message.reserve)>>))
        (PRM_COMPLETE: forall loc (PROMISED_PS: lc_ps.(PSLocal.promises) loc = true),
          exists ts,
            (<<LE: le ts n>>) /\
            (<<PROMISED_ARM: Promises.lookup ts prm_arm>>))
        (MEM_SOUND: forall ts msg_arm
                           (GET_ARM: Memory.get_msg ts mem_arm = Some msg_arm),
          exists loc_ps from msg_ps,
            (<<LOC: msg_arm.(Msg.loc) = Zpos loc_ps>>) /\
            (<<GET_PS: PSMemory.get loc_ps (ntt ts) mem_ps = Some (from, msg_ps)>>) /\
            (__guard__ (
               (<<FROM: from = PSTime.bot>>) \/
               exists fts fval ftid,
                 (<<FROM: from = ntt fts>>) /\
                 (<<GET_FROM_ARM: Memory.get_msg fts mem_arm = Some (Msg.mk msg_arm.(Msg.loc) fval ftid)>>) /\
                 (<<LATEST: Memory.latest msg_arm.(Msg.loc) fts ts mem_arm>>))) /\
            (__guard__ (
               (<<RESERVED: msg_ps = Message.reserve>>) /\
               (<<PROMISED: le ts n ->
                            (<<GPROMISED: gprm_ps loc_ps = true>>) /\
                            (<<PROMISED_PS: lc_ps.(PSLocal.promises) loc_ps <-> msg_arm.(Msg.tid) = tid>>) /\
                            (<<PROMISED_ARM: Promises.lookup ts prm_arm <-> msg_arm.(Msg.tid) = tid>>)>>) \/
               exists val_ps released na,
                 (<<MSG: msg_ps = Message.message val_ps released na>>) /\
                 (<<VAL: sim_val val_ps msg_arm.(Msg.val)>>) /\
                 (<<MSG_FWD: msg_arm.(Msg.tid) = tid ->
                             PSView.opt_le released (Some (lc_ps.(PSLocal.tview).(PSTView.rel) loc_ps))>>))))
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
                             (Local.promises (RMWExecUnit.local eu1)) (RMWExecUnit.mem eu1))
        (STEPS2: if after_sc
                 then rtc (RMWExecUnit.state_step_dmbsy_over (S n) tid) eu1 eu2
                 else rtc (RMWExecUnit.state_step_dmbsy_over n tid) eu1 eu2)
        (PROMISES: eu2.(RMWExecUnit.local).(Local.promises) = bot)
  .

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
      unfold ifc. condtac; ss. apply LE.
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
        (MEM: sim_memory tid n lc_ps gprm_ps mem_ps lc_arm.(Local.promises) mem_arm)
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
    inv TVIEW. clear REL ACQ OLD FWD.
    specialize (CUR loc_ps). ss.
    eapply sim_memory_latest_le; try exact CUR; eauto.
    - apply Memory.latest_join; ss.
      eapply Memory.latest_mon2; try exact LATEST_PRE. apply VIEW_PRE.
    - inv TVIEW_CLOSED. inv CUR0. specialize (RLX loc_ps). des. eauto.
  Qed.

  Lemma sim_memory_read_arm
        tid n lc_ps gprm_ps mem_ps prm_arm mem_arm
        loc loc_ps ts val_arm
        (MEM: sim_memory tid n lc_ps gprm_ps mem_ps prm_arm mem_arm)
        (INHABITED: PSMemory.inhabited mem_ps)
        (LE: le ts n)
        (LOC: loc = Zpos loc_ps)
        (READ: Memory.read loc ts mem_arm = Some val_arm):
    (<<PROMISED_ARM: Promises.lookup ts prm_arm>>) \/
    (<<GPROMISED: gprm_ps loc_ps = true>>) /\
    (<<PROMISED: lc_ps.(PSLocal.promises) loc_ps = false>>) \/
    exists from val released na,
      (<<GET_PS: PSMemory.get loc_ps (ntt ts) mem_ps = Some (from, Message.message val released na)>>) /\
      (<<VAL: sim_val val val_arm>>).
  Proof.
    unfold Memory.read in *. destruct ts; ss.
    - inv READ. right. right. esplits; eauto.
    - des_ifs. destruct t. ss. inversion e. subst.
      inv MEM. exploit MEM_SOUND; eauto.
      { instantiate (2:=S ts). eauto. }
      s. i. des. inv LOC.
      unguardH x1. des; subst.
      + exploit PROMISED; ss. i. des.
        destruct (Id.eq_dec tid0 tid); subst; auto.
        right. left. splits; ss.
        destruct (PSLocal.promises lc_ps loc_ps0) eqn:X; ss.
        exploit PROMISED_PS; ss.
      + right. right. esplits; eauto.
  Qed.

  Lemma sim_read_step
        tid n
        lc1_ps gl1_ps
        ord loc
        ex ord_arm (vloc: ValA.t (A:=View.t (A:=unit))) res ts lc1_arm mem_arm lc2_arm
        (TVIEW1: sim_tview (PSLocal.tview lc1_ps) lc1_arm)
        (MEM1: sim_memory tid n lc1_ps (Global.promises gl1_ps) (Global.memory gl1_ps) (Local.promises lc1_arm) mem_arm)
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
        (<<MEM2: sim_memory tid n lc2_ps (Global.promises gl1_ps) (Global.memory gl1_ps) (Local.promises lc2_arm) mem_arm>>)) \/
    (exists val,
        (<<STEP_PS: PSLocal.racy_read_step lc1_ps gl1_ps loc None val ord>>) /\
        (<<VAL: sim_val val res.(ValA.val)>>) /\
        (<<TVIEW2: sim_tview (PSLocal.tview lc1_ps) lc2_arm>>) /\
        (<<MEM2: sim_memory tid n lc1_ps (Global.promises gl1_ps) (Global.memory gl1_ps) (Local.promises lc2_arm) mem_arm>>)).
  Proof.
    exploit (Local.read_incr (A:=unit)); eauto. i.
    inv STEP.
    exploit sim_memory_read_arm; eauto; try apply GL_WF1_PS. i. des; auto.
    { (* race with a promise *)
      ss. right. right. esplits; eauto.
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
      - econs; eauto; try refl.
      - ss.
      - econs; s; i.
        + admit.
        + admit.
        + admit.
        + admit.
        + admit.
        + admit.
      - inv MEM1. econs; s; eauto.
    }
  Admitted.
End PStoRMW.
