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

Definition orr (a b: bool): bool := a || b.

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
      rmw_instr_dmb
        (Ordering.le Ordering.acqrel ordr || Ordering.le Ordering.seqcst ordw)
        (Ordering.le Ordering.acqrel ordr || Ordering.le Ordering.acqrel ordw)
        (Ordering.le Ordering.seqcst ordw)
        (Ordering.le Ordering.acqrel ordw)
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

  Definition sim_regs (regs_ps: RegFile.t) (regs_arm: RMap.t (A:=View.t (A:=unit))): Prop :=
    forall r, sim_val (IdentFun.find r regs_ps) (RMap.find r regs_arm).(ValA.val).

  Variant sim_program_event: forall (e_ps: ProgramEvent.t) (e_arm: RMWEvent.t (A:=View.t (A:=unit))), Prop :=
    | sim_program_event_internal:
      sim_program_event ProgramEvent.silent RMWEvent.internal
    | sim_program_event_control
        ctrl:
      sim_program_event ProgramEvent.silent (RMWEvent.control ctrl)
    | sim_program_event_read
        loc_ps val_ps ord_ps
        ord_arm loc_arm val_arm
        (LOC: loc_arm.(ValA.val) = Zpos loc_ps)
        (VAL: sim_val val_ps val_arm.(ValA.val))
        (ORD: ord_arm = ps_to_rmw_ordr ord_ps)
      :
      sim_program_event (ProgramEvent.read loc_ps val_ps ord_ps)
                        (RMWEvent.read ord_arm loc_arm val_arm)
    | sim_program_event_write
        loc_ps val_ps ord_ps
        ord_arm loc_arm val_arm
        (LOC: loc_arm.(ValA.val) = Zpos loc_ps)
        (VAL: sim_val val_ps val_arm.(ValA.val))
        (ORD: ord_arm = ps_to_rmw_ordw ord_ps)
      :
      sim_program_event (ProgramEvent.write loc_ps val_ps ord_ps)
                        (RMWEvent.write ord_arm loc_arm val_arm)
    | sim_program_event_fadd
        loc_ps vold_ps vnew_ps ordr_ps ordw_ps
        ordr_arm ordw_arm loc_arm vold_arm vnew_arm
        (LOC: loc_arm.(ValA.val) = Zpos loc_ps)
        (VOLD: sim_val vold_ps vold_arm.(ValA.val))
        (VNEW: sim_val vnew_ps vnew_arm.(ValA.val))
        (ORDR: ordr_arm = ps_to_rmw_ordr ordr_ps)
        (ORDW: ordw_arm = ps_to_rmw_ordw ordw_ps)
      :
      sim_program_event (ProgramEvent.update loc_ps vold_ps vnew_ps ordr_ps ordw_ps)
                        (RMWEvent.fadd ordr_arm ordw_arm loc_arm vold_arm vnew_arm)
    | sim_program_event_dmb
        ordr_ps ordw_ps
        rr rw wr ww
        (RR: rr = Ordering.le Ordering.acqrel ordr_ps || Ordering.le Ordering.seqcst ordw_ps)
        (RW: rw = Ordering.le Ordering.acqrel ordr_ps || Ordering.le Ordering.acqrel ordw_ps)
        (WR: wr = Ordering.le Ordering.seqcst ordw_ps)
        (WW: ww = Ordering.le Ordering.acqrel ordw_ps):
      sim_program_event (ProgramEvent.fence ordr_ps ordw_ps)
                        (RMWEvent.dmb rr rw wr ww)
  .
  #[export] Hint Constructors sim_program_event: core.

  Variant sim_state (st_ps: State.t) (st_arm: RMWState.t (A:=View.t (A:=unit))): Prop :=
    | sim_state_intro
        (STMTS: RMWState.stmts st_arm = ps_to_rmw_stmts (State.stmts st_ps))
        (REGS: sim_regs st_ps.(State.regs) st_arm.(RMWState.rmap))
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
              (ntt (View.ts (join (join lc_arm.(Local.vrn) lc_arm.(Local.vro)) (lc_arm.(Local.coh) (Zpos loc))))))
        (VNEW: le lc_arm.(Local.vrn) lc_arm.(Local.vwn))
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
                 (<<PROMISED_ARM: Promises.lookup ts lc_arm.(Local.promises) = false>>))))
        (MEM_COMPLETE: forall loc_ps from to msg_ps
                              (TO: PSTime.lt PSTime.bot to)
                              (GET_PS: PSMemory.get loc_ps to mem_ps = Some (from, msg_ps)),
          exists ts msg_arm,
            (<<TO: to = ntt ts>>) /\
            (<<GET_ARM: Memory.get_msg ts mem_arm = Some msg_arm>>) /\
            (<<LOC: msg_arm.(Msg.loc) = Zpos loc_ps>>))
        (FWD: forall loc ts (FWD: (lc_arm.(Local.fwdbank) loc).(FwdItem.ts) = ts),
            exists loc_ps from val released na,
              (<<LOC: loc = Zpos loc_ps>>) /\
              (<<GET_PS: PSMemory.get loc_ps (ntt ts) mem_ps = Some (from, Message.message val released na)>>) /\
              (<<REL_FWD: if (lc_arm.(Local.fwdbank) loc).(FwdItem.ex)
                          then forall loc, PSTime.le
                                        ((PSView.unwrap released).(View.rlx) loc)
                                        (ntt (View.ts (join (join lc_arm.(Local.vrn) lc_arm.(Local.vro))
                                                            (lc_arm.(Local.coh) (Zpos loc)))))
                            (* PSView.opt_le released (Some lc_ps.(PSLocal.tview).(PSTView.acq)) *)
                          else PSView.opt_le released (Some (lc_ps.(PSLocal.tview).(PSTView.rel) loc_ps))>>))
        (RELEASED: forall loc from to val released na
                          (GET: PSMemory.get loc to mem_ps = Some (from, Message.message val released na)),
          forall loc', PSTime.le ((View.unwrap released).(View.rlx) loc') to)
  .

  Variant sim_thread (tid: Ident.t) (n: Time.t)
    (th_ps: PSThread.t lang_ps) (eu: RMWExecUnit.t (A:=unit)): Prop :=
    | sim_thread_intro
        (SIM_STATE: sim_state (PSThread.state th_ps) (RMWExecUnit.state eu))
        (SIM_TVIEW: sim_tview (PSLocal.tview (PSThread.local th_ps)) (RMWExecUnit.local eu))
        (SIM_MEM: sim_memory tid n
                             (PSThread.local th_ps)
                             (PSGlobal.promises (PSThread.global th_ps))
                             (PSGlobal.memory (PSThread.global th_ps))
                             (RMWExecUnit.local eu) (RMWExecUnit.mem eu))
  .

  Lemma sim_val_eq_inv
        val1 val2 val_arm
        (VAL1: sim_val val1 val_arm)
        (VAL2: sim_val val2 val_arm):
    val1 = val2.
  Proof.
    inv VAL1. inv VAL2. ss.
  Qed.

  Lemma sim_regs_eval_expr
        regs_ps regs_arm e
        (SIM: sim_regs regs_ps regs_arm):
    sim_val (RegFile.eval_expr regs_ps e) (sem_expr regs_arm (ps_to_rmw_expr e)).(ValA.val).
  Proof.
    induction e; ss.
    - destruct op. ss.
      inv IHe; ss. condtac; econs.
    - destruct op; inv IHe1; inv IHe2; ss.
  Qed.

  Lemma sim_regs_add
        regs_ps regs_arm
        r val_ps (val_arm: ValA.t (A:=View.t (A:=unit)))
        (SIM: sim_regs regs_ps regs_arm)
        (VAL: sim_val val_ps val_arm.(ValA.val)):
    sim_regs (IdentFun.add r val_ps regs_ps)
             (RMap.add r val_arm regs_arm).
  Proof.
    ii. rewrite IdentFun.add_spec, RMap.add_o.
    condtac; ss; subst.
    - condtac; ss. congr.
    - condtac; ss.
  Qed.

  Lemma sim_state_step
        st1_ps st1_arm e_arm st2_arm
        (SIM1: sim_state st1_ps st1_arm)
        (STEP: RMWState.step e_arm st1_arm st2_arm):
    exists e_ps st2_ps,
      (<<STEP_PS: State.step e_ps st1_ps st2_ps>>) /\
      (<<EVENT: sim_program_event e_ps e_arm>>) /\
      (<<SIM2: sim_state st2_ps st2_arm>>).
  Proof.
    destruct st1_ps as [regs1_ps stmts1_ps].
    destruct st1_arm as [stmts1_arm regs1_arm].
    destruct st2_arm as [stmts2_arm regs2_arm].
    inv SIM1. ss.
    destruct stmts1_ps; ss; subst; [inv STEP|].
    destruct t; ss; cycle 1.
    { (* ite *)
      inv STEP. condtac.
      - esplits; [econs 2|..]; ss.
        + des_ifs.
          exploit sim_regs_eval_expr; eauto.
          rewrite Heq. ii. inv x0. congr.
        + econs; ss. rewrite <- List.map_app. ss.
      - esplits; [econs 3|..]; ss.
        + des_ifs.
          exploit sim_regs_eval_expr; eauto.
          rewrite Heq. ii. inv x0. congr.
        + econs; ss. rewrite <- List.map_app. ss.
    }
    { (* dowhile *)
      inv STEP. esplits; [econs 4|..]; ss.
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
      apply sim_regs_add; ss.
      apply sim_regs_eval_expr; ss.
    }
    { (* load *)
      esplits; [econs 1; econs 3|..]; eauto.
      econs; ss.
      apply sim_regs_add; ss.
    }
    { (* store *)
      esplits; [econs 1; econs 4|..]; eauto.
      econs; ss.
      apply sim_regs_eval_expr; ss.
    }
    { (* fadd *)
      esplits; [econs 1; econs 5|..]; eauto.
      - econs; ss. s.
        exploit sim_regs_eval_expr; eauto. i.
        inv x0. rewrite <- H0. ss.
      - econs; ss.
        apply sim_regs_add; ss.
    }
    { (* dmb *)
      esplits; [econs 1; econs 6|..]; eauto.
    }
  Qed.

  Lemma sim_tview_le
        tview lc1_arm lc2_arm
        (SIM: sim_tview tview lc1_arm)
        (LE: Local.le lc1_arm lc2_arm)
        (VNEW2: le lc2_arm.(Local.vrn) lc2_arm.(Local.vwn)):
    sim_tview tview lc2_arm.
  Proof.
    inv SIM. econs; ss; i.
    - etrans; eauto. apply le_ntt.
      eapply join_le; try apply Time.order; try apply LE.
    - etrans; eauto. apply le_ntt.
      eapply join_le; try apply Time.order; try apply LE.
    - etrans; eauto. apply le_ntt.
      repeat eapply join_le; try apply Time.order; try apply LE.
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
    inv TVIEW. clear REL ACQ.
    specialize (CUR loc_ps). ss.
    eapply sim_memory_latest_le; try exact CUR; eauto.
    - apply Memory.latest_join; ss.
      eapply Memory.latest_mon2; try exact LATEST_PRE. apply VIEW_PRE.
    - inv TVIEW_CLOSED. inv CUR0. specialize (RLX loc_ps). des. eauto.
  Qed.

  Lemma sim_memory_read
        tid n lc_ps gprm_ps mem_ps lc_arm mem_arm
        loc loc_ps ts ord val_arm
        (MEM: sim_memory tid n lc_ps gprm_ps mem_ps lc_arm mem_arm)
        (INHABITED: PSMemory.inhabited mem_ps)
        (LE: le (FwdItem.read_view (Local.fwdbank lc_arm loc) ts ord).(View.ts) n)
        (LOC: loc = Zpos loc_ps)
        (READ: Memory.read loc ts mem_arm = Some val_arm):
    (<<PROMISED_ARM: Promises.lookup ts lc_arm.(Local.promises)>>) \/
    (<<GPROMISED: gprm_ps loc_ps = true>>) /\
    (<<PROMISED: lc_ps.(PSLocal.promises) loc_ps = false>>) \/
    exists from val released na,
      (<<GET_PS: PSMemory.get loc_ps (ntt ts) mem_ps = Some (from, Message.message val released na)>>) /\
      (<<VAL: sim_val val val_arm>>) /\
      (<<REL_FWD: (lc_arm.(Local.fwdbank) loc).(FwdItem.ts) = ts ->
                  if (lc_arm.(Local.fwdbank) loc).(FwdItem.ex)
                  then PSView.opt_le released (Some lc_ps.(PSLocal.tview).(PSTView.acq))
                  else PSView.opt_le released (Some (lc_ps.(PSLocal.tview).(PSTView.rel) loc_ps))>>).
  Proof.
    unfold Memory.read in *. destruct ts; ss.
    { inv READ. right. right. esplits; eauto. condtac; ss. }
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
      exploit FWD; try exact e. i. des. inv LOC. ss.
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
        inv LOC. rewrite GET_PS0 in *. inv GET_PS. ss.
  Qed.

  Lemma wf_arm_fwd
        tid mem_arm
        ts loc ord lc_arm
        (WF: RMWLocal.wf (A:=unit) tid lc_arm mem_arm):
    ts <= View.ts (Local.coh lc_arm loc) \/
    ts <= View.ts (FwdItem.read_view (Local.fwdbank lc_arm loc) ts ord).
  Proof.
    inv WF. clear - FWD.
    unfold FwdItem.read_view. condtac; ss.
    - left. apply andb_prop in X. des.
      destruct (FwdItem.ts (Local.fwdbank lc_arm loc) == ts); ss.
      etrans; [|apply FWD].
      rewrite e. ss.
    - right. ss.
  Qed.

  Lemma sim_read
        tid n
        lc1_ps gl1_ps
        ord loc
        ex ord_arm (vloc: ValA.t (A:=View.t (A:=unit))) res ts lc1_arm mem_arm lc2_arm
        (TVIEW1: sim_tview (PSLocal.tview lc1_ps) lc1_arm)
        (MEM1: sim_memory tid n lc1_ps (Global.promises gl1_ps) (Global.memory gl1_ps) lc1_arm mem_arm)
        (LC_WF1_PS: PSLocal.wf lc1_ps gl1_ps)
        (GL_WF1_PS: PSGlobal.wf gl1_ps)
        (WF1_ARM: RMWLocal.wf tid lc1_arm mem_arm)
        (ORD: ord_arm = ps_to_rmw_ordr ord)
        (LOC: vloc.(ValA.val) = Zpos loc)
        (VRO: le lc2_arm.(Local.vro).(View.ts) n)
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
    exploit sim_memory_read; eauto; try apply GL_WF1_PS.
    { ss. etrans; try exact VRO.
      do 2 (etrans; [|apply join_r]). refl.
    }
    i. des; auto.
    { (* race with a promise *)
      ss. right. right.
      esplits; eauto; [|econs; ss; apply MEM1].
      eapply sim_tview_le; try exact TVIEW1; ss; i.
      eapply join_le; try apply View.order; try refl. apply TVIEW1.
    }

    { (* normal read *)
      exploit sim_tview_readable; try exact LATEST; eauto; try apply LC_WF1_PS.
      { apply joins_le. right. left. ss. }
      ss. i. des.
      right. left. esplits.
      { econs; eauto; try refl. }
      { ss. }

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
            exploit (wf_arm_fwd ts); eauto. i. des.
            - etrans; [|apply join_l]. apply x2.
            - etrans; [|apply join_r]. etrans; [|apply join_r]. apply x2.
          }
          { condtac; ss; try apply PSTime.bot_spec.
            destruct released; s; try apply PSTime.bot_spec.
            unfold FwdItem.read_view. condtac; ss.
            - apply andb_prop in X0. des.
              rewrite negb_true_iff in X1.
              exploit REL_FWD.
              { destruct (FwdItem.ts (Local.fwdbank lc1_arm (ValA.val vloc)) == ts); ss. }
              condtac.
              + i. inv x2.
                rewrite andb_true_l in X1.
                apply orb_false_elim in X1. des.
                destruct ord; ss.
              + i. inv x2.
                etrans; [apply LE|].
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
            destruct released; s; try apply PSTime.bot_spec.
            unfold FwdItem.read_view. condtac; ss.
            - apply andb_prop in X0. des.
              rewrite negb_true_iff in X1.
              exploit REL_FWD.
              { destruct (FwdItem.ts (Local.fwdbank lc1_arm (ValA.val vloc)) == ts); ss. }
              condtac.
              + i. inv x2.
                etrans; [apply LE|].
                etrans; [apply TVIEW1|].
                apply le_ntt. ss.
                eapply join_le; [apply Time.order|..].
                * eapply join_le; apply Time.order.
                * unfold fun_add. condtac; ss.
                  rewrite e. apply join_l.
              + i. inv x2.
                etrans; [apply LE|].
                etrans; [apply LC_WF1_PS|].
                etrans; [apply LC_WF1_PS|].
                etrans; [apply TVIEW1|].
                apply le_ntt. ss.
                eapply join_le; [apply Time.order|..].
                * eapply join_le; apply Time.order.
                * unfold fun_add. condtac; ss.
                  rewrite e. apply join_l.
            - unfold ifc. repeat (condtac; try by destruct ord; ss).
              + inv MEM1. exploit RELEASED; eauto. i.
                clear PRM_SOUND PRM_COMPLETE MEM_SOUND MEM_COMPLETE RELEASED.
                etrans; try apply x2. apply le_ntt.
                etrans; [|apply join_l].
                etrans; [|apply join_r].
                etrans; [|apply join_r].
                apply join_r.
              + inv MEM1. exploit RELEASED; eauto. i.
                clear PRM_SOUND PRM_COMPLETE MEM_SOUND MEM_COMPLETE RELEASED.
                etrans; try apply x2. apply le_ntt.
                etrans; [|apply join_l].
                etrans; [|apply join_r].
                etrans; [|apply join_r].
                apply join_r.
          }
        }

        { eapply join_le; try apply View.order; try refl. apply TVIEW1. }
      }

      { inv MEM1. econs; s; eauto. i.
        exploit FWD; eauto. i. des.
        esplits; eauto. condtac; ss.
        etrans; eauto. econs.
        etrans; [|apply View.join_l]. apply View.join_l.
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

  Lemma sim_fulfill
        tid n
        lc1_ps gl1_ps
        ord loc
        (ex: bool) ord_arm (vloc: ValA.t (A:=View.t (A:=unit))) vval res ts view_pre lc1_arm mem_arm lc2_arm
        releasedm
        (TVIEW1: sim_tview (PSLocal.tview lc1_ps) lc1_arm)
        (MEM1: sim_memory tid n lc1_ps (Global.promises gl1_ps) (Global.memory gl1_ps) lc1_arm mem_arm)
        (LC_WF1_PS: PSLocal.wf lc1_ps gl1_ps)
        (GL_WF1_PS: PSGlobal.wf gl1_ps)
        (WF1_ARM: RMWLocal.wf tid lc1_arm mem_arm)
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
        revert PROMISED_ARM.
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
          rewrite Promises.unset_o. condtac; ss. congr.
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
          + right. esplits; eauto.
            rewrite Promises.unset_o. condtac; ss.
      }

      { (* MEM_COMPLETE *)
        revert GET_PS0.
        erewrite PSMemory.add_o; eauto. condtac; ss.
        - i. des. inv GET_PS0. esplits; eauto.
        - erewrite Memory.remove_o; eauto. condtac; ss. eauto.
      }

      { (* FWD *)
        revert FWD1. unfold fun_add. condtac; ss.
        - i. inversion e. subst.
          exploit PSMemory.add_get0; try exact x3. i. des.
          esplits; try exact GET0; ss. condtac.
          + unfold TView.write_released. condtac; econs.
            apply PSView.join_spec.
            * inv RELEASEDM1; ss; try apply PSView.bot_spec.
              etrans; try exact LE. apply PSView.join_l.
            * ss. unfold LocFun.add. condtac; ss.
              condtac; ss; apply PSView.join_spec.
              { etrans; [apply LC_WF1_PS|]. apply PSView.join_l. }
              { apply PSView.join_r. }
              { etrans; [apply LC_WF1_PS|]. s.
                etrans; [apply LC_WF1_PS|]. apply PSView.join_l.
              }
              { apply PSView.join_r. }
          + subst.
            unfold TView.write_released. condtac; econs. ss.
            unfold LocFun.add. condtac; ss.
            condtac; ss; apply PSView.join_spec; try apply PSView.bot_spec; try refl.
        - i. exploit FWD0; eauto. i. des.
          exploit PSMemory.remove_get1; try exact GET_PS0; eauto. i. des; ss.
          exploit PSMemory.add_get1; try exact x4; eauto. i.
          esplits; try exact x5; ss.
          condtac.
          + etrans; try exact REL_FWD. econs. apply PSView.join_l.
          + etrans; try exact REL_FWD. econs.
            unfold LocFun.add. condtac; try refl. subst.
            condtac; try apply PSView.join_l.
            etrans; [|apply PSView.join_l]. apply LC_WF1_PS.
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

  Lemma sim_dmb
        tid n
        lc1_ps gl1_ps lc1_arm mem_arm
        ordr ordw
        rr rw wr ww lc2_arm
        (TVIEW1: sim_tview (PSLocal.tview lc1_ps) lc1_arm)
        (SC1: forall loc, PSTime.le (gl1_ps.(PSGlobal.sc) loc) (ntt n))
        (MEM1: sim_memory tid n lc1_ps (Global.promises gl1_ps) (Global.memory gl1_ps) lc1_arm mem_arm)
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
      (<<MEM2: sim_memory tid n lc2_ps (Global.promises gl2_ps) (Global.memory gl2_ps) lc2_arm mem_arm>>).
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
      esplits; eauto. condtac; ss.
      - etrans; eauto. econs. apply PSView.join_l.
      - etrans; eauto. econs. condtac; ss; try refl.
        condtac; ss; cycle 1.
        { condtac; ss; try apply LC_WF1_PS.
          etrans; apply LC_WF1_PS.
        }
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

  Lemma sim_control
        tid n
        lc1_ps gl1_ps lc1_arm mem_arm
        ctrl lc2_arm
        (TVIEW1: sim_tview (PSLocal.tview lc1_ps) lc1_arm)
        (MEM1: sim_memory tid n lc1_ps (Global.promises gl1_ps) (Global.memory gl1_ps) lc1_arm mem_arm)
        (STEP: Local.control ctrl lc1_arm lc2_arm):
    (<<TVIEW2: sim_tview (PSLocal.tview lc1_ps) lc2_arm>>) /\
    (<<MEM2: sim_memory tid n lc1_ps (Global.promises gl1_ps) (Global.memory gl1_ps) lc2_arm mem_arm>>).
  Proof.
    exploit (Local.control_incr (A:=unit)); eauto. i.
    inv STEP. split.
    - eapply sim_tview_le; eauto. s. apply TVIEW1.
    - inv MEM1. ss.
  Qed.

  Lemma read_ts_coh
        tid (lc1 lc2: Local.t (A:=unit)) mem
        ex ord vloc res ts
        (WF: RMWLocal.wf tid lc1 mem)
        (READ: Local.read ex ord vloc res ts lc1 mem lc2):
    le ts (lc2.(Local.coh) vloc.(ValA.val)).(View.ts).
  Proof.
    inv READ. ss.
    unfold fun_add. condtac; ss; try congr. clear e X.
    unfold FwdItem.read_view. condtac; ss.
    - apply andb_prop in X. des.
      revert X. unfold proj_sumbool. condtac; ss.
      i. r in e. subst. clear X1.
      etrans; [apply WF|]. apply join_l.
    - etrans; [|apply join_r]. apply join_r.
  Qed.

  Lemma update_ts
        tid (lc1 lc2 lc3: Local.t (A:=unit)) mem
        exr ordr vlocr vold ts_old
        exw ordw vlocw vnew res ts_new view_pre
        (WF: RMWLocal.wf tid lc1 mem)
        (READ: Local.read exr ordr vlocr vold ts_old lc1 mem lc2)
        (FULFILL: Local.fulfill exw ordw vlocw vnew res ts_new tid view_pre lc2 mem lc3)
        (LOC: vlocr.(ValA.val) = vlocw.(ValA.val)):
    ts_old < ts_new.
  Proof.
    exploit read_ts_coh; eauto. i.
    eapply Nat.le_lt_trans; try exact x0.
    rewrite LOC. inv FULFILL. inv WRITABLE. ss.
  Qed.

  Lemma sim_thread_step
        tid n th1_ps eu1 eu2
        (SIM1: sim_thread tid n th1_ps eu1)
        (LC_WF1_PS: PSLocal.wf (PSThread.local th1_ps) (PSThread.global th1_ps))
        (GL_WF1_PS: PSGlobal.wf (PSThread.global th1_ps))
        (WF1_ARM: RMWLocal.wf tid (RMWExecUnit.local eu1) (RMWExecUnit.mem eu1))
        (STEP_ARM: RMWExecUnit.state_step (Some n) tid eu1 eu2)
        (VRO: le eu2.(RMWExecUnit.local).(Local.vro).(View.ts) n)
        (FULFILLABLE: RMWLocal.fulfillable eu2.(RMWExecUnit.local) eu2.(RMWExecUnit.mem)):
    exists th2_ps,
      (<<STEPS_PS: rtc (@PSThread.tau_step _) th1_ps th2_ps>>) /\
      (<<SIM2: sim_thread tid n th2_ps eu2>>).
  Proof.
    destruct th1_ps as [st1_ps lc1_ps gl1_ps].
    destruct eu1 as [st1_arm lc1_arm mem1_arm].
    destruct eu2 as [st2_arm lc2_arm mem2_arm].
    inv SIM1. inv STEP_ARM. inv STEP. ss. subst.
    exploit sim_state_step; eauto. i. des.
    inv LOCAL; inv EVENT.
    { (* internal *)
      esplits.
      - econs 2; try refl.
        econs 1; [econs 2; [|econs 1]|]; eauto.
      - ss.
    }

    { (* read *)
      exploit sim_read; try exact STEP; eauto. i. des.
      - exfalso.
        exploit (FULFILLABLE ts); try by (inv STEP; ss). i. des.
        dup WF1_ARM. inv WF1_ARM0.
        exploit PRM; eauto. i. des.
        clear COH VRN VWN FWD PRM.
        exploit LT_COH; eauto. i.
        exploit read_ts_coh; eauto. i.
        clear - STEP GET x0 x1.
        inv STEP. ss.
        unfold Memory.get_msg in *. destruct ts; ss.
        revert MSG. unfold Memory.read. ss.
        rewrite GET. condtac; ss. i.
        rewrite e in *.
        eapply Nat.lt_strorder.
        eapply Nat.lt_le_trans; [exact x0|]. apply x1.
      - exploit sim_val_eq_inv; [exact VAL|exact VAL0|]. i. subst.
        esplits.
        + econs 2; try refl.
          econs 1; [econs 2; [|econs 2]|]; eauto.
        + ss.
      - exploit sim_val_eq_inv; [exact VAL|exact VAL0|]. i. subst.
        esplits.
        + econs 2; try refl.
          econs 1; [econs 2; [|econs 8]|]; eauto.
        + ss.
    }

    { (* fulfill *)
      exploit sim_fulfill; try exact STEP; eauto; ss.
      { Transparent Ordering.le.
        i. apply PF in H. destruct ord_ps; ss.
      }
      { i. apply PSTime.bot_spec. }
      i. des. inv VAL.
      esplits.
      - econs 2.
        { econs 1; [econs 1; econs 3|]; eauto. }
        econs 2; try refl.
        econs 1; [econs 2; [|econs 3]|]; eauto.
      - ss.
    }

    { (* fadd *)
      exploit update_ts; eauto. intro TS.
      exploit sim_read; try exact STEP_READ; eauto.
      { exploit (Local.control_incr (A:=unit)); eauto. i.
        exploit (Local.fulfill_incr (A:=unit)); eauto. i.
        etrans; [apply x1|]. etrans; [apply x0|]. ss.
      }
      i. des.
      - exfalso.
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
        etrans; [|apply x1].
        replace (Msg.loc msg) with (ValA.val vloc); cycle 1.
        { clear - STEP_READ GET.
          inv STEP_READ. ss.
          revert GET. unfold Memory.get_msg. destruct ts_old; ss. i.
          revert MSG. unfold Memory.read. s. rewrite GET. condtac; ss.
        }
        clear - STEP_FULFILL.
        inv STEP_FULFILL. ss.
        unfold fun_add. condtac; ss. congr.
      - exploit PSLocal.read_step_future; try exact STEP_PS0; eauto. i. des.
        exploit (RMWLocal.read_wf (A:=unit)); eauto. i.
        exploit sim_fulfill; try exact STEP_FULFILL; eauto; ss.
        { Transparent Ordering.le.
          i. apply PF in H. destruct ordw_ps; ss.
        }
        { (* TODO: in PS, if a message is written by na/pln, message view = bot *)
          inv STEP_PS0. ss.
          admit.
        }
        { i. inv STEP_PS0. ss.
          inv SIM_MEM. exploit RELEASED; eauto.
          etrans; try apply x1. econs.
          apply lt_ntt. ss.
        }
        i. des.
        admit.
      - admit.
    }

    { (* dmb *)
      exploit sim_dmb; try exact STEP; eauto.
      { admit. }
      { admit. }
      i. des. esplits.
      - econs 2; try refl.
        econs; [econs 2; [|econs 5]|]; eauto.
      - ss.
    }

    { (* control *)
      exploit sim_control; try exact LC; eauto. i. des.
      esplits.
      - econs 2; try refl.
        econs; [econs 2; [|econs 1]|]; eauto.
      - ss.
    }
  Admitted.

  Variant sim_thread_exec (tid: Ident.t) (n: Time.t) (after_sc: bool)
    (th_ps: PSThread.t lang_ps) (eu: RMWExecUnit.t (A:=unit)): Prop :=
    | sim_thread_exec_intro
        sc eu1 eu2 eu3
        (STEPS1: rtc (RMWExecUnit.state_step None tid) eu eu1)
        (SIM_THREAD: sim_thread tid n th_ps eu1)
        (SC: sc = if after_sc then S n else n)
        (STEPS2: rtc (RMWExecUnit.state_step_dmbsy_over (Some n) sc tid) eu1 eu2)
        (PROMISES2: forall ts (PROMISED: Promises.lookup ts eu2.(RMWExecUnit.local).(Local.promises)),
            lt n ts)
        (STEPS3: rtc (RMWExecUnit.state_step_dmbsy_over (Some n) sc tid) eu2 eu3)
        (PROMISES3: eu3.(RMWExecUnit.local).(Local.promises) = bot)
  .

  Variant sim_thread_sl (tid: Ident.t) (n: Time.t) (after_sc: bool)
    (gl_ps: PSGlobal.t) (mem_arm: Memory.t):
    forall (sl_ps: {lang: language & Language.state lang} * PSLocal.t)
           (sl_arm: RMWState.t (A:=View.t (A:=unit)) * Local.t (A:=unit)), Prop :=
    | sim_thread_sl_intro
        st_ps lc_ps st_arm lc_arm
        (SIM_THREAD: sim_thread_exec tid n after_sc
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
End PStoRMW.
