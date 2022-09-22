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
From PromisingIR Require Import Reserves.
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

Definition ps_to_rmw_instr (i: Instr.t): rmw_instrT :=
  match i with
  | Instr.skip =>
      rmw_instr_skip
  | Instr.assign reg e =>
      rmw_instr_assign reg (ps_to_rmw_expr e)
  | Instr.load reg loc ord =>
      rmw_instr_load
        (if Ordering.le Ordering.acqrel ord then OrdR.acquire_pc else OrdR.pln)
        reg (expr_const (Zpos loc))
  | Instr.store loc e ord =>
      rmw_instr_store
        (if Ordering.le Ordering.acqrel ord
         then OrdW.release_pc
         else if Ordering.le Ordering.relaxed ord then OrdW.srlx else OrdW.pln)
        (expr_const (Zpos loc)) (ps_to_rmw_expr e)
  | Instr.fadd reg loc e ordr ordw =>
      rmw_instr_fadd
        (if Ordering.le Ordering.acqrel ordr then OrdR.acquire_pc else OrdR.pln)
        (if Ordering.le Ordering.acqrel ordw
         then OrdW.release_pc
         else if Ordering.le Ordering.relaxed ordw then OrdW.srlx else OrdW.pln)
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
  #[export] Hint Constructors sim_val.

  Variant sim_state (st_ps: State.t) (st_arm: RMWState.t (A:=View.t (A:=unit))): Prop :=
    | sim_state_intro
        (STMTS: RMWState.stmts st_arm = ps_to_rmw_stmts (State.stmts st_ps))
        (REGS: forall r, sim_val (IdentFun.find r st_ps.(State.regs))
                                 (RMap.find r st_arm.(RMWState.rmap)).(ValA.val))
  .
  #[export] Hint Constructors sim_state.

  Variant sim_tview (tview: TView.t) (lc_arm: Local.t (A:=unit)): Prop :=
    | sim_tview_intro
        (REL: forall loc loc',
            PSTime.le
              ((tview.(TView.rel) loc).(View.rlx) loc')
              (ntt (View.ts (join lc_arm.(Local.vwn) (ifc (PSLoc.eq_dec loc' loc) (lc_arm.(Local.coh) (Zpos loc)))))))
        (CUR: forall loc,
            PSTime.le
              (tview.(TView.cur).(View.rlx) loc)
              (ntt (View.ts (join lc_arm.(Local.vrn) (lc_arm.(Local.coh) (Zpos loc))))))
        (ACQ: forall loc,
            PSTime.le
              (tview.(TView.cur).(View.rlx) loc)
              (ntt (View.ts (join lc_arm.(Local.vrn) (lc_arm.(Local.coh) (Zpos loc))))))
        (OLD: forall loc, le (lc_arm.(Local.coh) loc) (join lc_arm.(Local.vro) lc_arm.(Local.vwo)))
        (FWD: forall loc,
            le (lc_arm.(Local.fwdbank) loc).(FwdItem.ts) (View.ts (lc_arm.(Local.coh) loc)))
  .
  #[export] Hint Constructors sim_tview.

  Variant sim_memory (tid: Ident.t) (n: Time.t)
    (lc_ps: PSLocal.t) (mem_ps: PSMemory.t)
    (prm_arm: Promises.t) (mem_arm: Memory.t): Prop :=
    | sim_memory_intro
        (PRM_SOUND: forall loc (PROMISED: lc_ps.(PSLocal.promises) loc = true),
          exists ts msg,
            (<<LE: le ts n>>) /\
            (<<PROMISED_ARM: Promises.lookup ts prm_arm>>) /\
            (<<GET_ARM: Memory.get_msg ts mem_arm = Some msg>>) /\
            (<<GET_PS: Memory.get loc (ntt ts) mem_ps = None>>))
        (MEM_SOUND: forall loc from to val_ps released na
                           (GET_PS: PSMemory.get loc to mem_ps = Some (from, Message.mk val_ps released na)),
          exists fts tts val_arm ttid,
            (<<TO: to = ntt tts>>) /\
            (<<FROM: from = ntt fts>>) /\
            (<<GET_ARM: Memory.get_msg tts mem_arm = Some (Msg.mk (Zpos loc) val_arm ttid)>>) /\
            (<<GET_FROM_ARM: exists val' ftid,
                Memory.get_msg fts mem_arm = Some (Msg.mk (Zpos loc) val' ftid)>>) /\
            (<<LATEST: Memory.latest (Zpos loc) fts tts mem_arm>>) /\
            (<<VAL: sim_val val_ps val_arm>>))
        (MEM_COMPLETE: forall loc ts val_arm tid'
                              (TS: le ts n)
                              (GET_ARM: Memory.get_msg ts mem_arm = Some (Msg.mk loc val_arm tid')),
          exists loc' from val_ps released na,
            (<<LOC: loc = Zpos loc'>>) /\
            (<<GET_PS: Memory.get loc' (ntt ts) mem_ps = Some (from, Message.mk val_ps released na)>>) /\
            (<<VAL: sim_val val_ps val_arm>>) /\
            (<<MSG_FWD: PSView.opt_le released (Some (lc_ps.(PSLocal.tview).(TView.rel) loc'))>>))
        (RELEASED: forall loc from to val released na
                          (GET: PSMemory.get loc to mem_ps = Some (from, Message.mk val released na)),
          forall loc', PSTime.le ((View.unwrap released).(View.rlx) loc') to)
  .

  Variant sim_thread (tid: Ident.t) (n: Time.t) (after_sc: bool)
    (th_ps: Thread.t lang_ps) (eu: RMWExecUnit.t (A:=unit)): Prop :=
    | sim_thread_intro
        eu1 eu2
        (STEPS1: rtc (RMWExecUnit.state_step tid) eu eu1)
        (SIM_STATE: sim_state (Thread.state th_ps) (RMWExecUnit.state eu1))
        (SIM_TVIEW: sim_tview (PSLocal.tview (Thread.local th_ps)) (RMWExecUnit.local eu1))
        (SIM_MEM: sim_memory tid n
                    (Thread.local th_ps) (Global.memory (Thread.global th_ps))
                    (Local.promises (RMWExecUnit.local eu1)) (RMWExecUnit.mem eu1))
        (STEPS2: if after_sc
                 then rtc (RMWExecUnit.state_step_dmbsy (S n) tid) eu1 eu2
                 else rtc (RMWExecUnit.state_step_dmbsy n tid) eu1 eu2)
        (PROMISES: eu2.(RMWExecUnit.local).(Local.promises) = bot)
  .

  Variant sim_thread_sl (tid: Ident.t) (n: Time.t) (after_sc: bool)
    (gl_ps: Global.t) (mem_arm: Memory.t):
    forall (sl_ps: {lang: language & Language.state lang} * PSLocal.t)
           (sl_arm: RMWState.t (A:=View.t (A:=unit)) * Local.t (A:=unit)), Prop :=
    | sim_thread_sl_intro
        st_ps lc_ps st_arm lc_arm
        (SIM_THREAD: sim_thread tid n after_sc
                       (Thread.mk _ st_ps lc_ps gl_ps) (RMWExecUnit.mk st_arm lc_arm mem_arm)):
      sim_thread_sl tid n after_sc gl_ps mem_arm
        (existT _ lang_ps st_ps, lc_ps) (st_arm, lc_arm)
  .

  Variant sim (n: Time.t) (c: Configuration.t) (m: RMWMachine.t): Prop :=
    | sim_intro
        m1
        (PROMISE_STEPS: rtc (RMWMachine.step RMWExecUnit.promise_step) m m1)
        (SIM_THREADS:
          forall tid,
            opt_rel
              (sim_thread_sl tid n true c.(Configuration.global) m.(RMWMachine.mem))
              (IdentMap.find tid c.(Configuration.threads))
              (IdMap.find tid m.(RMWMachine.tpool)))
        (SIM_SC: forall loc,
            PSTime.le (c.(Configuration.global).(Global.sc) loc) (ntt n))
  .
End PStoRMW.
