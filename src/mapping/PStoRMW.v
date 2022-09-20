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

Require Import PromisingArch.lib.Basic.
Require Import PromisingArch.lib.Order.
Require Import PromisingArch.lib.Time.
Require Import PromisingArch.lib.Lang.

Require Import PromisingArch.promising.Promising.
Require Import PromisingArch.mapping.RMWLang.
Require Import PromisingArch.mapping.RMWPromising.
Require Import PromisingArch.mapping.PSLang.

Set Implicit Arguments.

Module PSLoc := PromisingLib.Loc.Loc.
Module PSTime := PromisingIR.Time.Time.
Module PSView := PromisingIR.View.View.
Module PSPromises := PromisingIR.Promises.Promises.
Module PSLocal := PromisingIR.Local.Local.
Module PSMemory := PromisingIR.Memory.Memory.

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
  Fixpoint ntt (n: nat): PSTime.t :=
    match n with
    | O => PSTime.bot
    | S n => PSTime.incr (ntt n)
    end.

  Lemma le_ntt
        m n
        (LE: m <= n):
    PSTime.le (ntt m) (ntt n).
  Proof.
    induction LE; try refl.
    etrans; eauto. ss. econs.
    apply PSTime.incr_spec.
  Qed.

  Lemma lt_ntt
        m n
        (LT: m < n):
    PSTime.lt (ntt m) (ntt n).
  Proof.
    eapply TimeFacts.lt_le_lt; try eapply le_ntt; eauto.
    apply PSTime.incr_spec.
  Qed.

  Lemma ntt_le
        m n
        (LE: PSTime.le (ntt m) (ntt n)):
    m <= n.
  Proof.
    destruct (Nat.le_gt_cases m n); ss.
    apply lt_ntt in H. timetac.
  Qed.

  Lemma ntt_lt
        m n
        (LT: PSTime.lt (ntt m) (ntt n)):
    m < n.
  Proof.
    destruct (Nat.le_gt_cases n m); ss.
    apply le_ntt in H. timetac.
  Qed.

  Lemma ntt_inj
        m n
        (EQ: ntt m = ntt n):
    m = n.
  Proof.
    apply le_antisym.
    - apply ntt_le. rewrite EQ. refl.
    - apply ntt_le. rewrite EQ. refl.
  Qed.


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

  Variant sim_val: forall (val_ps: Const.t) (val_arm: Val.t), Prop :=
    | sim_val_num
        v:
      sim_val (Const.num v) v
    | sim_val_undef
        v:
      sim_val Const.undef v
  .

  (* TODO: from? *)
  Variant sim_memory (tid: Ident.t) (n: Time.t)
    (prm_ps: BoolMap.t) (prm_arm: Promises.t)
    (mem_ps: PSMemory.t) (mem_arm: Memory.t): Prop :=
    | sim_memory_intro
        (PRM_SOUND: forall loc (PROMISED: prm_ps loc = true),
          exists ts msg,
            (<<LE: le ts n>>) /\
            (<<PROMISED_ARM: Promises.lookup ts prm_arm>>) /\
            (<<GET_ARM: Memory.get_msg ts mem_arm = Some msg>>) /\
            (<<GET_PS: Memory.get loc (ntt ts) mem_ps = None>>))
        (MEM_SOUND: forall loc from to val_ps released na
                           (GET_PS: PSMemory.get loc to mem_ps = Some (from, Message.mk val_ps released na)),
          exists ts val_arm,
            (<<TO: to = ntt ts>>) /\
            (<<GET_ARM: Memory.get_msg ts mem_arm = Some (Msg.mk (Zpos loc) val_arm tid)>>) /\
            (<<VAL: sim_val val_ps val_arm>>))
        (MEM_COMPLETE: forall loc ts val_arm tid'
                              (TS: le ts n)
                              (GET_ARM: Memory.get_msg ts mem_arm = Some (Msg.mk loc val_arm tid')),
          exists loc' from val_ps released na,
            (<<LOC: loc = Zpos loc'>>) /\
            (<<GET_PS: Memory.get loc' (ntt ts) mem_ps = Some (from, Message.mk val_ps released na)>>) /\
            (<<VAL: sim_val val_ps val_arm>>))
  .
End PStoRMW.
