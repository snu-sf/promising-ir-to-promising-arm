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
Require Import PromisingArch.lib.Lang.

Require Import PromisingArch.promising.Promising.
Require Import PromisingArch.mapping.RMWLang.
Require Import PromisingArch.mapping.RMWPromising.
Require Import PromisingArch.mapping.PSLang.

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
