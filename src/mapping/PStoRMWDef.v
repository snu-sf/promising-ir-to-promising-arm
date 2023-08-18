Require Import NArith.
Require Import PArith.
Require Import ZArith.
Require Import Lia.
Require Import EquivDec.
Require Import RelationClasses.
Require Import Bool.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingFlat Require Import Basic.
From PromisingFlat Require Import Axioms.
From PromisingFlat Require Import Language.
From PromisingFlat Require Import Event.
From PromisingFlat Require Import Loc.

From PromisingFlat Require Import Time.
From PromisingFlat Require Import View.
From PromisingFlat Require Import BoolMap.
From PromisingFlat Require Import Promises.
From PromisingFlat Require Import Cell.
From PromisingFlat Require Import Memory.
From PromisingFlat Require Import TView.
From PromisingFlat Require Import Global.
From PromisingFlat Require Import Local.
From PromisingFlat Require Import Thread.
From PromisingFlat Require Import Configuration.

Require Import PromisingArch.lib.Basic.
Require Import PromisingArch.lib.Order.
Require Import PromisingArch.lib.Time.
Require Import PromisingArch.lib.Lang.

Require Import PromisingArch.mapping.RMWLang.
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

Definition ps_to_rmw_ordr (ord: Ordering.t): OrdR.t :=
  if Ordering.le Ordering.acqrel ord
  then OrdR.acquire_pc
  else OrdR.pln.

Definition ps_to_rmw_ordw (ord: Ordering.t): OrdW.t :=
  if Ordering.le Ordering.acqrel ord
  then OrdW.release_pc
  else
    if Ordering.le Ordering.plain ord
    then OrdW.strong
    else OrdW.pln.

Definition ps_to_rmw_instr (i: Instr.t): rmw_instrT :=
  match i with
  | Instr.skip =>
      rmw_instr_skip
  | Instr.assign reg e =>
      rmw_instr_assign reg (ps_to_rmw_expr e)
  | Instr.load reg eloc ord =>
      rmw_instr_load (ps_to_rmw_ordr ord) reg (ps_to_rmw_expr eloc)
  | Instr.store eloc e ord =>
      rmw_instr_store (ps_to_rmw_ordw ord) (ps_to_rmw_expr eloc) (ps_to_rmw_expr e)
  | Instr.fadd reg eloc e ordr ordw =>
      rmw_instr_fadd
        (ps_to_rmw_ordr ordr) (ps_to_rmw_ordw ordw)
        reg (ps_to_rmw_expr eloc) (ps_to_rmw_expr e)
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

Definition ps_to_rmw_program (prog_ps: ps_program) (prog_arm: rmw_program): Prop :=
  forall tid,
    option_rel
      (fun stmts_ps stmts_arm => stmts_arm = ps_to_rmw_stmts stmts_ps)
      (IdentMap.find tid prog_ps) (IdMap.find tid prog_arm).
