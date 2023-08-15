Require Import NArith.
Require Import PArith.
Require Import ZArith.
Require Import Lia.
Require Import EquivDec.
Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingFlat Require Import Basic.
From PromisingFlat Require Import Axioms.
From PromisingFlat Require Import Language.
From PromisingFlat Require Import Event.
From PromisingFlat Require Import Loc.

Require Import PromisingArch.lib.Basic.
Require Import PromisingArch.lib.Lang.

Set Implicit Arguments.


Module Expr.
  Inductive t: Type :=
  | const (c: Const.num_t)
  | reg (r: Id.t)
  | op1 (op: opT1) (e: t)
  | op2 (op: opT2) (e1 e2: t)
  .
  #[global]
    Hint Constructors t: core.

  Definition eval_op1 (op:opT1) (c:Const.t): Const.t :=
    match op with
    | op_not =>
      match (Const.eqb c Const.zero) with
      | None => Const.undef
      | Some b =>
        if b then Const.one else Const.zero
      end
    end.

  Definition eval_op2 (op:opT2): forall (op1 op2:Const.t), Const.t :=
    match op with
    | op_add => Const.add
    | op_sub => Const.sub
    | op_mul => Const.mul
    end.
End Expr.

Module Instr.
  Variant t: Type :=
    | skip
    | assign (reg:Id.t) (e:Expr.t)
    | load (reg:Id.t) (eloc:Expr.t) (ord:Ordering.t)
    | store (eloc:Expr.t) (e:Expr.t) (ord:Ordering.t)
    | fadd (reg:Id.t) (eloc:Expr.t) (addendum:Expr.t) (ordr ordw:Ordering.t)
    | fence (ordr ordw:Ordering.t)
  .
  #[global]
    Hint Constructors t: core.
End Instr.

Module Stmt.
  Inductive t :=
  | instr (i: Instr.t)
  | ite (cond: Expr.t) (s1 s2: list t)
  | dowhile (s: list t) (cond: Expr.t)
  .
  #[global]
    Hint Constructors t: core.
  Coercion instr: Instr.t >-> t.
End Stmt.


Module RegFile.
  Definition t := IdentFun.t Const.t.

  Definition init: t := IdentFun.init Const.zero.

  Fixpoint eval_expr (rf: t) (e: Expr.t): Const.t :=
    match e with
    | Expr.const c => c
    | Expr.reg r => IdentFun.find r rf
    | Expr.op1 op e => Expr.eval_op1 op (eval_expr rf e)
    | Expr.op2 op e1 e2 => Expr.eval_op2 op (eval_expr rf e1) (eval_expr rf e2)
    end.

  Variant eval_instr: forall (rf1:t) (i:Instr.t) (e:ProgramEvent.t) (rf2:t), Prop :=
  | eval_skip
      rf:
      eval_instr
        rf
        Instr.skip
        ProgramEvent.silent
        rf
  | eval_assign
      rf lhs rhs:
      eval_instr
        rf
        (Instr.assign lhs rhs)
        ProgramEvent.silent
        (IdentFun.add lhs (eval_expr rf rhs) rf)
  | eval_load_undef
      rf reg eloc ord
      (ELOC: eval_expr rf eloc = Const.undef):
      eval_instr
        rf
        (Instr.load reg eloc ord)
        ProgramEvent.failure
        rf
  | eval_load
      rf reg eloc loc ord val
      (ELOC: eval_expr rf eloc = Const.num loc):
      eval_instr
        rf
        (Instr.load reg eloc ord)
        (ProgramEvent.read loc val ord)
        (IdentFun.add reg val rf)
  | eval_store_undef
      rf eloc e ord
      (ELOC: eval_expr rf eloc = Const.undef):
      eval_instr
        rf
        (Instr.store eloc e ord)
        ProgramEvent.failure
        rf
  | eval_store
      rf eloc loc e ord
      (ELOC: eval_expr rf eloc = Const.num loc):
      eval_instr
        rf
        (Instr.store eloc e ord)
        (ProgramEvent.write loc (eval_expr rf e) ord)
        rf
  | eval_fadd_undef
      rf reg eloc addendum ordr ordw
      (ELOC: eval_expr rf eloc = Const.undef):
    eval_instr
      rf
      (Instr.fadd reg eloc addendum ordr ordw)
      ProgramEvent.failure
      rf
  | eval_fadd
      rf reg eloc loc addendum ordr ordw
      old new
      (ELOC: eval_expr rf eloc = Const.num loc)
      (NEW: new = Const.add old (eval_expr rf addendum)):
    eval_instr
      rf
      (Instr.fadd reg eloc addendum ordr ordw)
      (ProgramEvent.update loc old new ordr ordw)
      (IdentFun.add reg old rf)
  | eval_fence
      rf ordr ordw:
      eval_instr
        rf
        (Instr.fence ordr ordw)
        (ProgramEvent.fence ordr ordw)
        rf
  .
End RegFile.


Module State.
  Structure t := mk {
    regs: RegFile.t;
    stmts: list Stmt.t;
  }.

  Definition init (stmts :list Stmt.t): t :=
    mk RegFile.init stmts.

  Definition is_terminal (s:t): Prop :=
    stmts s = nil.

  Inductive step: forall (e:ProgramEvent.t) (s1:t) (s1:t), Prop :=
  | step_instr
      rf1 i e rf2 stmts
      (INSTR: RegFile.eval_instr rf1 i e rf2):
      step e
           (mk rf1 ((Stmt.instr i)::stmts))
           (mk rf2 stmts)
  | step_ite_true
      rf cond s1 s2 stmts
      (COND: match RegFile.eval_expr rf cond with
             | Const.undef => True
             | Const.num n => n <> 0%Z
             end):
      step ProgramEvent.silent
           (mk rf ((Stmt.ite cond s1 s2)::stmts))
           (mk rf (s1 ++ stmts))
  | step_ite_false
      rf cond s1 s2 stmts
      (COND: match RegFile.eval_expr rf cond with
             | Const.undef => True
             | Const.num n => n = 0%Z
             end):
      step ProgramEvent.silent
           (mk rf ((Stmt.ite cond s1 s2)::stmts))
           (mk rf (s2 ++ stmts))
  | step_dowhile
      rf s cond stmts:
      step ProgramEvent.silent
           (mk rf ((Stmt.dowhile s cond)::stmts))
           (mk rf (s ++ [Stmt.ite cond ((Stmt.dowhile s cond)::stmts) stmts]))
  .

  Inductive opt_step: forall (e:ProgramEvent.t) (st1 st2:t), Prop :=
  | opt_step_none
      st:
      opt_step ProgramEvent.silent st st
  | opt_step_some
      e st1 st2
      (STEP: step e st1 st2):
      opt_step e st1 st2
  .
End State.

Definition ps_program: Type := IdentMap.t (list Stmt.t).

Program Definition lang_ps: Language.t ProgramEvent.t :=
  Language.mk
    State.init
    State.is_terminal
    State.step.
