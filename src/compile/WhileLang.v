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

Require Import PromisingArch.lib.Basic.
Require Import PromisingArch.lib.Lang.

Set Implicit Arguments.


Module Expr.
  Inductive t: Type :=
  | const (c: Const.t)
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
    | load (reg:Id.t) (loc:Loc.Loc.t) (ord:Ordering.t)
    | store (loc:Loc.Loc.t) (e:Expr.t) (ord:Ordering.t)
    | fadd (reg:Id.t) (loc:Loc.Loc.t) (addendum:Expr.t) (ordr ordw:Ordering.t)
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
  Definition t := IdMap.t Const.t.

  Definition init: t := IdMap.empty _.

  Definition find (reg:Id.t) (rf:t): Const.t :=
    match IdMap.find reg rf with
    | Some v => v
    | None => 0%Z
    end.

  Definition add (reg:Id.t) (val:Const.t) (rf:t): t :=
    IdMap.add reg val rf.

  Lemma add_o reg' reg val rf:
    find reg' (add reg val rf) =
    if reg' == reg
    then val
    else find reg' rf.
  Proof.
    unfold add, find. rewrite IdMap.add_spec.
    repeat match goal with
           | [|- context[if ?c then _ else _]] => destruct c
           end; ss.
  Qed.

  Fixpoint eval_expr (rf: t) (e: Expr.t): Const.t :=
    match e with
    | Expr.const c => c
    | Expr.reg r => find r rf
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
        (add lhs (eval_expr rf rhs) rf)
  | eval_load
      rf reg loc ord val:
      eval_instr
        rf
        (Instr.load reg loc ord)
        (ProgramEvent.read loc val ord)
        (add reg val rf)
  | eval_store
      rf loc e ord:
      eval_instr
        rf
        (Instr.store loc e ord)
        (ProgramEvent.write loc (eval_expr rf e) ord)
        rf
  | eval_fadd
      rf reg loc addendum ordr ordw
      old new
      (NEW: new = Const.add old (eval_expr rf addendum)):
    eval_instr
      rf
      (Instr.fadd reg loc addendum ordr ordw)
      (ProgramEvent.update loc old new ordr ordw)
      (add reg old rf)
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
           (mk rf (s ++ (Stmt.ite cond ((Stmt.dowhile s cond)::nil) nil) :: stmts))
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

Program Definition lang: Language.t ProgramEvent.t :=
  Language.mk
    State.init
    State.is_terminal
    State.step.
