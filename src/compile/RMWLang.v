Require Import NArith.
Require Import PArith.
Require Import ZArith.
Require Import Lia.
Require Import EquivDec.

From sflib Require Import sflib.

Require Import PromisingArch.lib.Basic.
Require Import PromisingArch.lib.Order.
Require Import PromisingArch.lib.Lang.

Set Implicit Arguments.


Inductive rmw_instrT :=
| rmw_instr_skip
| rmw_instr_assign (lhs:Id.t) (rhs:exprT)
| rmw_instr_load (ord:OrdR.t) (res:Id.t) (eloc:exprT)
| rmw_instr_store (ord:OrdW.t) (res:Id.t) (eloc:exprT) (eval:exprT)
| rmw_instr_fadd (ordr:OrdR.t) (ordw:OrdW.t) (res:Id.t) (eloc:exprT) (eadd:exprT)
| rmw_instr_barrier (b:Barrier.t)
.
#[export]
Hint Constructors rmw_instrT: core.
Coercion rmw_instr_barrier: Barrier.t >-> rmw_instrT.

Definition regs_of_rmw_instr (i: rmw_instrT): IdSet.t :=
  match i with
  | rmw_instr_assign lhs rhs => IdSet.add lhs (regs_of_expr rhs)
  | rmw_instr_load _ res eloc => IdSet.add res (regs_of_expr eloc)
  | rmw_instr_store _ res eloc eval => IdSet.add res (IdSet.union (regs_of_expr eloc) (regs_of_expr eval))
  | rmw_instr_fadd _ _ res eloc eadd => IdSet.add res (IdSet.union (regs_of_expr eloc) (regs_of_expr eadd))
  | _ => IdSet.empty
  end.

Inductive rmw_stmtT :=
| rmw_stmt_instr (i:rmw_instrT)
| rmw_stmt_if (cond:exprT) (s1 s2:list rmw_stmtT)
| rmw_stmt_dowhile (s:list rmw_stmtT) (cond:exprT)
.
#[export]
Hint Constructors rmw_stmtT: core.
Coercion rmw_stmt_instr: rmw_instrT >-> rmw_stmtT.

Definition rmw_program := IdMap.t (list rmw_stmtT).


Module RMWEvent.
  Inductive t A `{_: orderC A} :=
  | internal
  | control (ctrl:A)
  | read (ord:OrdR.t) (vloc:ValA.t (A:=A)) (res:ValA.t (A:=A))
  | write (ord:OrdW.t) (vloc:ValA.t (A:=A)) (vval:ValA.t (A:=A)) (res:ValA.t (A:=A))
  | fadd (ordr:OrdR.t) (ordw:OrdW.t) (vloc vold vnew: ValA.t (A:=A))
  | barrier (b:Barrier.t)
  .
End RMWEvent.

Module RMWState.
Section RMWState.
  Context A `{_: orderC A}.

  Inductive t := mk {
    stmts: list rmw_stmtT;
    rmap: RMap.t (A:=A);
  }.

  Definition init (stmts:list rmw_stmtT): t := mk stmts (RMap.init (A:=A)).

  Definition is_terminal (st:t): Prop :=
    st.(stmts) = [].
  #[local]
  Hint Unfold is_terminal: core.

  Inductive step: forall (e:RMWEvent.t (A:=A)) (st1 st2:t), Prop :=
  | step_skip
      stmts rmap:
      step RMWEvent.internal
           (mk ((rmw_stmt_instr rmw_instr_skip)::stmts) rmap)
           (mk stmts rmap)
  | step_assign
      lhs rhs stmts rmap rmap'
      (RMAP: rmap' = RMap.add lhs (sem_expr rmap rhs) rmap):
      step RMWEvent.internal
           (mk ((rmw_stmt_instr (rmw_instr_assign lhs rhs))::stmts) rmap)
           (mk stmts rmap')
  | step_load
      o res eloc stmts rmap vloc vres rmap'
      (LOC: vloc = sem_expr rmap eloc)
      (RMAP: rmap' = RMap.add res vres rmap):
      step (RMWEvent.read o vloc vres)
           (mk ((rmw_stmt_instr (rmw_instr_load o res eloc))::stmts) rmap)
           (mk stmts rmap')
  | step_store
      o res eloc eval stmts rmap vloc vval vres rmap'
      (LOC: vloc = sem_expr rmap eloc)
      (VAL: vval = sem_expr rmap eval)
      (RMAP: rmap' = RMap.add res vres rmap):
      step (RMWEvent.write o vloc vval vres)
           (mk ((rmw_stmt_instr (rmw_instr_store o res eloc eval))::stmts) rmap)
           (mk stmts rmap')
  | step_fadd
      or ow res eloc eadd stmts rmap vloc vold vnew rmap'
      (LOC: vloc = sem_expr rmap eloc)
      (NEW: vnew = sem_op2 op_add vold (sem_expr rmap eadd))
      (RMAP: rmap' = RMap.add res vold rmap):
      step (RMWEvent.fadd or ow vloc vold vnew)
           (mk ((rmw_stmt_instr (rmw_instr_fadd or ow res eloc eadd))::stmts) rmap)
           (mk stmts rmap')
  | step_barrier
      b stmts rmap:
      step (RMWEvent.barrier b)
           (mk ((rmw_stmt_instr (rmw_instr_barrier b))::stmts) rmap)
           (mk stmts rmap)
  | step_if
      cond vcond s1 s2 stmts rmap stmts'
      (COND: vcond = sem_expr rmap cond)
      (STMTS: stmts' = (if vcond.(ValA.val) <> 0%Z then s1 else s2) ++ stmts):
      step (RMWEvent.control vcond.(ValA.annot))
           (mk ((rmw_stmt_if cond s1 s2)::stmts) rmap)
           (mk stmts' rmap)
  | step_dowhile
      s cond stmts rmap stmts'
      (STMTS: stmts' = s ++ [rmw_stmt_if cond ((rmw_stmt_dowhile s cond) :: stmts) stmts]):
      step RMWEvent.internal
           (mk ((rmw_stmt_dowhile s cond)::stmts) rmap)
           (mk stmts' rmap)
  .
  #[local]
  Hint Constructors step: core.
End RMWState.
End RMWState.
