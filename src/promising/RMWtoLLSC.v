From Paco Require Import paco.

Require Import Relations.
Require Import EquivDec.
Require Import Equality.
Require Import List.
Require Import Bool.
Require Import Lia.
Require Import NArith.
Require Import PArith.
Require Import ZArith.
Require Import FMapPositive.
Require Import FSetPositive.
Require Import EquivDec.
Require Import sflib.

Require Import PromisingArch.lib.Basic.
Require Import PromisingArch.lib.Order.
Require Import PromisingArch.lib.Time.
Require Import PromisingArch.lib.Lang.

Require Import PromisingArch.promising.Promising.

Set Implicit Arguments.


Fixpoint rmw_to_llsc_stmt (tmp: Id.t) (stmt: stmtT): list stmtT :=
  match stmt with
  | stmt_instr (instr_fadd ordr ordw res eloc eadd) =>
    [stmt_dowhile
       [stmt_instr (instr_load true ordr res eloc);
        stmt_instr (instr_store true ordw tmp eloc (expr_op2 op_add (expr_reg res) eadd))]
       (expr_op1 op_not (expr_reg tmp))]
  | stmt_if cond s1 s2 =>
    [stmt_if cond
             (List.fold_right (@List.app _) [] (List.map (rmw_to_llsc_stmt tmp) s1))
             (List.fold_right (@List.app _) [] (List.map (rmw_to_llsc_stmt tmp) s2))]
  | stmt_dowhile s cond =>
    [stmt_dowhile
       (List.fold_right (@List.app _) [] (List.map (rmw_to_llsc_stmt tmp) s)) cond]
  | _ => [stmt]
  end.

Inductive fresh (r: Id.t): forall (stmt: stmtT), Prop :=
| fresh_instr
    i
    (FRESH: ~ IdSet.mem r (regs_of_instr i)):
  fresh r (stmt_instr i)
| fresh_cond
    cond s1 s2
    (FRESH_COND: ~ IdSet.mem r (regs_of_expr cond))
    (FRESH_STMT1: List.Forall (fresh r) s1)
    (FRESH_STMT2: List.Forall (fresh r) s2):
  fresh r (stmt_if cond s1 s2)
| fresh_dowhile
    s cond
    (FRESH_STMT: List.Forall (fresh r) s)
    (FRESH_COND: ~ IdSet.mem r (regs_of_expr cond)):
  fresh r (stmt_dowhile s cond)
.


Section SIM.
  Variant _sim_machine (sim: Machine.t -> Machine.t -> Prop) (m_src m_tgt: Machine.t): Prop :=
    | _sim_machine_intro:
      _sim_machine sim m_src m_tgt
  .
  #[local] Hint Constructors _sim_machine: paco.

  Lemma sim_machine_monotone: monotone2 _sim_machine.
  Proof.
    ii. econs.
  Qed.
  #[local] Hint Resolve sim_machine_monotone.

  Definition sim_machine := paco2 _sim_machine bot2.
End SIM.
