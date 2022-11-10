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
Require Import PromisingArch.mapping.PStoRMW.
Require Import PromisingArch.mapping.RMWtoLLSC.

Set Implicit Arguments.


Definition ps_to_arm_stmts (reg1 reg2: Id.t) (s: list Stmt.t): list stmtT :=
  rmw_to_llsc_stmts reg1 reg2 (ps_to_rmw_stmts s).

Definition ps_to_arm_program (prog_ps: ps_program) (prog_arm: program): Prop :=
  forall tid, exists reg1 reg2,
    option_rel
      (fun stmts_ps stmts_arm => stmts_arm = ps_to_arm_stmts reg1 reg2 stmts_ps)
      (IdentMap.find tid prog_ps) (IdMap.find tid prog_arm).
