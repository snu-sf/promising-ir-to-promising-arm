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
Require Import PromisingArch.mapping.PStoRMWDef.
Require Import PromisingArch.mapping.PStoRMWThread.

Set Implicit Arguments.


Module PStoRMWConsistent.
  Import PStoRMWThread.

  Lemma sim_thread_exec_consistent
        tid n after_sc th1_ps eu
        (SIM1: sim_thread_exec tid n after_sc th1_ps eu)
        (SC1: forall loc, PSTime.le (th1_ps.(PSThread.global).(PSGlobal.sc) loc) (ntt n))
        (LC_WF1_PS: PSLocal.wf (PSThread.local th1_ps) (PSThread.global th1_ps))
        (GL_WF1_PS: PSGlobal.wf (PSThread.global th1_ps))
        (WF_ARM: RMWLocal.wf tid (RMWExecUnit.local eu) (RMWExecUnit.mem eu)):
    PSThread.consistent th1_ps.
  Proof.
  Admitted.
End PStoRMWConsistent.
