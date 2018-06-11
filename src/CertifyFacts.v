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

Require Import Basic.
Require Import Order.
Require Import Time.
Require Import Lang.
Require Import Promising.
Require Import Algorithmic.

Set Implicit Arguments.


Lemma no_promise_step
      tid aeu1 aeu2
      (STEP: AExecUnit.step tid aeu1 aeu2)
      (WF: ExecUnit.wf tid aeu1)
      (NOPROMISE: aeu1.(ExecUnit.local).(Local.promises) = bot):
  <<NOPROMISE: aeu2.(ExecUnit.local).(Local.promises) = bot>> /\
  <<TAINT: aeu2.(AExecUnit.aux).(AExecUnit.taint) = aeu1.(AExecUnit.aux).(AExecUnit.taint)>>.
Proof.
  destruct aeu1 as [[st1 lc1 mem1] aux1].
  destruct aeu2 as [[st2 lc2 mem2] aux2].
  ss. inv STEP.
  - (* state_step *)
    inv STEP0. inv STEP. ss. subst. inv LOCAL.
    + inv LC. eauto.
    + inv STEP. ss. destruct ex; ss.
    + inv WF. ss. inv LOCAL. inv STEP. inv WRITABLE. ss.
      exploit PROMISES0; eauto. rewrite NOPROMISE, Promises.lookup_bot. ss.
    + inv STEP. ss. esplits; ss.
      funext. i. propext. econs; i.
      * inv H; ss.
      * left. ss.
    + inv STEP. ss.
    + inv STEP. ss.
    + inv STEP. ss.
    + inv STEP. ss.
  - (* write step *)
    inv STEP0. ss. subst.
    inv LOCAL. ss.
Qed.

Lemma no_promise_steps
      tid aeu1 aeu2
      (STEPS: rtc (AExecUnit.step tid) aeu1 aeu2)
      (WF: ExecUnit.wf tid aeu1)
      (NOPROMISE: aeu1.(ExecUnit.local).(Local.promises) = bot):
  <<NOPROMISE: aeu2.(ExecUnit.local).(Local.promises) = bot>> /\
  <<TAINT: aeu2.(AExecUnit.aux).(AExecUnit.taint) = aeu1.(AExecUnit.aux).(AExecUnit.taint)>>.
Proof.
  revert NOPROMISE. induction STEPS; ss. i.
  exploit no_promise_step; eauto. i. des.
  exploit IHSTEPS; eauto.
  { eapply AExecUnit.step_wf; eauto. }
  i. des.
  esplits; ss. etrans; eauto.
Qed.