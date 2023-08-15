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

Require Import PromisingArch.promising.Promising.
Require Import PromisingArch.mapping.RMWLang.
Require Import PromisingArch.mapping.RMWPromising.
Require Import PromisingArch.mapping.PSLang.
Require Import PromisingArch.mapping.PStoRMWUtils.
Require Import PromisingArch.mapping.PStoRMWDef.
Require Import PromisingArch.mapping.PStoRMWThread.

Set Implicit Arguments.


Module PStoRMWTerminal.
  Import PStoRMWThread.

  Lemma sim_state_is_terminal
        st_ps st_arm
        (SIM: sim_state st_ps st_arm):
    Language.is_terminal lang_ps st_ps <-> RMWState.is_terminal st_arm.
  Proof.
    inv SIM.
    destruct st_ps, st_arm; ss. subst.
    unfold Language.is_terminal, RMWState.is_terminal. s.
    unfold State.is_terminal. s.
    split; i; subst; ss.
    destruct stmts; ss.
  Qed.

  Lemma sim_memory_is_terminal
        tid n lc_ps gprm_ps mem_ps lc_arm mem_arm
        (SIM: sim_memory tid n lc_ps gprm_ps mem_ps lc_arm mem_arm)
        (SOUND: Promises.sound tid lc_arm.(Local.promises) mem_arm)
        (N: n = length mem_arm):
    PSLocal.is_terminal lc_ps <-> lc_arm.(Local.promises) = bot.
  Proof.
    inv SIM. split; i.
    - inv H. apply Promises.le_antisym; try apply Promises.bot_spec.
      ii. r in H.
      exploit PRM_SOUND; eauto.
      rewrite PROMISES. i. des.
      exploit PROMISED_PS; ss.
      exploit SOUND; eauto. i. des.
      unfold Memory.get_msg in GET.
      destruct i; ss.
      apply nth_error_some in GET.
      unfold le. nia.
    - econs. apply BoolMap.antisym; try apply BoolMap.bot_spec.
      ii. exploit PRM_COMPLETE; eauto.
      rewrite H. i. des.
      rewrite Promises.lookup_bot in PROMISED_ARM. ss.
  Qed.

  Lemma sim_thread_exec_terminal
        tid n th1_ps eu eu2
        (SIM1: sim_thread_exec tid n true th1_ps eu eu2)
        (N: n = length eu.(RMWExecUnit.mem))
        (SC1: forall loc, PSTime.le (th1_ps.(PSThread.global).(PSGlobal.sc) loc) (ntt n))
        (LC_WF1_PS: PSLocal.wf (PSThread.local th1_ps) (PSThread.global th1_ps))
        (GL_WF1_PS: PSGlobal.wf (PSThread.global th1_ps))
        (WF_ARM: RMWExecUnit.wf tid eu)
        (RMW_WF_ARM: RMWLocal.wf tid (RMWExecUnit.local eu) (RMWExecUnit.mem eu)):
    exists th2_ps,
      (<<STEPS_PS: rtc (@PSThread.tau_step _) th1_ps th2_ps>>) /\
      ((<<SIM2: sim_thread_exec tid n true th2_ps eu eu2>>) /\
       (<<SC2: forall loc, PSTime.le (th2_ps.(PSThread.global).(PSGlobal.sc) loc) (ntt n)>> /\
       (<<TERMINAL_ST: Language.is_terminal _ th2_ps.(PSThread.state)>>) /\
       (<<TERMINAL_LC: PSLocal.is_terminal th2_ps.(PSThread.local)>>)) \/
       exists e_ps th3_ps,
         (<<STEP_PS: PSThread.step e_ps th2_ps th3_ps>>) /\
         (<<FAILURE: ThreadEvent.get_machine_event e_ps = MachineEvent.failure>>)).
  Proof.
    inv SIM1.
    exploit (RMWExecUnit.rtc_state_step_wf (A:=unit)); try exact STEPS1; eauto. intro WF1_ARM.
    exploit (RMWExecUnit.rtc_state_step_wf (A:=unit));
      try eapply rtc_mon; try exact STEPS2;
      try apply RMWExecUnit.dmbsy_over_state_step; eauto. intro WF2_ARM.
    exploit (RMWExecUnit.rtc_state_step_memory (A:=unit)); try exact STEPS1. i.
    exploit (RMWExecUnit.rtc_state_step_memory (A:=unit));
      try eapply rtc_mon; try exact STEPS2;
      try apply RMWExecUnit.dmbsy_over_state_step; eauto. i.
    exploit (RMWExecUnit.rtc_state_step_rmw_wf (A:=unit)); try exact STEPS1; eauto. intro RMW_WF1_ARM.
    exploit (rtc_dmbsy_over_length_non_dmbsy (A:=unit)); try exact STEPS2; eauto; i.
    { rewrite x0. nia. }
    exploit sim_thread_rtc_step;
      try exact SIM_THREAD;
      try eapply rtc_mon; try exact x1;
      try apply RMWExecUnit.non_dmbsy_dmbsy_exact; eauto.
    { rewrite <- x0, <- x1.
      inv WF2_ARM. inv LOCAL. ss.
    }
    { ii. rewrite PROMISES in *.
      rewrite Promises.lookup_bot in *. ss.
    }
    i. des; [|esplits; eauto].
    esplits; eauto. left. splits; ss.
    { econs.
      - etrans; [exact STEPS1|].
        eapply rtc_mon; try eapply RMWExecUnit.state_step_pf_none.
        eapply rtc_mon; try eapply RMWExecUnit.non_dmbsy_state_step.
        exact x2.
      - ss.
      - refl.
      - eauto.
      - ss.
      - ss.
    }
    { inv SIM2. erewrite sim_state_is_terminal; eauto. }
    { inv SIM2. erewrite sim_memory_is_terminal; eauto; try congr.
      exploit (RMWExecUnit.rtc_state_step_rmw_wf (A:=unit));
        try eapply rtc_mon; try exact x2;
        try apply RMWExecUnit.non_dmbsy_state_step; ss. i.
      apply x3.
    }
  Qed.
End PStoRMWTerminal.
