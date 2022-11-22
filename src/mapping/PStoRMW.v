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
Require Import PromisingArch.mapping.PStoRMWConsistent.

Set Implicit Arguments.
Set Nested Proofs Allowed.


Module PStoRMW.
  Import PStoRMWThread.
  Import PStoRMWConsistent.

  Variant sim_thread_sl (tid: Ident.t) (n: Time.t) (after_sc: bool)
    (gl_ps: PSGlobal.t) (mem_arm: Memory.t):
    forall (sl_ps: {lang: language & Language.state lang} * PSLocal.t)
           (sl_arm: RMWState.t (A:=View.t (A:=unit)) * Local.t (A:=unit)), Prop :=
    | sim_thread_sl_intro
        st_ps lc_ps st_arm lc_arm
        (SIM_THREAD: sim_thread_exec tid n after_sc
                       (PSThread.mk _ st_ps lc_ps gl_ps) (RMWExecUnit.mk st_arm lc_arm mem_arm)):
      sim_thread_sl tid n after_sc gl_ps mem_arm
        (existT _ lang_ps st_ps, lc_ps) (st_arm, lc_arm)
  .

  Variant sim (n: Time.t) (after_sc: bool) (c: PSConfiguration.t) (m: RMWMachine.t): Prop :=
    | sim_intro
        m1
        (PROMISE_STEPS: rtc (RMWMachine.step RMWExecUnit.promise_step) m m1)
        (SIM_THREADS:
          forall tid,
            opt_rel
              (sim_thread_sl tid n after_sc c.(PSConfiguration.global) m1.(RMWMachine.mem))
              (IdentMap.find tid c.(PSConfiguration.threads))
              (IdMap.find tid m1.(RMWMachine.tpool)))
        (SIM_SC: forall loc,
            PSTime.le (c.(PSConfiguration.global).(PSGlobal.sc) loc) (ntt n))
  .


  Lemma sim_thread_exec_sc
        tid n th1_ps eu
        (SIM1: sim_thread_exec tid n false th1_ps eu)
        (SC1: forall loc, PSTime.le (th1_ps.(PSThread.global).(PSGlobal.sc) loc) (ntt n))
        (LC_WF1_PS: PSLocal.wf (PSThread.local th1_ps) (PSThread.global th1_ps))
        (GL_WF1_PS: PSGlobal.wf (PSThread.global th1_ps))
        (WF_ARM: RMWLocal.wf tid (RMWExecUnit.local eu) (RMWExecUnit.mem eu)):
    exists th2_ps,
      (<<STEPS_PS: rtc (@PSThread.tau_step _) th1_ps th2_ps>>) /\
      ((<<SIM2: sim_thread_exec tid n true th2_ps eu>>) /\
       (<<SC2: forall loc, PSTime.le (th2_ps.(PSThread.global).(PSGlobal.sc) loc) (ntt n)>>) \/
       exists e_ps th3_ps,
         (<<STEP_PS: PSThread.step e_ps th2_ps th3_ps>>) /\
         (<<FAILURE: ThreadEvent.get_machine_event e_ps = MachineEvent.failure>>)).
  Proof.
    inv SIM1.
    exploit (dmbsy_le_cases (A:=unit)); try exact STEPS2. i. des.
    { esplits; try refl. left. split; ss. econs; eauto. }
    exploit rtc_n1; try exact STEPS_DMBSY1.
    { eapply RMWExecUnit.dmbsy_dmbsy_exact. eauto. }
    intro STEPS_EXACT.
    exploit sim_thread_rtc_step; try exact SIM_THREAD; try exact STEPS_EXACT; eauto.
    { eapply (RMWExecUnit.rtc_state_step_rmw_wf (A:=unit)); eauto. }
    { eapply dmbsy_vro_after. eauto. }
    { eapply (RMWExecUnit.rtc_state_step_fulfillable (A:=unit));
        try eapply rtc_mon; try eapply RMWExecUnit.dmbsy_over_state_step;
        try exact STEPS_DMBSY2.
      ii. rewrite PROMISES, Promises.lookup_bot in *. ss.
    }
    i. des; [|esplits; eauto].
    esplits; eauto. left. split; ss.
    econs.
    - etrans; [exact STEPS1|].
      eapply rtc_mon; try eapply RMWExecUnit.pf_state_step_state_step.
      eapply rtc_mon; try eapply RMWExecUnit.dmbsy_exact_state_step.
      eapply rtc_n1; try exact STEPS_DMBSY1.
      eapply RMWExecUnit.dmbsy_dmbsy_exact. eauto.
    - ss.
    - refl.
    - eauto.
    - ss.

    (* inv SIM1. *)
    (* exploit (dmbsy_le_cases (A:=unit)); try exact STEPS3. i. des. *)
    (* { exploit (dmbsy_le_cases (A:=unit)); try exact STEPS2. i. des. *)
    (*   { esplits; try refl. left. split; ss. econs; eauto. } *)
    (*   exploit rtc_n1; try exact STEPS_DMBSY1. *)
    (*   { eapply RMWExecUnit.dmbsy_dmbsy_exact. eauto. } *)
    (*   intro STEPS_EXACT. *)
    (*   exploit sim_thread_rtc_step; try exact SIM_THREAD; try exact STEPS_EXACT; eauto. *)
    (*   { eapply (RMWExecUnit.rtc_state_step_rmw_wf (A:=unit)); eauto. } *)
    (*   { eapply dmbsy_vro_after. eauto. } *)
    (*   { rewrite STEPS_DMBSY in STEPS_DMBSY2. *)
    (*     eapply (RMWExecUnit.rtc_state_step_fulfillable (A:=unit)); *)
    (*       try eapply rtc_mon; try eapply RMWExecUnit.dmbsy_over_state_step; *)
    (*       try exact STEPS_DMBSY2. *)
    (*     ii. rewrite PROMISES3, Promises.lookup_bot in *. ss. *)
    (*   } *)
    (*   i. des; [|esplits; eauto]. *)
    (*   esplits; eauto. left. split; ss. *)
    (*   econs. *)
    (*   - etrans; [exact STEPS1|]. *)
    (*     eapply rtc_mon; try eapply RMWExecUnit.pf_state_step_state_step. *)
    (*     eapply rtc_mon; try eapply RMWExecUnit.dmbsy_exact_state_step. *)
    (*     eapply rtc_n1; try exact STEPS_DMBSY1. *)
    (*     eapply RMWExecUnit.dmbsy_dmbsy_exact. eauto. *)
    (*   - ss. *)
    (*   - refl. *)
    (*   - eauto. *)
    (*   - ss. *)
    (*   - eauto. *)
    (*   - ss. *)
    (* } *)

    (* { exploit rtc_implies; try exact STEPS_DMBSY1; *)
    (*     try eapply (RMWExecUnit.dmbsy_exact_dmbsy_over (A:=unit)). i. *)
    (*   rewrite x0 in STEPS2. *)
    (*   exploit (steps_dmbsy (A:=unit)); try exact STEPS2; eauto. i. *)
    (*   exploit rtc_n1; try exact x1. *)
    (*   { eapply RMWExecUnit.dmbsy_dmbsy_exact. eauto. } *)
    (*   intro STEPS_EXACT. *)
    (*   exploit sim_thread_rtc_step; try exact SIM_THREAD; try exact STEPS_EXACT; eauto. *)
    (*   { eapply (RMWExecUnit.rtc_state_step_rmw_wf (A:=unit)); eauto. } *)
    (*   { eapply dmbsy_vro_after. eauto. } *)
    (*   { eapply (RMWExecUnit.rtc_state_step_fulfillable (A:=unit)); *)
    (*       try eapply rtc_mon; try eapply RMWExecUnit.dmbsy_over_state_step; *)
    (*       try exact STEPS_DMBSY2. *)
    (*     ii. rewrite PROMISES3, Promises.lookup_bot in *. ss. *)
    (*   } *)
    (*   i. des; [|esplits; eauto]. *)
    (*   esplits; eauto. left. split; ss. *)
    (*   econs. *)
    (*   - etrans; [exact STEPS1|]. *)
    (*     eapply rtc_mon; try eapply RMWExecUnit.pf_state_step_state_step. *)
    (*     eapply rtc_mon; try eapply RMWExecUnit.dmbsy_exact_state_step. *)
    (*     exact STEPS_EXACT. *)
    (*   - ss. *)
    (*   - refl. *)
    (*   - eauto. *)
    (*   - hexploit (RMWExecUnit.rtc_state_step_promises_le (A:=unit)); *)
    (*       try eapply rtc_implies; try eapply RMWExecUnit.dmbsy_over_state_step; try exact STEPS3. *)
    (*     i. auto. *)
    (*   - eauto. *)
    (*   - ss. *)
    (* } *)
  Qed.

  Lemma sim_memory_future
        gl gl'
        tid n lc_ps lc_arm mem_arm
        tid' lc_ps' lc_arm'
        (SIM: sim_memory tid n lc_ps (Global.promises gl) (Global.memory gl) lc_arm mem_arm)
        (FUTURE: Global.future gl gl')
        (WF': PSLocal.wf lc_ps gl')
        (SIM': sim_memory tid' n lc_ps' (Global.promises gl') (Global.memory gl') lc_arm' mem_arm):
    sim_memory tid n lc_ps (Global.promises gl') (Global.memory gl') lc_arm mem_arm.
  Proof.
    inv SIM. inv SIM'. econs; ss; i.
    { (* MEM_SOUND *)
      exploit MEM_SOUND0; eauto. i. des.
      esplits; eauto. clear x1.
      exploit MEM_SOUND; eauto. i. des. clear x2.
      rewrite LOC0 in *. inv LOC.
      unguardH x1. des; subst.
      - unguardH x0. des; subst.
        + left. split; ss. i.
          exploit PROMISED0; eauto. i. des.
          exploit PROMISED; eauto. i. des.
          splits; ss.
        + right. esplits; eauto.
          destruct (Promises.lookup ts (Local.promises lc_arm)) eqn:PRM; ss.
          exploit PRM_SOUND; eauto. i. des.
          rewrite GET_ARM0 in *. inv GET_ARM.
          rewrite LOC in *. inv LOC0.
          inv WF'. exploit RESERVES; eauto. i. congr.
      - right.
        exploit PSMemory.future_get1; try apply FUTURE; eauto. i. des.
        unguardH x0. des; try congr.
        rewrite x1 in *. inv GET_PS.
        esplits; eauto.
    }
    { (* FWD *)
      exploit FWD; eauto. i. des.
      exploit PSMemory.future_get1; try apply FUTURE; eauto. i. des.
      esplits; eauto.
    }
  Qed.

  Lemma sim_sc
        n c1 m
        (SIM1: sim n false c1 m)
        (WF1_PS: PSConfiguration.wf c1)
        (WF_ARM: RMWMachine.rmw_wf m):
    exists c2,
      (<<STEPS_PS: rtc PSConfiguration.tau_step c1 c2>>) /\
      ((<<SIM2: sim n true c2 m>>) \/
       exists tid c3,
         (<<STEP: PSConfiguration.step MachineEvent.failure tid c2 c3>>)).
  Proof.
    inv SIM1.
    exploit RMWMachine.rtc_step_promise_step_rmw_wf; eauto.
    clear WF_ARM. intro WF_ARM.
    assert (exists tids,
               (<<IN: forall tid (IN: List.In tid tids),
                   opt_rel
                     (sim_thread_sl tid n false c1.(PSConfiguration.global) m1.(RMWMachine.mem))
                     (IdentMap.find tid c1.(PSConfiguration.threads))
                     (IdMap.find tid m1.(RMWMachine.tpool))>>) /\
               (<<OUT: forall tid (OUT: ~ List.In tid tids),
                   opt_rel
                     (sim_thread_sl tid n true c1.(PSConfiguration.global) m1.(RMWMachine.mem))
                     (IdentMap.find tid c1.(PSConfiguration.threads))
                     (IdMap.find tid m1.(RMWMachine.tpool))>>) /\
               (<<NODUP: List.NoDup tids>>)).
    { exists (IdentSet.elements (PSThreads.tids (PSConfiguration.threads c1))).
      splits; i.
      - specialize (SIM_THREADS tid).
        inv SIM_THREADS; ss. econs. ss.
      - specialize (SIM_THREADS tid).
        inv SIM_THREADS; ss. exfalso.
        exploit PSThreads.tids_o. rewrite <- H0. s. i.
        rewrite IdentSet.mem_spec in x0.
        rewrite <- IdentSet.elements_spec1 in x0.
        apply OUT. clear - x0.
        induction (IdentSet.elements (PSThreads.tids (PSConfiguration.threads c1)));
          inv x0; ss; auto.
      - specialize (IdentSet.elements_spec2w (PSThreads.tids (PSConfiguration.threads c1))). i.
        clear - H. induction H; econs; eauto.
    }
    des. clear SIM_THREADS.
    revert c1 WF1_PS SIM_SC IN OUT NODUP.
    induction tids; i.
    { esplits; try refl. left. econs; eauto. }
    destruct c1 as [ths1 gl1], m1 as [tpool1 mem1_arm].
    exploit (IN a); ss; auto. intro SIM_THREAD.
    destruct (IdentMap.find a ths1) as [[[lang st1_ps] lc1_ps]|] eqn:FIND_PS; cycle 1.
    { inv SIM_THREAD.
      eapply IHtids; try exact WF1_PS; eauto.
      - s. i.
        destruct (Ident.eq_dec tid a).
        { subst. rewrite FIND_PS, <- H. ss. }
        eapply (OUT tid). ii. des; eauto.
      - inv NODUP. ss.
    }

    inv SIM_THREAD.
    symmetry in H. rename H into FIND_ARM.
    destruct b as [st1_arm lc1_arm].
    inv REL. apply inj_pair2 in H1. subst.
    dup WF1_PS. inv WF1_PS0. inv WF. ss.
    exploit THREADS; eauto. intro LC_WF_PS.
    rename GL_WF into GL_WF_PS.
    clear DISJOINT THREADS PROMISES.
    dup WF_ARM. inv WF_ARM0.
    exploit WF; eauto.
    clear WF. s. intro WF1_ARM.
    exploit sim_thread_exec_sc; try exact SIM_THREAD; eauto. i. des; cycle 1.
    { (* UB *)
      destruct th3_ps.
      esplits; try refl.
      right. esplits. rewrite <- FAILURE.
      econs; try apply FIND_PS; eauto. i. congr.
    }

    destruct th2_ps as [st2_ps lc2_ps gl2]. ss.
    exploit PSThread.rtc_tau_step_future; try exact STEPS_PS; eauto. s. i. des.
    hexploit sim_thread_exec_consistent; try exact SIM2; ss. intro CONSISTENT.
    exploit (@rtc_thread_tau_step_rtc_tau_step (Configuration.mk ths1 gl1)); eauto. s. i. des.
    exploit PSConfiguration.rtc_tau_step_future; try exact x0; ss. i. des.
    exploit IHtids; try exact WF2; ss.
    { i. rewrite IdentMap.gsspec. condtac; subst.
      { inv NODUP. ss. }
      exploit IN; eauto. i. inv x1.
      { destruct (IdentMap.find tid ths1) eqn:FIND; ss. }
      destruct (IdentMap.find tid ths1) eqn:FIND; ss. inv H0.
      destruct p as [[lang' st_ps] lc_ps], b as [st_arm lc_arm]. inv REL.
      apply inj_pair2 in H2. subst. econs. econs.
      inv SIM_THREAD0. econs; eauto.
      inv SIM_THREAD1. econs; ss.
      exploit (RMWExecUnit.rtc_state_step_memory (A:=unit)); try exact STEPS1.
      s. i. rewrite x1 in *. clear x1.
      inv SIM2. inv SIM_THREAD0. ss.
      exploit (RMWExecUnit.rtc_state_step_memory (A:=unit)); try exact STEPS0.
      s. i. rewrite x1 in *. clear x1.
      inv SIM_THREAD. inv SIM_THREAD0. ss.
      exploit (RMWExecUnit.rtc_state_step_memory (A:=unit)); try exact STEPS4.
      s. i. rewrite x1 in *. clear x1.
      eapply (@sim_memory_future gl1 gl2); eauto.
      inv WF1_PS. inv WF. ss.
      exploit THREADS; try exact FIND. i.
      exploit DISJOINT; try exact n0; eauto. i. symmetry in x2.
      exploit PSThread.rtc_tau_step_disjoint;
        try exact STEPS_PS; try exact x2; eauto. s. i. des. ss.
    }
    { i. rewrite IdentMap.gsspec. condtac; subst.
      { rewrite FIND_ARM. econs. ss. }
      exploit (OUT tid).
      { ii. des; congr. }
      i. inv x1.
      { destruct (IdentMap.find tid ths1) eqn:FIND; ss. }
      destruct (IdentMap.find tid ths1) eqn:FIND; ss. inv H0.
      destruct p as [[lang' st_ps] lc_ps], b as [st_arm lc_arm]. inv REL.
      apply inj_pair2 in H2. subst. econs. econs.
      inv SIM_THREAD0. econs; eauto.
      inv SIM_THREAD1. econs; ss.
      exploit (RMWExecUnit.rtc_state_step_memory (A:=unit)); try exact STEPS1.
      s. i. rewrite x1 in *. clear x1.
      inv SIM2. inv SIM_THREAD0. ss.
      exploit (RMWExecUnit.rtc_state_step_memory (A:=unit)); try exact STEPS0.
      s. i. rewrite x1 in *. clear x1.
      inv SIM_THREAD. inv SIM_THREAD0. ss.
      exploit (RMWExecUnit.rtc_state_step_memory (A:=unit)); try exact STEPS4.
      s. i. rewrite x1 in *. clear x1.
      eapply (@sim_memory_future gl1 gl2); eauto.
      inv WF1_PS. inv WF. ss.
      exploit THREADS; try exact FIND. i.
      exploit DISJOINT; try exact n0; eauto. i. symmetry in x2.
      exploit PSThread.rtc_tau_step_disjoint;
        try exact STEPS_PS; try exact x2; eauto. s. i. des. ss.
    }
    { inv NODUP. ss. }
    i. des.
    - esplits; [|left; eauto]. etrans; eauto.
    - esplits; [|right; eauto]. etrans; eauto.
  Qed.
End PStoRMW.
