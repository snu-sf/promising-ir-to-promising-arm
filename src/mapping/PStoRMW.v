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
Require Import PromisingArch.mapping.PStoRMWInit.
Require Import PromisingArch.mapping.PStoRMWThread.
Require Import PromisingArch.mapping.PStoRMWConsistent.

Set Implicit Arguments.
Set Nested Proofs Allowed.


Module PStoRMW.
  Import PStoRMWInit.
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
        (SIM_THREADS:
          forall tid,
            opt_rel
              (sim_thread_sl tid n after_sc c.(PSConfiguration.global) m.(RMWMachine.mem))
              (IdentMap.find tid c.(PSConfiguration.threads))
              (IdMap.find tid m.(RMWMachine.tpool)))
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
      eapply rtc_mon; try eapply RMWExecUnit.state_step_pf_none.
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
        + left. splits; ss. i.
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
                     (sim_thread_sl tid n false c1.(PSConfiguration.global) m.(RMWMachine.mem))
                     (IdentMap.find tid c1.(PSConfiguration.threads))
                     (IdMap.find tid m.(RMWMachine.tpool))>>) /\
               (<<OUT: forall tid (OUT: ~ List.In tid tids),
                   opt_rel
                     (sim_thread_sl tid n true c1.(PSConfiguration.global) m.(RMWMachine.mem))
                     (IdentMap.find tid c1.(PSConfiguration.threads))
                     (IdMap.find tid m.(RMWMachine.tpool))>>) /\
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
    destruct c1 as [ths1 gl1], m as [tpool1 mem1_arm].
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

  Lemma sim_memory_future_S
        gl gl'
        tid n lc_ps lc_arm mem_arm
        tid' lc_ps' lc_arm'
        (SIM: sim_memory tid n lc_ps (Global.promises gl) (Global.memory gl) lc_arm mem_arm)
        (FUTURE: Global.future gl gl')
        (WF': PSLocal.wf lc_ps gl')
        (SIM': sim_memory tid' (S n) lc_ps' (Global.promises gl') (Global.memory gl') lc_arm' mem_arm):
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
        + left. splits; ss. i.
          exploit PROMISED0; eauto.
          { unfold le in *. nia. }
          i. des.
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

  Lemma sim_memory_S_already
        tid n lc_ps gprm_ps mem_ps lc_arm mem_arm
        msg_arm
        (SIM: sim_memory tid n lc_ps gprm_ps mem_ps lc_arm mem_arm)
        (GET: Memory.get_msg (S n) mem_arm = Some msg_arm)
        (TID: msg_arm.(Msg.tid) = tid)
        (NON_PROMISED: Promises.lookup (S n) lc_arm.(Local.promises) = false):
    sim_memory tid (S n) lc_ps gprm_ps mem_ps lc_arm mem_arm.
  Proof.
    inv SIM.
    move GET at bottom.
    move NON_PROMISED at bottom.
    econs; eauto; i.
    { exploit PRM_SOUND; eauto. i. des.
      esplits; eauto. i. inv H; auto. congr.
    }
    { exploit PRM_COMPLETE; eauto. i. des.
      esplits; eauto. etrans; eauto. unfold le. nia.
    }
    { exploit MEM_SOUND; eauto. i. des.
      esplits; eauto. clear x1.
      unguardH x0. des; [left|right]; esplits; eauto.
      i. inv H; auto.
      rewrite GET_ARM in *. inv GET.
      exploit PROMISED_ARM0; eauto. i. congr.
    }
  Qed.

  Lemma sim_memory_S_other
        tid tid'
        n lc_ps gprm_ps mem_ps lc_arm mem_arm
        lc_ps' lc_arm'
        msg_arm
        (TID: tid <> tid')
        (DISJOINT: Local.disjoint lc_ps lc_ps')
        (SIM: sim_memory tid n lc_ps gprm_ps mem_ps lc_arm mem_arm)
        (SIM': sim_memory tid' (S n) lc_ps' gprm_ps mem_ps lc_arm' mem_arm)
        (GET_ARM: Memory.get_msg (S n) mem_arm = Some msg_arm)
        (MSG_TID: msg_arm.(Msg.tid) = tid'):
    sim_memory tid (S n) lc_ps gprm_ps mem_ps lc_arm mem_arm.
  Proof.
    inv SIM. inv SIM'.
    move GET_ARM at bottom.
    econs; eauto; i.
    - exploit PRM_SOUND; eauto. i. des.
      esplits; eauto. i.
      inv H; eauto.
      rewrite GET_ARM in *. inv GET_ARM0. ss.
    - exploit PRM_COMPLETE; eauto. i. des.
      esplits; eauto. etrans; eauto. unfold le. nia.
    - exploit MEM_SOUND; eauto. i. des.
      esplits; eauto. clear x1. unguardH x0.
      des; [left|right]; esplits; eauto.
      i. inv H; eauto.
      rewrite GET_ARM in *. inv GET_ARM0.
      exploit MEM_SOUND0; eauto. i. des. clear x1.
      rewrite LOC in *. inv LOC0.
      rewrite GET_PS in *. inv GET_PS0.
      unguardH x0. des; try congr.
      exploit PROMISED0; try refl. i. des.
      exploit PROMISED_PS0; try refl. i.
      repeat split; try congr; i.
      inv DISJOINT. exploit PROMISES_DISJOINT; eauto. ss.
  Qed.

  Lemma sim_memory_S_fulfill
        tid n lc_ps gprm_ps mem_ps lc_arm mem_arm
        msg_arm
        (SIM: sim_memory tid n lc_ps gprm_ps mem_ps lc_arm mem_arm)
        (GET_ARM: Memory.get_msg (S n) mem_arm = Some msg_arm)
        (MSG_TID: msg_arm.(Msg.tid) = tid)
        (FULFILLED: Promises.lookup (S n) lc_arm.(Local.promises) = false):
    sim_memory tid (S n) lc_ps gprm_ps mem_ps lc_arm mem_arm.
  Proof.
    inv SIM.
    move GET_ARM at bottom.
    move FULFILLED at bottom.
    exploit MEM_SOUND; eauto. i. des.
    unguardH x0. des; subst.
    { exploit PROMISED_ARM0; eauto. congr. }
    econs; eauto; i.
    - exploit PRM_SOUND; try exact PROMISED_ARM0. i. des.
      esplits; eauto. i. inv H; auto. congr.
    - exploit PRM_COMPLETE; eauto. i. des.
      esplits; eauto. etrans; eauto. unfold le. nia.
    - exploit MEM_SOUND; try exact GET_ARM0. i. des.
      esplits; eauto. clear x2.
      unguardH x0. des; [left|right]; esplits; eauto.
      i. inv H; auto. congr.
  Qed.

  Variant promised_thread {lang} (loc: PSLoc.t) (th1 th2: PSThread.t lang): Prop :=
    | promised_thread_intro
        (STATE: th2.(PSThread.state) = th1.(PSThread.state))
        (TVIEW: th2.(PSThread.local).(PSLocal.tview) = th1.(PSThread.local).(PSLocal.tview))
        (PRM: th2.(PSThread.local).(PSLocal.promises) =
              fun loc' => if PSLoc.eq_dec loc' loc then true
                       else th1.(PSThread.local).(PSLocal.promises) loc')
        (RSV: th2.(PSThread.local).(PSLocal.reserves) = th1.(PSThread.local).(PSLocal.reserves))
        (SC: th2.(PSThread.global).(Global.sc) = th1.(PSThread.global).(Global.sc))
        (GPRM: th2.(PSThread.global).(Global.promises) =
               fun loc' => if PSLoc.eq_dec loc' loc then true
                        else th1.(PSThread.global).(Global.promises) loc')
        (MEM: th2.(PSThread.global).(Global.memory) = th1.(PSThread.global).(Global.memory))
  .

  Lemma sim_memory_S_promise
        tid n lc1_ps gprm1_ps mem1_ps lc_arm mem_arm
        msg_arm
        loc lc2_ps gprm2_ps mem2_ps
        (SIM: sim_memory tid n lc1_ps gprm1_ps mem1_ps lc_arm mem_arm)
        (PRM_ARM: Promises.lookup (S n) lc_arm.(Local.promises) = true)
        (GET_ARM: Memory.get_msg (S n) mem_arm = Some msg_arm)
        (MSG_TID: msg_arm.(Msg.tid) = tid)
        (LOC: msg_arm.(Msg.loc) = Zpos loc)
        (TVIEW: lc2_ps.(PSLocal.tview) = lc1_ps.(PSLocal.tview))
        (PRM: lc2_ps.(PSLocal.promises) =
              fun loc' => if PSLoc.eq_dec loc' loc then true
                       else lc1_ps.(PSLocal.promises) loc')
        (RSV: lc2_ps.(PSLocal.reserves) = lc1_ps.(PSLocal.reserves))
        (GPRM: gprm2_ps =
               fun loc' => if PSLoc.eq_dec loc' loc then true
                        else gprm1_ps loc')
        (MEM: mem2_ps = mem1_ps)
        (NON_OTHER: gprm1_ps loc -> lc1_ps.(PSLocal.promises) loc):
    sim_memory tid (S n) lc2_ps gprm2_ps mem2_ps lc_arm mem_arm.
  Proof.
    inv SIM. econs; ss; i.
    { exploit PRM_SOUND; eauto. i. des.
      esplits; eauto.
      - rewrite RSV. eassumption.
      - i. inv H.
        + rewrite GET_ARM0 in *. inv GET_ARM.
          rewrite LOC0 in *. inv LOC.
          rewrite PRM. condtac; ss.
        + rewrite PRM. condtac; ss. auto.
    }
    { revert PROMISED_PS.
      rewrite PRM. condtac; i.
      - subst. esplits; eauto. refl.
      - exploit PRM_COMPLETE; eauto. i. des.
        esplits; eauto. etrans; eauto. unfold le. nia.
    }
    { exploit MEM_SOUND; eauto. i. des.
      esplits; eauto. clear x1.
      unguardH x0. des; [|right; esplits; eauto].
      left. splits; ss. i. inv H.
      - rewrite GET_ARM0 in *. inv GET_ARM.
        rewrite LOC0 in *. inv LOC.
        rewrite PRM. condtac; ss.
      - rewrite PRM. condtac; eauto.
        subst. repeat split; ss.
        exploit PROMISED; ss. i. des. eauto.
    }
    { rewrite TVIEW. eauto. }
  Qed.

  Lemma sim_thread_exec_S
        tid n th1_ps eu
        (SIM: sim_thread_exec tid n true th1_ps eu)
        (PROMISED: Promises.lookup (S n) eu.(RMWExecUnit.local).(Local.promises) = true)
        (SC1: forall loc, PSTime.le (th1_ps.(PSThread.global).(PSGlobal.sc) loc) (ntt n))
        (LC_WF1_PS: PSLocal.wf (PSThread.local th1_ps) (PSThread.global th1_ps))
        (GL_WF1_PS: PSGlobal.wf (PSThread.global th1_ps))
        (WF_ARM: RMWLocal.wf tid (RMWExecUnit.local eu) (RMWExecUnit.mem eu)):
    exists th2_ps,
      (<<STEPS_PS: rtc (@PSThread.tau_step _) th1_ps th2_ps>>) /\
      ((<<SIM2: sim_thread_exec tid (S n) false th2_ps eu>>) /\
       (<<SC2: forall loc, PSTime.le (th2_ps.(PSThread.global).(PSGlobal.sc) loc) (ntt n)>>) \/
       exists e_ps th3_ps,
         (<<STEP_PS: PSThread.step e_ps th2_ps th3_ps>>) /\
         (<<FAILURE: ThreadEvent.get_machine_event e_ps = MachineEvent.failure>>)).
  Proof.
    inv SIM.
    exploit (steps_fulfill_cases (A:=unit)); try exact STEPS2; ss. i. unguard. des.
    { esplits; try refl. left. split; ss.
      econs; try exact PROMISES; eauto.
      inv SIM_THREAD. econs; ss.
      inv WF_ARM. exploit PRM; eauto. i. des.
      exploit (RMWExecUnit.rtc_state_step_memory (A:=unit)); try exact STEPS1. i.
      rewrite <- x0 in *.
      eapply sim_memory_S_already; eauto.
    }
    assert (FULFILL_STEPS: rtc (RMWExecUnit.state_step_dmbsy_exact (Some n) n tid) eu1 eu1').
    { clear - STEPS0 FULFILL.
      exploit (fulfill_step_vwn (A:=unit)); eauto. i. des.
      clear - STEPS0 VWN1.
      induction STEPS0; try refl.
      econs 2; try apply IHSTEPS0; ss.
      inv H. econs.
      - eapply RMWExecUnit.state_step0_pf_mon; try exact STEP. nia.
      - i. exploit DMBSY; eauto. i.
        destruct e; ss. destruct rr, rw, wr, ww; ss.
        cut (S n <= y.(RMWExecUnit.local).(Local.vwn).(View.ts)).
        { i. exfalso.
          exploit (RMWExecUnit.rtc_state_step_incr (A:=unit));
            try eapply rtc_mon; try exact STEPS0;
            try apply RMWExecUnit.dmbsy_over_state_step. i.
          inv x2. inv LC. unfold le in *. nia.
        }
        clear - STEP x1.
        inv STEP. inv LOCAL; ss. inv STEP. rewrite LC2. ss.
        inv EVENT. ss.
        etrans; [eauto|].
        etrans; [|apply join_r].
        eapply join_le; [apply Time.order|..]; ss.
        apply join_l.
    }

    destruct (OrdW.ge OrdW.pln ord) eqn:ORD.
    { (* pln *)
      exploit (fulfill_step_future (A:=unit)); eauto. i. des.
      replace eu1''.(RMWExecUnit.mem) with eu1.(RMWExecUnit.mem) in GET_ARM; cycle 1.
      { exploit (RMWExecUnit.rtc_state_step_memory (A:=unit));
          try eapply rtc_mon; try exact STEPS0;
          try apply RMWExecUnit.dmbsy_over_state_step. i.
        inv FULFILL; congr.
      }
      dup SIM_THREAD. inv SIM_THREAD0. clear SIM_STATE SIM_TVIEW.
      inv SIM_MEM. clear PRM_SOUND PRM_COMPLETE MEM_COMPLETE FWD RELEASED.
      exploit MEM_SOUND; eauto. clear MEM_SOUND. i. des.
      cut (exists th2_ps,
              (<<STEPS: rtc (@PSThread.tau_step _) th1_ps th2_ps>>) /\
              ((<<PROMISED: promised_thread loc_ps th1_ps th2_ps>>) /\
               (<<NON_OTHER: th1_ps.(PSThread.global).(Global.promises) loc_ps ->
                             th1_ps.(PSThread.local).(PSLocal.promises) loc_ps>>) \/
               exists e_ps th3_ps,
                 (<<STEP_PS: PSThread.step e_ps th2_ps th3_ps>>) /\
                 (<<FAILURE: ThreadEvent.get_machine_event e_ps = MachineEvent.failure>>))).
      { i. des; [|esplits; eauto].
        esplits; try exact STEPS.
        left. split; cycle 1.
        { inv PROMISED1. rewrite SC. ss. }
        econs.
        - exact STEPS1.
        - inv SIM_THREAD. econs; try by (inv PROMISED1; congr).
          eapply sim_memory_S_promise; eauto; apply PROMISED1.
        - refl.
        - etrans; [exact STEPS0|].
          econs 2; [|exact STEPS3].
          exploit (fulfill_step_state_step0_pln (A:=unit)); eauto. i. des.
          econs; eauto. ss.
        - ss.
      }

      destruct (th1_ps.(PSThread.local).(PSLocal.promises) loc_ps) eqn:PRM_PS.
      { esplits; try refl. left.
        split; ss. econs; ss.
        - extensionality l. condtac; ss; congr.
        - extensionality l. condtac; ss. subst.
          inv LC_WF1_PS. eauto.
      }
      { destruct (th1_ps.(PSThread.global).(Global.promises) loc_ps) eqn:GPRM_PS; cycle 1.
        { (* promise *)
          destruct th1_ps as [st1 lc1 mem1]. ss. esplits.
          - econs 2; try refl. econs.
            + econs 1. econs 1. econs.
              * econs 1; econs; eauto.
              * refl.
              * refl.
            + ss.
          - left. ss.
        }

        (* promised by another thread *)
        clear x1 x0.
        exploit sim_thread_sim_thread_cons; eauto. intro SIM_CONS.
        exploit (RMWExecUnit.rtc_state_step_rmw_wf (A:=unit)); try exact STEPS1; eauto. i.
        exploit (RMWExecUnit.rtc_state_step_rmw_wf (A:=unit));
          try eapply rtc_mon; try exact STEPS0;
          try apply RMWExecUnit.dmbsy_over_state_step; ss. i.
        exploit (fulfill_step_vcap (A:=unit)); try exact FULFILL; ss. i. des.
        hexploit (RMWExecUnit.rtc_state_step_fulfillable (A:=unit));
          try eapply rtc_mon; try exact STEPS3;
          try apply RMWExecUnit.dmbsy_over_state_step.
        { ii. rewrite PROMISES in *. rewrite Promises.lookup_bot in *. ss. }
        i. hexploit (fulfill_step_fulfillable (A:=unit)); eauto. intro FULFILLABLE.
        exploit sim_thread_cons_rtc_step; try exact FULFILL_STEPS; eauto; try nia.
        i. des; [|esplits; eauto].
        esplits; try exact STEPS_PS. right.
        exploit PSThread.rtc_tau_step_promises_minus; try exact STEPS_PS. i.
        eapply equal_f in x2. revert x2.
        unfold BoolMap.minus. rewrite PRM_PS, GPRM_PS. ss.
        destruct (th2_ps.(PSThread.local).(PSLocal.promises) loc_ps) eqn:PRM_PS2,
            (th2_ps.(PSThread.global).(Global.promises) loc_ps) eqn:GPRM_PS2; ss.
        i. clear x2.
        destruct th2_ps as [st2_ps lc2_ps gl2_ps]. ss.
        inv SIM2. inv FULFILL.
        - exploit sim_state_cons_write; eauto. i. des.
          replace loc_ps0 with loc_ps in *; cycle 1.
          { destruct eu1''. ss.
            exploit LOC0.
            { cut (vloc.(ValA.annot).(View.ts) <= View.ts (Local.vcap local)).
              { i. etrans; [exact H0|]. nia. }
              inv FULFILL0. ss. ets.
            }
            i. inv FULFILL0. ss.
            exploit (RMWExecUnit.rtc_state_step_memory (A:=unit));
              try eapply rtc_mon; try exact FULFILL_STEPS;
              try apply RMWExecUnit.dmbsy_exact_state_step. i.
            rewrite x3 in MSG. rewrite MSG in *.
            destruct msg_arm. ss. clarify.
            rewrite H2 in *. inv x2. ss.
          }
          esplits.
          + econs 2; [|econs 9]; eauto.
          + ss.
        - exploit sim_state_cons_fadd_weak; eauto. i. des.
          specialize (x3 vold.(ValA.val)). des. ss.
          replace loc_ps0 with loc_ps in *; cycle 1.
          { destruct eu1''. ss.
            exploit LOC0.
            { cut (vloc.(ValA.annot).(View.ts) <= View.ts (Local.vcap local)).
              { i. etrans; [exact H0|]. nia. }
              inv STEP_CONTROL. ss.
              inv STEP_FULFILL. ss.
              ets.
            }
            i. inv STEP_FULFILL. ss.
            exploit (RMWExecUnit.rtc_state_step_memory (A:=unit));
              try eapply rtc_mon; try exact FULFILL_STEPS;
              try apply RMWExecUnit.dmbsy_exact_state_step. i.
            rewrite x3 in MSG. rewrite MSG in *.
            destruct msg_arm. ss. clarify.
            rewrite H2 in *. inv x2. ss.
          }
          esplits.
          + econs 2; [|econs 10]; eauto.
          + ss.
      }
    }

    { (* >= strong *)
      assert (STEPS: rtc (RMWExecUnit.state_step_dmbsy_exact (Some n) n tid) eu1 eu1'').
      { exploit (fulfill_step_state_step0 (A:=unit)); eauto. i. des.
        eapply rtc_n1; try exact FULFILL_STEPS. econs; eauto. ss.
      }
      exploit sim_thread_rtc_step; try exact STEPS; eauto.
      { eapply RMWExecUnit.rtc_state_step_rmw_wf; eauto. }
      { exploit (fulfill_step_vro (A:=unit)); eauto; try by destruct ord. i. des.
        unfold le. nia.
      }
      { eapply RMWExecUnit.rtc_state_step_fulfillable;
          try eapply rtc_mon;
          try apply RMWExecUnit.dmbsy_over_state_step;
          try exact STEPS3.
        ii. revert PROMISED1.
        rewrite PROMISES, Promises.lookup_bot. ss.
      }
      i. des; [|esplits; eauto].
      esplits; try exact STEPS_PS. left. split; ss.
      econs.
      - etrans; [eauto|].
        eapply rtc_mon; try exact STEPS. i.
        eapply RMWExecUnit.state_step_pf_none.
        eapply RMWExecUnit.dmbsy_exact_state_step. eauto.
      - inv SIM2. econs; eauto.
        exploit (fulfill_step_future (A:=unit)); eauto. i. des.
        eapply sim_memory_S_fulfill; eauto.
      - refl.
      - eauto.
      - ss.
    }
  Qed.

  Lemma sim_S
        n c1 m
        (SIM1: sim n true c1 m)
        (LT: n < length m.(RMWMachine.mem))
        (MEMORY: RMWMachine.promised_memory m)
        (WF1_PS: PSConfiguration.wf c1)
        (WF_ARM: RMWMachine.rmw_wf m):
    exists c2,
      (<<STEPS_PS: rtc PSConfiguration.tau_step c1 c2>>) /\
      ((<<SIM2: sim (S n) false c2 m>>) \/
       exists tid c3,
         (<<STEP: PSConfiguration.step MachineEvent.failure tid c2 c3>>)).
  Proof.
    destruct c1 as [ths1 gl1], m as [mpool1 mem_arm1].
    destruct (Memory.get_msg (S n) mem_arm1) as [[]|] eqn:GET_ARM; cycle 1.
    { unfold Memory.get_msg in *. ss.
      rewrite List.nth_error_None in GET_ARM. nia.
    }
    exploit MEMORY; eauto. s. i. des.
    rename st into st1_arm, lc into lc1_arm, FIND into FIND_ARM.
    inv SIM1. ss.
    exploit SIM_THREADS. rewrite FIND_ARM. i. inv x0.
    destruct a as [[lang st1_ps] lc1_ps]. inv REL.
    apply inj_pair2 in H2. subst.
    rename H0 into FIND_PS.
    dup WF1_PS. inv WF1_PS0. inv WF.
    exploit THREADS; eauto.
    intro LC_WF1_PS. rename GL_WF into GL_WF1_PS.
    clear DISJOINT THREADS PROMISES.
    dup WF_ARM. inv WF_ARM0. exploit WF; eauto. s. intro WF1_ARM.
    clear WF.
    exploit sim_thread_exec_S; try exact SIM_THREAD; eauto. i. des; cycle 1.
    { destruct th3_ps.
      esplits; try refl. right. esplits.
      rewrite <- FAILURE. econs.
      - eauto.
      - eassumption.
      - eassumption.
      - ss.
    }

    exploit PSThread.rtc_tau_step_future; try exact SIM2; eauto. s. i. des.
    exploit sim_thread_exec_consistent; try exact SIM2; eauto.
    { i. etrans; eauto. apply le_ntt. nia. }
    intro CONS.
    exploit (@rtc_thread_tau_step_rtc_tau_step (Configuration.mk ths1 gl1));
      try exact STEPS_PS; eauto. s. i. des.
    esplits; try exact x0. left.
    econs; s; cycle 1.
    { i. etrans; eauto. econs. apply PSTime.incr_spec. }
    intro tid'. rewrite IdentMap.gsspec. condtac.
    { subst. rewrite FIND_ARM. econs. econs.
      destruct th2_ps. ss.
    }
    specialize (SIM_THREADS tid').
    inv SIM_THREADS; destruct (IdentMap.find tid' ths1) eqn:FIND_PS'; ss.
    rename H into FIND_ARM'. inv H0.
    destruct p as [[lang' st_ps'] lc_ps'], b as [st_arm' lc_arm']. inv REL.
    apply inj_pair2 in H1. subst. econs. econs.
    inv SIM_THREAD0. econs; try exact STEPS1; try exact PROMISES; try refl.
    - clear - WF1_PS GET_ARM FIND_PS STEPS_PS SIM2 GL_FUTURE n0 FIND_PS' STEPS1 SIM_THREAD1.
      inv SIM_THREAD1. econs; ss. clear SIM_STATE SIM_TVIEW.
      inv WF1_PS. inv WF. ss.
      exploit (THREADS tid); eauto. intro LC_WF_PS.
      exploit (THREADS tid'); eauto. intro LC_WF_PS'.
      exploit DISJOINT; try exact n0; eauto.
      clear DISJOINT THREADS PROMISES. intro DISJOINT. symmetry in DISJOINT.
      exploit PSThread.rtc_tau_step_disjoint;
        try exact STEPS_PS; try exact DISJOINT; ss. i. des.
      inv SIM2. inv SIM_THREAD. clear eu2 STEPS2 PROMISES SIM_STATE SIM_TVIEW.
      exploit (RMWExecUnit.rtc_state_step_memory (A:=unit)); try exact STEPS1. s. i.
      exploit (RMWExecUnit.rtc_state_step_memory (A:=unit)); try exact STEPS0. s. i.
      rewrite x0, x1 in *. clear x0 x1.
      exploit sim_memory_future_S; try exact GL_FUTURE; try exact SIM_MEM0; eauto. intro X.
      eapply sim_memory_S_other; try exact X; try exact SIM_MEM0; eauto.
      symmetry. ss.
    - exploit (RMWExecUnit.rtc_state_step_memory (A:=unit)); try exact STEPS1. s. i.
      rewrite <- x1 in GET_ARM.
      clear - n0 GET_ARM STEPS2.
      revert GET_ARM. induction STEPS2; i; try refl.
      exploit IHSTEPS2.
      { inv H. inv STEP. congr. }
      i. econs 2; eauto.
      clear - n0 H GET_ARM.
      inv H. econs; eauto.
      inv STEP. econs; eauto.
      inv LOCAL.
      + econs 1; eauto.
      + econs 2; eauto.
      + econs 3; eauto. i. inv H; auto.
        inv STEP. rewrite GET_ARM in *. congr.
      + econs 4; eauto. i. inv H; auto.
        inv STEP_FULFILL. i. rewrite GET_ARM in *. congr.
      + econs 5; eauto.
      + econs 6; eauto.
  Qed.

  Lemma sim_length
        n c1 m
        (SIM1: sim n false c1 m)
        (LT: n <= length m.(RMWMachine.mem))
        (MEMORY: RMWMachine.promised_memory m)
        (WF1_PS: PSConfiguration.wf c1)
        (WF_ARM: RMWMachine.rmw_wf m):
    exists c2,
      (<<STEPS_PS: rtc PSConfiguration.tau_step c1 c2>>) /\
      ((<<SIM2: sim (length m.(RMWMachine.mem)) true c2 m>>) \/
       exists tid c3,
         (<<STEP: PSConfiguration.step MachineEvent.failure tid c2 c3>>)).
  Proof.
    remember ((length m.(RMWMachine.mem)) - n) as k.
    replace n with ((length m.(RMWMachine.mem)) - k) in * by nia.
    clear n Heqk.
    revert k c1 SIM1 LT WF1_PS.
    induction k; i.
    { rewrite Nat.sub_0_r in *.
      exploit sim_sc; eauto.
    }
    destruct (le_lt_dec (S k) (length m.(RMWMachine.mem))); cycle 1.
    { apply IHk; ss; try nia.
      replace (length m.(RMWMachine.mem) - k)
        with (length m.(RMWMachine.mem) - S k) by nia. ss.
    }
    exploit sim_sc; eauto. i. des; [|esplits; eauto].
    exploit rtc_tau_step_future; try exact STEPS_PS; eauto. i. des.
    exploit sim_S; try exact SIM2; eauto; try nia. i. des.
    - exploit rtc_tau_step_future; try exact STEPS_PS0; eauto. i. des.
      replace (S (length (RMWMachine.mem m) - S k))
        with (length (RMWMachine.mem m) - k) in * by nia.
      exploit IHk; try exact SIM0; eauto; try nia. i. des.
      + esplits; [|left; eauto]. repeat (etrans; eauto).
      + esplits; [|right; eauto]. repeat (etrans; eauto).
    - esplits; [|right; eauto]. etrans; eauto.
  Qed.
End PStoRMW.
