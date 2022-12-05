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


Module PStoRMWInit.
  Import PStoRMWThread.

  Variant sim_memory_init (tid: Ident.t) (rsv_ps: PSMemory.t) (mem_ps: PSMemory.t) (mem_arm: Memory.t): Prop :=
    | sim_memory_init_intro
        (MEM_SOUND: forall ts msg_arm
                           (GET_ARM: Memory.get_msg ts mem_arm = Some msg_arm),
          exists loc_ps from,
            (<<LOC: msg_arm.(Msg.loc) = Zpos loc_ps>>) /\
            (<<GET_PS: PSMemory.get loc_ps (ntt ts) mem_ps = Some (from, Message.reserve)>>) /\
            (<<RESERVED: msg_arm.(Msg.tid) = tid ->
                         PSMemory.get loc_ps (ntt ts) rsv_ps = Some (from, Message.reserve)>>) /\
            (<<TS: PSTime.lt from (ntt ts)>>) /\
            (__guard__ (
               (<<FROM: from = PSTime.bot>>) \/
               exists fts fval ftid,
                 (<<FROM: from = ntt fts>>) /\
                 (<<GET_FROM_ARM: Memory.get_msg fts mem_arm = Some (Msg.mk msg_arm.(Msg.loc) fval ftid)>>) /\
                 (<<EMPTY: empty_loc msg_arm.(Msg.loc) fts ts mem_arm>>))))
        (MEM_COMPLETE: forall loc_ps from to msg_ps
                              (TO: PSTime.lt PSTime.bot to)
                              (GET_PS: PSMemory.get loc_ps to mem_ps = Some (from, msg_ps)),
          exists ts msg_arm,
            (<<TO: to = ntt ts>>) /\
            (<<MSG_PS: msg_ps = Message.reserve>>) /\
            (<<GET_ARM: Memory.get_msg ts mem_arm = Some msg_arm>>) /\
            (<<LOC: msg_arm.(Msg.loc) = Zpos loc_ps>>))
  .

  Variant sim_thread_init (tid: Ident.t) (th_ps: PSThread.t lang_ps) (eu: RMWExecUnit.t (A:=unit)): Prop :=
    | sim_thread_init_intro
        (PROMISES_PS: PSLocal.promises (PSThread.local th_ps) = BoolMap.bot)
        (FWD: forall loc, eu.(RMWExecUnit.local).(Local.fwdbank) loc = FwdItem.mk bot bot false)
        (SIM_STATE: sim_state (PSThread.state th_ps) (RMWExecUnit.state eu))
        (SIM_TVIEW: sim_tview (PSLocal.tview (PSThread.local th_ps)) (RMWExecUnit.local eu))
        (SIM_MEM: sim_memory_init tid
                                  (PSLocal.reserves (PSThread.local th_ps))
                                  (PSGlobal.memory (PSThread.global th_ps))
                                  (RMWExecUnit.mem eu))
  .

  Variant sim_thread_sl_init (tid: Ident.t) (gl_ps: PSGlobal.t) (mem_arm: Memory.t):
    forall (sl_ps: {lang: language & Language.state lang} * PSLocal.t)
           (sl_arm: RMWState.t (A:=View.t (A:=unit)) * Local.t (A:=unit)), Prop :=
    | sim_thread_sl_init_intro
        st_ps lc_ps st_arm lc_arm
        (SIM_THREAD: sim_thread_init tid
                       (PSThread.mk _ st_ps lc_ps gl_ps) (RMWExecUnit.mk st_arm lc_arm mem_arm)):
      sim_thread_sl_init tid gl_ps mem_arm
        (existT _ lang_ps st_ps, lc_ps) (st_arm, lc_arm)
  .

  Variant sim_init (c: PSConfiguration.t) (m: RMWMachine.t): Prop :=
    | sim_init_intro
        (SIM_THREADS:
          forall tid,
            opt_rel
              (sim_thread_sl_init tid c.(PSConfiguration.global) m.(RMWMachine.mem))
              (IdentMap.find tid c.(PSConfiguration.threads))
              (IdMap.find tid m.(RMWMachine.tpool)))
        (SIM_SC: c.(PSConfiguration.global).(PSGlobal.sc) = TimeMap.bot)
  .

  Definition ps_locations_only (mem: Memory.t): Prop :=
    forall ts msg_arm (GET: Memory.get_msg ts mem = Some msg_arm),
    exists loc_ps, msg_arm.(Msg.loc) = Zpos loc_ps.

  Lemma promise_step_ps_locations_only
        tid (eu1 eu2: RMWExecUnit.t (A:=unit))
        (LOCS: ps_locations_only eu2.(RMWExecUnit.mem))
        (STEP: RMWExecUnit.promise_step tid eu1 eu2):
    ps_locations_only eu1.(RMWExecUnit.mem).
  Proof.
    destruct eu1, eu2.
    inv STEP. inv LOCAL. inv MEM2. ss. subst.
    ii. unfold Memory.get_msg in GET.
    destruct ts; ss.
    exploit (LOCS (S ts)).
    { unfold Memory.get_msg. s.
      eapply nth_error_app_mon; eauto.
    }
    i. des. eauto.
  Qed.

  Lemma machine_promise_step_ps_locations_only
        m1 m2
        (LOCS: ps_locations_only m2.(RMWMachine.mem))
        (STEP: RMWMachine.step RMWExecUnit.promise_step m1 m2):
    ps_locations_only m1.(RMWMachine.mem).
  Proof.
    inv STEP.
    hexploit promise_step_ps_locations_only; try exact STEP0; ss.
  Qed.

  Lemma rtc_machine_promise_step_ps_locations_only
        m1 m2
        (LOCS: ps_locations_only m2.(RMWMachine.mem))
        (STEP: rtc (RMWMachine.step RMWExecUnit.promise_step) m1 m2):
    ps_locations_only m1.(RMWMachine.mem).
  Proof.
    induction STEP; ss.
    eapply machine_promise_step_ps_locations_only; try exact H. auto.
  Qed.

  Lemma init_sim_memory_init tid:
    sim_memory_init tid PSMemory.bot PSMemory.init Memory.empty.
  Proof.
    econs; i.
    - unfold Memory.get_msg in *. destruct ts; ss.
      apply nth_error_some in GET_ARM. ss. nia.
    - exploit PSMemory.init_get; eauto. i. des. subst. inv TO.
  Qed.

  Lemma init_sim_init
        prog_ps
        prog_arm
        (COMPILE: ps_to_rmw_program prog_ps prog_arm):
    sim_init (Configuration.init (IdentMap.map (fun s => existT _ lang_ps s) prog_ps))
             (RMWMachine.init prog_arm).
  Proof.
    econs; ss. i.
    specialize (COMPILE tid).
    unfold Threads.init.
    rewrite IdentMap.Facts.map_o in *.
    rewrite IdentMap.Facts.map_o in *.
    rewrite IdMap.map_spec.
    destruct (IdentMap.find tid prog_ps) eqn:FIND_PS,
        (IdMap.find tid prog_arm) eqn:FIND_ARM; ss.
    econs. econs. econs; ss.
    - econs; ss. ii.
      unfold RegFile.init.
      rewrite IdentFun.init_spec.
      unfold RMap.find, RMap.init.
      rewrite IdMap.gempty. ss.
    - econs; ss; refl.
    - clear. econs; i.
      + destruct ts; ss.
        unfold Memory.get_msg in *. ss.
        apply nth_error_some in GET_ARM. ss. nia.
      + exploit PSMemory.init_get; eauto. i. des. subst. inv TO.
  Qed.

  Lemma reserve_step_future
        lang loc from to (th1 th2: PSThread.t lang)
        (STEP: PSThread.step (ThreadEvent.reserve loc from to) th1 th2):
    (<<STATE: th1.(PSThread.state) = th2.(PSThread.state)>>) /\
    (<<TVIEW: th1.(PSThread.local).(PSLocal.tview) = th2.(PSThread.local).(PSLocal.tview)>>) /\
    (<<PRM: th1.(PSThread.local).(PSLocal.promises) = th2.(PSThread.local).(PSLocal.promises)>>) /\
    (<<RSV: PSMemory.le th1.(PSThread.local).(PSLocal.reserves) th2.(PSThread.local).(PSLocal.reserves)>>) /\
    (<<SC: th1.(PSThread.global).(Global.sc) = th2.(PSThread.global).(Global.sc)>>) /\
    (<<GPRM: th1.(PSThread.global).(Global.promises) = th2.(PSThread.global).(Global.promises)>>) /\
    (<<MEM: PSMemory.le th1.(PSThread.global).(Global.memory) th2.(PSThread.global).(Global.memory)>>).
  Proof.
    inv STEP; inv LOCAL. inv LOCAL0. inv RESERVE. ss.
    splits; ss; eauto using PSMemory.add_le.
  Qed.

  Lemma sim_thread_init_promise_step
        tid th1_ps (eu1 eu2: RMWExecUnit.t (A:=unit))
        (SIM1: sim_thread_init tid th1_ps eu1)
        (LC_WF1_PS: PSLocal.wf (PSThread.local th1_ps) (PSThread.global th1_ps))
        (LOCS: ps_locations_only eu2.(RMWExecUnit.mem))
        (STEP: RMWExecUnit.promise_step tid eu1 eu2):
    exists loc from to th2_ps,
      (<<STEP_PS: PSThread.step (ThreadEvent.reserve loc from to) th1_ps th2_ps>>) /\
      (<<SIM2: sim_thread_init tid th2_ps eu2>>).
  Proof.
    destruct th1_ps as [st1_ps lc1_ps [sc1_ps gprm1_ps mem1_ps]].
    destruct eu1 as [st1_arm lc1_arm mem1_arm].
    destruct eu2 as [st2_arm lc2_arm mem2_arm].
    inv SIM1. ss. inv STEP. ss. subst.
    inv LOCAL. inv MEM2.
    exploit (LOCS (S (length mem1_arm))).
    { unfold Memory.get_msg. ss.
      rewrite List.nth_error_app2; try refl.
      rewrite Nat.sub_diag. ss.
    }
    s. i. des. subst.
    specialize (Memory.get_latest (Zpos loc_ps) mem1_arm). i. des.
    exploit (@PSMemory.add_exists mem1_ps loc_ps (ntt ts) (ntt (S (length mem1_arm))) Message.reserve).
    { i. inv SIM_MEM.
      destruct (TimeFacts.le_lt_dec to2 PSTime.bot).
      { ii. inv LHS. inv RHS. ss.
        cut (PSTime.lt from2 PSTime.bot).
        { i. inv H1. }
        eapply TimeFacts.lt_le_lt; eauto.
      }
      exploit MEM_COMPLETE; eauto. i. des. subst.
      unfold Memory.get_msg in GET_ARM. destruct ts0; ss.
      exploit (H (S ts0)).
      { unfold Memory.read. ss. rewrite GET_ARM.
        rewrite LOC. condtac; ss. congr.
      }
      ii. inv LHS. inv RHS. ss.
      exploit TimeFacts.lt_le_lt; [exact FROM|exact TO0|]. i.
      rewrite incr_ntt_S in *.
      apply ntt_lt in x2. nia.
    }
    { apply lt_ntt.
      exploit Memory.read_get_msg; eauto. i. des.
      { subst. unfold Time.bot. nia. }
      unfold Memory.get_msg in *. destruct ts; ss.
      exploit nth_error_some; eauto. i. nia.
    }
    { econs. }
    i. des.
    exploit PSMemory.add_exists_le; try exact x0; try apply LC_WF1_PS. i. des.

    esplits.
    { econs 1. econs 2. econs; eauto. }
    { inv SIM_MEM. econs; ss.
      { destruct lc1_ps, lc1_arm. ss.
        inv SIM_TVIEW. econs; ss.
      }
      econs; i.
      { exploit Memory.get_msg_snoc_inv; eauto. i. des.
        - exploit MEM_SOUND; eauto. i. des.
          exploit PSMemory.add_get1; try exact GET_PS; eauto. i.
          esplits; eauto.
          + i. exploit RESERVED; eauto. i.
            eapply PSMemory.add_get1; eauto.
          + unguard. des; eauto. right. subst.
            exploit Memory.get_msg_mon; try exact GET_FROM_ARM. i.
            esplits; eauto.
            eapply empty_loc_app; eauto.
        - subst.
          exploit PSMemory.add_get0; try exact x0. i. des.
          exploit PSMemory.add_get0; try exact x1. i. des.
          esplits; ss; eauto.
          + rewrite incr_ntt_S. apply lt_ntt.
            exploit read_ts; try exact H0. i. nia.
          + unguard. destruct ts; auto. right.
            unfold Memory.read in H0. ss. des_ifs.
            destruct t. ss. r in e. subst.
            esplits.
            * rewrite incr_ntt_S. refl.
            * unfold Memory.get_msg. ss.
              eapply nth_error_app_mon; eauto.
            * ii. rewrite List.nth_error_app1 in MSG; try nia.
              exploit (H (S ts0)).
              { unfold Memory.read. s.
                rewrite MSG, LOC. condtac; ss. congr.
              }
              i. nia.
      }
      { revert GET_PS.
        erewrite PSMemory.add_o; eauto. condtac; ss; i.
        - des. inv GET_PS. esplits.
          + rewrite incr_ntt_S. refl.
          + ss.
          + unfold Memory.get_msg. s.
            rewrite List.nth_error_app2; try refl.
            rewrite Nat.sub_diag. ss.
          + ss.
        - guardH o.
          exploit MEM_COMPLETE; eauto. i. des.
          esplits; eauto.
          revert GET_ARM. unfold Memory.get_msg.
          destruct ts0; ss. i.
          eapply nth_error_app_mon; eauto.
      }
    }
  Qed.

  Lemma sim_memory_init_other
        tid rsv_ps mem1_ps mem_arm
        tid' rsv_ps' mem2_ps mem_interference
        (SIM1: sim_memory_init tid rsv_ps mem1_ps mem_arm)
        (SIM_OTHER: sim_memory_init tid' rsv_ps' mem2_ps (mem_arm ++ mem_interference))
        (INTERFERENCE: forall msg (IN: List.In msg mem_interference),
            msg.(Msg.tid) <> tid)
        (LE: PSMemory.le mem1_ps mem2_ps):
    sim_memory_init tid rsv_ps mem2_ps (mem_arm ++ mem_interference).
  Proof.
    inv SIM1. inv SIM_OTHER. econs; eauto; i.
    exploit Memory.get_msg_app_inv; eauto. i. des.
    - exploit MEM_SOUND; eauto. i. des. esplits; eauto.
      unguard. des; auto. right. esplits; eauto.
      + eapply Memory.get_msg_mon; eauto.
      + eapply empty_loc_app; ss. nia.
    - exploit MEM_SOUND0; eauto. i. des.
      esplits; eauto. i.
      apply List.nth_error_In in x1.
      exploit INTERFERENCE; eauto. ss.
  Qed.

  Lemma sim_init_promise_step
        c1 (m1 m2: RMWMachine.t)
        (SIM1: sim_init c1 m1)
        (WF1_PS: PSConfiguration.wf c1)
        (LOCS: ps_locations_only m2.(RMWMachine.mem))
        (STEP: RMWMachine.step RMWExecUnit.promise_step m1 m2):
    exists tid c2,
      (<<STEP_PS: PSConfiguration.step MachineEvent.silent tid c1 c2>>) /\
      (<<SIM2: sim_init c2 m2>>).
  Proof.
    destruct c1 as [ths1 gl1].
    destruct m1 as [tpool1 mem1_arm], m2 as [tpool2 mem2_arm].
    inv SIM1. inv STEP. ss. subst.
    generalize (SIM_THREADS tid).
    rewrite FIND. i. inv H. inv REL.
    inv WF1_PS. inv WF. exploit THREADS; eauto. s. i.
    clear DISJOINT THREADS PROMISES.
    exploit sim_thread_init_promise_step; try exact SIM_THREAD; eauto; ss. i. des.
    destruct th2_ps. esplits.
    - replace MachineEvent.silent with
        (ThreadEvent.get_machine_event (ThreadEvent.reserve loc from to)) by ss.
      econs; eauto. ss. i.
      econs 2; try refl. inv SIM2. ss.
    - exploit reserve_step_future; eauto. s. i. des. subst.
      econs; s; try congr. i.
      rewrite IdentMap.gsspec, IdMap.add_spec.
      do 2 condtac; try congr; subst.
      + inv SIM_THREAD. ss. econs. econs. ss.
      + specialize (SIM_THREADS tid0). inv SIM_THREADS.
        { destruct (IdentMap.find tid0 ths1); ss. }
        destruct (IdentMap.find tid0 ths1) eqn:FIND_PS'; ss. inv H0.
        inv REL. econs. econs.
        inv SIM_THREAD0. ss. econs; ss.
        inv STEP0. inv LOCAL. inv MEM2. ss. subst.
        inv SIM2. ss.
        eapply sim_memory_init_other; eauto.
        ii. inv IN; ss.
  Qed.

  Lemma sim_init_rtc_promise_step
        c1 (m1 m2: RMWMachine.t)
        (SIM1: sim_init c1 m1)
        (WF1_PS: PSConfiguration.wf c1)
        (LOCS: ps_locations_only m2.(RMWMachine.mem))
        (STEPS: rtc (RMWMachine.step RMWExecUnit.promise_step) m1 m2):
    exists c2,
      (<<STEPS_PS: rtc PSConfiguration.tau_step c1 c2>>) /\
      (<<SIM2: sim_init c2 m2>>).
  Proof.
    revert c1 SIM1 WF1_PS.
    induction STEPS; i; eauto.
    hexploit rtc_machine_promise_step_ps_locations_only; try exact STEPS; ss. i.
    exploit sim_init_promise_step; try exact H; eauto. i. des.
    exploit PSConfiguration.step_future; eauto. i. des.
    exploit IHSTEPS; try exact SIM2; eauto. i. des.
    esplits; [|eauto].
    econs; eauto. econs. eauto.
  Qed.
End PStoRMWInit.
