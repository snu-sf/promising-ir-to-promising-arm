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
        (SIM_MEM: sim_memory_init tid
                                  (PSLocal.reserves (PSThread.local th_ps))
                                  (PSGlobal.memory (PSThread.global th_ps))
                                  (RMWExecUnit.mem eu))
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

  Lemma init_sim_memory_init tid:
    sim_memory_init tid PSMemory.bot PSMemory.init Memory.empty.
  Proof.
    econs; i.
    - unfold Memory.get_msg in *. destruct ts; ss.
      apply nth_error_some in GET_ARM. ss. nia.
    - exploit PSMemory.init_get; eauto. i. des. subst. inv TO.
  Qed.

  Lemma empty_loc_app
        loc from to mem1 mem2
        (TO: to <= S (length mem1))
        (EMPTY: empty_loc loc from to mem1):
    empty_loc loc from to (mem1 ++ mem2).
  Proof.
    ii. eapply EMPTY; eauto.
    rewrite List.nth_error_app1 in MSG; ss. nia.
  Qed.

  Lemma read_ts
        loc ts mem val
        (READ: Memory.read loc ts mem = Some val):
    ts <= length mem.
  Proof.
    unfold Memory.read in *.
    destruct ts; ss; try nia. des_ifs.
    exploit nth_error_some; eauto.
  Qed.

  Lemma get_msg_ts
        ts mem msg
        (GET: Memory.get_msg ts mem = Some msg):
    ts <= length mem.
  Proof.
    unfold Memory.get_msg in *.
    destruct ts; ss.
    exploit nth_error_some; eauto.
  Qed.

  Lemma incr_ntt_S ts: PSTime.incr (ntt ts) = ntt (S ts).
  Proof.
    ss.
  Qed.

  Lemma sim_memory_init_promise_step
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
    { inv SIM_MEM. econs. ss. econs; i.
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
End PStoRMWInit.
