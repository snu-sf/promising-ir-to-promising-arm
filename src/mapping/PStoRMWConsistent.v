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

  Definition sim_val_cons (n: Time.t) (val_ps: Const.t) (val_arm: ValA.t (A:=View.t (A:=unit))): Prop :=
    le val_arm.(ValA.annot).(View.ts) n -> sim_val val_ps val_arm.(ValA.val).

  Definition sim_regs_cons (n: Time.t) (regs_ps: RegFile.t) (regs_arm: RMap.t (A:=View.t (A:=unit))): Prop :=
    forall r, sim_val_cons n (IdentFun.find r regs_ps) (RMap.find r regs_arm).

  Variant sim_state_cons (n: Time.t) (st_ps: State.t) (st_arm: RMWState.t (A:=View.t (A:=unit))): Prop :=
    | sim_state_cons_intro
        (STMTS: RMWState.stmts st_arm = ps_to_rmw_stmts (State.stmts st_ps))
        (REGS: sim_regs_cons n st_ps.(State.regs) st_arm.(RMWState.rmap))
  .
  #[export] Hint Constructors sim_state: core.

  Variant sim_memory_cons (tid: Ident.t) (n: Time.t)
    (lc_ps: PSLocal.t) (gprm_ps: BoolMap.t) (mem_ps: PSMemory.t)
    (lc_arm: Local.t (A:=unit)) (mem_arm: Memory.t): Prop :=
    | sim_memory_intro
        (PRM_SOUND: forall ts (PROMISED_ARM: Promises.lookup ts lc_arm.(Local.promises)),
          exists msg_arm loc_ps from,
            (<<GET_ARM: Memory.get_msg ts mem_arm = Some msg_arm>>) /\
            (<<TID: msg_arm.(Msg.tid) = tid>>) /\
            (<<LOC: msg_arm.(Msg.loc) = Zpos loc_ps>>) /\
            (<<RESERVED: Memory.get loc_ps (ntt ts) (PSLocal.reserves lc_ps) = Some (from, Message.reserve)>>) /\
            (<<PROMISED_PS: le ts n -> lc_ps.(PSLocal.promises) loc_ps = true>>))
        (PRM_COMPLETE: forall loc (PROMISED_PS: lc_ps.(PSLocal.promises) loc = true),
          exists ts msg_arm,
            (<<LE: le ts n>>) /\
            (<<PROMISED_ARM: Promises.lookup ts lc_arm.(Local.promises)>>) /\
            (<<GET_ARM: Memory.get_msg ts mem_arm = Some msg_arm>>) /\
            (<<LOC: msg_arm.(Msg.loc) = Zpos loc>>))
        (MEM_SOUND: forall ts msg_arm
                           (GET_ARM: Memory.get_msg ts mem_arm = Some msg_arm),
          exists loc_ps from msg_ps,
            (<<LOC: msg_arm.(Msg.loc) = Zpos loc_ps>>) /\
            (<<GET_PS: PSMemory.get loc_ps (ntt ts) mem_ps = Some (from, msg_ps)>>) /\
            (<<TS: PSTime.lt from (ntt ts)>>) /\
            (__guard__ (
               (<<FROM: from = PSTime.bot>>) \/
               exists fts fval ftid,
                 (<<FROM: from = ntt fts>>) /\
                 (<<GET_FROM_ARM: Memory.get_msg fts mem_arm = Some (Msg.mk msg_arm.(Msg.loc) fval ftid)>>) /\
                 (<<LATEST: Memory.latest msg_arm.(Msg.loc) fts ts mem_arm>>))) /\
            (__guard__ (
               (<<MSG: msg_ps = Message.reserve>>) /\
               (<<PROMISED_ARM: Promises.lookup ts lc_arm.(Local.promises) <-> msg_arm.(Msg.tid) = tid>>) /\
               (<<PROMISED: le ts n ->
                            (<<GPROMISED: gprm_ps loc_ps = true>>) /\
                            (<<PROMISED_PS: lc_ps.(PSLocal.promises) loc_ps <-> msg_arm.(Msg.tid) = tid>>)>>) \/
               exists val_ps released na,
                 (<<MSG: msg_ps = Message.message val_ps released na>>) /\
                 (<<VAL: le ts n -> sim_val val_ps msg_arm.(Msg.val)>>) /\
                 (<<PROMISED_ARM: Promises.lookup ts lc_arm.(Local.promises) = false>>))))
        (MEM_COMPLETE: forall loc_ps from to msg_ps
                              (TO: PSTime.lt PSTime.bot to)
                              (GET_PS: PSMemory.get loc_ps to mem_ps = Some (from, msg_ps)),
          (exists fts,
              (<<FROM: from = ntt fts>>) /\
              (<<OUT: forall ts msg_arm
                        (LE: le fts ts)
                        (GET_ARM: Memory.get_msg ts mem_arm = Some msg_arm),
                  msg_arm.(Msg.loc) <> Zpos loc_ps>>)) \/
          exists ts msg_arm,
            (<<TO: to = ntt ts>>) /\
            (<<GET_ARM: Memory.get_msg ts mem_arm = Some msg_arm>>) /\
            (<<LOC: msg_arm.(Msg.loc) = Zpos loc_ps>>))
        (FWD: forall loc ts (FWD: (lc_arm.(Local.fwdbank) loc).(FwdItem.ts) = ts),
            exists loc_ps from val released na,
              (<<LOC: loc = Zpos loc_ps>>) /\
              (<<GET_PS: PSMemory.get loc_ps (ntt ts) mem_ps = Some (from, Message.message val released na)>>) /\
              (<<REL_FWD: if (lc_arm.(Local.fwdbank) loc).(FwdItem.ex)
                          then forall loc, PSTime.le
                                        ((PSView.unwrap released).(View.rlx) loc)
                                        (ntt (View.ts (join (join lc_arm.(Local.vrn) lc_arm.(Local.vro))
                                                            (lc_arm.(Local.coh) (Zpos loc)))))
                            (* PSView.opt_le released (Some lc_ps.(PSLocal.tview).(PSTView.acq)) *)
                          else PSView.le (View.unwrap released) (lc_ps.(PSLocal.tview).(PSTView.rel) loc_ps)>>))
        (RELEASED: forall loc from to val released na
                          (GET: PSMemory.get loc to mem_ps = Some (from, Message.message val released na)),
          forall loc', PSTime.le ((View.unwrap released).(View.rlx) loc') to)
  .

  Variant sim_thread_cons (tid: Ident.t) (n: Time.t)
    (th_ps: PSThread.t lang_ps) (eu: RMWExecUnit.t (A:=unit)): Prop :=
    | sim_thread_cons_intro
        (SIM_STATE: sim_state_cons n (PSThread.state th_ps) (RMWExecUnit.state eu))
        (SIM_TVIEW: sim_tview (PSLocal.tview (PSThread.local th_ps)) (RMWExecUnit.local eu))
        (SIM_MEM: sim_memory_cons tid n
                                  (PSThread.local th_ps)
                                  (PSGlobal.promises (PSThread.global th_ps))
                                  (PSGlobal.memory (PSThread.global th_ps))
                                  (RMWExecUnit.local eu) (RMWExecUnit.mem eu))
  .

  Lemma sim_regs_cons_eval_expr
        n regs_ps regs_arm e
        (SIM: sim_regs_cons n regs_ps regs_arm):
    sim_val_cons n (RegFile.eval_expr regs_ps e) (sem_expr regs_arm (ps_to_rmw_expr e)).
  Proof.
    induction e; ss.
    - ii. exploit IHe; eauto. i.
      destruct op. ss. inv x0; ss.
      condtac; econs.
    - ii. ss.
      exploit IHe1; [etrans; eauto; apply join_l|]. i.
      exploit IHe2; [etrans; eauto; apply join_r|]. i.
      destruct op; inv x0; inv x1; ss.
  Qed.

  Lemma sim_regs_cons_add
        n regs_ps regs_arm
        r val_ps (val_arm: ValA.t (A:=View.t (A:=unit)))
        (SIM: sim_regs_cons n regs_ps regs_arm)
        (VAL: sim_val_cons n val_ps val_arm):
    sim_regs_cons n (IdentFun.add r val_ps regs_ps)
                  (RMap.add r val_arm regs_arm).
  Proof.
    ii. rewrite IdentFun.add_spec, RMap.add_o.
    condtac; ss; subst.
    - condtac; try congr.
      revert H. rewrite RMap.add_o. condtac; ss.
    - condtac; ss. apply SIM.
      revert H. rewrite RMap.add_o. condtac; ss.
  Qed.

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
