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
From sflib Require Import sflib.

Require Import PromisingArch.lib.Basic.
Require Import PromisingArch.lib.Order.
Require Import PromisingArch.lib.Time.
Require Import PromisingArch.lib.Lang.

Set Implicit Arguments.


(* TODO:
1. define TSO
  - copy & paste modules Msg, Memory, View from src/promising/Promising.v
  - define modules TsoLocal, TsoExecUnit, TsoMachine (see https://github.com/kaist-cp/view-hw/blob/master/src/promising/TsoPromising.v)
2. add alloced/freed messages
3. define malloc/free transitions (see: https://github.com/snu-sf/promising-ir/issues/5)
*)

Module TsoMsg.
  Inductive t := mk {
    loc: Loc.t;
    val: Val.t;
    tid: Id.t;
  }.
  #[global]
  Hint Constructors t: core.

  Global Program Instance eqdec: EqDec t eq.
  Next Obligation.
    destruct x, y.

    destruct (loc0 == loc1); cycle 1.
    { right. intro X. inv X. intuition. }

    destruct (val0 == val1); cycle 1.
    { right. intro X. inv X. intuition. }

    destruct (tid0 == tid1); cycle 1.
    { right. intro X. inv X. intuition. }

    left. f_equal; intuition.
  Defined.
End TsoMsg.

Module TsoMemory.
  Definition t := list TsoMsg.t.

  Definition empty: t := [].
  
  Definition read (loc:Loc.t) (ts:Time.t) (mem:t): option Val.t :=
    match Time.pred_opt ts with
      | None => Some Val.default
      | Some ts => 
        match List.nth_error mem ts with
          | None => None
          | Some msg =>
            if msg.(TsoMsg.loc) == loc 
            then Some msg.(TsoMsg.val)
            else None
          end
        end.

  Definition get_msg (ts: Time.t) (mem:t): option TsoMsg.t :=
      match Time.pred_opt ts with 
      | None => None
      | Some ts => List.nth_error mem ts
      end.

  Definition append (msg: TsoMsg.t) (mem:t): Time.t * t :=
    (S (length mem), mem ++ [msg]).
  
  Definition no_msgs (from to:nat) (pred:TsoMsg.t -> Prop) (mem:t): Prop :=
    forall ts msg
    (TS1: from < S ts)
    (TS2: S ts <= to)
    (MSG: List.nth_error mem ts = Some msg),
    ~ pred msg.

  Definition latest (loc:Loc.t) (from to:Time.t) (mem:t): Prop :=
    TsoMeomory.no_msgs from to (fun msg => msg.(TsoMsg.loc) = loc) mem.

  Fixpoint latest_ts (loc:Loc.t) (from to:Time.t) (mem:t): Prop :=
    match to with
    | 0 => 0
    | S to => 
      match List.nth_error mem to with
      | Some (TsoMsg.mk loc0 _ _) =>
        if (Loc.eq_dec loc0 loc) then S to else latest_ts loc to mem
      | _ => latest_ts loc to mem
      end
    end
  .

  Definition exclusive (tid:Id.t) (loc:Loc.t) (from to: Time.t) (mem:t):Prop :=
    TsoMemory.no_msgs from to (fun msg => msg.(TsoMsg.loc) = loc /\ msg.(TsoMsg.tid) <> tid) mem.

  (* Lemmas *)

  Lemma read_mon ts loc val mem1 mem2
        (READ: TsoMemory.read loc ts mem1 = Some val):
    TsoMemory.read loc ts (mem1 ++ mem2) = Some val.
  Proof. Admitted.

  Lemma get_msg_mon ts msg mem1 mem2
        (READ: TsoMemory.get_msg ts mem1 = Some msg):
    TsoMemory.get_msg ts (mem1 ++ mem2) = Some msg.
  Proof. Admitted.

  Lemma get_msg_read ts mem loc val tid
        (GET: get_msg ts mem = Some (TsoMsg.mk loc val tid)):
    read loc ts mem = Some val.
  Proof.
  Admitted.

  Lemma read_get_msg
        loc ts mem val
        (READ: read loc ts mem = Some val):
    (ts = Time.bot /\ val = Val.default) \/
    (exists tid, get_msg ts mem = Some (TsoMsg.mk loc val tid)).
  Proof. Admitted.

  Lemma get_msg_app_inv
        ts mem1 mem2 m
        (GET: get_msg ts (mem1 ++ mem2) = Some m):
    (ts <= length mem1 /\ get_msg ts mem1 = Some m) \/
    (ts > length mem1 /\ List.nth_error mem2 (ts - (S (length mem1))) = Some m).
  Proof. Admitted.

  Lemma get_msg_snoc_inv
        ts mem msg m
        (GET: get_msg ts (mem ++ [msg]) = Some m):
    (ts <= length mem /\ get_msg ts mem = Some m) \/
    (ts = S (length mem) /\ msg = m).
  Proof. Admitted.

  Lemma get_latest
        loc mem:
    exists ts val,
      (forall ts' val (READ: read loc ts' mem = Some val), ts' <= ts) /\
      read loc ts mem = Some val.
  Proof. Admitted.

  Lemma latest_lt
        loc ts1 ts2 ts3 mem msg
        (LATEST: TsoMemory.latest loc ts1 ts2 mem)
        (LT: ts1 < ts3)
        (MSG: TsoMemory.get_msg ts3 mem = Some msg)
        (LOC: msg.(TsoMsg.loc) = loc):
    ts2 < ts3.
  Proof. Admitted.

  Lemma ge_latest loc ts1 ts2 mem
        (GE: ts2 <= ts1):
    TsoMemory.latest loc ts1 ts2 mem.
  Proof. Admitted.

  Lemma latest_mon1
        loc ts1 ts2 ts3 mem
        (LATEST: latest loc ts1 ts3 mem)
        (LT: ts1 <= ts2):
    latest loc ts2 ts3 mem.
  Proof. Admitted.

  Lemma latest_mon2
        loc ts1 ts2 ts3 mem
        (LATEST: latest loc ts1 ts3 mem)
        (LT: ts2 <= ts3):
    latest loc ts1 ts2 mem.
  Proof. Admitted.

  Lemma latest_join
        loc ts ts1 ts2 mem
        (LATEST1: latest loc ts ts1 mem)
        (LATEST2: latest loc ts ts2 mem):
    latest loc ts (join ts1 ts2) mem.
  Proof. Admitted.

  Lemma latest_ts_spec
        loc to mem:
    <<LE: latest_ts loc to mem <= to>> /\
    <<READ: exists val, read loc (latest_ts loc to mem) mem = Some val>>.
  Proof. Admitted.

  Lemma latest_ts_mon
        loc to1 to2 mem
        (LE: to1 <= to2):
    latest_ts loc to1 mem <= latest_ts loc to2 mem.
  Proof. Admitted.

  Lemma latest_ts_append
        loc to mem1 mem2:
    latest_ts loc to mem1 <= latest_ts loc to (mem1 ++ mem2).
  Proof. Admitted.

  Lemma latest_ts_latest
        loc from to mem
        (LATEST: latest_ts loc to mem = from):
    latest loc from to mem.
  Proof. Admitted.

  Lemma latest_latest_ts
        loc from to mem
        (LATEST: latest loc from to mem):
    latest_ts loc to mem <= from.
  Proof. Admitted.

  Lemma latest_ts_read_lt
        loc from to mem v val
        (LATEST: latest_ts loc to mem = from)
        (READ: read loc v mem = Some val)
        (LT: from < v):
    to < v.
  Proof. Admitted.

  Lemma latest_ts_read_le
        loc to mem v val
        (READ: read loc v mem = Some val)
        (LE: v <= to):
    v <= latest_ts loc to mem.
  Proof. Admitted.

  Lemma no_msgs_split
        a b c pred mem
        (AB: a <= b)
        (BC: b <= c):
    no_msgs a c pred mem <->
    no_msgs a b pred mem /\ no_msgs b c pred mem.
  Proof. Admitted.

  Lemma no_msgs_split'
        a b c pred mem:
    no_msgs a b pred mem /\ no_msgs b c pred mem ->
    no_msgs a c pred mem.
  Proof. Admitted.

  Lemma no_msgs_full
        pred from to mem1 mem2
        (TO: to <= length mem1)
        (NOMSGS: no_msgs from to pred mem1):
    no_msgs from to pred (mem1 ++ mem2).
  Proof. Admitted.

  Lemma no_msgs_weaken
        a b c pred mem1 mem2
        (BC: b <= c)
        (NOMSGS: no_msgs a c pred (mem1 ++ mem2)):
    no_msgs a b pred mem1.
  Proof. Admitted.

  Lemma ge_no_msgs
        ts1 ts2 pred mem
        (GE: ts2 <= ts1):
    no_msgs ts1 ts2 pred mem.
  Proof. Admitted.

  Lemma latest_uniq
        ts1 ts2 ts loc mem val1 val2
        (TS1: ts1 <= ts)
        (TS2: ts2 <= ts)
        (LATEST1: latest loc ts1 ts mem)
        (LATEST2: latest loc ts2 ts mem)
        (MSG1: read loc ts1 mem = Some val1)
        (MSG2: read loc ts2 mem = Some val2):
    ts1 = ts2.
  Proof. Admitted.

End TsoMemory.

Module TsoView.
Section TsoView.
  Context `{A: Type, _: orderC A eq}.

  Inductive t := mk {
    ts: Time.t;
    annot: A;
  }.
  #[local]
  Hint Constructors t: core.

  Inductive _le (a b:t): Prop :=
  | _le_intro
    (TS: le a.(ts) b.(ts))
    (ANNOT: le a.(annot) b.(annot))
  .

  Definition _join (a b:t): t :=
    mk (join a.(ts) b.(ts)) (join a.(annot) b.(annot)).

  Definition _bot: t := mk bot bot.

  Global Program Instance preorder: PreOrder _le.
  Next Obligation. ii. econs; refl. Qed.
  Next Obligation. ii. inv H1. inv H2. econs; etrans; eauto. Qed.

  Global Program Instance partialorder: PartialOrder eq _le.
  Next Obligation.
    ii. econs.
    - i. subst. econs; refl.
    - i. destruct x, x0. inv H1. inv H2. inv H3. ss. f_equal.
      + intuition.
      + antisym; ss.
  Qed.

  Global Program Instance order:
    @orderC
      t
      eq
      _le
      _join
      _bot
      _ _ _.
  Next Obligation.
    unfold _join. destruct a, b; ss. econs; s; apply join_l.
  Qed.
  Next Obligation.
    unfold _join. destruct a, b; ss. econs; s; apply join_r.
  Qed.
  Next Obligation.
    unfold _join. destruct a, b; ss. econs; s; apply join_assoc.
  Qed.
  Next Obligation.
    unfold _join. destruct a, b; ss. econs; s; apply join_comm.
  Qed.
  Next Obligation.
    inv AC. inv BC. econs; s; apply join_spec; ss.
  Qed.
  Next Obligation.
    econs; apply bot_spec.
  Qed.

  Lemma ts_join a b:
    (join a b).(TsoView.ts) = join (a.(TsoView,ts)) (b.(TsoView.ts)).
  Proof. Admitted.

  Lemma ts_ifc a b:
    (ifc a b).(TsoView.ts) = ifc a b.(TsoView.ts).
  Proof. Admitted.

  Lemma ts_bot:
    bot.(TsoView.ts) = bot.
  Proof. Admitted.

  Lemma eq_time_eq
        (v1 v2:t)
        (EQ: v1 = v2):
    v1.(ts) = v2.(ts).
  Proof. Admitted.

End TsoView.
End TsoView.

Module TsoLocal.
Section TsoLocal.
  Inductive t := mk {
    coh: Loc.t -> TsoView.t (A:=unit);
    vrn: TsoView.t (A:=unit);
  }.
  Hint Constructors t.

  Definition read_view (coh:TsoView.t (A:=unit)) (tsx:Time.t): TsoView.t (A:=unit) :=
    if coh.(TsoView.ts) == tsx
    then TsoView.mk bot bot
    else TsoView.mk tsx bot.

  Definition init: t:= mk bot bot.

  Inductive read (vloc res:ValA.t (A:=unit)) (ts:Time.t) (lc1:t) (mem1: TsoMemory.t) (lc2:t): Prop :=
  | read_intro
      loc val
      view_pre view_post
      (LOC: loc = vloc.(ValA.val))
      (VIEW_PRE: view_pre = lc1.(vrn))
      (COH: le (lc1.(coh) loc).(TsoView.ts) ts)
      (LATEST: TsoMemory.latest loc ts view_pre.(TsoView.ts) mem1)
      (MSG: TsoMemory.read loc ts mem1 = Some val)
      (VIEW_POST: view_post = read_view (lc1.(coh) loc) ts)
      (RES: res = ValA.mk _ val bot)
      (LC2: lc2 = 
            mk
              (fun_add loc (TsoView.mk ts bot) lc1.(coh))
              (join lc1.(vrn) view_post))
  .
  Hint Constructors read.

  Inductive writable (vloc vval:ValA.t (A:=unit)) (tid:Id.t) (lc1:t) (mem1: TsoMemory.t): Prop :=
    | writable_intro
        loc cohmax
        (LOC: loc = vloc.(ValA.val))
        (COHMAX: fun_max lc1.(coh) cohmax)
        (EXT: lt cohmax.(TsoView.ts) ts)
  .
  Hint Constructors writable.

  Inductive rmw (vloc vold vnew: ValA.t (A:=unit)) (old_ts:Time.t) (ts:Time.t) (tid:Id.t) (lc1:t) (mem1:TsoMemory.t) (lc2:t): Prop:=
  | rmw_intro
      loc old new view_post
      (LOC: loc = vloc.(ValA.val))
      (COH: le (lc1.(coh) loc).(TsoView.ts) old_ts)
      (OLD_RANGE: lt old_ts ts)
      (EX: TsoMemory.exclusive tid loc old_ts ts mem1)
      (OLD_MSG: TsoMemory.read loc old_ts mem1 = Some old)
      (OLD: old = vold.(ValA.val))
      (NEW: new = vnew.(ValA.val))
      (WRITABLE: writable vloc vnew tid lc1 mem1 ts)
      (MSG: TsoMemory.get_msg ts mem1 = Some (TsoMsg.mk loc new tid))
      (VIEW_POST: view_post = TsoView.mk ts bot)
      (LC2: lc2 = 
            mk
              (fun_add loc (TsoView.mk ts bot) lc1.(coh))
              (join lc1.(vrn) view_post))
  
  .
  Hint Constructors rmw.
  
  Inductive rmw_failure (vloc vold res:ValA.t (A:=unit)) (old_ts:Time.t) (lc1:t) (mem1:TsoMemory.t) (lc2:t): Prop :=
  | rmw_failure_intro
      loc old
      view_pre view_post
      (LOC: loc = vloc.(ValA.val))
      (VIEW_PRE: view_pre = lc1.(vrn))
      (COH: le (lc1.(coh) loc).(TsoView.ts) old_ts)
      (LATEST: TsoMemory.latest loc old_ts view_pre.(TsoView.ts) mem1)
      (OLD_MSG: TsoMemory.read loc old_ts mem1 = Some old)
      (OLD: old = vold.(ValA.val))
      (VIEW_POST: view_post = read_view (lc1.(coh) loc) old_ts)
      (RES: res = ValA.mk _ old bot)
      (LC2: lc2 = 
            mk
              (fun_add loc (TsoView.mk old_ts bot) lc1.(coh))
              (join lc1.(vrn) view_post))
  
  .
  Hint Constructors rmw_failure.

  Inductive mfence (lc1 lc2:t): Prop :=
  | mfence_intro
      cohmax
      (COHMAX: fun_max lc1.(coh) cohmax)
      (LC2: lc2 = 
            mk
              lc1.(coh)
              (join lc1.(vrn) cohmax))
  .
  Hint Constructors mfence.

  Inductive write (vloc vval res: ValA.t (A:=unit)) (ts:Time.t) (tid:Id.t) (lc1:t) (mem1: TsoMemory.t) (lc2:t) (mem2:TsoMemory.t): Prop :=
  | write_intro
      loc val
      (LOC: loc = vloc.(ValA.val))
      (VAL: val = vval.(ValA.val))
      (RES: res = ValA.mk _ 0 bot)
      (MEM: TsoMemory.append (TsoMsg.mk loc val tid) mem1 = (ts, mem2))
      (LC2: lc2 =
            mk
              (fun_add loc (TsoView.mk ts bot) lc1.(coh))
              lc1.(vrn))
  .
  Hint Constructors write.

  Inductive step (event:Event.t (A:=unit)) (tid:Id.t) (mem:TsoMemory.t) (lc1 lc2:t): Prop :=
  | step_internal
      (EVENT: event = Event.internal)
      (LC: lc2 = lc1)
  | step_read
      vloc res ts ord
      (EVENT: event = Event.read false false ord vloc res)
      (STEP: read vloc res ts lc1 mem lc2)
  | step_rmw
      vloc vold vnew old_ts ts ordr ordw
      (EVENT: event = Event.rmw ordr ordw vloc vold vnew)
      (STEP: rmw vloc vold vnew old_ts ts tid lc1 mem lc2)
  | step_rmw_failure
      vloc vold old_ts ord res
      (EVENT: event = Event.read false true ord vloc res)
      (STEP: rmw_failure vloc vold res old_ts lc1 mem lc2)
  | step_mfence
      b
      (EVENT: event = Event.barrier b)
      (BARRIER: Barrier.is_mfence b)
      (STEP: mfence lc1 lc2)
  | step_sfence
      b
      (EVENT: event = Event.barrier b)
      (BARRIER: Barrier.is_sfence b)
      (STEP: sfence lc1 lc2)
  | step_flush
      vloc
      (EVENT: event = Event.flush vloc)
      (STEP: flush vloc lc1 lc2)ß
  .
  Hint Constructors step.

  Inductive view_step (event:Event.t (A:=unit)) (tid:Id.t) (mem1 mem2:TsoMemory.t) (lc1 lc2: t): Prop :=
  | view_step_internal
      (EVENT: event = Event.internal)
      (LC: lc2 = lc1)
      (MEM: mem2 = mem1)
  | view_step_read
      vloc res ts ord
      (EVENT: event = Event.read false false ord vloc res)
      (STEP: read vloc res ts lc1 mem1 lc2)
  | view_step_write
      vloc vval res ts ord
      (EVENT: event = Event.write false ord vloc vval res)
      (STEP: vrmw vloc vold vnew old_ts ts tid lc1 mem1 lc2 mem2)
  | view_step_rmw
        vloc vold vnew old_ts ts ordr ordw
        (EVENT: event = Event.rmw ordr ordw vloc vold vnew)
        (STEP: vrmw vloc vold vnew old_ts ts tid lc1 mem1 lc2 mem2)
  | view_step_rmw_failure
        vloc vold old_ts ord res
        (EVENT: event = Event.read false true ord vloc res)
        (STEP: rmw_failure vloc vold res old_ts lc1 mem1 lc2)
        (MEM: mem2 = mem1)
  | view_step_mfence
        b
        (EVENT: event = Event.barrier b)
        (BARRIER: Barrier.is_mfence b)
        (STEP: mfence lc1 lc2)
        (MEM: mem2 = mem1)
  | view_step_sfence
        b
        (EVENT: event = Event.barrier b)
        (BARRIER: Barrier.is_sfence b)
        (STEP: sfence lc1 lc2)
        (MEM: mem2 = mem1)
  | view_step_flush
        vloc
        (EVENT: event = Event.flush vloc)
        (STEP: flush vloc lc1 lc2)
        (MEM: mem2 = mem1)
  .
  Hint Constructors view_step.

  Inductive wf_fwdbank (loc:Loc.t) (mem:TsoMemory.t) (coh: Time.t): Prop :=
  | wf_fwdbank_intro
      (VAL: exists val, TsoMemory.read loc coh mem = Some val)
  .
  Hint Constructors wf_fwdbank.

  Inductive wf_cohmax (lc:t): Prop :=
  | wf_cohmax_intro
      cohmax
      (COHMAX: fun_max lc.(coh) cohmax)
      (VRN: lc.(vrn).(TsoView.ts) <= cohmax.(TsoView.ts))
  .
  Hint Constructors wf_cohmax.

  Inductive wf (tid:Id.t) (mem:TsoMemory.t) (lc:t): Prop :=
  | wf_intro
      (COH: forall loc, (lc.(coh) loc).(TsoView.ts) <= List.length mem)
      (VRN: lc.(vrn).(TsoView.ts) <= List.length mem)
      (FWDBANK: forall loc, wf_fwd_bank loc mem (lc.(coh) loc).(TsoView.ts))
      (COHMAX: wf_cohmax lc)
      (NFWD: forall ts msg
                (MSG: TsoMemory.get_msg ts mem = Some msg)
                (TID: msg.(TsoMsg.tid) <> tid),
            ts <= lc.(vrn).(TsoView.ts))
      (NINTERVENING: forall loc from to
                (LATEST: TsoMemory.latest loc from to mem),
            (lc.(coh) loc).(TsoView.ts) <= from \/ to < (lc.(coh) loc).(TsoView.ts))
  .
  Hint Constructors wf.

  (* Lemmas *)



End TsoLocal.
End TsoLocal.

Module TsoExecUnit.
Section TsoExecUnit.
  Inductive t := mk {
    state: State.t (A:=unit);
    local: TsoLocal.t;
    mem: TsoMemory.t;
  }.
  Hint Constructors t.

  Inductive state_step0 (tid:Id.t) (e1 e2: Event.t (A:=unit)) (eu1 eu2:t): Prop :=
  | state_step0_intro
      (STATE: State.step e1 eu1.(state) eu2.(state))
      (LOCAL: TsoLocal.step e2 tid eu1.(mem) eu1.(local) eu2.(local))
      (MEM: eu2.(mem) = eu1.(mem))
  .
  Hint Constructors state_step0.

  Inductive state_step (tid:Id.t) (eu1 eu2:t): Prop :=
  | state_step_intro
      e
      (STEP: state_step0 tid e e eu1 eu2)
  .
  Hint Constructors state_step.

  Inductive step (tid:Id.t) (eu1 eu2:t): Prop :=
  | step_state (STEP: state_step tid eu1 eu2)
  .
  Hint Constructors step.

  Inductive view_step0 (tid:Id.t) (e1 e2: Event.t (A:=unit)) (eu1 eu2:t) : Prop :=
  | view_step0_intro
      (STATE: State.step e1 eu1.(state) eu2.(state))
      (LOCAL: TsoLocal.view_step e2 tid eu1.(mem) eu2.(mem) eu1.(local) eu2.(local))
  .
  Hint Constructors view_step0.

  Inductive view_step (tid:Id.t) (eu1 eu2:t): Prop :=
  | view_step_intro
      e
      (STEP: view_step0 tid e e eu1 eu2)
  .
  Hint Constructors view_step.

  Inductive wf (tid:Id.t) (eu:t): Prop :=
  | wf_intro
      (LOCAL: TsoLocal.wf tid eu.(mem) eu.(local))
  .
  Hint Constructors wf.

  Inductive le (eu1 eu2:t) : Prop :=
  | le_intro
      mem'
      (LC: TsoLocal.le eu1.(local) eu2.(local))
      (MEM: eu2.(mem) = eu1.(mem) ++ mem')
  .

  Global Program Instance le_partial_order: PreOrder le.
  Next Obligation. 
      econs.
      - refl.
      - rewrite app_nil_r. ss.
  Qed.
  Next Obligation.
      ii. inv H. inv H0. econs; etrans; eauto.
      rewrite MEM, app_assoc. eauto.
  Qed.

  (* Lemmas *)
  Lemma state_step0_wf tid e eu1 eu2
        (STEP: state_step0 tid e e eu1 eu2)
        (WF: wf tid eu1):
      wf tid eu2.
  Proof. Admitted.

  Lemma state_step_wf tid eu1 eu2
        (STEP: state_step tid eu1 eu2)
        (WF: wf tid eu1):
      wf tid eu2.
  Proof. Admitted.

  Lemma rtc_state_step_wf tid eu1 eu2
        (STEP: rtc (state_step tid) eu1 eu2)
        (WF: wf tid eu1):
      wf tid eu2.
  Proof. Admitted.

  Lemma step_wf tid eu1 eu2
        (STEP: step tid eu1 eu2)
        (WF: wf tid eu1):
    wf tid eu2.
  Proof. Admitted.

  Lemma view_step0_wf tid e eu1 eu2
        (STEP: view_step0 tid e e eu1 eu2)
        (WF: wf tid eu1):
    wf tid eu2.
  Proof. Admitted.

  Lemma view_step_wf tid eu1 eu2
        (STEP: view_step tid eu1 eu2)
        (WF: wf tid eu1):
    wf tid eu2.
  Proof. Admitted.

  Lemma rtc_view_step_wf tid eu1 eu2
        (STEP: rtc (view_step tid) eu1 eu2)
        (WF: wf tid eu1):
    wf tid eu2.
  Proof. Admitted.

  Lemma state_step_incr tid eu1 eu2
        (STEP: state_step tid eu1 eu2):
    le eu1 eu2.
  Proof. Admitted.

  Lemma rtc_state_step_incr tid eu1 eu2
        (STEP: rtc (state_step tid) eu1 eu2):
    le eu1 eu2.
  Proof. Admitted.

  Lemma step_incr tid eu1 eu2
        (STEP: step tid eu1 eu2):
    le eu1 eu2.
  Proof. Admitted.

  Lemma rtc_state_step_mem
        tid eu1 eu2
        (STEP: rtc (TsoExecUnit.state_step tid) eu1 eu2):
      eu1.(TsoExecUnit.mem) = eu2.(TsoExecUnit.mem).
  Proof. Admitted.

  Lemma no_promise_rmw_spec.
  Proof. Admitted.

End TsoExecUnit.
End TsoExecUnit.

Module TsoMachine.
  Inductive t := mk {
    tpool: IdMap.t (State.t (A:=unit) * TsoLocal.t);
    mem: TsoMemory.t;
  }.
  Hint Constructors t.

  Definition init (p:program): t := 
      mk
        (IndMap.map (fun stmts => (State.init stmts, TsoLocal.init)) p)
        TsoMemory.empty.

  Inductive is_terminal (m:t) : Prop :=
  | is_terminal_intro
      (TERMINAL:
          forall tid st lc
            (FIND: IdMap.find tid m.(tpool) = Some (st, lc)),
            State.is_terminal st)
  .
  Hint Constructors is_terminal.

  Inductive step (eustep: forall (tid:Id.t) (eu1 eu2: TsoExecUnit.t), Prop) (m1 m2:t): Prop :=
  | step_intro
      tid st1 lc1 st2 lc2
      (FIND: IdMap.find tid m1.(tpool) = Some (st1, lc1))
      (STEP: eustep tid (TsoExecUnit.mk st1 lc1 m1.(mem)) (TsoExecUnit.mk st2 lc2 m2.(mem)))
      (TPOOL: m2.(tpool) = IdMap.add tid (st2, lc2) m1.(tpool))
  .
  Hint Constructors step.

  Inductive wf (m:t) : Prop :=
  | wf_intro
      (WF: forall tid st lc
            (FIND: IdMap.find tid m.(tpool) = Some (st, lc)),
        TsoExecUnit.wf tid (TsoExecUnit.mk st lc m.(mem)))
  .
  Hint Constructors wf.

  Inductive exec (p:program) (m:t): Prop :=
  | exec_intro
      (STEP: rtc (step TsoExecUnit.step) (init p) m)
  .
  Hint Constructors exec.

  Inductive view_exec (p:program) (m:t): Prop :=
  | view_exec_intro
      (STEP: rtc (step TsoExecUnit.view_step) (init p) m)
  .
  Hint Constructors view_exec.

  Inductive equiv (m1 m2:t) : Prop :=
  | equiv_intro
      (TPOOL: IdMap.Equal m1.(tpool) m2.(tpool))
      (MEM:  m1.(mem) = m2.(mem))
  .



  (* Lemmas *)

  Lemma rtc_eu_step_step
        eustep tid m st1 lc1 mem1 st2 lc2 mem2
        (FIND: IdMap.find tid m.(tpool) = Some (st1, lc1))
        (MEM: m.(mem) = mem1)
        (EX: rtc (eustep tid)
                 (TsoExecUnit.mk st1 lc1 mem1)
                 (TsoExecUnit.mk st2 lc2 mem2)):
    rtc (step eustep)
      m
      (mk
        (IdMap.add tid (st2, lc2) m.(tpool))
        mem2).
  Proof. Admitted.

  Lemma init_wf p:
    wf (init p).
  Proof. Admitted.

  Lemma step_state_step_wf
        m1 m2
        (STEP: step TsoExecUnit.state_step m1 m2)
        (WF: wf m1):
    wf m2.
  Proof. Admitted.

  Lemma rtc_step_state_step_wf
        m1 m2
        (STEP: rtc (step TsoExecUnit.state_step) m1 m2)
        (WF: wf m1):
    wf m2.
  Proof. Admitted.

  Lemma step_step_wf
        m1 m2
        (STEP: step TsoExecUnit.step m1 m2)
        (WF: wf m1):
    wf m2.
  Proof. Admitted.

  Lemma rtc_step_step_wf
        m1 m2
        (STEP: rtc (step TsoExecUnit.step) m1 m2)
        (WF: wf m1):
    wf m2.
  Proof. Admitted.

  Lemma step_view_step_wf
        m1 m2
        (STEP: step TsoExecUnit.view_step m1 m2)
        (WF: wf m1):
    wf m2.
  Proof. Admitted.

  Lemma rtc_step_view_step_wf
        m1 m2
        (STEP: rtc (step TsoExecUnit.view_step) m1 m2)
        (WF: wf m1):
    wf m2.
  Proof. Admitted.

  Lemma step_mon
        (eustep1 eustep2: _ -> _ -> _ -> Prop)
        (EUSTEP: forall tid m1 m2, eustep1 tid m1 m2 -> eustep2 tid m1 m2):
    forall m1 m2, step eustep1 m1 m2 -> step eustep2 m1 m2.
  Proof. Admitted.

  Lemma rtc_step_mon
        (eustep1 eustep2: _ -> _ -> _ -> Prop)
        (EUSTEP: forall tid m1 m2, eustep1 tid m1 m2 -> eustep2 tid m1 m2):
    forall m1 m2, rtc (step eustep1) m1 m2 -> rtc (step eustep2) m1 m2.
  Proof. Admitted.

  Lemma state_exec_wf
        m1 m2
        (STEP: state_exec m1 m2)
        (WF: wf m1):
    wf m2.
  Proof. Admitted.

  Lemma unlift_step_state_step
        m1 m2 tid st1 lc1
        (STEPS: rtc (step TsoExecUnit.state_step) m1 m2)
        (TPOOL: IdMap.find tid m1.(tpool) = Some (st1, lc1)):
    exists st2 lc2,
      <<TPOOL: IdMap.find tid m2.(tpool) = Some (st2, lc2) /\
      <<STEPS: rtc (TsoExecUnit.state_step tid)
                   (TsoExecUnit.mk st1 lc1 m1.(mem))
                   (TsoExecUnit.mk st2 lc2 m2.(mem))>>.
  Proof. Admitted.

  Lemma step_get_msg_tpool
        p m ts msg
        (STEPS: rtc (step TsoExecUnit.step) (init p) m)
        (MSG: TsoMemory.get_msg ts m.(mem) = Some msg):
    exists sl, IdMap.find msg(TsoMsg.tid) m.(tpool) = Some sl.
  Proof. Admitted.
End TsoMachine.