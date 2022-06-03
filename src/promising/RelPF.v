Require Import FunctionalExtensionality.
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
From Paco Require Import paco.

Require Import PromisingArch.lib.Basic.
Require Import PromisingArch.lib.Order.
Require Import PromisingArch.lib.Time.
Require Import PromisingArch.lib.Lang.

Require Import PromisingArch.promising.Promising.
Require Import PromisingArch.promising.Sim.

Set Implicit Arguments.
Set Nested Proofs Allowed.


Module RelPFLocal.
  Section RelPFLocal.
    Import Local.
    Context `{A: Type, _: orderC A eq}.

    Variant step (event:Event.t (A:=View.t (A:=A))) (tid:Id.t)
              (lc1:t) (mem1:Memory.t) (lc2:t) (mem2:Memory.t): Prop :=
    | step_internal
        (EVENT: event = Event.internal)
        (LC: lc2 = lc1)
        (MEM: mem2 = mem1)
    | step_read
        ex ord vloc res ts
        (EVENT: event = Event.read ex ord vloc res)
        (STEP: read ex ord vloc res ts lc1 mem1 lc2)
        (MEM: mem2 = mem1)
    | step_fulfill
        ex ord vloc vval res ts view_pre
        (ORD: OrdW.ge ord OrdW.release_pc)
        (EVENT: event = Event.write ex ord vloc vval res)
        (STEP: fulfill ex ord vloc vval res ts tid view_pre lc1 mem1 lc2)
        (MEM: mem2 = mem1)
    | step_write
        lc1'
        ex ord vloc vval res ts view_pre
        (EVENT: event = Event.write ex ord vloc vval res)
        (PROMISE: promise vloc.(ValA.val) vval.(ValA.val) ts tid lc1 mem1 lc1' mem2)
        (STEP: fulfill ex ord vloc vval res ts tid view_pre lc1' mem2 lc2)
    | step_write_failure
        ex ord vloc vval res
        (EVENT: event = Event.write ex ord vloc vval res)
        (STEP: write_failure ex res lc1 lc2)
        (MEM: mem2 = mem1)
    | step_fadd_fulfill
        ordr ordw vloc vold vnew ts_old ts_new res lc1' view_pre
        (ORD: OrdW.ge ordw OrdW.release_pc)
        (EVENT: event = Event.fadd ordr ordw vloc vold vnew)
        (STEP_READ: read true ordr vloc vold ts_old lc1 mem1 lc1')
        (STEP_FULFILL: fulfill true ordw vloc vnew res ts_new tid view_pre lc1' mem1 lc2)
        (MEM: mem2 = mem1)
    | step_fadd_write
        ordr ordw vloc vold vnew ts_old ts_new res lc1' lc1'' view_pre
        (EVENT: event = Event.fadd ordr ordw vloc vold vnew)
        (STEP_READ: read true ordr vloc vold ts_old lc1 mem1 lc1')
        (PROMISE: promise vloc.(ValA.val) vnew.(ValA.val) ts_new tid lc1' mem1 lc1'' mem2)
        (STEP_FULFILL: fulfill true ordw vloc vnew res ts_new tid view_pre lc1'' mem2 lc2)
        (MEM: mem2 = mem1)
    | step_isb
        (EVENT: event = Event.barrier Barrier.isb)
        (STEP: isb lc1 lc2)
        (MEM: mem2 = mem1)
    | step_dmb
        rr rw wr ww
        (EVENT: event = Event.barrier (Barrier.dmb rr rw wr ww))
        (STEP: dmb rr rw wr ww lc1 lc2)
        (MEM: mem2 = mem1)
    | step_control
        ctrl
        (EVENT: event = Event.control ctrl)
        (LC: control ctrl lc1 lc2)
        (MEM: mem2 = mem1)
    .
    #[local]
     Hint Constructors step: core.
  End RelPFLocal.
End RelPFLocal.


Module RelPFExecUnit.
  Section RelPFExecUnit.
    Import ExecUnit.
    Context `{A: Type, _: orderC A eq}.

    Variant state_step0 (tid:Id.t) (e1 e2:Event.t (A:=View.t (A:=A))) (eu1 eu2:t): Prop :=
    | state_step0_intro
        (STATE: State.step e1 eu1.(state) eu2.(state))
        (LOCAL: RelPFLocal.step e2 tid eu1.(local) eu1.(mem) eu2.(local)  eu2.(mem))
    .
    #[local]
     Hint Constructors state_step0: core.

    Variant state_step (tid:Id.t) (eu1 eu2:t): Prop :=
    | state_step_intro
        e
        (STEP: state_step0 tid e e eu1 eu2)
    .
    #[local]
     Hint Constructors state_step: core.

    Variant step (tid:Id.t) (eu1 eu2:t): Prop :=
    | step_state (STEP: state_step tid eu1 eu2)
    | step_promise (STEP: promise_step tid eu1 eu2)
    .
    #[local]
     Hint Constructors step: core.
  End RelPFExecUnit.
End RelPFExecUnit.


Module RelPFMachine.
  Import Machine.

  Variant exec (p:program) (m:t): Prop :=
  | exec_intro
      (STEP: rtc (step RelPFExecUnit.step) (init p) m)
      (NOPROMISE: no_promise m)
  .
  #[global]
   Hint Constructors exec: core.
End RelPFMachine.
