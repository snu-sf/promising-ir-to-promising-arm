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
