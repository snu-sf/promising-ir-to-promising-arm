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

Require Import PromisingArch.mapping.RMWLang.
Require Import PromisingArch.mapping.RMWPromising.

Set Implicit Arguments.


Section SIM_EU.
  Variable tid: Id.t.

  Definition SIM_EU: Type := RMWExecUnit.t (A:=unit) -> ExecUnit.t (A:=unit) -> Prop.

  Definition _sim_eu (sim_eu: SIM_EU)
             (eu1_src: RMWExecUnit.t (A:=unit)) (eu1_tgt: ExecUnit.t (A:=unit)): Prop :=
    (<<TERMINAL:
      forall (TERMINAL_TGT: ExecUnit.is_terminal eu1_tgt),
      exists eu2_src,
        (<<STEPS_SRC: rtc (RMWExecUnit.state_step None tid) eu1_src eu2_src>>) /\
        (<<TERMINAL_SRC: RMWExecUnit.is_terminal eu2_src>>) /\
        (<<MEMORY2: RMWExecUnit.mem eu2_src = ExecUnit.mem eu1_tgt>>)>>) /\
    (<<STEP:
      forall eu2_tgt
        (STEP_TGT: ExecUnit.state_step tid eu1_tgt eu2_tgt),
      exists eu2_src,
        (<<STEP_SRC: rtc (RMWExecUnit.state_step None tid) eu1_src eu2_src>>) /\
        (<<SIM: sim_eu eu2_src eu2_tgt>>)>>)
  .
  #[local] Hint Unfold _sim_eu: paco.

  Lemma sim_eu_monotone: monotone2 _sim_eu.
  Proof.
    ii. red in IN. des.
    red. esplits; eauto. i.
    exploit STEP; eauto. i. des.
    esplits; eauto.
  Qed.
  #[local] Hint Resolve sim_eu_monotone: paco.

  Definition sim_eu := paco2 _sim_eu bot2.
End SIM_EU.
Arguments sim_eu [_] _ _.
#[export] Hint Resolve sim_eu_monotone: paco.


Lemma sim_eu_state_step
      tid eu1_src eu1_tgt eu2_tgt
      (SIM: @sim_eu tid eu1_src eu1_tgt)
      (STEP_TGT: ExecUnit.state_step tid eu1_tgt eu2_tgt):
  exists eu2_src,
    (<<STEP_SRC: rtc (RMWExecUnit.state_step None tid) eu1_src eu2_src>>) /\
    (<<SIM: @sim_eu tid eu2_src eu2_tgt>>).
Proof.
  punfold SIM. r in SIM. des.
  exploit STEP; eauto. i. des.
  esplits; eauto.
  inv SIM; ss.
Qed.

Lemma sim_eu_rtc_state_step
      tid eu1_src eu1_tgt eu2_tgt
      (SIM: @sim_eu tid eu1_src eu1_tgt)
      (STEPS_TGT: rtc (ExecUnit.state_step tid) eu1_tgt eu2_tgt):
  exists eu2_src,
    (<<STEP_SRC: rtc (RMWExecUnit.state_step None tid) eu1_src eu2_src>>) /\
    (<<SIM: @sim_eu tid eu2_src eu2_tgt>>).
Proof.
  revert eu1_src SIM.
  induction STEPS_TGT; i; eauto.
  exploit sim_eu_state_step; try exact H; eauto. i. des.
  exploit IHSTEPS_TGT; eauto. i. des.
  esplits; [|eauto]. etrans; eauto.
Qed.

Lemma sim_eu_terminal
      tid eu1_src eu1_tgt
      (SIM: @sim_eu tid eu1_src eu1_tgt)
      (TERMINAL_TGT: ExecUnit.is_terminal eu1_tgt):
  exists eu2_src,
    (<<STEP_SRC: rtc (RMWExecUnit.state_step None tid) eu1_src eu2_src>>) /\
    (<<TERMINAL_SRC: RMWExecUnit.is_terminal eu2_src>>).
Proof.
  punfold SIM. r in SIM. des.
  exploit TERMINAL; eauto. i. des. eauto.
Qed.


Fixpoint rmw_to_llsc_stmt (tmp1 tmp2: Id.t) (stmt: rmw_stmtT): list stmtT :=
  match stmt with
  | rmw_stmt_instr rmw_instr_skip =>
      [stmt_instr instr_skip]
  | rmw_stmt_instr (rmw_instr_assign lhs rhs) =>
      [stmt_instr (instr_assign lhs rhs)]
  | rmw_stmt_instr (rmw_instr_load ord res eloc) =>
      [stmt_instr (instr_load false ord res eloc)]
  | rmw_stmt_instr (rmw_instr_store ord eloc eval) =>
      [stmt_instr (instr_store false ord tmp1 eloc eval)]
  | rmw_stmt_instr (rmw_instr_fadd ordr ordw res eloc eadd) =>
      [stmt_dowhile
         [stmt_instr (instr_load true ordr tmp1 eloc);
          stmt_instr (instr_store true ordw tmp2 eloc (expr_op2 op_add (expr_reg tmp1) eadd))]
         (expr_reg tmp2);
       stmt_if (expr_reg tmp1) [] [];
       stmt_instr (instr_assign res (expr_reg tmp1))]
  | rmw_stmt_instr (rmw_instr_dmb rr rw wr ww) =>
      [stmt_instr (instr_barrier (Barrier.dmb rr rw wr ww))]
  | rmw_stmt_if cond s1 s2 =>
      [stmt_if cond
               (List.fold_right (@List.app _) [] (List.map (rmw_to_llsc_stmt tmp1 tmp2) s1))
               (List.fold_right (@List.app _) [] (List.map (rmw_to_llsc_stmt tmp1 tmp2) s2))]
  | rmw_stmt_dowhile s cond =>
      [stmt_dowhile
         (List.fold_right (@List.app _) [] (List.map (rmw_to_llsc_stmt tmp1 tmp2) s)) cond]
  end.

Definition rmw_to_llsc_stmts (tmp1 tmp2: Id.t) (stmts: list rmw_stmtT): list stmtT :=
  List.fold_right (@List.app _) [] (List.map (rmw_to_llsc_stmt tmp1 tmp2) stmts).

Inductive fresh (regs: IdSet.t): forall (stmt: rmw_stmtT), Prop :=
| fresh_instr
    i
    (FRESH: IdSet.disjoint regs (regs_of_rmw_instr i)):
  fresh regs (rmw_stmt_instr i)
| fresh_if
    cond s1 s2
    (FRESH_COND: IdSet.disjoint regs (regs_of_expr cond))
    (FRESH_STMT1: List.Forall (fresh regs) s1)
    (FRESH_STMT2: List.Forall (fresh regs) s2):
  fresh regs (rmw_stmt_if cond s1 s2)
| fresh_dowhile
    s cond
    (FRESH_STMT: List.Forall (fresh regs) s)
    (FRESH_COND: IdSet.disjoint regs (regs_of_expr cond)):
  fresh regs (rmw_stmt_dowhile s cond)
.

Definition rmw_to_llsc_program (p_src: rmw_program) (p_tgt: program): Prop :=
  forall tid, exists tmp1 tmp2,
    option_rel
      (fun stmts_src stmts_tgt =>
         (<<TMP: ~ (tmp1 = tmp2)>>) /\
         (<<FRESH: List.Forall (fresh (IdSet.add tmp2 (IdSet.singleton tmp1))) stmts_src>>) /\
         (<<STMTS: stmts_tgt = rmw_to_llsc_stmts tmp1 tmp2 stmts_src>>))
      (IdMap.find tid p_src) (IdMap.find tid p_tgt).


Variant sim_val (v_src v_tgt: ValA.t (A:=View.t (A:=unit))): Prop :=
| sim_val_intro
    (VAL: ValA.val v_src = ValA.val v_tgt)
    (ANNOT: le (ValA.annot v_src) (ValA.annot v_tgt))
.
#[export] Hint Constructors sim_val: core.

#[export] Program Instance sim_val_PreOrder: PreOrder sim_val.
Next Obligation.
  ii. destruct x. econs; ss. refl.
Qed.
Next Obligation.
  ii. inv H. inv H0.
  destruct x, y, z. ss.
  econs; ss; try congr.
  etrans; eauto.
Qed.

Lemma sim_val_sem_op2
      op2 v1_src v2_src v1_tgt v2_tgt
      (SIM1: sim_val v1_src v1_tgt)
      (SIM2: sim_val v2_src v2_tgt):
  sim_val (sem_op2 op2 v1_src v2_src) (sem_op2 op2 v1_tgt v2_tgt).
Proof.
  inv SIM1. inv SIM2.
  unfold sem_op2. econs; s; try congr.
  eapply join_le; try eapply View.order; ss.
Qed.

Definition sim_rmap (regs: IdSet.t) (rmap_src rmap_tgt: RMap.t (A:=View.t (A:=unit))): Prop :=
  forall r (NEQ: ~ IdSet.In r regs),
    sim_val (RMap.find r rmap_src) (RMap.find r rmap_tgt).

#[export] Program Instance sim_rmap_PreOrder regs: PreOrder (sim_rmap regs).
Next Obligation.
  ii. refl.
Qed.
Next Obligation.
  ii. etrans; eauto.
Qed.

Lemma sim_rmap_sem_expr
      regs rmap_src rmap_tgt
      expr
      (SIM: sim_rmap regs rmap_src rmap_tgt)
      (EXPR: IdSet.disjoint regs (regs_of_expr expr)):
  sim_val (sem_expr rmap_src expr) (sem_expr rmap_tgt expr).
Proof.
  revert EXPR.
  induction expr; i; ss.
  - refl.
  - apply SIM. ii.
    eapply EXPR; eauto.
    eapply IdSet.singleton_2. ss.
  - apply IHexpr in EXPR. inv EXPR.
    unfold sem_op1. econs; s; congr.
  - exploit IHexpr1; ii.
    { eauto using IdSet.union_2. }
    exploit IHexpr2; ii.
    { eauto using IdSet.union_3. }
    inv x0. inv x1.
    unfold sem_op2. econs; s; try congr.
    eapply join_le; try eapply View.order; ss.
Qed.

Lemma sim_rmap_add
      regs rmap_src rmap_tgt
      r v_src v_tgt
      (RMAP: sim_rmap regs rmap_src rmap_tgt)
      (VAL: sim_val v_src v_tgt):
  sim_rmap regs (RMap.add r v_src rmap_src) (RMap.add r v_tgt rmap_tgt).
Proof.
  ii. do 2 rewrite RMap.add_o.
  condtac; ss; eauto.
Qed.

Lemma sim_rmap_add_l
      regs rmap_src rmap_tgt
      r v
      (RMAP: sim_rmap regs rmap_src rmap_tgt)
      (IN: IdSet.In r regs):
  sim_rmap regs (RMap.add r v rmap_src) rmap_tgt.
Proof.
  ii. rewrite RMap.add_o.
  condtac; ss; eauto. inversion e. congr.
Qed.

Lemma sim_rmap_add_r
      regs rmap_src rmap_tgt
      r v
      (RMAP: sim_rmap regs rmap_src rmap_tgt)
      (IN: IdSet.In r regs):
  sim_rmap regs rmap_src (RMap.add r v rmap_tgt).
Proof.
  ii. rewrite RMap.add_o.
  condtac; ss; eauto. inversion e. congr.
Qed.

Variant sim_fwditem (fwd_src fwd_tgt: FwdItem.t (A:=unit)): Prop :=
| sim_fwditem_intro
    (TS: FwdItem.ts fwd_src = FwdItem.ts fwd_tgt)
    (VIEW: le (FwdItem.view fwd_src) (FwdItem.view fwd_tgt))
    (EX: FwdItem.ex fwd_src = FwdItem.ex fwd_tgt)
.
#[export] Hint Constructors sim_fwditem: core.

#[export] Program Instance sim_fwditem_PreOrder: PreOrder sim_fwditem.
Next Obligation.
  ii. destruct x. econs; ss. refl.
Qed.
Next Obligation.
  ii. inv H. inv H0.
  destruct x, y, z. ss.
  econs; ss; try congr.
  etrans; eauto.
Qed.

Variant sim_exbank (ex_src ex_tgt: Exbank.t (A:=unit)): Prop :=
| sim_exbank_intro
    (LOC: Exbank.loc ex_src = Exbank.loc ex_tgt)
    (TS: Exbank.ts ex_src = Exbank.ts ex_tgt)
    (VIEW: le (Exbank.view ex_src) (Exbank.view ex_tgt))
.
#[export] Hint Constructors sim_exbank: core.

#[export] Program Instance sim_exbank_PreOrder: PreOrder sim_exbank.
Next Obligation.
  ii. destruct x. econs; ss. refl.
Qed.
Next Obligation.
  ii. inv H. inv H0.
  destruct x, y, z. ss.
  econs; ss; try congr.
  etrans; eauto.
Qed.

Lemma sim_fwditem_read_view
      fwd_src fwd_tgt
      (SIM: sim_fwditem fwd_src fwd_tgt):
  forall ts ord,
    le (FwdItem.read_view fwd_src ts ord) (FwdItem.read_view fwd_tgt ts ord).
Proof.
  inv SIM. i. unfold FwdItem.read_view.
  rewrite TS, EX. condtac; ss. refl.
Qed.

Variant sim_local (lc_src lc_tgt: Local.t (A:=unit)): Prop :=
| sim_local_intro
    (COH: le lc_src.(Local.coh) lc_tgt.(Local.coh))
    (VRN: le lc_src.(Local.vrn) lc_tgt.(Local.vrn))
    (VWN: le lc_src.(Local.vwn) lc_tgt.(Local.vwn))
    (VRO: le lc_src.(Local.vro) lc_tgt.(Local.vro))
    (VWO: le lc_src.(Local.vwo) lc_tgt.(Local.vwo))
    (VCAP: le lc_src.(Local.vcap) lc_tgt.(Local.vcap))
    (VREL: le lc_src.(Local.vrel) lc_tgt.(Local.vrel))
    (FWDBANK: forall loc, sim_fwditem (lc_src.(Local.fwdbank) loc) (lc_tgt.(Local.fwdbank) loc))
    (PROMISES: Local.promises lc_src = Local.promises lc_tgt)
.
#[export] Hint Constructors sim_local: core.

#[export] Program Instance sim_local_PreOrder: PreOrder sim_local.
Next Obligation.
  ii. destruct x. econs; refl.
Qed.
Next Obligation.
  ii. inv H. inv H0.
  destruct x, y, z; ss.
  econs; ss; try refl; etrans; eauto.
Qed.

Lemma le_latest
      loc ts view_src view_tgt mem
      (LE: view_src <= view_tgt)
      (LATEST: Memory.latest loc ts view_tgt mem):
  Memory.latest loc ts view_src mem.
Proof.
  unfold Memory.latest, Memory.no_msgs in *. i.
  eapply LATEST; eauto. etrans; eauto.
Qed.

Ltac sim_viewtac :=
  repeat
    (try match goal with
         | [|- orderC _ _] => (try apply View.order); (try apply Time.order)
         | [|- le ?v ?v] => refl
         | [|- View._le ?v ?v] => refl
         | [|- le (join _ _) (join _ _)] => eapply join_le
         | [|- le (View._join _ _) (View._join _ _)] => eapply join_le
         | [|- View._le (join _ _) (join _ _)] => eapply join_le
         | [|- View._le (View._join _ _) (View._join _ _)] => eapply join_le
         | [|- (join _ _) <= (join _ _)] => eapply join_le
         | [|- le (ifc ?c _) (ifc ?c _)] =>
             let cond := fresh "COND" in destruct c eqn:cond; ss
         | [|- View._le (ifc ?c _) (ifc ?c _)] =>
             let cond := fresh "COND" in destruct c eqn:cond; ss
         | [|- le (fun_add _ _ _) (fun_add _ _ _)] => ii; unfold fun_add
         | [|- ?rel (if ?c then _ else _) (if ?c then _ else _)] =>
             let cond := fresh "COND" in destruct c eqn:cond; ss
         | [|- le (FwdItem.read_view _ _ _) (FwdItem.read_view _ _ _)] => eapply sim_fwditem_read_view
         | [|- View._le (FwdItem.read_view _ _ _) (FwdItem.read_view _ _ _)] => eapply sim_fwditem_read_view
         | [|- View.ts ?a <= View.ts ?b] =>
             cut (le a b);
             try (let h := fresh "X" in intro h; apply h)
         | [H: (le ?a ?b) |- le (?a ?loc) (?b ?loc)] => apply H
         | [|- sim_fwditem (fun_add _ _ _ _) (fun_add _ _ _ _)] => unfold fun_add
         | [|- sim_fwditem (FwdItem.mk _ _ _) (FwdItem.mk _ _ _)] => econs
         end;
     ss; eauto; i).

Lemma sim_local_read
      ex ord vloc_tgt res_tgt ts lc1_tgt mem_tgt lc2_tgt
      vloc_src mem_src lc1_src
      (LOCAL: sim_local lc1_src lc1_tgt)
      (MEMORY: mem_src = mem_tgt)
      (VLOC: sim_val vloc_src vloc_tgt)
      (STEP_TGT: Local.read ex ord vloc_tgt res_tgt ts lc1_tgt mem_tgt lc2_tgt):
  exists res_src lc2_src,
    (<<STEP_SRC: Local.read ex ord vloc_src res_src ts lc1_src mem_src lc2_src>>) /\
    (<<RES: sim_val res_src res_tgt>>) /\
    (<<LOCAL2: sim_local lc2_src lc2_tgt>>) /\
    (<<EX_TRUE: ex = true -> option_rel sim_exbank lc2_src.(Local.exbank) lc2_tgt.(Local.exbank)>>) /\
    (<<EX_FALSE: ex = false -> lc1_src.(Local.exbank) = lc2_src.(Local.exbank)>>).
Proof.
  destruct lc1_src, lc1_tgt. inv LOCAL. ss.
  destruct vloc_src, vloc_tgt. inv VLOC. ss. subst.
  inv STEP_TGT. ss.
  esplits.
  - econs; eauto; ss.
    + eapply le_latest; try exact COH0. sim_viewtac.
    + eapply le_latest; try exact LATEST. sim_viewtac.
  - ss. econs; ss. sim_viewtac.
  - s. econs; ss; sim_viewtac.
  - s. i. subst. econs; ss. sim_viewtac.
  - s. i. subst. ss.
Qed.

Lemma sim_local_fulfill
      ex ord vloc_tgt vval_tgt res ts tid view_pre_tgt lc1_tgt mem_tgt lc2_tgt
      vloc_src vval_src mem_src lc1_src
      (LOCAL: sim_local lc1_src lc1_tgt)
      (MEMORY: mem_src = mem_tgt)
      (VLOC: sim_val vloc_src vloc_tgt)
      (VVAL: sim_val vval_src vval_tgt)
      (EXBANK: ex = true -> option_rel sim_exbank (Local.exbank lc1_src) (Local.exbank lc1_tgt))
      (STEP_TGT: Local.fulfill ex ord vloc_tgt vval_tgt res ts tid view_pre_tgt lc1_tgt mem_tgt lc2_tgt):
  exists view_pre_src lc2_src,
    (<<STEP_SRC: Local.fulfill ex ord vloc_src vval_src res ts tid view_pre_src lc1_src mem_src lc2_src>>) /\
    (<<VIEW_PRE_SRC: le view_pre_src view_pre_tgt>>) /\
    (<<LOCAL2: sim_local lc2_src lc2_tgt>>) /\
    (<<EXBANK: ex = false -> lc1_src.(Local.exbank) = lc2_src.(Local.exbank)>>).
Proof.
  destruct lc1_src, lc1_tgt. inv LOCAL. ss.
  destruct vloc_src, vloc_tgt. inv VLOC. ss. subst.
  destruct vval_src, vval_tgt. inv VVAL. ss. subst.
  inv STEP_TGT. ss.
  inv WRITABLE. ss.
  esplits.
  - econs; eauto; ss.
    + econs; eauto; ss.
      * eapply Nat.le_lt_trans; try exact COH0. sim_viewtac.
      * eapply Nat.le_lt_trans; try exact EXT. sim_viewtac.
        destruct ex; ss.
        destruct exbank, exbank0; ss; try refl.
        apply EXBANK. ss.
      * destruct ex; ss. i.
        exploit EX; eauto. i. des. subst.
        exploit EXBANK; eauto. i. destruct exbank; ss.
        esplits; eauto.
        inv x0. rewrite LOC, TS. ss.
    + ss.
  - s. sim_viewtac.
    destruct ex; ss.
    destruct exbank, exbank0; ss; try refl.
    apply EXBANK. ss.
  - s. econs; ss; sim_viewtac.
  - s. i. subst. ss.
Qed.

Lemma sim_local_isb
      lc1_tgt lc2_tgt
      lc1_src
      (LOCAL: sim_local lc1_src lc1_tgt)
      (STEP_TGT: Local.isb lc1_tgt lc2_tgt):
  exists lc2_src,
    (<<STEP_SRC: Local.isb lc1_src lc2_src>>) /\
    (<<LOCAL2: sim_local lc2_src lc2_tgt>>) /\
    (<<EXBANK: lc1_src.(Local.exbank) = lc2_src.(Local.exbank)>>).
Proof.
  destruct lc1_src, lc1_tgt. inv LOCAL. ss.
  inv STEP_TGT. ss.
  esplits.
  - econs; ss.
  - econs; ss; sim_viewtac.
  - ss.
Qed.

Lemma sim_local_dmb
      rr rw wr ww lc1_tgt lc2_tgt
      lc1_src
      (LOCAL: sim_local lc1_src lc1_tgt)
      (STEP_TGT: Local.dmb rr rw wr ww lc1_tgt lc2_tgt):
  exists lc2_src,
    (<<STEP_SRC: Local.dmb rr rw wr ww lc1_src lc2_src>>) /\
    (<<LOCAL2: sim_local lc2_src lc2_tgt>>) /\
    (<<EXBANK: lc1_src.(Local.exbank) = lc2_src.(Local.exbank)>>).
Proof.
  destruct lc1_src, lc1_tgt. inv LOCAL. ss.
  inv STEP_TGT. ss.
  esplits.
  - econs; ss.
  - econs; ss; sim_viewtac.
  - ss.
Qed.

Lemma sim_local_control
      (ctrl_tgt: View.t (A:=unit)) lc1_tgt lc2_tgt
      ctrl_src lc1_src
      (LOCAL: sim_local lc1_src lc1_tgt)
      (CTRL: le ctrl_src ctrl_tgt)
      (STEP_TGT: Local.control ctrl_tgt lc1_tgt lc2_tgt):
  exists lc2_src,
    (<<STEP_SRC: Local.control ctrl_src lc1_src lc2_src>>) /\
    (<<LOCAL2: sim_local lc2_src lc2_tgt>>) /\
    (<<EXBANK: lc1_src.(Local.exbank) = lc2_src.(Local.exbank)>>).
Proof.
  destruct lc1_src, lc1_tgt. inv LOCAL. ss.
  inv STEP_TGT. ss.
  esplits.
  - econs; ss.
  - econs; ss; sim_viewtac.
  - ss.
Qed.

Lemma read_sim_local
      ex ord vloc res ts lc1 mem (lc2: Local.t (A:=unit))
      (READ: Local.read ex ord vloc res ts lc1 mem lc2):
  sim_local lc1 lc2.
Proof.
  inv READ. econs; ss;
    try apply join_l; try refl.
  ii. unfold fun_add. condtac; try refl.
  inversion e. subst. apply join_l.
Qed.

Lemma unfold_rmw_to_llsc_stmts
      tmp1 tmp2 s stmts:
  rmw_to_llsc_stmts tmp1 tmp2 (s :: stmts) =
  (rmw_to_llsc_stmt tmp1 tmp2 s) ++ rmw_to_llsc_stmts tmp1 tmp2 stmts.
Proof.
   ss.
Qed.

Lemma fold_right_app
      A (l1 l2: list (list A)):
  fold_right (@List.app _) [] l1 ++ fold_right (@List.app _) [] l2 =
  fold_right (@List.app _) [] (l1 ++ l2).
Proof.
  induction l1; ss.
  rewrite <- app_assoc.
  rewrite IHl1. ss.
Qed.

Section RMWtoLLSC.
  Hypothesis ARCH: arch = armv8.

  Lemma rmw_to_llsc_sim_eu
        tid tmp1 tmp2
        stmts_src rmap_src lc_src mem_src
        stmts_tgt rmap_tgt lc_tgt mem_tgt
        (TMP: tmp1 <> tmp2)
        (FRESH: List.Forall (fresh (IdSet.add tmp2 (IdSet.singleton tmp1))) stmts_src)
        (STMTS: stmts_tgt = rmw_to_llsc_stmts tmp1 tmp2 stmts_src)
        (RMAP: sim_rmap (IdSet.add tmp2 (IdSet.singleton tmp1)) rmap_src rmap_tgt)
        (LOCAL: sim_local lc_src lc_tgt)
        (EXBANK: lc_src.(Local.exbank) = None)
        (MEMORY: mem_src = mem_tgt):
    @sim_eu tid
            (RMWExecUnit.mk (RMWState.mk stmts_src rmap_src) lc_src mem_src)
            (ExecUnit.mk (State.mk stmts_tgt rmap_tgt) lc_tgt mem_tgt).
  Proof.
    revert_until tmp2.
    pcofix CIH. i.
    pfold. red. ss. subst. splits.
    { (* terminal *)
      i. red in TERMINAL_TGT. ss. des.
      esplits; try refl. red. ss. split.
      - red in TERMINAL_TGT. red. ss.
        destruct stmts_src; ss.
        destruct r0; ss. destruct i; ss.
      - inv LOCAL. congr.
    }

    i. inv STEP_TGT. inv STEP. ss.
    destruct stmts_src; try by inv STATE.
    destruct eu2_tgt as [[stmts2_tgt rmap2_tgt] lc2_tgt mem2_tgt]. ss. subst.
    destruct r0; cycle 1.
    { (* if *)
      inv STATE. inv LOCAL0; inv EVENT.
      inv FRESH. inv H1.
      exploit sim_rmap_sem_expr; try exact FRESH_COND; eauto. i. inv x0.
      exploit sim_local_control; try exact LOCAL; eauto. i. des.
      eexists (RMWExecUnit.mk _ _ _). splits.
      { econs 2; try refl. econs. econs; ss.
        - econs; ss.
        - econs 6; eauto.
      }
      rewrite VAL. condtac; ss.
      - right. eapply CIH; eauto.
        + rewrite List.Forall_app. split; ss.
        + rewrite fold_right_app.
          rewrite <- map_app. ss.
        + congr.
      - right. eapply CIH; eauto.
        + rewrite List.Forall_app. split; ss.
        + rewrite fold_right_app.
          rewrite <- map_app. ss.
        + congr.
    }

    { (* while *)
      inv STATE. inv LOCAL0; inv EVENT.
      eexists (RMWExecUnit.mk _ _ _). splits.
      { econs 2; try refl. econs. econs; ss.
        - econs. ss.
        - econs 1; eauto.
      }
      right. eapply CIH; eauto.
      - inv FRESH. inv H1.
        rewrite List.Forall_app. split; ss.
        repeat (econs; ss).
      - unfold rmw_to_llsc_stmts.
        rewrite map_app.
        rewrite <- fold_right_app. ss.
    }

    inv FRESH.
    rewrite unfold_rmw_to_llsc_stmts in STATE.
    destruct i; ss.
    { (* skip *)
      inv STATE. inv LOCAL0; inv EVENT.
      eexists (RMWExecUnit.mk _ _ _). splits.
      { econs 2; try refl. econs. econs; ss.
        - econs.
        - econs 1; eauto.
      }
      right. eapply CIH; eauto.
    }

    { (* assign *)
      inv STATE. inv LOCAL0; inv EVENT.
      eexists (RMWExecUnit.mk _ _ _). splits.
      { econs 2; try refl. econs. econs; ss.
        - econs. ss.
        - econs 1; ss.
      }
      right. eapply CIH; eauto.
      apply sim_rmap_add; auto.
      eapply sim_rmap_sem_expr; eauto.
      inv H1. ii. ss.
      eapply FRESH; eauto.
      apply IdSet.add_2. ss.
    }

    { (* load *)
      inv STATE. inv LOCAL0; inv EVENT.
      exploit sim_local_read; try exact LOCAL; eauto.
      { eapply sim_rmap_sem_expr; eauto.
        inv H1. ss. ii. eapply FRESH; eauto.
        apply IdSet.add_2. ss.
      }
      i. des.
      eexists (RMWExecUnit.mk _ _ _). splits.
      { econs 2; try refl. econs. econs; ss.
        - econs; eauto.
        - econs 2; eauto.
      }
      right. eapply CIH; eauto.
      - apply sim_rmap_add; ss.
      - rewrite <- EX_FALSE; ss.
    }

    { (* store *)
      inv STATE. inv LOCAL0; inv EVENT; cycle 1.
      { inv STEP. ss. }
      exploit sim_local_fulfill; try exact LOCAL; eauto.
      { eapply sim_rmap_sem_expr; eauto.
        inv H1. ss. ii. eapply FRESH; eauto.
        apply IdSet.union_2. ss.
      }
      { eapply sim_rmap_sem_expr; eauto.
        inv H1. ss. ii. eapply FRESH; eauto.
        apply IdSet.union_3. ss.
      }
      { i. subst. ss. }
      i. des.
      eexists (RMWExecUnit.mk _ _ _). splits.
      { econs 2; try refl. econs. econs; ss.
        - econs; ss.
        - econs 3; eauto.
      }
      right. eapply CIH; eauto.
      - apply sim_rmap_add_r; ss.
        apply IdSet.add_2, IdSet.singleton_2. ss.
      - rewrite <- EXBANK0; ss.
    }

    { (* fadd *)
      inv STATE. inv LOCAL0; inv EVENT.
      esplits; [refl|]. left.
      rename rmap2_tgt into rmap_tgt.
      revert rmap_tgt lc_tgt RMAP LOCAL.
      pcofix CIH_LOOP. i.
      pfold. red. s. splits.
      { i. repeat (red in TERMINAL_TGT; des; ss). }

      (* exclusive load *)
      i. destruct eu2_tgt as [[]].
      inv STEP_TGT. inv STEP. ss. subst.
      inv STATE. inv LOCAL0; inv EVENT.
      esplits; [refl|]. left.
      pfold. red. s. splits.
      { i. repeat (red in TERMINAL_TGT; des; ss). }

      (* exclusive store *)
      i. destruct eu2_tgt as [[]].
      inv STEP_TGT. inv STEP0. ss. subst.
      inv STATE. inv LOCAL0; inv EVENT.

      { (* exclusive store - succeed *)
        clear CIH_LOOP.
        esplits; [refl|]. left.
        pfold. red. s. splits.
        { i. repeat (red in TERMINAL_TGT; des; ss). }

        (* if *)
        i. destruct eu2_tgt as [[]].
        inv STEP_TGT. inv STEP1. ss. subst.
        inv STATE. inv LOCAL0; inv EVENT.
        condtac; ss.
        { exfalso. apply c.
          rewrite RMap.add_o. condtac; try congr.
          inv STEP0. ss.
        }
        clear e X.
        replace local1 with local0 in *; cycle 1.
        { destruct local0, local1.
          inv LC; ss. inv LC2. f_equal.
          rewrite RMap.add_o. condtac; try congr.
          inv STEP0. ss. rewrite ARCH. ss.
          rewrite bot_join; ss.
          destruct view_pre. destruct annot. ss.
          apply View.order.
        }
        clear local1 LC.
        esplits; [refl|].
        left. pfold. red. s. splits.
        { i. repeat (red in TERMINAL_TGT; des; ss). }

        (* fake branch on read value *)
        i. destruct eu2_tgt as [[]].
        inv STEP_TGT. inv STEP1. ss. subst.
        inv STATE. inv LOCAL0; inv EVENT.

        exploit sim_local_read; try exact STEP; eauto.
        { eapply sim_rmap_sem_expr; eauto.
          inv H1. ss. ii. eapply FRESH; eauto.
          apply IdSet.add_2, IdSet.union_2. ss.
        }
        i. des.
        exploit sim_local_fulfill; try exact STEP0; eauto.
        { eapply sim_rmap_sem_expr.
          - eapply sim_rmap_add_r; eauto.
            apply IdSet.add_2, IdSet.singleton_2. ss.
          - inv H1. ss. ii.
            eapply FRESH; eauto.
            apply IdSet.add_2, IdSet.union_2. ss.
        }
        { apply sim_val_sem_op2.
          - rewrite RMap.add_o. condtac; try congr. eauto.
          - eapply sim_rmap_sem_expr.
            + eapply sim_rmap_add_r; eauto.
              apply IdSet.add_2, IdSet.singleton_2. ss.
            + inv H1. ss. ii.
              eapply FRESH; eauto.
              apply IdSet.add_2, IdSet.union_3. ss.
        }
        i. des.
        exploit sim_local_control; try exact LC; eauto.
        { rewrite RMap.add_o. condtac; try congr. clear c X.
          rewrite RMap.add_o. condtac; try congr. clear e X.
          apply RES.
        }
        i. des.

        eexists (RMWExecUnit.mk _ _ _). splits.
        { econs 2; try refl. econs. econs; s.
          - econs; eauto.
          - econs 4; eauto.
          - ss.
        }
        match goal with
        | [|-context[if ?c then ?s else ?s]] =>
            replace (if c then s else s) with s by (condtac; ss); s
        end.
        left. pfold. red. s. splits.
        { i. repeat (red in TERMINAL_TGT; des; ss). }

        (* assign *)
        i. destruct eu2_tgt as [[]].
        inv STEP_TGT. inv STEP1. ss. subst.
        inv STATE. inv LOCAL3; inv EVENT.
        esplits; [refl|].
        right. eapply CIH; eauto.
        - rewrite List.app_nil_r. ss.
        - apply sim_rmap_add.
          + apply sim_rmap_add_r; cycle 1.
            { apply IdSet.add_1. ss. }
            apply sim_rmap_add_r; ss.
            apply IdSet.add_2. apply IdSet.singleton_2. ss.
          + unfold sem_expr.
            rewrite RMap.add_o. condtac; ss.
            rewrite RMap.add_o. condtac; try congr.
        - inv STEP_SRC0. ss.
      }

      { (* exclusive store - fail *)
        inv STEP0. clear CIH EX.
        esplits; try refl. left.
        pfold. red. s. splits.
        { i. repeat (red in TERMINAL_TGT; des; ss). }

        (* if *)
        i. destruct eu2_tgt as [[]].
        inv STEP_TGT. inv STEP0. ss. subst.
        inv STATE. inv LOCAL0; inv EVENT. inv LC. ss.
        repeat rewrite RMap.add_eq; ss.
        replace (join (Local.vcap local) bot) with (Local.vcap local); cycle 1.
        { rewrite bot_join; ss. apply View.order. }
        esplits; try refl. left.
        pfold. red. ss. splits.
        { i. repeat (red in TERMINAL_TGT; des; ss). }

        (* dowhile *)
        i. destruct eu2_tgt as [[]].
        inv STEP_TGT. inv STEP0. ss. subst.
        inv STATE. inv LOCAL0; inv EVENT. ss.
        esplits; [refl|]. right.
        repeat rewrite List.app_nil_r.
        eapply CIH_LOOP.
        - apply sim_rmap_add_r; cycle 1.
          { apply IdSet.add_1. ss. }
          apply sim_rmap_add_r; ss.
          apply IdSet.add_2. apply IdSet.singleton_2. ss.
        - exploit read_sim_local; try exact STEP. i.
          etrans; eauto. etrans; eauto.
          destruct local. ss.
          econs; s; refl.
      }
    }

    { (* barrier *)
      inv STATE. inv LOCAL0; inv EVENT.
      exploit sim_local_dmb; eauto. i. des.
      eexists (RMWExecUnit.mk _ _ _). splits.
      { econs 2; try refl. econs. econs; ss.
        - econs; ss.
        - econs 5; eauto.
      }
      right. eapply CIH; eauto. congr.
    }
  Qed.


  Variant sim_sl (tmp1 tmp2: Id.t):
    forall (sl_src: RMWState.t (A:=View.t (A:=unit)) * Local.t (A:=unit))
           (sl_tgt: State.t (A:=View.t (A:=unit)) * Local.t (A:=unit)), Prop :=
    | sim_sl_intro
        st_src lc_src
        st_tgt lc_tgt
        (TMP: tmp1 <> tmp2)
        (FRESH: List.Forall (fresh (IdSet.add tmp2 (IdSet.singleton tmp1))) st_src.(RMWState.stmts))
        (STMTS: st_tgt.(State.stmts) = rmw_to_llsc_stmts tmp1 tmp2 st_src.(RMWState.stmts))
        (RMAP: sim_rmap (IdSet.add tmp2 (IdSet.singleton tmp1)) st_src.(RMWState.rmap) st_tgt.(State.rmap))
        (LOCAL: sim_local lc_src lc_tgt)
        (EXBANK: lc_src.(Local.exbank) = None):
      sim_sl tmp1 tmp2 (st_src, lc_src) (st_tgt, lc_tgt)
  .

  Variant sim (m_src: RMWMachine.t) (m_tgt: Machine.t): Prop :=
    | sim_machine_intro
        (TPOOL: forall tid, exists tmp1 tmp2,
            opt_rel (sim_sl tmp1 tmp2)
              (IdMap.find tid (RMWMachine.tpool m_src))
              (IdMap.find tid (Machine.tpool m_tgt)))
        (MEMORY: RMWMachine.mem m_src = Machine.mem m_tgt)
  .

  Lemma sim_sl_sim_eu
        tid tmp1 tmp2
        sl_src sl_tgt
        mem_src mem_tgt
        (SIM: sim_sl tmp1 tmp2 sl_src sl_tgt)
        (MEM: mem_src = mem_tgt):
    @sim_eu tid
            (RMWExecUnit.mk (fst sl_src) (snd sl_src) mem_src)
            (ExecUnit.mk (fst sl_tgt) (snd sl_tgt) mem_tgt).
  Proof.
    inv SIM. s.
    destruct st_src, st_tgt. ss.
    eapply rmw_to_llsc_sim_eu; eauto.
  Qed.

  Lemma init_sim
        prog_src prog_tgt
        (COMPILE: rmw_to_llsc_program prog_src prog_tgt):
    sim (RMWMachine.init prog_src) (Machine.init prog_tgt).
  Proof.
    econs; ss. i.
    specialize (COMPILE tid). des.
    exists tmp1, tmp2.
    do 2 rewrite IdMap.map_spec.
    destruct (IdMap.find tid prog_src) eqn:FIND_SRC,
        (IdMap.find tid prog_tgt) eqn:FIND_TGT; ss. des.
    econs. econs; ss; try refl.
  Qed.

  Lemma sim_local_promise
        lc1_src mem1_src
        lc1_tgt mem1_tgt
        loc val ts tid
        lc2_tgt mem2_tgt
        (SIM1: sim_local lc1_src lc1_tgt)
        (MEM1: mem1_src = mem1_tgt)
        (STEP_TGT: Local.promise loc val ts tid lc1_tgt mem1_tgt lc2_tgt mem2_tgt):
    exists lc2_src mem2_src,
      (<<STEP_SRC: Local.promise loc val ts tid lc1_src mem1_src lc2_src mem2_src>>) /\
      (<<SIM2: sim_local lc2_src lc2_tgt>>) /\
      (<<MEM2: mem2_src = mem2_tgt>>).
  Proof.
    destruct lc1_src, lc1_tgt. inv SIM1. ss. subst.
    inv STEP_TGT. ss.
    esplits.
    - econs; eauto.
    - ss.
    - ss.
  Qed.

  Lemma sim_sl_promise_step
        tmp1 tmp2 tid
        st1_src lc1_src mem1_src
        st1_tgt lc1_tgt mem1_tgt
        st2_tgt lc2_tgt mem2_tgt
        (SIM1: sim_sl tmp1 tmp2 (st1_src, lc1_src) (st1_tgt, lc1_tgt))
        (MEM1: mem1_src = mem1_tgt)
        (STEP_TGT: ExecUnit.promise_step tid
                     (ExecUnit.mk st1_tgt lc1_tgt mem1_tgt)
                     (ExecUnit.mk st2_tgt lc2_tgt mem2_tgt)):
    exists st2_src lc2_src mem2_src,
      (<<STEP_SRC: RMWExecUnit.promise_step tid
                     (RMWExecUnit.mk st1_src lc1_src mem1_src)
                     (RMWExecUnit.mk st2_src lc2_src mem2_src)>>) /\
      (<<SIM2: sim_sl tmp1 tmp2 (st2_src, lc2_src) (st2_tgt, lc2_tgt)>>) /\
      (<<MEM2: mem2_src = mem2_tgt>>).
  Proof.
    inv SIM1. inv STEP_TGT. ss. subst.
    exploit sim_local_promise; eauto. i. des. subst.
    esplits.
    - econs; s; eauto.
    - econs; ss. inv STEP_SRC. ss.
    - ss.
  Qed.

  Lemma sim_promise_step
        m1_src m1_tgt m2_tgt
        (SIM1: sim m1_src m1_tgt)
        (STEP_TGT: Machine.step ExecUnit.promise_step m1_tgt m2_tgt):
    exists m2_src,
      (<<STEP_SRC: RMWMachine.step RMWExecUnit.promise_step m1_src m2_src>>) /\
      (<<SIM2: sim m2_src m2_tgt>>).
  Proof.
    destruct m1_src as [tpool1_src mem1_src],
        m1_tgt as [tpool1_tgt mem1_tgt].
    inv SIM1. inv STEP_TGT. ss.
    exploit TPOOL. i. des.
    rewrite FIND in x0. inv x0.
    destruct a as [st1_src lc1_src].
    symmetry in H0. rename H0 into FIND_SRC.
    exploit sim_sl_promise_step; eauto. i. des.
    eexists (RMWMachine.mk _ _).
    esplits.
    - econs; s; eauto.
    - econs; ss. i.
      rewrite TPOOL0.
      do 2 rewrite IdMap.add_spec.
      condtac; eauto.
  Qed.

  Lemma sim_rtc_promise_step
        m1_src m1_tgt m2_tgt
        (SIM1: sim m1_src m1_tgt)
        (STEP_TGT: rtc (Machine.step ExecUnit.promise_step) m1_tgt m2_tgt):
    exists m2_src,
      (<<STEP_SRC: rtc (RMWMachine.step RMWExecUnit.promise_step) m1_src m2_src>>) /\
      (<<SIM2: sim m2_src m2_tgt>>).
  Proof.
    revert m1_src SIM1.
    induction STEP_TGT; i; eauto.
    exploit sim_promise_step; eauto. i. des.
    exploit IHSTEP_TGT; eauto. i. des.
    esplits; [|eauto]. etrans; eauto.
  Qed.

  Lemma sim_eu_exec
        tid eu1_src eu1_tgt eu2_tgt
        (SIM: @sim_eu tid eu1_src eu1_tgt)
        (STEPS_TGT: rtc (ExecUnit.state_step tid) eu1_tgt eu2_tgt)
        (TERMINAL_ST: State.is_terminal eu2_tgt.(ExecUnit.state))
        (TERMINAL_LC: eu2_tgt.(ExecUnit.local).(Local.promises) = bot):
    exists eu2_src,
      (<<STEPS_SRC: rtc (RMWExecUnit.state_step None tid) eu1_src eu2_src>>) /\
      (<<TERMINAL_ST: RMWState.is_terminal eu2_src.(RMWExecUnit.state)>>) /\
      (<<TERMINAL_LC: eu2_src.(RMWExecUnit.local).(Local.promises) = bot>>).
  Proof.
    exploit sim_eu_rtc_state_step; eauto. i. des.
    punfold SIM0. inv SIM0. des.
    exploit H; [econs; ss|]. i. des.
    esplits; try apply TERMINAL_SRC.
    etrans; eauto.
  Qed.

  Lemma sim_state_exec
        m1_src m1_tgt m_tgt
        (SIM: sim m1_src m1_tgt)
        (EXEC_TGT: Machine.state_exec m1_tgt m_tgt)
        (TERMINAL_TGT: Machine.is_terminal m_tgt):
    exists m_src,
      (<<EXEC_SRC: RMWMachine.state_exec m1_src m_src>>) /\
      (<<TERMINAL_TGT: RMWMachine.is_terminal m_src>>) /\
      (<<MEMORY: RMWMachine.mem m_src = Machine.mem m_tgt>>).
  Proof.
    inv SIM. inv EXEC_TGT.
    assert (exists tids,
               (<<IN: forall tid (IN: List.In tid tids),
                   (<<SIM:
                     exists tid1 tid2,
                       opt_rel
                         (sim_sl tid1 tid2)
                         (IdMap.find tid m1_src.(RMWMachine.tpool))
                         (IdMap.find tid m1_tgt.(Machine.tpool))>>) /\
                   (<<EXEC_TGT:
                     opt_rel
                       (fun sl1 sl2 =>
                          rtc (ExecUnit.state_step tid)
                            (ExecUnit.mk (fst sl1) (snd sl1) m1_tgt.(Machine.mem))
                            (ExecUnit.mk (fst sl2) (snd sl2) m1_tgt.(Machine.mem)))
                       (IdMap.find tid m1_tgt.(Machine.tpool))
                       (IdMap.find tid m_tgt.(Machine.tpool))>>)>>) /\
               (<<OUT: forall tid (OUT: ~ List.In tid tids),
                   (<<TERMINAL: forall st_src lc_src
                                  (FIND: IdMap.find tid m1_src.(RMWMachine.tpool) = Some (st_src, lc_src)),
                       (<<TERMINAL_ST: RMWState.is_terminal st_src>>) /\
                       (<<TERMINAL_LC: lc_src.(Local.promises) = bot>>)>>)>>) /\
               (<<NODUP: List.NoDup tids>>)).
    { exists (List.map fst (IdMap.elements m1_src.(RMWMachine.tpool))).
      splits; ss.
      - ii. exfalso. apply OUT.
        setoid_rewrite IdMap.elements_spec in FIND.
        revert FIND. clear.
        generalize (IdMap.elements m1_src.(RMWMachine.tpool)). i.
        induction l; ss.
        destruct a. des_ifs; auto.
      - specialize (IdMap.elements_3w m1_src.(RMWMachine.tpool)). clear.
        generalize (IdMap.elements m1_src.(RMWMachine.tpool)). i.
        induction l; ss.
        inv H. econs; eauto.
        clear - H2. ii.
        induction l; ss. des; eauto.
        destruct a0, a; ss. subst.
        apply H2. left. ss.
    }
    des.
    clear TPOOL TPOOL0.
    revert m1_src m1_tgt IN OUT NODUP MEMORY MEM.

    induction tids; i.
    { exists m1_src. splits.
      - econs; ss. ii.
        destruct (IdMap.find id (RMWMachine.tpool m1_src)); ss.
        econs. refl.
      - econs. i. eapply OUT; eauto.
      - congr.
    }
    exploit IN; [left; refl|]. i. des.
    inv SIM.
    { eapply IHtids; eauto; ii.
      - eapply IN. right. ss.
      - destruct (Id.eq_dec tid a).
        + subst. congr.
        + eapply OUT; eauto. ii. inv H1; ss.
      - inv NODUP. ss.
    }
    destruct a0 as [st1_src lc1_src], b as [st1_tgt lc1_tgt].
    exploit sim_sl_sim_eu; try exact REL; try exact MEMORY. s. intro SIM_EU.
    rewrite <- H in *. inv EXEC_TGT.
    destruct b as [st2_tgt lc2_tgt]. ss.
    inv TERMINAL_TGT. exploit TERMINAL; eauto. i. des.
    exploit sim_eu_exec; try exact REL0; eauto. i. des.
    destruct eu2_src as [st2_src lc2_src mem2_src].
    exploit (RMWExecUnit.rtc_state_step_memory (A:=unit)); try exact STEPS_SRC. s. i. subst.
    destruct m1_src as [tpool1_src mem1_src],
        m1_tgt as [tpool1_tgt mem1_tgt]. ss.
    exploit (IHtids
              (RMWMachine.mk (IdMap.add a (st2_src, lc2_src) tpool1_src) mem1_src)
              (Machine.mk (IdMap.add a (st2_tgt, lc2_tgt) tpool1_tgt) mem1_tgt)); ss.
    { clear IHtids. i.
      repeat rewrite IdMap.add_spec.
      condtac; ss; eauto.
      r in e. subst. inv NODUP. ss.
    }
    { clear IHtids. ii. revert FIND.
      rewrite IdMap.add_spec. condtac; i.
      - r in e. inv FIND. auto.
      - eapply OUT; eauto. ii. des; ss. congr.
    }
    { inv NODUP. ss. }
    i. des. esplits; eauto.
    inv EXEC_SRC. econs; ss.
    ii. specialize (TPOOL id). inv TPOOL.
    - revert H2. rewrite IdMap.add_spec. condtac; ss. i.
      rewrite <- H2. ss.
    - revert H2. rewrite IdMap.add_spec. condtac; ss; i.
      + r in e. subst. inv H2.
        rewrite <- H0. econs. ss. etrans; eauto.
      + rewrite <- H2. econs. ss.
  Qed.

  Theorem rmw_to_llsc
          prog_src prog_tgt m_tgt
          (COMPILE: rmw_to_llsc_program prog_src prog_tgt)
          (EXEC_TGT: Machine.pf_exec prog_tgt m_tgt)
          (TERMINAL_TGT: Machine.is_terminal m_tgt):
    exists m_src,
      (<<EXEC_SRC: RMWMachine.pf_exec prog_src m_src>>) /\
      (<<TERMINAL_TGT: RMWMachine.is_terminal m_src>>) /\
      (<<MEMORY: RMWMachine.mem m_src = Machine.mem m_tgt>>).
  Proof.
    inv EXEC_TGT.
    exploit init_sim; eauto. intro SIM.
    exploit sim_rtc_promise_step; eauto. i. des.
    exploit sim_state_exec; eauto. i. des.
    esplits.
    - econs; eauto. inv TERMINAL_TGT0.
      econs. i. eapply TERMINAL; eauto.
    - ss.
    - ss.
  Qed.
End RMWtoLLSC.
