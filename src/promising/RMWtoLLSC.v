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


Fixpoint rmw_to_llsc_stmt (tmp: Id.t) (stmt: stmtT): list stmtT :=
  match stmt with
  | stmt_instr (instr_fadd ordr ordw res eloc eadd) =>
    [stmt_dowhile
       [stmt_instr (instr_load true ordr res eloc);
        stmt_instr (instr_store true ordw tmp eloc (expr_op2 op_add (expr_reg res) eadd))]
       (expr_op1 op_not (expr_reg tmp))]
  | stmt_if cond s1 s2 =>
    [stmt_if cond
             (List.fold_right (@List.app _) [] (List.map (rmw_to_llsc_stmt tmp) s1))
             (List.fold_right (@List.app _) [] (List.map (rmw_to_llsc_stmt tmp) s2))]
  | stmt_dowhile s cond =>
    [stmt_dowhile
       (List.fold_right (@List.app _) [] (List.map (rmw_to_llsc_stmt tmp) s)) cond]
  | _ => [stmt]
  end.

Definition rmw_to_llsc_stmts (tmp: Id.t) (stmts: list stmtT): list stmtT :=
  List.fold_right (@List.app _) [] (List.map (rmw_to_llsc_stmt tmp) stmts).

Definition rmw_to_llsc_program (p_src p_tgt: program): Prop :=
  forall tid, exists tmp,
    option_rel
      (fun stmts_src stmts_tgt => stmts_tgt = rmw_to_llsc_stmts tmp stmts_src)
      (IdMap.find tid p_src) (IdMap.find tid p_tgt).

Inductive fresh (r: Id.t): forall (stmt: stmtT), Prop :=
| fresh_instr
    i
    (FRESH: ~ IdSet.mem r (regs_of_instr i)):
  fresh r (stmt_instr i)
| fresh_if
    cond s1 s2
    (FRESH_COND: ~ IdSet.mem r (regs_of_expr cond))
    (FRESH_STMT1: List.Forall (fresh r) s1)
    (FRESH_STMT2: List.Forall (fresh r) s2):
  fresh r (stmt_if cond s1 s2)
| fresh_dowhile
    s cond
    (FRESH_STMT: List.Forall (fresh r) s)
    (FRESH_COND: ~ IdSet.mem r (regs_of_expr cond)):
  fresh r (stmt_dowhile s cond)
.

Definition is_exclusive (i: instrT): bool :=
  match i with
  | instr_load ex _ _ _
  | instr_store ex _ _ _ _ => ex
  | _ => false
  end.

Inductive exclusive_free: forall (stmt: stmtT), Prop :=
| exclusive_free_instr
    i
    (EXFREE: ~ is_exclusive i):
  exclusive_free (stmt_instr i)
| exclusive_free_if
    cond s1 s2
    (EXFREE1: List.Forall exclusive_free s1)
    (EXFREE2: List.Forall exclusive_free s2):
  exclusive_free (stmt_if cond s1 s2)
| exclusive_free_dowhile
    s cond
    (EXFREE: List.Forall exclusive_free s):
  exclusive_free (stmt_dowhile s cond)
.


Variant sim_val (v_src v_tgt: ValA.t (A:=View.t (A:=unit))): Prop :=
| sim_val_intro
    (VAL: ValA.val v_src = ValA.val v_tgt)
    (ANNOT: le (ValA.annot v_src) (ValA.annot v_tgt))
.

Definition sim_rmap (tmp: Id.t) (rmap_src rmap_tgt: RMap.t (A:=View.t (A:=unit))): Prop :=
  forall r (NEQ: r <> tmp),
    sim_val (RMap.find r rmap_src) (RMap.find r rmap_tgt).

Variant sim_local (lc_src lc_tgt: Local.t (A:=unit)): Prop :=
| sim_local_intro
    (COH: lc_src.(Local.coh) = lc_tgt.(Local.coh))
    (VRN: lc_src.(Local.vrn) = lc_tgt.(Local.vrn))
    (VWN: lc_src.(Local.vwn) = lc_tgt.(Local.vwn))
    (VRO: lc_src.(Local.vro) = lc_tgt.(Local.vro))
    (VWO: lc_src.(Local.vwo) = lc_tgt.(Local.vwo))
    (VCAP: lc_src.(Local.vcap) = lc_tgt.(Local.vcap))
    (VREL: lc_src.(Local.vrel) = lc_tgt.(Local.vrel))
    (FWDBANK: lc_src.(Local.fwdbank) = lc_tgt.(Local.fwdbank))
    (EXBANK: lc_src.(Local.exbank) = None)
    (PROMISES: Local.promises lc_src = Local.promises lc_tgt)
.
#[export] Hint Constructors sim_local: core.

Lemma sim_local_step
      e tid mem_tgt lc1_tgt lc2_tgt
      mem_src lc1_src
      (LOCAL: sim_local lc1_src lc1_tgt)
      (MEMORY: mem_src = mem_tgt)
      (STEP_TGT: Local.step e tid mem_tgt lc1_tgt lc2_tgt)
      (EXFREE: match e with
               | Event.read ex _ _ _
               | Event.write ex _ _ _ _ => ex = false
               | _ => True
               end):
  exists lc2_src,
    (<<STEP_SRC: Local.step e tid mem_src lc1_src lc2_src>>) /\
    (<<LOCAL2: sim_local lc2_src lc2_tgt>>).
Proof.
  destruct lc1_src, lc1_tgt. inv LOCAL; ss. subst.
  inv STEP_TGT; subst.
  { (* internal *)
    esplits; [econs 1|]; eauto.
  }
  { (* read *)
    inv STEP. ss.
    esplits; [econs 2|].
    - ss.
    - econs; eauto.
    - ss.
  }
  { (* fulfill *)
    inv STEP. ss.
    esplits; [econs 3|].
    - ss.
    - econs; eauto. ss.
      inv WRITABLE. ss. econs; eauto. i. ss.
    - ss.
  }
  { (* write failure *)
    inv STEP. ss.
  }
  { (* fadd *)
    inv STEP_READ. ss.
    inv STEP_FULFILL. ss.
    esplits; [econs 5|].
    - ss.
    - econs; eauto.
    - econs; eauto. ss.
      inv WRITABLE. ss. econs; eauto. i. ss.
    - ss.
  }
  { (* isb *)
    inv STEP. ss.
    esplits; [econs 6|]; ss.
  }
  { (* dmb *)
    inv STEP. ss.
    esplits; [econs 7|]; ss.
  }
  { (* control *)
    inv LC. ss.
    esplits; [econs 8|]; ss.
  }        
Qed.


Section RMWtoLLSC.
  Hypothesis ARCH: arch = armv8.

  Lemma rmw_to_llsc_sim_eu
        tid tmp
        stmts_src rmap_src lc_src mem_src
        stmts_tgt rmap_tgt lc_tgt mem_tgt
        (FRESH: List.Forall (fresh tmp) stmts_src)
        (EXFREE: List.Forall exclusive_free stmts_src)
        (STMTS: stmts_tgt = rmw_to_llsc_stmts tmp stmts_src)
        (RMAP: sim_rmap tmp rmap_src rmap_tgt)
        (LOCAL: sim_local lc_src lc_tgt)
        (MEMORY: mem_src = mem_tgt):
    @sim_eu tid
            (ExecUnit.mk (State.mk stmts_src rmap_src) lc_src mem_src)
            (ExecUnit.mk (State.mk stmts_tgt rmap_tgt) lc_tgt mem_tgt).
  Proof.
    revert_until tmp.
    pcofix CIH. i.
    pfold. red. ss. subst. splits.
    { (* terminal *)
      i. red in TERMINAL_TGT. ss. des.
      esplits; try refl. red. ss. split; cycle 1.
      { inv LOCAL. congr. }
      red in TERMINAL_TGT. red. ss.
      destruct stmts_src; ss.
      destruct s; ss. destruct i; ss.
    }

    i. inv STEP_TGT. inv STEP. ss.
    destruct stmts_src; try by inv STATE.
    destruct eu2_tgt as [[stmts2_tgt rmap2_tgt] lc2_tgt mem2_tgt]. ss. subst.
    exploit sim_local_step; try exact LOCAL0; eauto.
    { destruct s; inv STATE; ss.
      - destruct i; ss. inv H1.
        inv EXFREE. inv H1. destruct ex0; ss.
      - destruct i; ss. inv H1.
        inv EXFREE. inv H1. destruct ex0; ss.
    }
    i. des.

    destruct s; cycle 1.
    { (* if *)
      inv STATE.
      eexists (ExecUnit.mk _ _ _). splits.
      { econs 2; try refl. econs.
        econs; try eapply STEP_SRC; ss.
        econs; eauto.
        admit. (* sem_expr *)
      }
      condtac; ss.
      - right. eapply CIH; eauto.
        + admit.
        + admit.
        + admit.
      - right. eapply CIH; eauto.
        + admit.
        + admit.
        + admit.
    }

    { (* while *)
      inv STATE.
      eexists (ExecUnit.mk _ _ _). splits.
      { econs 2; try refl. econs.
        econs; try eapply STEP_SRC; ss.
        econs; eauto.
      }
      right. eapply CIH; eauto.
      - admit.
      - admit.
      - admit.
    }

    admit.
  Admitted.
End RMWtoLLSC.


Variant sim_sl (tmp: Id.t):
  forall (sl_src sl_tgt: State.t (A:=View.t (A:=unit)) * Local.t (A:=unit)), Prop :=
| sim_sl_intro
    stmts_src rmap_src lc_src
    stmts_tgt rmap_tgt lc_tgt
    (STMTS: stmts_tgt = rmw_to_llsc_stmts tmp stmts_src)
    (RMAP: sim_rmap tmp rmap_src rmap_tgt)
    (LOCAL: lc_src = lc_tgt) (* TODO: fix *):
  sim_sl tmp (State.mk stmts_src rmap_src, lc_src) (State.mk stmts_tgt rmap_tgt, lc_tgt)
.

Variant sim_machine (m_src m_tgt: Machine.t): Prop :=
| sim_machine_intro
    (TPOOL: forall tid, exists tmp,
        option_rel (sim_sl tmp)
                   (IdMap.find tid (Machine.tpool m_src))
                   (IdMap.find tid (Machine.tpool m_tgt)))
    (MEMORY: Machine.mem m_src = Machine.mem m_tgt)
.


Theorem rmw_to_llsc_sim
        prog_src prog_tgt
        (PROGRAM: rmw_to_llsc_program prog_src prog_tgt):
  @sim sim_machine (Machine.init prog_src) (Machine.init prog_tgt).
Proof.
Admitted.
