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
Set Nested Proofs Allowed.


Module PStoRMW.
  Import PStoRMWThread.

  Variant sim_thread_exec (tid: Ident.t) (n: Time.t) (after_sc: bool)
    (th_ps: PSThread.t lang_ps) (eu: RMWExecUnit.t (A:=unit)): Prop :=
    | sim_thread_exec_intro
        sc eu1 eu2 eu3
        (STEPS1: rtc (RMWExecUnit.state_step None tid) eu eu1)
        (SIM_THREAD: sim_thread tid n th_ps eu1)
        (SC: sc = if after_sc then S n else n)
        (STEPS2: rtc (RMWExecUnit.state_step_dmbsy_over (Some n) sc tid) eu1 eu2)
        (PROMISES2: forall ts (PROMISED: Promises.lookup ts eu2.(RMWExecUnit.local).(Local.promises)),
            lt n ts)
        (STEPS3: rtc (RMWExecUnit.state_step_dmbsy_over (Some n) sc tid) eu2 eu3)
        (PROMISES3: eu3.(RMWExecUnit.local).(Local.promises) = bot)
  .

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

  Variant sim (n: Time.t) (c: PSConfiguration.t) (m: RMWMachine.t): Prop :=
    | sim_intro
        m1
        (PROMISE_STEPS: rtc (RMWMachine.step RMWExecUnit.promise_step) m m1)
        (SIM_THREADS:
          forall tid,
            opt_rel
              (sim_thread_sl tid n true c.(PSConfiguration.global) m.(RMWMachine.mem))
              (IdentMap.find tid c.(PSConfiguration.threads))
              (IdMap.find tid m.(RMWMachine.tpool)))
        (SIM_SC: forall loc,
            PSTime.le (c.(PSConfiguration.global).(PSGlobal.sc) loc) (ntt n))
  .
End PStoRMW.
