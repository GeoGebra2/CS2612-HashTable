Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Require Import hashtbl_strategy_goal.
Import naive_C_Rules.
Require Import hashtbl_lib.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma hashtbl_strategy0_correctness : hashtbl_strategy0.
Proof.
  pre_process.
  simpl.
  entailer!.
Qed.

Lemma hashtbl_strategy1_correctness : hashtbl_strategy1.
Proof.
  pre_process.
  simpl.
  entailer!.
Qed.

Lemma hashtbl_strategy2_correctness : hashtbl_strategy2.
Proof.
  pre_process.
  induction l; simpl.
  + entailer!.
  + entailer!.
Admitted.

Lemma hashtbl_strategy3_correctness : hashtbl_strategy3.
Proof.
  pre_process.
  Intros.
  subst.
  entailer!.
Qed.

Lemma hashtbl_strategy9_correctness : hashtbl_strategy9.
Proof.
  pre_process.
  Intros.
  subst.
  entailer!.
  easy.
Qed.

Lemma hashtbl_strategy10_correctness : hashtbl_strategy10.
Proof.
  pre_process.
  entailer!.
  subst.
  easy.
Qed.

Lemma hashtbl_strategy11_correctness : hashtbl_strategy11.
Proof.
  pre_process.
  entailer!.
  subst.
  easy.
Qed.

Lemma hashtbl_strategy12_correctness : hashtbl_strategy12.
Proof.
  pre_process.
  entailer!.
  subst.
  easy.
Qed.

Lemma hashtbl_strategy13_correctness : hashtbl_strategy13.
Proof.
  pre_process.
  entailer!.
Admitted.

Lemma hashtbl_strategy14_correctness : hashtbl_strategy14.
  pre_process_default.
Admitted.

Lemma hashtbl_strategy15_correctness : hashtbl_strategy15.
  pre_process_default.
Admitted.

Lemma hashtbl_strategy19_correctness : hashtbl_strategy19.
  pre_process_default.
Admitted.

Lemma hashtbl_strategy22_correctness : hashtbl_strategy22.
  pre_process_default.
Admitted.

Lemma hashtbl_strategy16_correctness : hashtbl_strategy16.
  pre_process_default.
Admitted.

Lemma hashtbl_strategy17_correctness : hashtbl_strategy17.
  pre_process_default.
Admitted.

Lemma hashtbl_strategy4_correctness : hashtbl_strategy4.
  pre_process_default.
Admitted.

Lemma hashtbl_strategy24_correctness : hashtbl_strategy24.
  pre_process_default.
Admitted.

Lemma hashtbl_strategy25_correctness : hashtbl_strategy25.
  pre_process_default.
Admitted.

Lemma hashtbl_strategy26_correctness : hashtbl_strategy26.
  pre_process_default.
Admitted.

Lemma hashtbl_strategy18_correctness : hashtbl_strategy18.
  pre_process_default.
Admitted.

Lemma hashtbl_strategy7_correctness : hashtbl_strategy7.
  pre_process_default.
Admitted.

Lemma hashtbl_strategy8_correctness : hashtbl_strategy8.
  pre_process_default.
Admitted.

Lemma hashtbl_strategy20_correctness : hashtbl_strategy20.
  pre_process_default.
Admitted.

Lemma hashtbl_strategy21_correctness : hashtbl_strategy21.
  pre_process_default.
Admitted.

Lemma hashtbl_strategy23_correctness : hashtbl_strategy23.
  pre_process_default.
Admitted.

Lemma hashtbl_strategy5_correctness : hashtbl_strategy5.
  pre_process_default.
Admitted.

Lemma hashtbl_strategy6_correctness : hashtbl_strategy6.
  pre_process_default.
Admitted.
