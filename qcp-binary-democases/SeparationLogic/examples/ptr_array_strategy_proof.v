Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
From SimpleC.SL Require Import SeparationLogic.
Require Import ptr_array_strategy_goal.

Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Require Import Coq.micromega.Lia.

Lemma ptr_array_strategy1_correctness : ptr_array_strategy1.
  pre_process_default.
  prop_apply (PtrArray.full_length). Intros.
  sep_apply (PtrArray.full_split_to_missing_i p i); [ | tauto].
  entailer!.
  Intros_r v.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
  subst.
  entailer!.
Qed.

Lemma ptr_array_strategy4_correctness : ptr_array_strategy4.
  pre_process_default.
  Intros; subst; entailer!.
Qed.

Lemma ptr_array_strategy5_correctness : ptr_array_strategy5.
Proof.  
  pre_process_default.
Qed.

Lemma ptr_array_strategy6_correctness : ptr_array_strategy6.
  pre_process_default.
  Intros; subst; entailer!.
Qed.

Lemma ptr_array_strategy7_correctness : ptr_array_strategy7.
  pre_process_default.
  sep_apply (PtrArray.ceil_split_to_missing_i p x i y); [ | tauto].
  entailer!.
  Intros_r_any.
  entailer!.
  apply derivable1_wand_sepcon_adjoint.
  entailer!.
  Intros; subst; entailer!.
Qed.

Lemma ptr_array_strategy8_correctness : ptr_array_strategy8.
  pre_process_default.
  Intros; subst.
  prop_apply (PtrArray.ceil_length p x y).
  prop_apply (PtrArray.ceil_length p y z).
  Intros.
  sep_apply (PtrArray.ceil_merge_to_ceil p x y z l1 l2) ; try lia.
  entailer!.
Qed.

Lemma ptr_array_strategy9_correctness : ptr_array_strategy9.
  pre_process_default.
  Intros. subst.
  prop_apply (PtrArray.ceil_length p x z).
  Intros.
  sep_apply (PtrArray.ceil_split_to_ceil p x y z (l1 ++ l2)) ; try lia.
  rewrite <- H2.
  rewrite sublist_app_exact1 by lia.
  rewrite sublist_split_app_r with (len := Zlength l1) by lia.
  replace (Zlength l1 - Zlength l1) with 0 by lia.
  rewrite Zlength_correct in *.
  rewrite length_app in H1.
  replace (z - x - Z.of_nat (Datatypes.length l1)) with (Zlength l2).
  rewrite sublist_self by lia.
  entailer!.
  rewrite Zlength_correct. lia.
Qed.

Lemma ptr_array_strategy10_correctness : ptr_array_strategy10.
  pre_process_default.
  Intros;subst.
  cbn.
  entailer!.
Qed.

Lemma ptr_array_strategy2_correctness : ptr_array_strategy2.
  pre_process_default.
  simpl.
  sep_apply (PtrArray.missing_i_merge_to_full); [ | tauto].
  rewrite replace_Znth_Znth by tauto.
  entailer!.
Qed.

Lemma ptr_array_strategy11_correctness : ptr_array_strategy11.
  pre_process_default.
  simpl.
  sep_apply (PtrArray.missing_i_merge_to_ceil); [ | tauto].
  rewrite replace_Znth_Znth by tauto.
  entailer!.
Qed.

Lemma ptr_array_strategy3_correctness : ptr_array_strategy3.
  pre_process_default.
  simpl.
  sep_apply (PtrArray.missing_i_merge_to_full); [ | tauto].
  entailer!.
Qed.

Lemma ptr_array_strategy12_correctness : ptr_array_strategy12.
  pre_process_default.
  simpl.
  sep_apply (PtrArray.missing_i_merge_to_ceil); [ | tauto].
  entailer!.
Qed.
