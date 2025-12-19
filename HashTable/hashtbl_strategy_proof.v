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
  pre_process_default.
Proof.
  simpl. unfold hashtbl_strategy0. reflexivity.
Qed.

Lemma hashtbl_strategy1_correctness : hashtbl_strategy1.
  pre_process_default.
Proof.
  simpl. unfold hashtbl_strategy1. reflexivity.
Qed.

Lemma hashtbl_strategy2_correctness : hashtbl_strategy2.
  pre_process_default.
Proof.
  Intros.
  rewrite H.
  simpl.
  entailer!.
Qed.

Lemma hashtbl_strategy3_correctness : hashtbl_strategy3.
  pre_process_default.
Proof.
  Intros.
  rewrite H.
  rewrite H0.
  reflexivity.
Qed.

Lemma hashtbl_strategy9_correctness : hashtbl_strategy9.
  pre_process_default.
Proof.
  Intros.
  rewrite H.
  simpl.
  entailer!.
Qed.

Lemma hashtbl_strategy10_correctness : hashtbl_strategy10.
  pre_process_default.
Proof.
  Intros.
  rewrite H.
  simpl.
  entailer!.
Qed.

Lemma hashtbl_strategy11_correctness : hashtbl_strategy11.
  pre_process_default.
Proof.
  Intros.
  rewrite H.
  simpl.
  entailer!.
Qed.

Lemma hashtbl_strategy12_correctness : hashtbl_strategy12.
  pre_process_default.
Proof.
  Intros.
  rewrite H.
  simpl.
  entailer!.
Qed.

Lemma hashtbl_strategy13_correctness : hashtbl_strategy13.
  pre_process_default.
Proof.
  entailer!.
  Intros_r l2.
  Intros_r v2.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
  subst.
  reflexivity.
Qed.
  
Lemma hashtbl_strategy14_correctness : hashtbl_strategy14.
  pre_process_default.
Proof.
  entailer!.
  Intros_r l2 r.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
  subst.
  reflexivity.
Qed.

Lemma hashtbl_strategy15_correctness : hashtbl_strategy15.
  pre_process_default.
Proof.
  rewrite <- logic_equiv_coq_prop_or.
  Intros.
  assert (p = 0) by (destruct H; congruence).
  clear H.
  subst p.
  entailer!.
  Intros_r l.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
  rewrite H.
  simpl sll.
  entailer!.
Qed.

Lemma hashtbl_strategy19_correctness : hashtbl_strategy19.
  pre_process_default.
Proof.
  Intros.
  rewrite H.
  simpl dll.
  entailer!.
Qed.

Lemma hashtbl_strategy22_correctness : hashtbl_strategy22.
  pre_process_default.
Proof.
  Intros.
  rewrite H, H0.
  simpl dllseg.
  entailer!.
Qed.

Lemma hashtbl_strategy26_correctness : hashtbl_strategy26.
  pre_process_default.
Proof.
  Intros.
  rewrite H.
  simpl sllseg.
  entailer!.
Qed.

Lemma hashtbl_strategy16_correctness : hashtbl_strategy16.
  pre_process_default.
Proof.
  rewrite <- logic_equiv_coq_prop_or.
  Intros.
  sep_apply (sll_not_zero p l).
  - Intros q l0.
    Exists p q l0.
    entailer!.
    rewrite <- logic_equiv_coq_prop_or.
    entailer!.
    rewrite <- derivable1_wand_sepcon_adjoint.
    entailer!.
  - assert (p <> 0) by (destruct H; congruence).
    unfold NULL.
    congruence.
Qed.


Lemma hashtbl_strategy17_correctness : hashtbl_strategy17.
  pre_process_default.
  Exists q.
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
Qed.

Lemma hashtbl_strategy4_correctness : hashtbl_strategy4.
  pre_process_default.
Proof.
  Intros.
  subst.
  reflexivity.
Qed.

Lemma hashtbl_strategy24_correctness : hashtbl_strategy24.
  pre_process_default.
Proof.
  Intros.
  subst.
  reflexivity.
Qed.

Lemma hashtbl_strategy25_correctness : hashtbl_strategy25.
  pre_process_default.
Proof.
  revert p.
  induction l; simpl sll; simpl sllseg; intros.
  - entailer!.
  - Intros y.
    Exists y.
    sep_apply IHl.
    entailer!.
Qed.

Lemma hashtbl_strategy18_correctness : hashtbl_strategy18.
  pre_process_default.
Proof.
  Intros.
  subst.
  reflexivity.
Qed.

Lemma hashtbl_strategy7_correctness : hashtbl_strategy7.
  pre_process_default.
Proof.
  Intros x0.
  Exists x0.
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
Qed.

Lemma hashtbl_strategy8_correctness : hashtbl_strategy8.
  pre_process_default.
Proof.
  Intros.
  Exists y.
  entailer!.
Qed.

Lemma hashtbl_strategy20_correctness : hashtbl_strategy20.
  pre_process_default.
Proof.
  rewrite <- logic_equiv_coq_prop_or.
  Intros.
  assert (p <> 0) by (destruct H; congruence).
  clear H.
  sep_apply (dll_not_zero p up l); [ | unfold NULL; exact H0 ].
  Intros down l0.
  Exists down l0.
  rewrite <- logic_equiv_coq_prop_or.
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
Qed.

Lemma hashtbl_strategy21_correctness : hashtbl_strategy21.
  pre_process_default.
Proof.
  rewrite <- logic_equiv_coq_prop_or.
  Intros.
  assert (p <> 0) by (destruct H; congruence).
  clear H.
  Exists (p :: l0).
  rewrite <- logic_equiv_coq_prop_or.
  entailer!.
  simpl dll.
  unfold NULL.
  Exists down.
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
Qed.

Lemma hashtbl_strategy23_correctness : hashtbl_strategy23.
  pre_process_default.
Proof.
  Intros.
  sep_apply (dllseg_head_neq x y x_up y_up l); [  | tauto ].
  Intros z l0.
  Exists z l0.
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
Qed.
  

Lemma hashtbl_strategy5_correctness : hashtbl_strategy5.
  pre_process_default.
  destruct l; simpl.
  + entailer!.
    rewrite <- logic_equiv_coq_prop_or.
    Intros.
    subst p.
    tauto.
  + Exists p l.
    Intros x.
    rewrite <- logic_equiv_coq_prop_or.
    Exists x.
    entailer!.
    Search derivable1.
    Intros.
    rewrite <- (derivable1_wand_sepcon_adjoint _ (TT &&
                                                      emp **
                                                      (&( p # "blist" ->ₛ "val") # Int |-> q
                                                      || &( p # "blist" ->ₛ "next") # Ptr |-> q))).
    

  entailer!.

Admitted.

Lemma hashtbl_strategy6_correctness : hashtbl_strategy6.
  pre_process_default.
  rewrite <- logic_equiv_coq_prop_or.
  Intros.
Admitted.
