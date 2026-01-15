Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import hashtbl_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Import naive_C_Rules.
Require Import hashtbl_lib.
Require Import hashtbl_lib.
Local Open Scope sac.
Require Import MapLib.

Lemma proof_of_hashtbl_findref_safety_wit_8 : hashtbl_findref_safety_wit_8.
Proof.
    pre_process.
Qed.

Lemma sll_nil_head: forall p,
    sll p nil |-- [|p = NULL|] && emp.
Proof.
    intros.
    simpl.
    entailer!.
Qed.

Lemma sll_back (p: Z): 
    p = NULL -> emp |-- sll p nil.
Proof.
    intros.
    simpl.
    entailer!.
Qed.


Lemma proof_of_hashtbl_findref_entail_wit_1 : hashtbl_findref_entail_wit_1.
Proof.
    pre_process.
    unfold repr_all_heads in H1.
    prop_apply (PtrArray.full_Zlength h_bucks 211 lh_2).
    rewrite (PtrArray.full_split_to_missing_i h_bucks (retval % 211) 211 lh_2 0).
    entailer!.
    Intros.
    pose proof H1 (retval % 211) (Znth (retval % 211) lh_2 0).
    assert (exists p, Znth (retval % 211) lh_2 0 = p) as [p Hp].
    { exists (Znth (retval % 211) lh_2 0); reflexivity. }
    assert (exists l, b0_2 (retval % 211) = Some (p, l)) as [l0 Hb0].
    {
      apply H1. split; auto.
      split.
      entailer!.
      rewrite <-H3.
      apply Z.rem_bound_pos.
      + subst retval.
        apply hash_string_in_range.
      + lia.
      + unfold Zlength in H3.
        unfold Zlength.
        assert (Zlength_aux 0 addr lh_2 = Zlength_aux 0 Z lh_2).
        {
            reflexivity.
        }
        rewrite H5.
        rewrite H3.
        apply Z.rem_bound_pos.
        - subst retval; apply hash_string_in_range.
        - lia.
    }
    destruct l0.
    + rewrite <- derivable1_orp_intros2.
    sep_apply (store_map_split store_sll (retval % 211) (p, nil) b0_2 Hb0).
    Exists h_bucks h_top_3 nil 0.
    Exists nil (Znth (retval % 211) lh_2 0).
    Exists nil lh_2 b0_2 l_2.
    entailer!.
    2: {
        subst p.
        entailer!.
    }
    2:{
        apply Z.rem_bound_pos; [ | lia].
        subst retval.
        apply hash_string_in_range.
    }
    2:{
        apply Z.rem_nonneg; [lia | ].
        subst retval.
        apply hash_string_in_range.
    }
    unfold store_sll at 2.
    simpl.
    entailer!.
    rewrite Hp.
    rewrite H5.
    rewrite <- logic_equiv_sepcon_emp.
    sepcon_lift (emp).
    rewrite (sll_back p); [ |tauto].
    sep_apply (store_map_merge store_sll (retval % 211) (p, nil) b0_2 ); [ | tauto] .
    entailer!.
Admitted.

Lemma proof_of_hashtbl_findref_entail_wit_4 : hashtbl_findref_entail_wit_4.
Proof. Admitted. 

Lemma proof_of_hashtbl_findref_return_wit_1 : hashtbl_findref_return_wit_1.
Proof. Admitted. 

Lemma proof_of_hashtbl_findref_return_wit_2 : hashtbl_findref_return_wit_2.
Proof. Admitted. 

Lemma proof_of_hashtbl_findref_return_wit_3 : hashtbl_findref_return_wit_3.
Proof. Admitted. 

Lemma proof_of_hashtbl_findref_which_implies_wit_1 : hashtbl_findref_which_implies_wit_1.
Proof. Admitted. 

Lemma proof_of_hashtbl_remove_entail_wit_1 : hashtbl_remove_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_hashtbl_remove_entail_wit_4 : hashtbl_remove_entail_wit_4.
Proof. Admitted. 

Lemma proof_of_hashtbl_remove_return_wit_1 : hashtbl_remove_return_wit_1.
Proof. Admitted. 

Lemma proof_of_hashtbl_remove_return_wit_2 : hashtbl_remove_return_wit_2.
Proof. Admitted. 

Lemma proof_of_hashtbl_remove_return_wit_3 : hashtbl_remove_return_wit_3.
Proof. Admitted. 

Lemma proof_of_hashtbl_remove_return_wit_4 : hashtbl_remove_return_wit_4.
Proof. Admitted. 

Lemma proof_of_hashtbl_remove_return_wit_5 : hashtbl_remove_return_wit_5.
Proof. Admitted. 

Lemma proof_of_hashtbl_remove_return_wit_6 : hashtbl_remove_return_wit_6.
Proof. Admitted. 

Lemma proof_of_hashtbl_remove_return_wit_7 : hashtbl_remove_return_wit_7.
Proof. Admitted. 

Lemma proof_of_hashtbl_remove_return_wit_8 : hashtbl_remove_return_wit_8.
Proof. Admitted. 

Lemma proof_of_hashtbl_remove_return_wit_9 : hashtbl_remove_return_wit_9.
Proof. Admitted. 

Lemma proof_of_hashtbl_remove_which_implies_wit_1 : hashtbl_remove_which_implies_wit_1.
Proof. Admitted. 

