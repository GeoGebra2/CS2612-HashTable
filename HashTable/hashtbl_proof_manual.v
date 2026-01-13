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

Lemma proof_of_hashtbl_findref_safety_wit_9 : hashtbl_findref_safety_wit_9.
Proof. 
    pre_process.
Qed.

Lemma proof_of_hashtbl_findref_entail_wit_1 : hashtbl_findref_entail_wit_1.
Proof. 
    pre_process.
    rewrite <- derivable1_orp_intros2.
    unfold repr_all_heads in H1.
    prop_apply (IntArray.full_Zlength h_bucks 211 lh_2).
    entailer!.
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
    Exists h_top_3 (m p) key_addr l_resres p.
    Exists buck .
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

