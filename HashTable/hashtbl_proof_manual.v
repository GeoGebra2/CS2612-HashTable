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
Require Import hashtbl_lib.
Local Open Scope sac.
Require Import MapLib.

Lemma proof_of_hashtbl_findref_entail_wit_1 : hashtbl_findref_entail_wit_1.
Proof. 
    pre_process.
    prop_apply (PtrArray.full_Zlength h_callee_bucks 211 lh_2).
    rewrite (PtrArray.full_split_to_missing_i h_callee_bucks (retval % 211) 211 lh_2 0).
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
    Exists (Znth (retval % 211) lh_2 0) h_callee_bucks nil l0.
    Exists l0 lh_2 b0_2 l_2.
    subst p.
    entailer!.
    sep_apply (store_map_split store_sll (retval % 211) (Znth (retval % 211) lh_2 0, l0) b0_2).
    unfold store_sll at 2.
    simpl.
    entailer!. 
    2: { unfold not_key. intros. simpl in *. tauto. }
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
    2:{ rewrite H. reflexivity. }
    2:{
        apply Z.rem_bound_pos; [ | lia ].
        subst retval.
        apply hash_string_in_range.
    }
    apply Hb0.
Qed.


Lemma proof_of_hashtbl_findref_entail_wit_4 : hashtbl_findref_entail_wit_4.
Proof. Admitted. 

Lemma proof_of_hashtbl_findref_return_wit_1 : hashtbl_findref_return_wit_1.
Proof. Admitted. 

Lemma proof_of_hashtbl_findref_return_wit_2 : hashtbl_findref_return_wit_2.
Proof. Admitted. 

Lemma proof_of_hashtbl_findref_return_wit_3 : hashtbl_findref_return_wit_3.
Proof. Admitted. 

Lemma proof_of_hashtbl_findref_which_implies_wit_1 : hashtbl_findref_which_implies_wit_1.
Proof. 
    pre_process.
    unfold store_hash_skeleton.
    Intros l lh b buck.
    Exists buck lh b l.
    entailer!.
Qed. 

Lemma proof_of_hashtbl_findref_which_implies_wit_2 : hashtbl_findref_which_implies_wit_2.
Proof. 
    pre_process.
    unfold contain_all_correct_addrs in H2.
    pose proof H2 i_v ind; destruct H4.
    rewrite (sll_head i_v l_res H).
    Intros l_resres.
    destruct H5. { exists (Znth ind lh 0), l0. split; [apply H1 | ]. rewrite H3. rewrite H6. apply in_elt. }
    destruct H5.
    sep_apply (store_map_split store_name x i_v m H5).
    unfold store_name at 2.
    Intros i_v_key.
    subst l_res.
    simpl.
    Intros i_v_next.
    Exists i_v_key i_v_next l_resres x.
    entailer!.
Qed.

Lemma proof_of_hashtbl_findref_which_implies_wit_4 : hashtbl_findref_which_implies_wit_4.
Proof. 
    pre_process.
    destruct l_prev.
    + rewrite <-derivable1_orp_intros1.
        simpl.
        entailer!.
        rewrite H.
        rewrite H0.
        entailer!.
    + rewrite <- derivable1_orp_intros2.
        Exists z l_prev.
        entailer!.
        simpl.
        entailer!.
Qed.

