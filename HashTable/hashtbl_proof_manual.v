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
    Exists h_callee_bucks (Znth (retval % 211) lh_2 0) nil l0.
    Exists l0 lh_2 b0_2 l_2.
    subst p.
    entailer!.
    sep_apply (store_map_split store_sll (retval % 211) (Znth (retval % 211) lh_2 0, l0) b0_2).
    unfold store_sll at 2.
    simpl.
    entailer!. 
    2: { apply Hb0. }
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

Admitted. 


Lemma proof_of_hashtbl_findref_entail_wit_4 : hashtbl_findref_entail_wit_4.
Proof. 
    pre_process.
    Exists h_bucks_2 p_next (l_prev_2++(p_current::nil)) l_resres.
    Exists l0_2 lh_2 b0_2 l_2.
    entailer!.

Admitted. 


Lemma proof_of_hashtbl_findref_return_wit_1 : hashtbl_findref_return_wit_1.
Proof. 
    pre_process.
    (* rewrite <-H2 in H6. *)
    rewrite <- derivable1_orp_intros2.
    Exists p_current.
    entailer!.
    sep_apply PtrArray.missing_i_merge_to_full.
    sep_apply (ptr_string_name p_current key_addr k_list_current).
    2: { lia. }
    2: { subst k_list_current. apply H6. }
    unfold store_hash_skeleton.
    sep_apply (store_map_merge store_name k_list_current p_current m H6).
    pose (lh' := update_nth_Z lh ind p_current).
    pose (b0' := update_b0_at b0 ind p_current lh').
    Exists l lh' b0' h_bucks.
    assert (NULL = 0). {reflexivity. } rewrite H19.
    entailer!.

Admitted. 

Lemma proof_of_hashtbl_findref_return_wit_2 : hashtbl_findref_return_wit_2.
Proof.
    pre_process.
    rewrite <- derivable1_orp_intros1.
    sep_apply sll_zero.
    sep_apply (sllseg_head (Znth ind lh 0) i_v l_prev).
    entailer!.
    + unfold store_hash_skeleton.
        Exists l lh b0 h_bucks.
        sep_apply PtrArray.missing_i_merge_to_full.
        rewrite replace_Znth_Znth.
        entailer!.
        2: {lia. }
        assert (NBUCK = 211). { reflexivity. }
        subst i_v.
        sep_apply sllseg_0_sll.
        subst l_res.
        rewrite app_nil_r in H7.
        subst l_prev.
        sep_apply (store_map_merge store_sll ind (Znth ind lh 0, l0) b0 H6).
        rewrite H14.
        entailer!.
        admit.
    + subst l_res.
        rewrite app_nil_r in H7.
        unfold contain_all_correct_addrs in H3.
        specialize (H3 (Znth ind lh 0) ind).
        rewrite H6 in H3.
        rewrite H7 in H3.
        specialize (H8 (Znth ind lh 0) k).
        destruct H12.
        - rewrite H11 in H8.
            simpl in *.
            admit.
        - pose proof H8 H11.

 Admitted. 

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
    destruct l_res.
    + simpl.
        Intros.
        assert (NULL = 0). { reflexivity. }
        rewrite H4 in H3.
        congruence.
    + simpl.
        Intros x.
        subst z.
        pose proof (in_elt i_v l_prev l_res).
        rewrite <- H2 in H4.
        unfold contain_all_correct_addrs in *.
        pose proof (H1 i_v ind).
        destruct H5.
        destruct H6.
        { exists (Znth ind lh 0), l0. split; [apply H0 | apply H4]. }
        destruct H6.
        sep_apply (store_map_split store_name x0 i_v m H6).
        unfold store_name at 2.
        Intros k_addr.
        Exists k_addr x l_res.
        Exists x0 i_v.
        entailer!.
Qed.

