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

Lemma proof_of_hashtbl_findref_entail_wit_1 : hashtbl_findref_entail_wit_1.
Proof. 
    pre_process.
    unfold contain_all_addrs in *.
    unfold repr_all_heads in *.
    unfold contain_all_correct_addrs in *.
    prop_apply (IntArray.full_Zlength h_bucks 211 lh_2).
    entailer!.
    repeat rewrite derivable1_sepcon_assoc1 in *.
    assert (0 <= retval % 211 < 211) as Hrem.
    {entailer!. 
        + apply Z.rem_nonneg; [lia | ].
            subst retval.
            apply hash_string_in_range.
        + apply Z.rem_bound_pos; [ |lia].
            subst retval.
            apply hash_string_in_range.
            }
    assert (exists p, Znth (retval % 211) lh_2 0 = p) as [p Hp].
    { exists (Znth (retval % 211) lh_2 0); reflexivity. }
    assert (exists l, b0_2 (retval % 211) = Some (p, l)) as [l0 Hb0].
    { apply H1. split; auto.
      split.
      entailer!.
      rewrite <-H3.
      apply Z.rem_bound_pos.
      + subst retval.
        apply hash_string_in_range.
      + unfold Zlength in H3.
        unfold Zlength.
        assert (Zlength_aux 0 addr lh_2 = Zlength_aux 0 Z lh_2).
        {
            reflexivity.
        }
        rewrite H4.
        rewrite H3.
        lia.
     }
    Exists h_bucks key_pre h_top_2 p k.
    Exists l0 h_bucks l0 nil.
    Exists lh_2 b0_2 l_2.
    entailer!.
    3: {

    }
    unfold IntArray.full.
    Search store_array.
    rewrite (store_array_split_to_missing_i Z (fun (x : addr) (lo a : Z) =>
                                                (x + lo * sizeof ( INT )) # Int |-> a)
                                                h_bucks (retval%211) 211 lh_2 (h_bucks + retval % 211 * sizeof ( PTR ))).
    
    Search sepcon.
    (* repeat rewrite derivable1_sepcon_assoc1. *)
    entailer!.
Admitted. 

Lemma proof_of_hashtbl_findref_entail_wit_4 : hashtbl_findref_entail_wit_4.
Proof.
    pre_process.
    destruct l_res_2.
    + Exists buck k0 h_top i_v_2 k_list_2.
        Exists l_res_2 h_bucks_2 l0_2.
        Exists l_prev_2 lh_2 b0_2 l.

 Admitted. 

Lemma proof_of_hashtbl_findref_return_wit_1 : hashtbl_findref_return_wit_1.
Proof. Admitted. 

Lemma proof_of_hashtbl_findref_return_wit_2 : hashtbl_findref_return_wit_2.
Proof. Admitted. 

Lemma proof_of_hashtbl_findref_which_implies_wit_1 : hashtbl_findref_which_implies_wit_1.
Proof. Admitted. 

