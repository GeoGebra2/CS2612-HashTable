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
From SimpleC.SL Require Import Mem SeparationLogic MapLib.
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
Proof. Admitted. 

Lemma proof_of_hashtbl_findref_entail_wit_4 : hashtbl_findref_entail_wit_4.
Proof. Admitted. 

Lemma proof_of_hashtbl_findref_return_wit_1 : hashtbl_findref_return_wit_1.
Proof. Admitted. 

Lemma proof_of_hashtbl_findref_return_wit_2 : hashtbl_findref_return_wit_2.
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

Lemma proof_of_hashtbl_free_blist_return_wit_1 : hashtbl_free_blist_return_wit_1.
Proof. Admitted. 

Lemma proof_of_hashtbl_free_blist_return_wit_2 : hashtbl_free_blist_return_wit_2.
Proof. pre_process. entailer!. rewrite H.
  sep_apply sll_zero.
  - entailer!. 
  simpl.
  entailer!.
  - entailer!.
Qed. 

Lemma proof_of_hashtbl_free_blist_which_implies_wit_1 : hashtbl_free_blist_which_implies_wit_1.
Proof. Admitted. 

Lemma proof_of_hashtbl_clear_entail_wit_1 : hashtbl_clear_entail_wit_1.
Proof. pre_process. Right.
(* 更完整的证明步骤 *)
assert (0 < 211) by lia.
prop_apply PtrArray.full_length.  (* 获取Zlength lh_2 = 211 *)
entailer!.
assert (0 <= 0 < Zlength lh_2) by (rewrite Zlength_correct; lia ).
(* 获取b 0的信息 *)
specialize (H0 0 (Znth 0 lh_2 0)).
destruct H0 as [H0_left H0_right].
assert (0 <= 0 < Zlength lh_2 /\ Znth 0 lh_2 0 = Znth 0 lh_2 0).
{ split; [lia|reflexivity]. }
assert (exists l : list addr, b_2 0 = Some (Znth 0 lh_2 0, l)) as Hex.
{apply H0_right. exact H0. }
destruct Hex as [li Hb].

(* 现在我们知道b 0 = Some (buck, li)，其中buck = Znth 0 lh_2 0 *)
sep_apply (store_map_split store_sll 0 (Znth 0 lh_2 0, li) b_2 Hb).

(* 从IntArray中提取指针 *)
sep_apply (PtrArray.full_split_to_missing_i h_bucks 0 211 lh_2 0).
2: { lia. }
sepcon_lift (store_sll 0 (Znth 0 lh_2 0, li)).
unfold store_sll.
Exists li.
Exists (Znth 0 lh_2 0).
Exists h_bucks.
Exists l_2.
Exists lh_2.
Exists b_2.
entailer!.
Qed.
 

Lemma proof_of_hashtbl_clear_entail_wit_2 : hashtbl_clear_entail_wit_2.
Proof. pre_process.
    assert (repr_all_heads lh_2 b_2).
    { exact H3. }
    assert (repr_all_heads lh_2 b_2).
    { exact H6. }
    destruct (Z_lt_ge_dec (i + 1) 211) as [Hlt | Hge].
    - Right.
      (* sepcon_lift (PtrArray.missing_i h_pre_bucks_3 i 0 211 lh_2).
      sepcon_lift ((h_pre_bucks_3 + i * sizeof ( PTR )) # Ptr |-> 0).
      sep_apply (PtrArray.missing_i_merge_to_full h_pre_bucks_3 i 211 0 lh_2). *)
      sepcon_lift (store_map_missing_i store_sll b_2 i).
      sep_apply (store_map_merge store_sll i (buck_i_2, nil) b_2).
      (* 2:{ specialize (H6 i buck_i_2). admit. } *)
      sepcon_lift (PtrArray.missing_i h_pre_bucks_3 i 0 211 lh_2).
      sepcon_lift ((h_pre_bucks_3 + i * sizeof ( PTR )) # Ptr |-> 0).
      prop_apply PtrArray.missing_i_length.
      entailer!.
      sep_apply (PtrArray.missing_i_merge_to_full h_pre_bucks_3 i 211 0 lh_2).
      (* assert ((replace_Znth i 0 lh_2) = lh_2).
      {admit. } *)
      2:{ lia. }
      assert (0 <= i < Zlength lh_2) by (rewrite Zlength_correct; lia ).
      specialize (H6 i (Znth i lh_2 0)).
      destruct H6 as [H6_left H6_right].
      assert (0 <= i < Zlength lh_2 /\ Znth i lh_2 0 = Znth i lh_2 0).
      { split; [exact H11|reflexivity]. }
      assert (exists l : list addr, b_2 i = Some (Znth i lh_2 0, l)) as Hex.
      {apply H6_right. exact H6. }
      destruct Hex as [li Hb].
      2:{ specialize (H6 i buck_i_2). admit. }
      prop_apply PtrArray.full_length.  (* 获取Zlength lh_2 = 211 *)
      entailer!.
      assert (0 <= (i+1) < Zlength lh_2) by (rewrite Zlength_correct; lia ).
      (* 获取b 0的信息 *)
      specialize (H7 (i+1) (Znth (i+1) lh_2 0)).
      destruct H7 as [H7_left H7_right].
      assert (0 <= (i+1) < Zlength lh_2 /\ Znth (i+1) lh_2 0 = Znth (i+1) lh_2 0).
      { split; [lia|reflexivity]. }
      assert (exists l : list addr, b_2 (i+1) = Some (Znth (i+1) lh_2 0, l)) as Hex_2.
      {apply H7_right. exact H7. }
      destruct Hex_2 as [li_2 Hb_2].

      (* 现在我们知道b 0 = Some (buck, li)，其中buck = Znth 0 lh_2 0 *)
      sep_apply (store_map_split store_sll (i+1) (Znth (i+1) lh_2 0, li_2) b_2 Hb_2).

      (* 从IntArray中提取指针 *)
      sep_apply (PtrArray.full_split_to_missing_i h_pre_bucks_3 (i+1) 211 (replace_Znth i 0 lh_2) 0).
      2: { lia. }
      sepcon_lift (store_sll (i + 1) (Znth (i + 1) lh_2 0, li_2)).
      unfold store_sll.
      Exists li_2.
      Exists (Znth (i + 1) lh_2 0).
      Exists h_pre_bucks_3.
      Exists l_2.
      Exists (replace_Znth i 0 lh_2).
      Exists b_2.
      entailer!.
      + rewrite Znth_replace_Znth_diff.
        reflexivity.
        lia.
      + apply repr_equal. 
        tauto.
    - Left.
      sepcon_lift (store_map_missing_i store_sll b_2 i).
      sep_apply (store_map_merge store_sll i (buck_i_2, nil) b_2).
      2:{ admit. }
      sepcon_lift (PtrArray.missing_i h_pre_bucks_3 i 0 211 lh_2).
      sepcon_lift ((h_pre_bucks_3 + i * sizeof ( PTR )) # Ptr |-> 0).
      sep_apply (PtrArray.missing_i_merge_to_full h_pre_bucks_3 i 211 0 lh_2).
      2:{ lia. }
      Exists h_pre_bucks_3.
      Exists l_2.
      Exists lh_2.
      Exists b_2.
      entailer!.
      sep_apply PtrArray.full_replace_nth; [ entailer! | lia ].
 Admitted. 

Lemma proof_of_hashtbl_clear_return_wit_1 : hashtbl_clear_return_wit_1.
Proof. pre_process. 
Admitted. 

Lemma proof_of_hashtbl_clear_which_implies_wit_1 : hashtbl_clear_which_implies_wit_1.
Proof. 
    pre_process. 
    unfold store_hash_skeleton. 
    Intros l lh b buck.
    Exists buck.
    Exists lh.
    Exists b.
    Exists l.
    entailer!.
Qed. 

