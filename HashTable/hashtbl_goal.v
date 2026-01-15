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
Require Import common_strategy_goal.
Require Import common_strategy_proof.
Require Import hashtbl_strategy_goal.
Require Import hashtbl_strategy_proof.
From SimpleC.EE Require Import int_array_strategy_goal.
From SimpleC.EE Require Import int_array_strategy_proof.
From SimpleC.EE Require Import uint_array_strategy_goal.
From SimpleC.EE Require Import uint_array_strategy_proof.
From SimpleC.EE Require Import undef_uint_array_strategy_goal.
From SimpleC.EE Require Import undef_uint_array_strategy_proof.
From SimpleC.EE Require Import array_shape_strategy_goal.
From SimpleC.EE Require Import array_shape_strategy_proof.
Require Import hashtbl_strategy_goal.
Require Import hashtbl_strategy_proof.

(*----- Function hashtbl_findref -----*)

Definition hashtbl_findref_safety_wit_1 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (bucks: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (retval: Z) ,
  [| (retval = (hash_string_coq (k))) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m b ) |]
  &&  (store_string key_pre k )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  (IntArray.full &((h_pre)  # "hashtbl" ->ₛ "bucks") 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (store_map store_sll b )
  **  (store_map store_name m )
  **  ((( &( "i" ) )) # Ptr  |->_)
  **  ((( &( "ind" ) )) # UInt  |->_)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
|--
  [| (211 <> 0) |]
.

Definition hashtbl_findref_safety_wit_2 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (bucks: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (retval: Z) ,
  [| (retval = (hash_string_coq (k))) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m b ) |]
  &&  (store_string key_pre k )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  (IntArray.full &((h_pre)  # "hashtbl" ->ₛ "bucks") 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (store_map store_sll b )
  **  (store_map store_name m )
  **  ((( &( "i" ) )) # Ptr  |->_)
  **  ((( &( "ind" ) )) # UInt  |->_)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
|--
  [| (211 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 211) |]
.

Definition hashtbl_findref_safety_wit_3 := 
forall (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (h_bucks: Z) (h: Z) (i_v_key: Z) (k_list: (@list Z)) (i_v_next: Z) (l_res: (@list Z)) (buck: Z) (i_v: Z) (i: Z) (ind: Z) (key: Z) (l_prev: (@list Z)) ,
  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "i" ) )) # Ptr  |-> i)
  **  ((i) # Ptr  |-> i_v)
  **  (sllseg buck i_v l_prev )
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  (sll i_v_next l_res )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  (store_string i_v_key k_list )
  **  (store_string key k )
  **  (store_map store_name m )
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_findref_safety_wit_4 := 
forall (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (h_bucks: Z) (h: Z) (i_v_key: Z) (k_list: (@list Z)) (i_v_next: Z) (l_res: (@list Z)) (buck: Z) (i_v: Z) (i: Z) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((m (k)) <> (m (k_list))) |] 
  &&  [| (i_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  (store_string key k )
  **  (store_string i_v_key k_list )
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "i" ) )) # Ptr  |-> i)
  **  ((i) # Ptr  |-> i_v)
  **  (sllseg buck i_v l_prev )
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  (sll i_v_next l_res )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
|--
  [| False |]
.

Definition hashtbl_findref_safety_wit_5 := 
forall (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (h_bucks: Z) (h: Z) (i_v_key: Z) (k_list: (@list Z)) (i_v_next: Z) (l_res: (@list Z)) (buck: Z) (i_v: Z) (i: Z) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| ((m (k)) = (m (k_list))) |] 
  &&  [| (i_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  (store_string key k )
  **  (store_string i_v_key k_list )
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "i" ) )) # Ptr  |-> i)
  **  ((i) # Ptr  |-> i_v)
  **  (sllseg buck i_v l_prev )
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  (sll i_v_next l_res )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
|--
  [| False |]
.

Definition hashtbl_findref_safety_wit_6 := 
forall (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (h_bucks: Z) (h: Z) (i_v_key: Z) (k_list: (@list Z)) (i_v_next: Z) (l_res: (@list Z)) (buck: Z) (i_v: Z) (i: Z) (ind: Z) (key: Z) (l_prev: (@list Z)) ,
  [| (i_v = 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "i" ) )) # Ptr  |-> i)
  **  ((i) # Ptr  |-> i_v)
  **  (sllseg buck i_v l_prev )
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  (sll i_v_next l_res )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  (store_string i_v_key k_list )
  **  (store_string key k )
  **  (store_map store_name m )
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_findref_entail_wit_1 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (bucks: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (retval: Z) ,
  [| (retval = (hash_string_coq (k))) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m b ) |]
  &&  (store_string key_pre k )
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  (IntArray.full &((h_pre)  # "hashtbl" ->ₛ "bucks") 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (store_map store_sll b )
  **  (store_map store_name m )
|--
  EX (h_bucks: Z)  (i_v_key: Z)  (k_list: (@list Z))  (i_v_next: Z)  (l_res: (@list Z))  (buck: Z)  (i_v: Z)  (l_prev: (@list Z)) ,
  [| (not_key key_pre l_prev ) |] 
  &&  [| (0 <= (retval % ( 211 ) )) |] 
  &&  [| ((retval % ( 211 ) ) < 211) |]
  &&  (((bucks + ((retval % ( 211 ) ) * sizeof(PTR) ) )) # Ptr  |-> i_v)
  **  (sllseg buck i_v l_prev )
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  (sll i_v_next l_res )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  (store_string i_v_key k_list )
  **  (store_string key_pre k )
  **  (store_map store_name m )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + ((retval % ( 211 ) ) * sizeof(PTR) ) )) # Ptr  |-> buck)
.

Definition hashtbl_findref_entail_wit_2_1 := 
forall (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (h_bucks: Z) (h: Z) (i_v_key: Z) (k_list: (@list Z)) (i_v_next: Z) (l_res: (@list Z)) (buck: Z) (i_v: Z) (i: Z) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| ((m (k)) <> (m (k_list))) |] 
  &&  [| (i_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  (store_string key k )
  **  (store_string i_v_key k_list )
  **  ((i) # Ptr  |-> i_v)
  **  (sllseg buck i_v l_prev )
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  (sll i_v_next l_res )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
|--
  EX (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| ((m (k)) = (m (k_list))) |] 
  &&  [| (i_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  (store_string key k )
  **  (store_string i_v_key k_list )
  **  ((i) # Ptr  |-> i_v)
  **  (sllseg buck i_v l_prev )
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  (sll i_v_next l_res )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
.

Definition hashtbl_findref_entail_wit_2_2 := 
forall (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (h_bucks: Z) (h: Z) (i_v_key: Z) (k_list: (@list Z)) (i_v_next: Z) (l_res: (@list Z)) (buck: Z) (i_v: Z) (i: Z) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| ((m (k)) = (m (k_list))) |] 
  &&  [| (i_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  (store_string key k )
  **  (store_string i_v_key k_list )
  **  ((i) # Ptr  |-> i_v)
  **  (sllseg buck i_v l_prev )
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  (sll i_v_next l_res )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
|--
  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| ((m (k)) = (m (k_list))) |] 
  &&  [| (i_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  (store_string key k )
  **  (store_string i_v_key k_list )
  **  ((i) # Ptr  |-> i_v)
  **  (sllseg buck i_v l_prev )
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  (sll i_v_next l_res )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
.

Definition hashtbl_findref_entail_wit_3_1 := 
forall (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (h_bucks: Z) (h: Z) (i_v_key: Z) (k_list: (@list Z)) (i_v_next: Z) (l_res: (@list Z)) (buck: Z) (i_v: Z) (i: Z) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((m (k)) <> (m (k_list))) |] 
  &&  [| (i_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  (store_string key k )
  **  (store_string i_v_key k_list )
  **  ((i) # Ptr  |-> i_v)
  **  (sllseg buck i_v l_prev )
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  (sll i_v_next l_res )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
|--
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((m (k)) <> (m (k_list))) |] 
  &&  [| (i_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  (store_string key k )
  **  (store_string i_v_key k_list )
  **  ((i) # Ptr  |-> i_v)
  **  (sllseg buck i_v l_prev )
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  (sll i_v_next l_res )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
.

Definition hashtbl_findref_entail_wit_3_2 := 
forall (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (h_bucks: Z) (h: Z) (i_v_key: Z) (k_list: (@list Z)) (i_v_next: Z) (l_res: (@list Z)) (buck: Z) (i_v: Z) (i: Z) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval_2: Z) ,
  [| (retval_2 = 0) |] 
  &&  [| (retval_2 = 1) |] 
  &&  [| ((m (k)) = (m (k_list))) |] 
  &&  [| (i_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  (store_string key k )
  **  (store_string i_v_key k_list )
  **  ((i) # Ptr  |-> i_v)
  **  (sllseg buck i_v l_prev )
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  (sll i_v_next l_res )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
|--
  EX (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((m (k)) <> (m (k_list))) |] 
  &&  [| (i_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  (store_string key k )
  **  (store_string i_v_key k_list )
  **  ((i) # Ptr  |-> i_v)
  **  (sllseg buck i_v l_prev )
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  (sll i_v_next l_res )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
.

Definition hashtbl_findref_entail_wit_4 := 
forall (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (h_bucks_2: Z) (h: Z) (i_v_key_2: Z) (k_list_2: (@list Z)) (i_v_next_2: Z) (l_res_2: (@list Z)) (buck_2: Z) (i_v_2: Z) (i: Z) (ind: Z) (key: Z) (l_prev_2: (@list Z)) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((m (k)) <> (m (k_list_2))) |] 
  &&  [| (i_v_2 <> 0) |] 
  &&  [| (not_key key l_prev_2 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  (store_string key k )
  **  (store_string i_v_key_2 k_list_2 )
  **  ((i) # Ptr  |-> i_v_2)
  **  (sllseg buck_2 i_v_2 l_prev_2 )
  **  ((&((i_v_2)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next_2)
  **  (sll i_v_next_2 l_res_2 )
  **  ((&((i_v_2)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key_2)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks_2)
  **  (((h_bucks_2 + (ind * sizeof(PTR) ) )) # Ptr  |-> buck_2)
|--
  EX (h_bucks: Z)  (i_v_key: Z)  (k_list: (@list Z))  (i_v_next: Z)  (l_res: (@list Z))  (buck: Z)  (i_v: Z)  (l_prev: (@list Z)) ,
  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  ((&((i_v_2)  # "blist" ->ₛ "next")) # Ptr  |-> i_v)
  **  (sllseg buck i_v l_prev )
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  (sll i_v_next l_res )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  (store_string i_v_key k_list )
  **  (store_string key k )
  **  (store_map store_name m )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
.

Definition hashtbl_findref_return_wit_1 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (h_bucks: Z) (h: Z) (i_v_key: Z) (k_list: (@list Z)) (i_v_next: Z) (l_res: (@list Z)) (buck: Z) (i_v: Z) (i: Z) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| ((m (k)) = (m (k_list))) |] 
  &&  [| (i_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  (store_string key k )
  **  (store_string i_v_key k_list )
  **  ((i) # Ptr  |-> i_v_next)
  **  (sllseg buck i_v l_prev )
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> buck)
  **  (sll i_v_next l_res )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> i_v)
|--
  ([| ((m (k)) = None) |] 
  &&  [| (&((i_v)  # "blist" ->ₛ "val") = 0) |]
  &&  (store_hash_skeleton h_pre m )
  **  (store_string key_pre k ))
  ||
  (EX (p: Z) ,
  [| ((m (k)) = (Some (p))) |] 
  &&  [| (&((i_v)  # "blist" ->ₛ "val") = p) |]
  &&  (store_hash_skeleton h_pre m )
  **  (store_string key_pre k ))
.

Definition hashtbl_findref_return_wit_2 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (h_bucks: Z) (h: Z) (i_v_key: Z) (k_list: (@list Z)) (i_v_next: Z) (l_res: (@list Z)) (buck: Z) (i_v: Z) (i: Z) (ind: Z) (key: Z) (l_prev: (@list Z)) ,
  [| (i_v = 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  ((i) # Ptr  |-> i_v)
  **  (sllseg buck i_v l_prev )
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  (sll i_v_next l_res )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  (store_string i_v_key k_list )
  **  (store_string key k )
  **  (store_map store_name m )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
|--
  ([| ((m (k)) = None) |] 
  &&  [| (0 = 0) |]
  &&  (store_hash_skeleton h_pre m )
  **  (store_string key_pre k ))
  ||
  (EX (p: Z) ,
  [| ((m (k)) = (Some (p))) |] 
  &&  [| (0 = p) |]
  &&  (store_hash_skeleton h_pre m )
  **  (store_string key_pre k ))
.

Definition hashtbl_findref_partial_solve_wit_1 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) ,
  (store_hash_skeleton h_pre m )
  **  (store_string key_pre k )
|--
  (store_hash_skeleton h_pre m )
  **  (store_string key_pre k )
.

Definition hashtbl_findref_partial_solve_wit_2 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (bucks: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) ,
  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m b ) |]
  &&  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  (IntArray.full &((h_pre)  # "hashtbl" ->ₛ "bucks") 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (store_map store_sll b )
  **  (store_map store_name m )
  **  (store_string key_pre k )
|--
  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m b ) |]
  &&  (store_string key_pre k )
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  (IntArray.full &((h_pre)  # "hashtbl" ->ₛ "bucks") 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (store_map store_sll b )
  **  (store_map store_name m )
.

Definition hashtbl_findref_partial_solve_wit_3 := 
forall (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (h_bucks: Z) (h: Z) (i_v_key: Z) (k_list: (@list Z)) (i_v_next: Z) (l_res: (@list Z)) (buck: Z) (i_v: Z) (i: Z) (ind: Z) (key: Z) (l_prev: (@list Z)) ,
  [| (i_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  ((i) # Ptr  |-> i_v)
  **  (sllseg buck i_v l_prev )
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  (sll i_v_next l_res )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  (store_string i_v_key k_list )
  **  (store_string key k )
  **  (store_map store_name m )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
|--
  [| (i_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  (store_map store_name m )
  **  (store_string key k )
  **  (store_string i_v_key k_list )
  **  ((i) # Ptr  |-> i_v)
  **  (sllseg buck i_v l_prev )
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  (sll i_v_next l_res )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
.

Definition hashtbl_findref_which_implies_wit_1 := 
forall (m: ((@list Z) -> (@option Z))) (h: Z) ,
  (store_hash_skeleton h m )
|--
  EX (bucks: Z)  (lh: (@list Z))  (b: (Z -> (@option (Z * (@list Z)))))  (l: (@list Z)) ,
  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m b ) |]
  &&  (dll &((h)  # "hashtbl" ->ₛ "top") 0 l )
  **  (IntArray.full &((h)  # "hashtbl" ->ₛ "bucks") 211 lh )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (store_map store_sll b )
  **  (store_map store_name m )
.

(*----- Function hashtbl_remove -----*)

Definition hashtbl_remove_safety_wit_1 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (bucks: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (retval: Z) ,
  [| (retval = (hash_string_coq (k))) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| (map_composable m1 m2 ) |]
  &&  (store_string key_pre k )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  (IntArray.full &((h_pre)  # "hashtbl" ->ₛ "bucks") 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m1 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((( &( "it" ) )) # Ptr  |->_)
  **  ((( &( "ind" ) )) # UInt  |->_)
  **  ((( &( "removed" ) )) # Ptr  |-> removed_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  (store_map store_uint m2 )
  **  ((removed_pre) # Int  |->_)
|--
  [| (211 <> 0) |]
.

Definition hashtbl_remove_safety_wit_2 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (bucks: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (retval: Z) ,
  [| (retval = (hash_string_coq (k))) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| (map_composable m1 m2 ) |]
  &&  (store_string key_pre k )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  (IntArray.full &((h_pre)  # "hashtbl" ->ₛ "bucks") 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m1 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((( &( "it" ) )) # Ptr  |->_)
  **  ((( &( "ind" ) )) # UInt  |->_)
  **  ((( &( "removed" ) )) # Ptr  |-> removed_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  (store_map store_uint m2 )
  **  ((removed_pre) # Int  |->_)
|--
  [| (211 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 211) |]
.

Definition hashtbl_remove_safety_wit_3 := 
forall (k: (@list Z)) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_up_down: Z) (dl_down: (@list Z)) (it_v_down: Z) (it_v_up_up: Z) (dl_mid: (@list Z)) (h_top: Z) (it_v_up: Z) (dl_up: (@list Z)) (h_bucks: Z) (h: Z) (it_v_key: Z) (k_list: (@list Z)) (it_v_next: Z) (l_res: (@list Z)) (buck: Z) (it_v: Z) (it: Z) (ind: Z) (key: Z) (l_prev: (@list Z)) ,
  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> it_v_next)
  **  (sll it_v_next l_res )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key)
  **  (store_string it_v_key k_list )
  **  (store_string key k )
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  ((&((it_v_up)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  (dllseg it_v_up it_v_down it_v_up_up it_v dl_mid )
  **  (dll it_v_down it_v dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_remove_safety_wit_4 := 
forall (k: (@list Z)) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_up_down: Z) (dl_down: (@list Z)) (it_v_down: Z) (it_v_up_up: Z) (dl_mid: (@list Z)) (h_top: Z) (it_v_up: Z) (dl_up: (@list Z)) (h_bucks: Z) (h: Z) (it_v_key: Z) (k_list: (@list Z)) (it_v_next: Z) (l_res: (@list Z)) (buck: Z) (it_v: Z) (it: Z) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((m1 (k)) <> (m1 (k_list))) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  (store_string key k )
  **  (store_string it_v_key k_list )
  **  ((( &( "b" ) )) # Ptr  |-> it_v)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> it_v_next)
  **  (sll it_v_next l_res )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  ((&((it_v_up)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  (dllseg it_v_up it_v_down it_v_up_up it_v dl_mid )
  **  (dll it_v_down it_v dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
|--
  [| False |]
.

Definition hashtbl_remove_safety_wit_5 := 
forall (k: (@list Z)) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_up_down: Z) (dl_down: (@list Z)) (it_v_down: Z) (it_v_up_up: Z) (dl_mid: (@list Z)) (h_top: Z) (it_v_up: Z) (dl_up: (@list Z)) (h_bucks: Z) (h: Z) (it_v_key: Z) (k_list: (@list Z)) (it_v_next: Z) (l_res: (@list Z)) (buck: Z) (it_v: Z) (it: Z) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| ((m1 (k)) = (m1 (k_list))) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  (store_string key k )
  **  (store_string it_v_key k_list )
  **  ((( &( "b" ) )) # Ptr  |-> it_v)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> it_v_next)
  **  (sll it_v_next l_res )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  ((&((it_v_up)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  (dllseg it_v_up it_v_down it_v_up_up it_v dl_mid )
  **  (dll it_v_down it_v dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
|--
  [| False |]
.

Definition hashtbl_remove_safety_wit_6 := 
forall (k: (@list Z)) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_up_down: Z) (dl_down: (@list Z)) (it_v_down: Z) (it_v_up_up: Z) (dl_mid: (@list Z)) (h_top: Z) (it_v_up: Z) (dl_up: (@list Z)) (h_bucks: Z) (h: Z) (it_v_key: Z) (k_list: (@list Z)) (it_v_next: Z) (l_res: (@list Z)) (buck: Z) (it_v: Z) (it: Z) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| ((m1 (k)) = (m1 (k_list))) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  (store_string key k )
  **  (store_string it_v_key k_list )
  **  ((( &( "b" ) )) # Ptr  |-> it_v)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> it_v_next)
  **  (sll it_v_next l_res )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  ((&((it_v_up)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  (dllseg it_v_up it_v_down it_v_up_up it_v dl_mid )
  **  (dll it_v_down it_v dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_remove_safety_wit_7 := 
forall (k: (@list Z)) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_up_down: Z) (dl_down: (@list Z)) (it_v_down: Z) (it_v_up_up: Z) (dl_mid: (@list Z)) (h_top: Z) (it_v_up: Z) (dl_up: (@list Z)) (h_bucks: Z) (h: Z) (it_v_key: Z) (k_list: (@list Z)) (it_v_next: Z) (l_res: (@list Z)) (buck: Z) (it_v: Z) (it: Z) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| ((m1 (k)) = (m1 (k_list))) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  (store_string key k )
  **  (store_string it_v_key k_list )
  **  ((( &( "b" ) )) # Ptr  |-> it_v)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> it_v_next)
  **  (sll it_v_next l_res )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  ((&((it_v_up)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  (dllseg it_v_up it_v_down it_v_up_up it_v dl_mid )
  **  (dll it_v_down it_v dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_remove_safety_wit_8 := 
forall (k: (@list Z)) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_up_down: Z) (dl_down: (@list Z)) (it_v_down: Z) (it_v_up_up: Z) (dl_mid: (@list Z)) (h_top: Z) (it_v_up: Z) (dl_up: (@list Z)) (h_bucks: Z) (h: Z) (it_v_key: Z) (k_list: (@list Z)) (it_v_next: Z) (l_res: (@list Z)) (buck: Z) (it_v: Z) (it: Z) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (it_v_up <> 0) |] 
  &&  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| ((m1 (k)) = (m1 (k_list))) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  (store_string key k )
  **  (store_string it_v_key k_list )
  **  ((( &( "b" ) )) # Ptr  |-> it_v)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> it_v_next)
  **  (sll it_v_next l_res )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  ((&((it_v_up)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  (dllseg it_v_up it_v_down it_v_up_up it_v dl_mid )
  **  (dll it_v_down it_v dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_remove_safety_wit_9 := 
forall (k: (@list Z)) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_up_down: Z) (dl_down: (@list Z)) (it_v_down: Z) (it_v_up_up: Z) (dl_mid: (@list Z)) (h_top: Z) (it_v_up: Z) (dl_up: (@list Z)) (h_bucks: Z) (h: Z) (it_v_key: Z) (k_list: (@list Z)) (it_v_next: Z) (l_res: (@list Z)) (buck: Z) (it_v: Z) (it: Z) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (it_v_up <> 0) |] 
  &&  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| ((m1 (k)) = (m1 (k_list))) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  (store_string key k )
  **  (store_string it_v_key k_list )
  **  ((( &( "b" ) )) # Ptr  |-> it_v)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> it_v_next)
  **  (sll it_v_next l_res )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  ((&((it_v_up)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  (dllseg it_v_up it_v_down it_v_up_up it_v dl_mid )
  **  (dll it_v_down it_v dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_remove_safety_wit_10 := 
forall (k: (@list Z)) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_up_down: Z) (dl_down: (@list Z)) (it_v_down: Z) (it_v_up_up: Z) (dl_mid: (@list Z)) (h_top: Z) (it_v_up: Z) (dl_up: (@list Z)) (h_bucks: Z) (h: Z) (it_v_key: Z) (k_list: (@list Z)) (it_v_next: Z) (l_res: (@list Z)) (buck: Z) (it_v: Z) (it: Z) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (it_v_up = 0) |] 
  &&  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| ((m1 (k)) = (m1 (k_list))) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  (store_string key k )
  **  (store_string it_v_key k_list )
  **  ((( &( "b" ) )) # Ptr  |-> it_v)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> it_v_next)
  **  (sll it_v_next l_res )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  ((&((it_v_up)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  (dllseg it_v_up it_v_down it_v_up_up it_v dl_mid )
  **  (dll it_v_down it_v dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_remove_safety_wit_11 := 
forall (k: (@list Z)) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_up_down: Z) (dl_down: (@list Z)) (it_v_down: Z) (it_v_up_up: Z) (dl_mid: (@list Z)) (h_top: Z) (it_v_up: Z) (dl_up: (@list Z)) (h_bucks: Z) (h: Z) (it_v_key: Z) (k_list: (@list Z)) (it_v_next: Z) (l_res: (@list Z)) (buck: Z) (it_v: Z) (it: Z) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (it_v_up = 0) |] 
  &&  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| ((m1 (k)) = (m1 (k_list))) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  (store_string key k )
  **  (store_string it_v_key k_list )
  **  ((( &( "b" ) )) # Ptr  |-> it_v)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> it_v_next)
  **  (sll it_v_next l_res )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  ((&((it_v_up)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  (dllseg it_v_up it_v_down it_v_up_up it_v dl_mid )
  **  (dll it_v_down it_v dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_remove_safety_wit_12 := 
forall (k: (@list Z)) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_up_down: Z) (dl_down: (@list Z)) (it_v_down: Z) (it_v_up_up: Z) (dl_mid: (@list Z)) (h_top: Z) (it_v_up: Z) (dl_up: (@list Z)) (h_bucks: Z) (h: Z) (it_v_key: Z) (k_list: (@list Z)) (it_v_next: Z) (l_res: (@list Z)) (buck: Z) (it_v: Z) (it: Z) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) (z: Z) (l0: (@list Z)) ,
  [| (dl_up = (cons (h_top) (l0))) |] 
  &&  [| (it_v_down = 0) |] 
  &&  [| (it_v_up = 0) |] 
  &&  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| ((m1 (k)) = (m1 (k_list))) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  (dllseg z it_v h_top it_v_up l0 )
  **  ((&((h_top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((&((h_top)  # "blist" ->ₛ "down")) # Ptr  |-> z)
  **  ((( &( "res" ) )) # UInt  |-> val)
  **  (store_string key k )
  **  (store_string it_v_key k_list )
  **  ((( &( "b" ) )) # Ptr  |-> it_v)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> it_v_next)
  **  (sllseg buck it_v l_prev )
  **  (sll it_v_next l_res )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  ((&((it_v_up)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  (dllseg it_v_up it_v_down it_v_up_up it_v dl_mid )
  **  (dll it_v_down it_v dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition hashtbl_remove_safety_wit_13 := 
forall (k: (@list Z)) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_up_down: Z) (dl_down: (@list Z)) (it_v_down: Z) (it_v_up_up: Z) (dl_mid: (@list Z)) (h_top: Z) (it_v_up: Z) (dl_up: (@list Z)) (h_bucks: Z) (h: Z) (it_v_key: Z) (k_list: (@list Z)) (it_v_next: Z) (l_res: (@list Z)) (buck: Z) (it_v: Z) (it: Z) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (it_v_down = 0) |] 
  &&  [| (it_v_up = 0) |] 
  &&  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| ((m1 (k)) = (m1 (k_list))) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  ((( &( "res" ) )) # UInt  |-> val)
  **  (store_string key k )
  **  (store_string it_v_key k_list )
  **  ((( &( "b" ) )) # Ptr  |-> it_v)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> it_v_next)
  **  (sllseg buck it_v l_prev )
  **  (sll it_v_next l_res )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  ((&((it_v_up)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  (dllseg it_v_up it_v_down it_v_up_up it_v dl_mid )
  **  (dll it_v_down it_v dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition hashtbl_remove_safety_wit_14 := 
forall (k: (@list Z)) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_up_down: Z) (dl_down: (@list Z)) (it_v_down: Z) (it_v_up_up: Z) (dl_mid: (@list Z)) (h_top: Z) (it_v_up: Z) (dl_up: (@list Z)) (h_bucks: Z) (h: Z) (it_v_key: Z) (k_list: (@list Z)) (it_v_next: Z) (l_res: (@list Z)) (buck: Z) (it_v: Z) (it: Z) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (it_v_down = 0) |] 
  &&  [| (it_v_up <> 0) |] 
  &&  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| ((m1 (k)) = (m1 (k_list))) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  ((( &( "res" ) )) # UInt  |-> val)
  **  (store_string key k )
  **  (store_string it_v_key k_list )
  **  ((( &( "b" ) )) # Ptr  |-> it_v)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> it_v_next)
  **  (sllseg buck it_v l_prev )
  **  (sll it_v_next l_res )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  ((&((it_v_up)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  (dllseg it_v_up it_v_down it_v_up_up it_v dl_mid )
  **  (dll it_v_down it_v dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition hashtbl_remove_safety_wit_15 := 
forall (k: (@list Z)) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_up_down: Z) (dl_down: (@list Z)) (it_v_down: Z) (it_v_up_up: Z) (dl_mid: (@list Z)) (h_top: Z) (it_v_up: Z) (dl_up: (@list Z)) (h_bucks: Z) (h: Z) (it_v_key: Z) (k_list: (@list Z)) (it_v_next: Z) (l_res: (@list Z)) (buck: Z) (it_v: Z) (it: Z) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) (z: Z) (l0: (@list Z)) ,
  [| (dl_up = (cons (h_top) (l0))) |] 
  &&  [| (it_v_down = 0) |] 
  &&  [| (it_v_up <> 0) |] 
  &&  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| ((m1 (k)) = (m1 (k_list))) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  (dllseg z it_v h_top it_v_up l0 )
  **  ((&((h_top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((&((h_top)  # "blist" ->ₛ "down")) # Ptr  |-> z)
  **  ((( &( "res" ) )) # UInt  |-> val)
  **  (store_string key k )
  **  (store_string it_v_key k_list )
  **  ((( &( "b" ) )) # Ptr  |-> it_v)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> it_v_next)
  **  (sllseg buck it_v l_prev )
  **  (sll it_v_next l_res )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  ((&((it_v_up)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  (dllseg it_v_up it_v_down it_v_up_up it_v dl_mid )
  **  (dll it_v_down it_v dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition hashtbl_remove_safety_wit_16 := 
forall (k: (@list Z)) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_up_down: Z) (dl_down: (@list Z)) (it_v_down: Z) (it_v_up_up: Z) (dl_mid: (@list Z)) (h_top: Z) (it_v_up: Z) (dl_up: (@list Z)) (h_bucks: Z) (h: Z) (it_v_key: Z) (k_list: (@list Z)) (it_v_next: Z) (l_res: (@list Z)) (buck: Z) (it_v: Z) (it: Z) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) (z: Z) (l0: (@list Z)) ,
  [| (dl_up = (cons (h_top) (l0))) |] 
  &&  [| (it_v_down <> 0) |] 
  &&  [| (it_v_up <> 0) |] 
  &&  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| ((m1 (k)) = (m1 (k_list))) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  (dllseg z it_v h_top it_v_up l0 )
  **  ((&((h_top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((&((h_top)  # "blist" ->ₛ "down")) # Ptr  |-> z)
  **  ((( &( "res" ) )) # UInt  |-> val)
  **  (store_string key k )
  **  (store_string it_v_key k_list )
  **  ((( &( "b" ) )) # Ptr  |-> it_v)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> it_v_next)
  **  (sllseg buck it_v l_prev )
  **  (sll it_v_next l_res )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  ((&((it_v_up)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  (dllseg it_v_up it_v_down it_v_up_up it_v dl_mid )
  **  (dll it_v_down it_v dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition hashtbl_remove_safety_wit_17 := 
forall (k: (@list Z)) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_up_down: Z) (dl_down: (@list Z)) (it_v_down: Z) (it_v_up_up: Z) (dl_mid: (@list Z)) (h_top: Z) (it_v_up: Z) (dl_up: (@list Z)) (h_bucks: Z) (h: Z) (it_v_key: Z) (k_list: (@list Z)) (it_v_next: Z) (l_res: (@list Z)) (buck: Z) (it_v: Z) (it: Z) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (it_v_down <> 0) |] 
  &&  [| (it_v_up <> 0) |] 
  &&  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| ((m1 (k)) = (m1 (k_list))) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  ((( &( "res" ) )) # UInt  |-> val)
  **  (store_string key k )
  **  (store_string it_v_key k_list )
  **  ((( &( "b" ) )) # Ptr  |-> it_v)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> it_v_next)
  **  (sllseg buck it_v l_prev )
  **  (sll it_v_next l_res )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  ((&((it_v_up)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  (dllseg it_v_up it_v_down it_v_up_up it_v dl_mid )
  **  (dll it_v_down it_v dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition hashtbl_remove_safety_wit_18 := 
forall (k: (@list Z)) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_up_down: Z) (dl_down: (@list Z)) (it_v_down: Z) (it_v_up_up: Z) (dl_mid: (@list Z)) (h_top: Z) (it_v_up: Z) (dl_up: (@list Z)) (h_bucks: Z) (h: Z) (it_v_key: Z) (k_list: (@list Z)) (it_v_next: Z) (l_res: (@list Z)) (buck: Z) (it_v: Z) (it: Z) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (it_v_down <> 0) |] 
  &&  [| (it_v_up = 0) |] 
  &&  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| ((m1 (k)) = (m1 (k_list))) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  ((( &( "res" ) )) # UInt  |-> val)
  **  (store_string key k )
  **  (store_string it_v_key k_list )
  **  ((( &( "b" ) )) # Ptr  |-> it_v)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> it_v_next)
  **  (sllseg buck it_v l_prev )
  **  (sll it_v_next l_res )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  ((&((it_v_up)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  (dllseg it_v_up it_v_down it_v_up_up it_v dl_mid )
  **  (dll it_v_down it_v dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition hashtbl_remove_safety_wit_19 := 
forall (k: (@list Z)) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_up_down: Z) (dl_down: (@list Z)) (it_v_down: Z) (it_v_up_up: Z) (dl_mid: (@list Z)) (h_top: Z) (it_v_up: Z) (dl_up: (@list Z)) (h_bucks: Z) (h: Z) (it_v_key: Z) (k_list: (@list Z)) (it_v_next: Z) (l_res: (@list Z)) (buck: Z) (it_v: Z) (it: Z) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) (z: Z) (l0: (@list Z)) ,
  [| (dl_up = (cons (h_top) (l0))) |] 
  &&  [| (it_v_down <> 0) |] 
  &&  [| (it_v_up = 0) |] 
  &&  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| ((m1 (k)) = (m1 (k_list))) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  (dllseg z it_v h_top it_v_up l0 )
  **  ((&((h_top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((&((h_top)  # "blist" ->ₛ "down")) # Ptr  |-> z)
  **  ((( &( "res" ) )) # UInt  |-> val)
  **  (store_string key k )
  **  (store_string it_v_key k_list )
  **  ((( &( "b" ) )) # Ptr  |-> it_v)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> it_v_next)
  **  (sllseg buck it_v l_prev )
  **  (sll it_v_next l_res )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  ((&((it_v_up)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  (dllseg it_v_up it_v_down it_v_up_up it_v dl_mid )
  **  (dll it_v_down it_v dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition hashtbl_remove_safety_wit_20 := 
forall (k: (@list Z)) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_up_down: Z) (dl_down: (@list Z)) (it_v_down: Z) (it_v_up_up: Z) (dl_mid: (@list Z)) (h_top: Z) (it_v_up: Z) (dl_up: (@list Z)) (h_bucks: Z) (h: Z) (it_v_key: Z) (k_list: (@list Z)) (it_v_next: Z) (l_res: (@list Z)) (buck: Z) (it_v: Z) (it: Z) (ind: Z) (key: Z) (l_prev: (@list Z)) ,
  [| (it_v = 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> it_v_next)
  **  (sll it_v_next l_res )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key)
  **  (store_string it_v_key k_list )
  **  (store_string key k )
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  ((&((it_v_up)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  (dllseg it_v_up it_v_down it_v_up_up it_v dl_mid )
  **  (dll it_v_down it_v dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_remove_safety_wit_21 := 
forall (k: (@list Z)) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_up_down: Z) (dl_down: (@list Z)) (it_v_down: Z) (it_v_up_up: Z) (dl_mid: (@list Z)) (h_top: Z) (it_v_up: Z) (dl_up: (@list Z)) (h_bucks: Z) (h: Z) (it_v_key: Z) (k_list: (@list Z)) (it_v_next: Z) (l_res: (@list Z)) (buck: Z) (it_v: Z) (it: Z) (ind: Z) (key: Z) (l_prev: (@list Z)) ,
  [| (it_v = 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> it_v_next)
  **  (sll it_v_next l_res )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key)
  **  (store_string it_v_key k_list )
  **  (store_string key k )
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  ((&((it_v_up)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  (dllseg it_v_up it_v_down it_v_up_up it_v dl_mid )
  **  (dll it_v_down it_v dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |-> 0)
  **  (store_map store_name m1 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_remove_entail_wit_1 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (bucks: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (retval: Z) ,
  [| (retval = (hash_string_coq (k))) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| (map_composable m1 m2 ) |]
  &&  (store_string key_pre k )
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  (IntArray.full &((h_pre)  # "hashtbl" ->ₛ "bucks") 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m1 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (store_map store_uint m2 )
  **  ((removed_pre) # Int  |->_)
|--
  EX (val: Z)  (it_v_down_up: Z)  (it_v_up_down: Z)  (dl_down: (@list Z))  (it_v_down: Z)  (it_v_up_up: Z)  (dl_mid: (@list Z))  (h_top: Z)  (it_v_up: Z)  (dl_up: (@list Z))  (h_bucks: Z)  (it_v_key: Z)  (k_list: (@list Z))  (it_v_next: Z)  (l_res: (@list Z))  (buck: Z)  (it_v: Z)  (l_prev: (@list Z)) ,
  [| (not_key key_pre l_prev ) |] 
  &&  [| (0 <= (retval % ( 211 ) )) |] 
  &&  [| ((retval % ( 211 ) ) < 211) |]
  &&  (((bucks + ((retval % ( 211 ) ) * sizeof(PTR) ) )) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> it_v_next)
  **  (sll it_v_next l_res )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key)
  **  (store_string it_v_key k_list )
  **  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + ((retval % ( 211 ) ) * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  ((&((it_v_up)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  (dllseg it_v_up it_v_down it_v_up_up it_v dl_mid )
  **  (dll it_v_down it_v dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((removed_pre) # Int  |->_)
  **  (store_map store_name m1 )
.

Definition hashtbl_remove_entail_wit_2_1 := 
forall (k: (@list Z)) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_up_down: Z) (dl_down: (@list Z)) (it_v_down: Z) (it_v_up_up: Z) (dl_mid: (@list Z)) (h_top: Z) (it_v_up: Z) (dl_up: (@list Z)) (h_bucks: Z) (h: Z) (it_v_key: Z) (k_list: (@list Z)) (it_v_next: Z) (l_res: (@list Z)) (buck: Z) (it_v: Z) (it: Z) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| ((m1 (k)) <> (m1 (k_list))) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  (store_string key k )
  **  (store_string it_v_key k_list )
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> it_v_next)
  **  (sll it_v_next l_res )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  ((&((it_v_up)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  (dllseg it_v_up it_v_down it_v_up_up it_v dl_mid )
  **  (dll it_v_down it_v dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((removed) # Int  |->_)
|--
  EX (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| ((m1 (k)) = (m1 (k_list))) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  (store_string key k )
  **  (store_string it_v_key k_list )
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> it_v_next)
  **  (sll it_v_next l_res )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  ((&((it_v_up)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  (dllseg it_v_up it_v_down it_v_up_up it_v dl_mid )
  **  (dll it_v_down it_v dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((removed) # Int  |->_)
.

Definition hashtbl_remove_entail_wit_2_2 := 
forall (k: (@list Z)) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_up_down: Z) (dl_down: (@list Z)) (it_v_down: Z) (it_v_up_up: Z) (dl_mid: (@list Z)) (h_top: Z) (it_v_up: Z) (dl_up: (@list Z)) (h_bucks: Z) (h: Z) (it_v_key: Z) (k_list: (@list Z)) (it_v_next: Z) (l_res: (@list Z)) (buck: Z) (it_v: Z) (it: Z) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| ((m1 (k)) = (m1 (k_list))) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  (store_string key k )
  **  (store_string it_v_key k_list )
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> it_v_next)
  **  (sll it_v_next l_res )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  ((&((it_v_up)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  (dllseg it_v_up it_v_down it_v_up_up it_v dl_mid )
  **  (dll it_v_down it_v dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((removed) # Int  |->_)
|--
  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| ((m1 (k)) = (m1 (k_list))) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  (store_string key k )
  **  (store_string it_v_key k_list )
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> it_v_next)
  **  (sll it_v_next l_res )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  ((&((it_v_up)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  (dllseg it_v_up it_v_down it_v_up_up it_v dl_mid )
  **  (dll it_v_down it_v dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((removed) # Int  |->_)
.

Definition hashtbl_remove_entail_wit_3_1 := 
forall (k: (@list Z)) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_up_down: Z) (dl_down: (@list Z)) (it_v_down: Z) (it_v_up_up: Z) (dl_mid: (@list Z)) (h_top: Z) (it_v_up: Z) (dl_up: (@list Z)) (h_bucks: Z) (h: Z) (it_v_key: Z) (k_list: (@list Z)) (it_v_next: Z) (l_res: (@list Z)) (buck: Z) (it_v: Z) (it: Z) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((m1 (k)) <> (m1 (k_list))) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  (store_string key k )
  **  (store_string it_v_key k_list )
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> it_v_next)
  **  (sll it_v_next l_res )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  ((&((it_v_up)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  (dllseg it_v_up it_v_down it_v_up_up it_v dl_mid )
  **  (dll it_v_down it_v dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((removed) # Int  |->_)
|--
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((m1 (k)) <> (m1 (k_list))) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  (store_string key k )
  **  (store_string it_v_key k_list )
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> it_v_next)
  **  (sll it_v_next l_res )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  ((&((it_v_up)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  (dllseg it_v_up it_v_down it_v_up_up it_v dl_mid )
  **  (dll it_v_down it_v dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((removed) # Int  |->_)
.

Definition hashtbl_remove_entail_wit_3_2 := 
forall (k: (@list Z)) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_up_down: Z) (dl_down: (@list Z)) (it_v_down: Z) (it_v_up_up: Z) (dl_mid: (@list Z)) (h_top: Z) (it_v_up: Z) (dl_up: (@list Z)) (h_bucks: Z) (h: Z) (it_v_key: Z) (k_list: (@list Z)) (it_v_next: Z) (l_res: (@list Z)) (buck: Z) (it_v: Z) (it: Z) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval_2: Z) ,
  [| (retval_2 = 0) |] 
  &&  [| (retval_2 = 1) |] 
  &&  [| ((m1 (k)) = (m1 (k_list))) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  (store_string key k )
  **  (store_string it_v_key k_list )
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> it_v_next)
  **  (sll it_v_next l_res )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  ((&((it_v_up)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  (dllseg it_v_up it_v_down it_v_up_up it_v dl_mid )
  **  (dll it_v_down it_v dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((removed) # Int  |->_)
|--
  EX (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((m1 (k)) <> (m1 (k_list))) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  (store_string key k )
  **  (store_string it_v_key k_list )
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> it_v_next)
  **  (sll it_v_next l_res )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  ((&((it_v_up)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  (dllseg it_v_up it_v_down it_v_up_up it_v dl_mid )
  **  (dll it_v_down it_v dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((removed) # Int  |->_)
.

Definition hashtbl_remove_entail_wit_4 := 
forall (k: (@list Z)) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val_2: Z) (it_v_down_up_2: Z) (it_v_up_down_2: Z) (dl_down_2: (@list Z)) (it_v_down_2: Z) (it_v_up_up_2: Z) (dl_mid_2: (@list Z)) (h_top_2: Z) (it_v_up_2: Z) (dl_up_2: (@list Z)) (h_bucks_2: Z) (h: Z) (it_v_key_2: Z) (k_list_2: (@list Z)) (it_v_next_2: Z) (l_res_2: (@list Z)) (buck_2: Z) (it_v_2: Z) (it: Z) (ind: Z) (key: Z) (l_prev_2: (@list Z)) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((m1 (k)) <> (m1 (k_list_2))) |] 
  &&  [| (it_v_2 <> 0) |] 
  &&  [| (not_key key l_prev_2 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  (store_string key k )
  **  (store_string it_v_key_2 k_list_2 )
  **  ((it) # Ptr  |-> it_v_2)
  **  (sllseg buck_2 it_v_2 l_prev_2 )
  **  ((&((it_v_2)  # "blist" ->ₛ "next")) # Ptr  |-> it_v_next_2)
  **  (sll it_v_next_2 l_res_2 )
  **  ((&((it_v_2)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key_2)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks_2)
  **  (((h_bucks_2 + (ind * sizeof(PTR) ) )) # Ptr  |-> buck_2)
  **  ((&((it_v_2)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_2)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top_2)
  **  (dllseg h_top_2 it_v_2 0 it_v_up_2 dl_up_2 )
  **  ((&((it_v_up_2)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up_2)
  **  ((&((it_v_2)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down_2)
  **  (dllseg it_v_up_2 it_v_down_2 it_v_up_up_2 it_v_2 dl_mid_2 )
  **  (dll it_v_down_2 it_v_2 dl_down_2 )
  **  ((&((it_v_up_2)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down_2)
  **  ((it_v_up_down_2) # Ptr  |-> it_v_2)
  **  ((&((it_v_down_2)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up_2)
  **  ((it_v_down_up_2) # Ptr  |-> it_v_2)
  **  ((&((it_v_2)  # "blist" ->ₛ "val")) # UInt  |-> val_2)
  **  ((removed) # Int  |->_)
|--
  EX (val: Z)  (it_v_down_up: Z)  (it_v_up_down: Z)  (dl_down: (@list Z))  (it_v_down: Z)  (it_v_up_up: Z)  (dl_mid: (@list Z))  (h_top: Z)  (it_v_up: Z)  (dl_up: (@list Z))  (h_bucks: Z)  (it_v_key: Z)  (k_list: (@list Z))  (it_v_next: Z)  (l_res: (@list Z))  (buck: Z)  (it_v: Z)  (l_prev: (@list Z)) ,
  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  ((&((it_v_2)  # "blist" ->ₛ "next")) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> it_v_next)
  **  (sll it_v_next l_res )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key)
  **  (store_string it_v_key k_list )
  **  (store_string key k )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  ((&((it_v_up)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  (dllseg it_v_up it_v_down it_v_up_up it_v dl_mid )
  **  (dll it_v_down it_v dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
.

Definition hashtbl_remove_return_wit_1 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_up_down: Z) (dl_down: (@list Z)) (it_v_down: Z) (it_v_up_up: Z) (dl_mid: (@list Z)) (h_top: Z) (it_v_up: Z) (dl_up: (@list Z)) (h_bucks: Z) (h: Z) (it_v_key: Z) (k_list: (@list Z)) (it_v_next: Z) (l_res: (@list Z)) (buck: Z) (it_v: Z) (it: Z) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) (z: Z) (l0: (@list Z)) ,
  [| (dl_up = (cons (h_top) (l0))) |] 
  &&  [| (it_v_down <> 0) |] 
  &&  [| (it_v_up = 0) |] 
  &&  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| ((m1 (k)) = (m1 (k_list))) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  (dllseg z it_v h_top it_v_up l0 )
  **  ((&((h_top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((&((h_top)  # "blist" ->ₛ "down")) # Ptr  |-> z)
  **  (store_string key k )
  **  (store_string it_v_key k_list )
  **  ((it) # Ptr  |-> it_v_next)
  **  (sllseg buck it_v l_prev )
  **  (sll it_v_next l_res )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  ((&((it_v_up)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  (dllseg it_v_up it_v_down it_v_up_up it_v dl_mid )
  **  (dll it_v_down it_v dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((removed) # Int  |-> 1)
|--
  ([| ((m1 (k)) = None) |] 
  &&  [| (val = 0) |]
  &&  (store_hash_skeleton h_pre (KP.remove_map (m1) (k)) )
  **  (store_string key_pre k )
  **  ((removed_pre) # Int  |-> 0)
  **  (store_map store_uint m2 ))
  ||
  (EX (key0: Z)  (v: Z)  (p: Z) ,
  [| ((m1 (k)) = (Some (&((p)  # "blist" ->ₛ "val")))) |] 
  &&  [| ((m2 (&((p)  # "blist" ->ₛ "val"))) = (Some (v))) |] 
  &&  [| (val = v) |]
  &&  (store_hash_skeleton h_pre (KP.remove_map (m1) (k)) )
  **  (store_string key_pre k )
  **  ((removed_pre) # Int  |-> 1)
  **  (store_map store_uint (PV.remove_map (m2) (p)) )
  **  ((&((p)  # "blist" ->ₛ "key")) # Ptr  |-> key0)
  **  (store_string key0 k )
  **  ((&((p)  # "blist" ->ₛ "up")) # Ptr  |->_)
  **  ((&((p)  # "blist" ->ₛ "down")) # Ptr  |->_)
  **  ((&((p)  # "blist" ->ₛ "next")) # Ptr  |->_)
  **  ((&((p)  # "blist" ->ₛ "val")) # UInt  |-> v))
.

Definition hashtbl_remove_return_wit_2 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_up_down: Z) (dl_down: (@list Z)) (it_v_down: Z) (it_v_up_up: Z) (dl_mid: (@list Z)) (h_top: Z) (it_v_up: Z) (dl_up: (@list Z)) (h_bucks: Z) (h: Z) (it_v_key: Z) (k_list: (@list Z)) (it_v_next: Z) (l_res: (@list Z)) (buck: Z) (it_v: Z) (it: Z) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (it_v_down <> 0) |] 
  &&  [| (it_v_up = 0) |] 
  &&  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| ((m1 (k)) = (m1 (k_list))) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  (store_string key k )
  **  (store_string it_v_key k_list )
  **  ((it) # Ptr  |-> it_v_next)
  **  (sllseg buck it_v l_prev )
  **  (sll it_v_next l_res )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  ((&((it_v_up)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  (dllseg it_v_up it_v_down it_v_up_up it_v dl_mid )
  **  (dll it_v_down it_v dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((removed) # Int  |-> 1)
|--
  ([| ((m1 (k)) = None) |] 
  &&  [| (val = 0) |]
  &&  (store_hash_skeleton h_pre (KP.remove_map (m1) (k)) )
  **  (store_string key_pre k )
  **  ((removed_pre) # Int  |-> 0)
  **  (store_map store_uint m2 ))
  ||
  (EX (key0: Z)  (v: Z)  (p: Z) ,
  [| ((m1 (k)) = (Some (&((p)  # "blist" ->ₛ "val")))) |] 
  &&  [| ((m2 (&((p)  # "blist" ->ₛ "val"))) = (Some (v))) |] 
  &&  [| (val = v) |]
  &&  (store_hash_skeleton h_pre (KP.remove_map (m1) (k)) )
  **  (store_string key_pre k )
  **  ((removed_pre) # Int  |-> 1)
  **  (store_map store_uint (PV.remove_map (m2) (p)) )
  **  ((&((p)  # "blist" ->ₛ "key")) # Ptr  |-> key0)
  **  (store_string key0 k )
  **  ((&((p)  # "blist" ->ₛ "up")) # Ptr  |->_)
  **  ((&((p)  # "blist" ->ₛ "down")) # Ptr  |->_)
  **  ((&((p)  # "blist" ->ₛ "next")) # Ptr  |->_)
  **  ((&((p)  # "blist" ->ₛ "val")) # UInt  |-> v))
.

Definition hashtbl_remove_return_wit_3 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_up_down: Z) (dl_down: (@list Z)) (it_v_down: Z) (it_v_up_up: Z) (dl_mid: (@list Z)) (h_top: Z) (it_v_up: Z) (dl_up: (@list Z)) (h_bucks: Z) (h: Z) (it_v_key: Z) (k_list: (@list Z)) (it_v_next: Z) (l_res: (@list Z)) (buck: Z) (it_v: Z) (it: Z) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (it_v_down <> 0) |] 
  &&  [| (it_v_up <> 0) |] 
  &&  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| ((m1 (k)) = (m1 (k_list))) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  (store_string key k )
  **  (store_string it_v_key k_list )
  **  ((it) # Ptr  |-> it_v_next)
  **  (sllseg buck it_v l_prev )
  **  (sll it_v_next l_res )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  ((&((it_v_up)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  (dllseg it_v_up it_v_down it_v_up_up it_v dl_mid )
  **  (dll it_v_down it_v dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((removed) # Int  |-> 1)
|--
  ([| ((m1 (k)) = None) |] 
  &&  [| (val = 0) |]
  &&  (store_hash_skeleton h_pre (KP.remove_map (m1) (k)) )
  **  (store_string key_pre k )
  **  ((removed_pre) # Int  |-> 0)
  **  (store_map store_uint m2 ))
  ||
  (EX (key0: Z)  (v: Z)  (p: Z) ,
  [| ((m1 (k)) = (Some (&((p)  # "blist" ->ₛ "val")))) |] 
  &&  [| ((m2 (&((p)  # "blist" ->ₛ "val"))) = (Some (v))) |] 
  &&  [| (val = v) |]
  &&  (store_hash_skeleton h_pre (KP.remove_map (m1) (k)) )
  **  (store_string key_pre k )
  **  ((removed_pre) # Int  |-> 1)
  **  (store_map store_uint (PV.remove_map (m2) (p)) )
  **  ((&((p)  # "blist" ->ₛ "key")) # Ptr  |-> key0)
  **  (store_string key0 k )
  **  ((&((p)  # "blist" ->ₛ "up")) # Ptr  |->_)
  **  ((&((p)  # "blist" ->ₛ "down")) # Ptr  |->_)
  **  ((&((p)  # "blist" ->ₛ "next")) # Ptr  |->_)
  **  ((&((p)  # "blist" ->ₛ "val")) # UInt  |-> v))
.

Definition hashtbl_remove_return_wit_4 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_up_down: Z) (dl_down: (@list Z)) (it_v_down: Z) (it_v_up_up: Z) (dl_mid: (@list Z)) (h_top: Z) (it_v_up: Z) (dl_up: (@list Z)) (h_bucks: Z) (h: Z) (it_v_key: Z) (k_list: (@list Z)) (it_v_next: Z) (l_res: (@list Z)) (buck: Z) (it_v: Z) (it: Z) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) (z: Z) (l0: (@list Z)) ,
  [| (dl_up = (cons (h_top) (l0))) |] 
  &&  [| (it_v_down <> 0) |] 
  &&  [| (it_v_up <> 0) |] 
  &&  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| ((m1 (k)) = (m1 (k_list))) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  (dllseg z it_v h_top it_v_up l0 )
  **  ((&((h_top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((&((h_top)  # "blist" ->ₛ "down")) # Ptr  |-> z)
  **  (store_string key k )
  **  (store_string it_v_key k_list )
  **  ((it) # Ptr  |-> it_v_next)
  **  (sllseg buck it_v l_prev )
  **  (sll it_v_next l_res )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  ((&((it_v_up)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  (dllseg it_v_up it_v_down it_v_up_up it_v dl_mid )
  **  (dll it_v_down it_v dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((removed) # Int  |-> 1)
|--
  ([| ((m1 (k)) = None) |] 
  &&  [| (val = 0) |]
  &&  (store_hash_skeleton h_pre (KP.remove_map (m1) (k)) )
  **  (store_string key_pre k )
  **  ((removed_pre) # Int  |-> 0)
  **  (store_map store_uint m2 ))
  ||
  (EX (key0: Z)  (v: Z)  (p: Z) ,
  [| ((m1 (k)) = (Some (&((p)  # "blist" ->ₛ "val")))) |] 
  &&  [| ((m2 (&((p)  # "blist" ->ₛ "val"))) = (Some (v))) |] 
  &&  [| (val = v) |]
  &&  (store_hash_skeleton h_pre (KP.remove_map (m1) (k)) )
  **  (store_string key_pre k )
  **  ((removed_pre) # Int  |-> 1)
  **  (store_map store_uint (PV.remove_map (m2) (p)) )
  **  ((&((p)  # "blist" ->ₛ "key")) # Ptr  |-> key0)
  **  (store_string key0 k )
  **  ((&((p)  # "blist" ->ₛ "up")) # Ptr  |->_)
  **  ((&((p)  # "blist" ->ₛ "down")) # Ptr  |->_)
  **  ((&((p)  # "blist" ->ₛ "next")) # Ptr  |->_)
  **  ((&((p)  # "blist" ->ₛ "val")) # UInt  |-> v))
.

Definition hashtbl_remove_return_wit_5 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_up_down: Z) (dl_down: (@list Z)) (it_v_down: Z) (it_v_up_up: Z) (dl_mid: (@list Z)) (h_top: Z) (it_v_up: Z) (dl_up: (@list Z)) (h_bucks: Z) (h: Z) (it_v_key: Z) (k_list: (@list Z)) (it_v_next: Z) (l_res: (@list Z)) (buck: Z) (it_v: Z) (it: Z) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) (z: Z) (l0: (@list Z)) ,
  [| (dl_up = (cons (h_top) (l0))) |] 
  &&  [| (it_v_down = 0) |] 
  &&  [| (it_v_up <> 0) |] 
  &&  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| ((m1 (k)) = (m1 (k_list))) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  (dllseg z it_v h_top it_v_up l0 )
  **  ((&((h_top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((&((h_top)  # "blist" ->ₛ "down")) # Ptr  |-> z)
  **  (store_string key k )
  **  (store_string it_v_key k_list )
  **  ((it) # Ptr  |-> it_v_next)
  **  (sllseg buck it_v l_prev )
  **  (sll it_v_next l_res )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  ((&((it_v_up)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  (dllseg it_v_up it_v_down it_v_up_up it_v dl_mid )
  **  (dll it_v_down it_v dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((removed) # Int  |-> 1)
|--
  ([| ((m1 (k)) = None) |] 
  &&  [| (val = 0) |]
  &&  (store_hash_skeleton h_pre (KP.remove_map (m1) (k)) )
  **  (store_string key_pre k )
  **  ((removed_pre) # Int  |-> 0)
  **  (store_map store_uint m2 ))
  ||
  (EX (key0: Z)  (v: Z)  (p: Z) ,
  [| ((m1 (k)) = (Some (&((p)  # "blist" ->ₛ "val")))) |] 
  &&  [| ((m2 (&((p)  # "blist" ->ₛ "val"))) = (Some (v))) |] 
  &&  [| (val = v) |]
  &&  (store_hash_skeleton h_pre (KP.remove_map (m1) (k)) )
  **  (store_string key_pre k )
  **  ((removed_pre) # Int  |-> 1)
  **  (store_map store_uint (PV.remove_map (m2) (p)) )
  **  ((&((p)  # "blist" ->ₛ "key")) # Ptr  |-> key0)
  **  (store_string key0 k )
  **  ((&((p)  # "blist" ->ₛ "up")) # Ptr  |->_)
  **  ((&((p)  # "blist" ->ₛ "down")) # Ptr  |->_)
  **  ((&((p)  # "blist" ->ₛ "next")) # Ptr  |->_)
  **  ((&((p)  # "blist" ->ₛ "val")) # UInt  |-> v))
.

Definition hashtbl_remove_return_wit_6 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_up_down: Z) (dl_down: (@list Z)) (it_v_down: Z) (it_v_up_up: Z) (dl_mid: (@list Z)) (h_top: Z) (it_v_up: Z) (dl_up: (@list Z)) (h_bucks: Z) (h: Z) (it_v_key: Z) (k_list: (@list Z)) (it_v_next: Z) (l_res: (@list Z)) (buck: Z) (it_v: Z) (it: Z) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (it_v_down = 0) |] 
  &&  [| (it_v_up <> 0) |] 
  &&  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| ((m1 (k)) = (m1 (k_list))) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  (store_string key k )
  **  (store_string it_v_key k_list )
  **  ((it) # Ptr  |-> it_v_next)
  **  (sllseg buck it_v l_prev )
  **  (sll it_v_next l_res )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  ((&((it_v_up)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  (dllseg it_v_up it_v_down it_v_up_up it_v dl_mid )
  **  (dll it_v_down it_v dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((removed) # Int  |-> 1)
|--
  ([| ((m1 (k)) = None) |] 
  &&  [| (val = 0) |]
  &&  (store_hash_skeleton h_pre (KP.remove_map (m1) (k)) )
  **  (store_string key_pre k )
  **  ((removed_pre) # Int  |-> 0)
  **  (store_map store_uint m2 ))
  ||
  (EX (key0: Z)  (v: Z)  (p: Z) ,
  [| ((m1 (k)) = (Some (&((p)  # "blist" ->ₛ "val")))) |] 
  &&  [| ((m2 (&((p)  # "blist" ->ₛ "val"))) = (Some (v))) |] 
  &&  [| (val = v) |]
  &&  (store_hash_skeleton h_pre (KP.remove_map (m1) (k)) )
  **  (store_string key_pre k )
  **  ((removed_pre) # Int  |-> 1)
  **  (store_map store_uint (PV.remove_map (m2) (p)) )
  **  ((&((p)  # "blist" ->ₛ "key")) # Ptr  |-> key0)
  **  (store_string key0 k )
  **  ((&((p)  # "blist" ->ₛ "up")) # Ptr  |->_)
  **  ((&((p)  # "blist" ->ₛ "down")) # Ptr  |->_)
  **  ((&((p)  # "blist" ->ₛ "next")) # Ptr  |->_)
  **  ((&((p)  # "blist" ->ₛ "val")) # UInt  |-> v))
.

Definition hashtbl_remove_return_wit_7 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_up_down: Z) (dl_down: (@list Z)) (it_v_down: Z) (it_v_up_up: Z) (dl_mid: (@list Z)) (h_top: Z) (it_v_up: Z) (dl_up: (@list Z)) (h_bucks: Z) (h: Z) (it_v_key: Z) (k_list: (@list Z)) (it_v_next: Z) (l_res: (@list Z)) (buck: Z) (it_v: Z) (it: Z) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (it_v_down = 0) |] 
  &&  [| (it_v_up = 0) |] 
  &&  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| ((m1 (k)) = (m1 (k_list))) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  (store_string key k )
  **  (store_string it_v_key k_list )
  **  ((it) # Ptr  |-> it_v_next)
  **  (sllseg buck it_v l_prev )
  **  (sll it_v_next l_res )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  ((&((it_v_up)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  (dllseg it_v_up it_v_down it_v_up_up it_v dl_mid )
  **  (dll it_v_down it_v dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((removed) # Int  |-> 1)
|--
  ([| ((m1 (k)) = None) |] 
  &&  [| (val = 0) |]
  &&  (store_hash_skeleton h_pre (KP.remove_map (m1) (k)) )
  **  (store_string key_pre k )
  **  ((removed_pre) # Int  |-> 0)
  **  (store_map store_uint m2 ))
  ||
  (EX (key0: Z)  (v: Z)  (p: Z) ,
  [| ((m1 (k)) = (Some (&((p)  # "blist" ->ₛ "val")))) |] 
  &&  [| ((m2 (&((p)  # "blist" ->ₛ "val"))) = (Some (v))) |] 
  &&  [| (val = v) |]
  &&  (store_hash_skeleton h_pre (KP.remove_map (m1) (k)) )
  **  (store_string key_pre k )
  **  ((removed_pre) # Int  |-> 1)
  **  (store_map store_uint (PV.remove_map (m2) (p)) )
  **  ((&((p)  # "blist" ->ₛ "key")) # Ptr  |-> key0)
  **  (store_string key0 k )
  **  ((&((p)  # "blist" ->ₛ "up")) # Ptr  |->_)
  **  ((&((p)  # "blist" ->ₛ "down")) # Ptr  |->_)
  **  ((&((p)  # "blist" ->ₛ "next")) # Ptr  |->_)
  **  ((&((p)  # "blist" ->ₛ "val")) # UInt  |-> v))
.

Definition hashtbl_remove_return_wit_8 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_up_down: Z) (dl_down: (@list Z)) (it_v_down: Z) (it_v_up_up: Z) (dl_mid: (@list Z)) (h_top: Z) (it_v_up: Z) (dl_up: (@list Z)) (h_bucks: Z) (h: Z) (it_v_key: Z) (k_list: (@list Z)) (it_v_next: Z) (l_res: (@list Z)) (buck: Z) (it_v: Z) (it: Z) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) (z: Z) (l0: (@list Z)) ,
  [| (dl_up = (cons (h_top) (l0))) |] 
  &&  [| (it_v_down = 0) |] 
  &&  [| (it_v_up = 0) |] 
  &&  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| ((m1 (k)) = (m1 (k_list))) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  (dllseg z it_v h_top it_v_up l0 )
  **  ((&((h_top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((&((h_top)  # "blist" ->ₛ "down")) # Ptr  |-> z)
  **  (store_string key k )
  **  (store_string it_v_key k_list )
  **  ((it) # Ptr  |-> it_v_next)
  **  (sllseg buck it_v l_prev )
  **  (sll it_v_next l_res )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  ((&((it_v_up)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  (dllseg it_v_up it_v_down it_v_up_up it_v dl_mid )
  **  (dll it_v_down it_v dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((removed) # Int  |-> 1)
|--
  ([| ((m1 (k)) = None) |] 
  &&  [| (val = 0) |]
  &&  (store_hash_skeleton h_pre (KP.remove_map (m1) (k)) )
  **  (store_string key_pre k )
  **  ((removed_pre) # Int  |-> 0)
  **  (store_map store_uint m2 ))
  ||
  (EX (key0: Z)  (v: Z)  (p: Z) ,
  [| ((m1 (k)) = (Some (&((p)  # "blist" ->ₛ "val")))) |] 
  &&  [| ((m2 (&((p)  # "blist" ->ₛ "val"))) = (Some (v))) |] 
  &&  [| (val = v) |]
  &&  (store_hash_skeleton h_pre (KP.remove_map (m1) (k)) )
  **  (store_string key_pre k )
  **  ((removed_pre) # Int  |-> 1)
  **  (store_map store_uint (PV.remove_map (m2) (p)) )
  **  ((&((p)  # "blist" ->ₛ "key")) # Ptr  |-> key0)
  **  (store_string key0 k )
  **  ((&((p)  # "blist" ->ₛ "up")) # Ptr  |->_)
  **  ((&((p)  # "blist" ->ₛ "down")) # Ptr  |->_)
  **  ((&((p)  # "blist" ->ₛ "next")) # Ptr  |->_)
  **  ((&((p)  # "blist" ->ₛ "val")) # UInt  |-> v))
.

Definition hashtbl_remove_return_wit_9 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_up_down: Z) (dl_down: (@list Z)) (it_v_down: Z) (it_v_up_up: Z) (dl_mid: (@list Z)) (h_top: Z) (it_v_up: Z) (dl_up: (@list Z)) (h_bucks: Z) (h: Z) (it_v_key: Z) (k_list: (@list Z)) (it_v_next: Z) (l_res: (@list Z)) (buck: Z) (it_v: Z) (it: Z) (ind: Z) (key: Z) (l_prev: (@list Z)) ,
  [| (it_v = 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> it_v_next)
  **  (sll it_v_next l_res )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key)
  **  (store_string it_v_key k_list )
  **  (store_string key k )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  ((&((it_v_up)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  (dllseg it_v_up it_v_down it_v_up_up it_v dl_mid )
  **  (dll it_v_down it_v dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((removed) # Int  |-> 0)
  **  (store_map store_name m1 )
|--
  ([| ((m1 (k)) = None) |] 
  &&  [| (0 = 0) |]
  &&  (store_hash_skeleton h_pre (KP.remove_map (m1) (k)) )
  **  (store_string key_pre k )
  **  ((removed_pre) # Int  |-> 0)
  **  (store_map store_uint m2 ))
  ||
  (EX (key0: Z)  (v: Z)  (p: Z) ,
  [| ((m1 (k)) = (Some (&((p)  # "blist" ->ₛ "val")))) |] 
  &&  [| ((m2 (&((p)  # "blist" ->ₛ "val"))) = (Some (v))) |] 
  &&  [| (0 = v) |]
  &&  (store_hash_skeleton h_pre (KP.remove_map (m1) (k)) )
  **  (store_string key_pre k )
  **  ((removed_pre) # Int  |-> 1)
  **  (store_map store_uint (PV.remove_map (m2) (p)) )
  **  ((&((p)  # "blist" ->ₛ "key")) # Ptr  |-> key0)
  **  (store_string key0 k )
  **  ((&((p)  # "blist" ->ₛ "up")) # Ptr  |->_)
  **  ((&((p)  # "blist" ->ₛ "down")) # Ptr  |->_)
  **  ((&((p)  # "blist" ->ₛ "next")) # Ptr  |->_)
  **  ((&((p)  # "blist" ->ₛ "val")) # UInt  |-> v))
.

Definition hashtbl_remove_partial_solve_wit_1 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) ,
  [| (map_composable m1 m2 ) |]
  &&  (store_hash_skeleton h_pre m1 )
  **  (store_map store_uint m2 )
  **  (store_string key_pre k )
  **  ((removed_pre) # Int  |->_)
|--
  [| (map_composable m1 m2 ) |]
  &&  (store_hash_skeleton h_pre m1 )
  **  (store_map store_uint m2 )
  **  (store_string key_pre k )
  **  ((removed_pre) # Int  |->_)
.

Definition hashtbl_remove_partial_solve_wit_2 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (bucks: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) ,
  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| (map_composable m1 m2 ) |]
  &&  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  (IntArray.full &((h_pre)  # "hashtbl" ->ₛ "bucks") 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m1 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (store_map store_uint m2 )
  **  (store_string key_pre k )
  **  ((removed_pre) # Int  |->_)
|--
  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| (map_composable m1 m2 ) |]
  &&  (store_string key_pre k )
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  (IntArray.full &((h_pre)  # "hashtbl" ->ₛ "bucks") 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m1 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (store_map store_uint m2 )
  **  ((removed_pre) # Int  |->_)
.

Definition hashtbl_remove_partial_solve_wit_3 := 
forall (k: (@list Z)) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_up_down: Z) (dl_down: (@list Z)) (it_v_down: Z) (it_v_up_up: Z) (dl_mid: (@list Z)) (h_top: Z) (it_v_up: Z) (dl_up: (@list Z)) (h_bucks: Z) (h: Z) (it_v_key: Z) (k_list: (@list Z)) (it_v_next: Z) (l_res: (@list Z)) (buck: Z) (it_v: Z) (it: Z) (ind: Z) (key: Z) (l_prev: (@list Z)) ,
  [| (it_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> it_v_next)
  **  (sll it_v_next l_res )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key)
  **  (store_string it_v_key k_list )
  **  (store_string key k )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  ((&((it_v_up)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  (dllseg it_v_up it_v_down it_v_up_up it_v dl_mid )
  **  (dll it_v_down it_v dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
|--
  [| (it_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  (store_map store_name m1 )
  **  (store_string key k )
  **  (store_string it_v_key k_list )
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> it_v_next)
  **  (sll it_v_next l_res )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  ((&((it_v_up)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  (dllseg it_v_up it_v_down it_v_up_up it_v dl_mid )
  **  (dll it_v_down it_v dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((removed) # Int  |->_)
.

Definition hashtbl_remove_partial_solve_wit_4 := 
forall (k: (@list Z)) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_up_down: Z) (dl_down: (@list Z)) (it_v_down: Z) (it_v_up_up: Z) (dl_mid: (@list Z)) (h_top: Z) (it_v_up: Z) (dl_up: (@list Z)) (h_bucks: Z) (h: Z) (it_v_key: Z) (k_list: (@list Z)) (it_v_next: Z) (l_res: (@list Z)) (buck: Z) (it_v: Z) (it: Z) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (it_v_down <> 0) |] 
  &&  [| (it_v_up = 0) |] 
  &&  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| ((m1 (k)) = (m1 (k_list))) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  (store_string key k )
  **  (store_string it_v_key k_list )
  **  ((it) # Ptr  |-> it_v_next)
  **  (sllseg buck it_v l_prev )
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> it_v_next)
  **  (sll it_v_next l_res )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  ((&((it_v_up)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  (dllseg it_v_up it_v_down it_v_up_up it_v dl_mid )
  **  (dll it_v_down it_v dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((removed) # Int  |->_)
|--
  EX (l0: (@list Z))  (z: Z) ,
  [| (dl_up = (cons (h_top) (l0))) |] 
  &&  [| (it_v_down <> 0) |] 
  &&  [| (it_v_up = 0) |] 
  &&  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| ((m1 (k)) = (m1 (k_list))) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |->_)
  **  (dllseg z it_v h_top it_v_up l0 )
  **  ((&((h_top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((&((h_top)  # "blist" ->ₛ "down")) # Ptr  |-> z)
  **  (store_string key k )
  **  (store_string it_v_key k_list )
  **  ((it) # Ptr  |-> it_v_next)
  **  (sllseg buck it_v l_prev )
  **  (sll it_v_next l_res )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  ((&((it_v_up)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  (dllseg it_v_up it_v_down it_v_up_up it_v dl_mid )
  **  (dll it_v_down it_v dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((removed) # Int  |->_)
.

Definition hashtbl_remove_partial_solve_wit_5 := 
forall (k: (@list Z)) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_up_down: Z) (dl_down: (@list Z)) (it_v_down: Z) (it_v_up_up: Z) (dl_mid: (@list Z)) (h_top: Z) (it_v_up: Z) (dl_up: (@list Z)) (h_bucks: Z) (h: Z) (it_v_key: Z) (k_list: (@list Z)) (it_v_next: Z) (l_res: (@list Z)) (buck: Z) (it_v: Z) (it: Z) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (it_v_down <> 0) |] 
  &&  [| (it_v_up = 0) |] 
  &&  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| ((m1 (k)) = (m1 (k_list))) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  (store_string key k )
  **  (store_string it_v_key k_list )
  **  ((it) # Ptr  |-> it_v_next)
  **  (sllseg buck it_v l_prev )
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> it_v_next)
  **  (sll it_v_next l_res )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  ((&((it_v_up)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  (dllseg it_v_up it_v_down it_v_up_up it_v dl_mid )
  **  (dll it_v_down it_v dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((removed) # Int  |->_)
|--
  [| (it_v_down <> 0) |] 
  &&  [| (it_v_up = 0) |] 
  &&  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| ((m1 (k)) = (m1 (k_list))) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |->_)
  **  (store_string key k )
  **  (store_string it_v_key k_list )
  **  ((it) # Ptr  |-> it_v_next)
  **  (sllseg buck it_v l_prev )
  **  (sll it_v_next l_res )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  ((&((it_v_up)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  (dllseg it_v_up it_v_down it_v_up_up it_v dl_mid )
  **  (dll it_v_down it_v dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((removed) # Int  |->_)
.

Definition hashtbl_remove_partial_solve_wit_6 := 
forall (k: (@list Z)) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_up_down: Z) (dl_down: (@list Z)) (it_v_down: Z) (it_v_up_up: Z) (dl_mid: (@list Z)) (h_top: Z) (it_v_up: Z) (dl_up: (@list Z)) (h_bucks: Z) (h: Z) (it_v_key: Z) (k_list: (@list Z)) (it_v_next: Z) (l_res: (@list Z)) (buck: Z) (it_v: Z) (it: Z) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (it_v_down <> 0) |] 
  &&  [| (it_v_up <> 0) |] 
  &&  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| ((m1 (k)) = (m1 (k_list))) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  (store_string key k )
  **  (store_string it_v_key k_list )
  **  ((it) # Ptr  |-> it_v_next)
  **  (sllseg buck it_v l_prev )
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> it_v_next)
  **  (sll it_v_next l_res )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  ((&((it_v_up)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  (dllseg it_v_up it_v_down it_v_up_up it_v dl_mid )
  **  (dll it_v_down it_v dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((removed) # Int  |->_)
|--
  [| (it_v_down <> 0) |] 
  &&  [| (it_v_up <> 0) |] 
  &&  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| ((m1 (k)) = (m1 (k_list))) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |->_)
  **  (store_string key k )
  **  (store_string it_v_key k_list )
  **  ((it) # Ptr  |-> it_v_next)
  **  (sllseg buck it_v l_prev )
  **  (sll it_v_next l_res )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  ((&((it_v_up)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  (dllseg it_v_up it_v_down it_v_up_up it_v dl_mid )
  **  (dll it_v_down it_v dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((removed) # Int  |->_)
.

Definition hashtbl_remove_partial_solve_wit_7 := 
forall (k: (@list Z)) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_up_down: Z) (dl_down: (@list Z)) (it_v_down: Z) (it_v_up_up: Z) (dl_mid: (@list Z)) (h_top: Z) (it_v_up: Z) (dl_up: (@list Z)) (h_bucks: Z) (h: Z) (it_v_key: Z) (k_list: (@list Z)) (it_v_next: Z) (l_res: (@list Z)) (buck: Z) (it_v: Z) (it: Z) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (it_v_down <> 0) |] 
  &&  [| (it_v_up <> 0) |] 
  &&  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| ((m1 (k)) = (m1 (k_list))) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  (store_string key k )
  **  (store_string it_v_key k_list )
  **  ((it) # Ptr  |-> it_v_next)
  **  (sllseg buck it_v l_prev )
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> it_v_next)
  **  (sll it_v_next l_res )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  ((&((it_v_up)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  (dllseg it_v_up it_v_down it_v_up_up it_v dl_mid )
  **  (dll it_v_down it_v dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((removed) # Int  |->_)
|--
  EX (l0: (@list Z))  (z: Z) ,
  [| (dl_up = (cons (h_top) (l0))) |] 
  &&  [| (it_v_down <> 0) |] 
  &&  [| (it_v_up <> 0) |] 
  &&  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| ((m1 (k)) = (m1 (k_list))) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |->_)
  **  (dllseg z it_v h_top it_v_up l0 )
  **  ((&((h_top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((&((h_top)  # "blist" ->ₛ "down")) # Ptr  |-> z)
  **  (store_string key k )
  **  (store_string it_v_key k_list )
  **  ((it) # Ptr  |-> it_v_next)
  **  (sllseg buck it_v l_prev )
  **  (sll it_v_next l_res )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  ((&((it_v_up)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  (dllseg it_v_up it_v_down it_v_up_up it_v dl_mid )
  **  (dll it_v_down it_v dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((removed) # Int  |->_)
.

Definition hashtbl_remove_partial_solve_wit_8 := 
forall (k: (@list Z)) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_up_down: Z) (dl_down: (@list Z)) (it_v_down: Z) (it_v_up_up: Z) (dl_mid: (@list Z)) (h_top: Z) (it_v_up: Z) (dl_up: (@list Z)) (h_bucks: Z) (h: Z) (it_v_key: Z) (k_list: (@list Z)) (it_v_next: Z) (l_res: (@list Z)) (buck: Z) (it_v: Z) (it: Z) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (it_v_down = 0) |] 
  &&  [| (it_v_up <> 0) |] 
  &&  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| ((m1 (k)) = (m1 (k_list))) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  (store_string key k )
  **  (store_string it_v_key k_list )
  **  ((it) # Ptr  |-> it_v_next)
  **  (sllseg buck it_v l_prev )
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> it_v_next)
  **  (sll it_v_next l_res )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  ((&((it_v_up)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  (dllseg it_v_up it_v_down it_v_up_up it_v dl_mid )
  **  (dll it_v_down it_v dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((removed) # Int  |->_)
|--
  EX (l0: (@list Z))  (z: Z) ,
  [| (dl_up = (cons (h_top) (l0))) |] 
  &&  [| (it_v_down = 0) |] 
  &&  [| (it_v_up <> 0) |] 
  &&  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| ((m1 (k)) = (m1 (k_list))) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |->_)
  **  (dllseg z it_v h_top it_v_up l0 )
  **  ((&((h_top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((&((h_top)  # "blist" ->ₛ "down")) # Ptr  |-> z)
  **  (store_string key k )
  **  (store_string it_v_key k_list )
  **  ((it) # Ptr  |-> it_v_next)
  **  (sllseg buck it_v l_prev )
  **  (sll it_v_next l_res )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  ((&((it_v_up)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  (dllseg it_v_up it_v_down it_v_up_up it_v dl_mid )
  **  (dll it_v_down it_v dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((removed) # Int  |->_)
.

Definition hashtbl_remove_partial_solve_wit_9 := 
forall (k: (@list Z)) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_up_down: Z) (dl_down: (@list Z)) (it_v_down: Z) (it_v_up_up: Z) (dl_mid: (@list Z)) (h_top: Z) (it_v_up: Z) (dl_up: (@list Z)) (h_bucks: Z) (h: Z) (it_v_key: Z) (k_list: (@list Z)) (it_v_next: Z) (l_res: (@list Z)) (buck: Z) (it_v: Z) (it: Z) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (it_v_down = 0) |] 
  &&  [| (it_v_up <> 0) |] 
  &&  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| ((m1 (k)) = (m1 (k_list))) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  (store_string key k )
  **  (store_string it_v_key k_list )
  **  ((it) # Ptr  |-> it_v_next)
  **  (sllseg buck it_v l_prev )
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> it_v_next)
  **  (sll it_v_next l_res )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  ((&((it_v_up)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  (dllseg it_v_up it_v_down it_v_up_up it_v dl_mid )
  **  (dll it_v_down it_v dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((removed) # Int  |->_)
|--
  [| (it_v_down = 0) |] 
  &&  [| (it_v_up <> 0) |] 
  &&  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| ((m1 (k)) = (m1 (k_list))) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |->_)
  **  (store_string key k )
  **  (store_string it_v_key k_list )
  **  ((it) # Ptr  |-> it_v_next)
  **  (sllseg buck it_v l_prev )
  **  (sll it_v_next l_res )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  ((&((it_v_up)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  (dllseg it_v_up it_v_down it_v_up_up it_v dl_mid )
  **  (dll it_v_down it_v dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((removed) # Int  |->_)
.

Definition hashtbl_remove_partial_solve_wit_10 := 
forall (k: (@list Z)) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_up_down: Z) (dl_down: (@list Z)) (it_v_down: Z) (it_v_up_up: Z) (dl_mid: (@list Z)) (h_top: Z) (it_v_up: Z) (dl_up: (@list Z)) (h_bucks: Z) (h: Z) (it_v_key: Z) (k_list: (@list Z)) (it_v_next: Z) (l_res: (@list Z)) (buck: Z) (it_v: Z) (it: Z) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (it_v_down = 0) |] 
  &&  [| (it_v_up = 0) |] 
  &&  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| ((m1 (k)) = (m1 (k_list))) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  (store_string key k )
  **  (store_string it_v_key k_list )
  **  ((it) # Ptr  |-> it_v_next)
  **  (sllseg buck it_v l_prev )
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> it_v_next)
  **  (sll it_v_next l_res )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  ((&((it_v_up)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  (dllseg it_v_up it_v_down it_v_up_up it_v dl_mid )
  **  (dll it_v_down it_v dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((removed) # Int  |->_)
|--
  [| (it_v_down = 0) |] 
  &&  [| (it_v_up = 0) |] 
  &&  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| ((m1 (k)) = (m1 (k_list))) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |->_)
  **  (store_string key k )
  **  (store_string it_v_key k_list )
  **  ((it) # Ptr  |-> it_v_next)
  **  (sllseg buck it_v l_prev )
  **  (sll it_v_next l_res )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  ((&((it_v_up)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  (dllseg it_v_up it_v_down it_v_up_up it_v dl_mid )
  **  (dll it_v_down it_v dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((removed) # Int  |->_)
.

Definition hashtbl_remove_partial_solve_wit_11 := 
forall (k: (@list Z)) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_up_down: Z) (dl_down: (@list Z)) (it_v_down: Z) (it_v_up_up: Z) (dl_mid: (@list Z)) (h_top: Z) (it_v_up: Z) (dl_up: (@list Z)) (h_bucks: Z) (h: Z) (it_v_key: Z) (k_list: (@list Z)) (it_v_next: Z) (l_res: (@list Z)) (buck: Z) (it_v: Z) (it: Z) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (it_v_down = 0) |] 
  &&  [| (it_v_up = 0) |] 
  &&  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| ((m1 (k)) = (m1 (k_list))) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  (store_string key k )
  **  (store_string it_v_key k_list )
  **  ((it) # Ptr  |-> it_v_next)
  **  (sllseg buck it_v l_prev )
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> it_v_next)
  **  (sll it_v_next l_res )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  ((&((it_v_up)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  (dllseg it_v_up it_v_down it_v_up_up it_v dl_mid )
  **  (dll it_v_down it_v dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((removed) # Int  |->_)
|--
  EX (l0: (@list Z))  (z: Z) ,
  [| (dl_up = (cons (h_top) (l0))) |] 
  &&  [| (it_v_down = 0) |] 
  &&  [| (it_v_up = 0) |] 
  &&  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| ((m1 (k)) = (m1 (k_list))) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |]
  &&  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |->_)
  **  (dllseg z it_v h_top it_v_up l0 )
  **  ((&((h_top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((&((h_top)  # "blist" ->ₛ "down")) # Ptr  |-> z)
  **  (store_string key k )
  **  (store_string it_v_key k_list )
  **  ((it) # Ptr  |-> it_v_next)
  **  (sllseg buck it_v l_prev )
  **  (sll it_v_next l_res )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> it_v_key)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  ((&((it_v_up)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_up)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  (dllseg it_v_up it_v_down it_v_up_up it_v dl_mid )
  **  (dll it_v_down it_v dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((removed) # Int  |->_)
.

Definition hashtbl_remove_which_implies_wit_1 := 
forall (m1: ((@list Z) -> (@option Z))) (h: Z) ,
  (store_hash_skeleton h m1 )
|--
  EX (bucks: Z)  (lh: (@list Z))  (b: (Z -> (@option (Z * (@list Z)))))  (l: (@list Z)) ,
  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  (dll &((h)  # "hashtbl" ->ₛ "top") 0 l )
  **  (IntArray.full &((h)  # "hashtbl" ->ₛ "bucks") 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m1 )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
.

(*----- Function hashtbl_free_blist -----*)

Definition hashtbl_free_blist_safety_wit_1 := 
forall (bl_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (l: (@list Z)) (bl_pre_key: Z) ,
  [| (map_composable m1 m2 ) |]
  &&  ((( &( "bl" ) )) # Ptr  |-> bl_pre)
  **  (sll bl_pre l )
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  ((&((bl_pre)  # "blist" ->ₛ "key")) # Ptr  |-> bl_pre_key)
  **  (store_string bl_pre_key k )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_free_blist_return_wit_1 := 
forall (bl_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (bl_pre_key: Z) (k1: (@list Z)) (bl_next: Z) ,
  [| (map_composable (KP.remove_map (m1) (k1)) (PV.remove_map (m2) (bl_next)) ) |] 
  &&  [| (bl_next = 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (bl_pre <> 0) |] 
  &&  [| (map_composable m1 m2 ) |]
  &&  (store_map store_name (KP.remove_map ((KP.remove_map (m1) (k1))) (k)) )
  **  (store_map store_uint (PV.remove_map ((PV.remove_map (m2) (bl_next))) (bl_pre)) )
  **  ((&((bl_pre)  # "blist" ->ₛ "key")) # Ptr  |-> bl_pre_key)
|--
  [| (bl_pre = 0) |] 
  &&  [| (map_composable m1 m2 ) |]
  &&  (store_map store_name (KP.remove_map (m1) (k)) )
  **  (store_map store_uint (PV.remove_map (m2) (bl_pre)) )
.

Definition hashtbl_free_blist_return_wit_2 := 
forall (bl_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (l: (@list Z)) (bl_pre_key: Z) ,
  [| (bl_pre = 0) |] 
  &&  [| (map_composable m1 m2 ) |]
  &&  (sll bl_pre l )
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  ((&((bl_pre)  # "blist" ->ₛ "key")) # Ptr  |-> bl_pre_key)
  **  (store_string bl_pre_key k )
|--
  [| (bl_pre = 0) |] 
  &&  [| (map_composable m1 m2 ) |]
  &&  (store_map store_name (KP.remove_map (m1) (k)) )
  **  (store_map store_uint (PV.remove_map (m2) (bl_pre)) )
.

Definition hashtbl_free_blist_partial_solve_wit_1 := 
forall (bl_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (l: (@list Z)) (bl_pre_key: Z) ,
  [| (bl_pre <> 0) |] 
  &&  [| (map_composable m1 m2 ) |]
  &&  (sll bl_pre l )
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  ((&((bl_pre)  # "blist" ->ₛ "key")) # Ptr  |-> bl_pre_key)
  **  (store_string bl_pre_key k )
|--
  [| (bl_pre <> 0) |] 
  &&  [| (map_composable m1 m2 ) |]
  &&  (sll bl_pre l )
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  ((&((bl_pre)  # "blist" ->ₛ "key")) # Ptr  |-> bl_pre_key)
  **  (store_string bl_pre_key k )
.

Definition hashtbl_free_blist_partial_solve_wit_2_pure := 
forall (bl_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (bl_pre_key: Z) (bl_next_key: Z) (k1: (@list Z)) (bl_next: Z) (l1: (@list Z)) ,
  [| (bl_pre <> 0) |] 
  &&  [| (map_composable m1 m2 ) |]
  &&  ((( &( "bl" ) )) # Ptr  |-> bl_pre)
  **  ((&((bl_pre)  # "blist" ->ₛ "next")) # Ptr  |-> bl_next)
  **  (sll bl_next l1 )
  **  ((&((bl_next)  # "blist" ->ₛ "key")) # Ptr  |-> bl_next_key)
  **  (store_string bl_next_key k1 )
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  ((&((bl_pre)  # "blist" ->ₛ "key")) # Ptr  |-> bl_pre_key)
  **  (store_string bl_pre_key k )
|--
  [| (map_composable m1 m2 ) |]
.

Definition hashtbl_free_blist_partial_solve_wit_2_aux := 
forall (bl_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (bl_pre_key: Z) (bl_next_key: Z) (k1: (@list Z)) (bl_next: Z) (l1: (@list Z)) ,
  [| (bl_pre <> 0) |] 
  &&  [| (map_composable m1 m2 ) |]
  &&  ((&((bl_pre)  # "blist" ->ₛ "next")) # Ptr  |-> bl_next)
  **  (sll bl_next l1 )
  **  ((&((bl_next)  # "blist" ->ₛ "key")) # Ptr  |-> bl_next_key)
  **  (store_string bl_next_key k1 )
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  ((&((bl_pre)  # "blist" ->ₛ "key")) # Ptr  |-> bl_pre_key)
  **  (store_string bl_pre_key k )
|--
  [| (map_composable m1 m2 ) |] 
  &&  [| (bl_pre <> 0) |] 
  &&  [| (map_composable m1 m2 ) |]
  &&  (sll bl_next l1 )
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  ((&((bl_next)  # "blist" ->ₛ "key")) # Ptr  |-> bl_next_key)
  **  (store_string bl_next_key k1 )
  **  ((&((bl_pre)  # "blist" ->ₛ "next")) # Ptr  |-> bl_next)
  **  ((&((bl_pre)  # "blist" ->ₛ "key")) # Ptr  |-> bl_pre_key)
  **  (store_string bl_pre_key k )
.

Definition hashtbl_free_blist_partial_solve_wit_2 := hashtbl_free_blist_partial_solve_wit_2_pure -> hashtbl_free_blist_partial_solve_wit_2_aux.

Definition hashtbl_free_blist_partial_solve_wit_3_pure := 
forall (bl_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (bl_pre_key: Z) (k1: (@list Z)) (bl_next: Z) ,
  [| (bl_next = 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (bl_pre <> 0) |] 
  &&  [| (map_composable m1 m2 ) |]
  &&  (store_map store_name (KP.remove_map (m1) (k1)) )
  **  (store_map store_uint (PV.remove_map (m2) (bl_next)) )
  **  ((( &( "bl" ) )) # Ptr  |-> bl_pre)
  **  ((&((bl_pre)  # "blist" ->ₛ "next")) # Ptr  |-> bl_next)
  **  ((&((bl_pre)  # "blist" ->ₛ "key")) # Ptr  |-> bl_pre_key)
  **  (store_string bl_pre_key k )
|--
  [| (map_composable (KP.remove_map (m1) (k1)) (PV.remove_map (m2) (bl_next)) ) |]
.

Definition hashtbl_free_blist_partial_solve_wit_3_aux := 
forall (bl_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (bl_pre_key: Z) (k1: (@list Z)) (bl_next: Z) ,
  [| (bl_next = 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (bl_pre <> 0) |] 
  &&  [| (map_composable m1 m2 ) |]
  &&  (store_map store_name (KP.remove_map (m1) (k1)) )
  **  (store_map store_uint (PV.remove_map (m2) (bl_next)) )
  **  ((&((bl_pre)  # "blist" ->ₛ "next")) # Ptr  |-> bl_next)
  **  ((&((bl_pre)  # "blist" ->ₛ "key")) # Ptr  |-> bl_pre_key)
  **  (store_string bl_pre_key k )
|--
  [| (map_composable (KP.remove_map (m1) (k1)) (PV.remove_map (m2) (bl_next)) ) |] 
  &&  [| (bl_next = 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (bl_pre <> 0) |] 
  &&  [| (map_composable m1 m2 ) |]
  &&  (store_map store_name (KP.remove_map (m1) (k1)) )
  **  (store_map store_uint (PV.remove_map (m2) (bl_next)) )
  **  (store_string bl_pre_key k )
  **  ((&((bl_pre)  # "blist" ->ₛ "key")) # Ptr  |-> bl_pre_key)
  **  ((&((bl_pre)  # "blist" ->ₛ "next")) # Ptr  |-> bl_next)
.

Definition hashtbl_free_blist_partial_solve_wit_3 := hashtbl_free_blist_partial_solve_wit_3_pure -> hashtbl_free_blist_partial_solve_wit_3_aux.

Definition hashtbl_free_blist_partial_solve_wit_4 := 
forall (bl_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (bl_pre_key: Z) (k1: (@list Z)) (bl_next: Z) ,
  [| (map_composable (KP.remove_map (m1) (k1)) (PV.remove_map (m2) (bl_next)) ) |] 
  &&  [| (bl_next = 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (bl_pre <> 0) |] 
  &&  [| (map_composable m1 m2 ) |]
  &&  (store_map store_name (KP.remove_map ((KP.remove_map (m1) (k1))) (k)) )
  **  (store_map store_uint (PV.remove_map ((PV.remove_map (m2) (bl_next))) (bl_pre)) )
  **  ((&((bl_pre)  # "blist" ->ₛ "key")) # Ptr  |-> bl_pre_key)
  **  ((&((bl_pre)  # "blist" ->ₛ "next")) # Ptr  |-> bl_next)
|--
  [| (map_composable (KP.remove_map (m1) (k1)) (PV.remove_map (m2) (bl_next)) ) |] 
  &&  [| (bl_next = 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (bl_pre <> 0) |] 
  &&  [| (map_composable m1 m2 ) |]
  &&  ((&((bl_pre)  # "blist" ->ₛ "next")) # Ptr  |->_)
  **  (store_map store_name (KP.remove_map ((KP.remove_map (m1) (k1))) (k)) )
  **  (store_map store_uint (PV.remove_map ((PV.remove_map (m2) (bl_next))) (bl_pre)) )
  **  ((&((bl_pre)  # "blist" ->ₛ "key")) # Ptr  |-> bl_pre_key)
.

Definition hashtbl_free_blist_which_implies_wit_1 := 
forall (l: (@list Z)) (bl: Z) ,
  (sll bl l )
|--
  EX (bl_next_key: Z)  (k1: (@list Z))  (bl_next: Z)  (l1: (@list Z)) ,
  ((&((bl)  # "blist" ->ₛ "next")) # Ptr  |-> bl_next)
  **  (sll bl_next l1 )
  **  ((&((bl_next)  # "blist" ->ₛ "key")) # Ptr  |-> bl_next_key)
  **  (store_string bl_next_key k1 )
.

(*----- Function hashtbl_clear -----*)

Definition hashtbl_clear_safety_wit_1 := 
forall (h_pre: Z) (top: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) ,
  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| (map_composable m1 m2 ) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  (IntArray.full &((h_pre)  # "hashtbl" ->ₛ "bucks") 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_clear_safety_wit_2 := 
forall (h_pre: Z) (top: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) ,
  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| (map_composable m1 m2 ) |]
  &&  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  (IntArray.full &((h_pre)  # "hashtbl" ->ₛ "bucks") 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_clear_safety_wit_3 := 
forall (h_pre: Z) (top: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (i: Z) (h_pre_bucks: Z) (lh: (@list Z)) ,
  [| (map_composable m1 m2 ) |] 
  &&  [| (i >= 211) |]
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (IntArray.full h_pre_bucks 211 lh )
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (211 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 211) |]
.

Definition hashtbl_clear_safety_wit_4 := 
forall (h_pre: Z) (top: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (i: Z) (h_pre_bucks: Z) (lh: (@list Z)) ,
  [| (i < 211) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (i >= 211) |]
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (IntArray.full h_pre_bucks 211 lh )
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| False |]
.

Definition hashtbl_clear_safety_wit_5 := 
forall (h_pre: Z) (top: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (buck_key: Z) (k: (@list Z)) (li: (@list Z)) (buck: Z) (i: Z) (h_pre_bucks: Z) (lh: (@list Z)) ,
  [| (map_composable m1 m2 ) |] 
  &&  [| (i >= 0) |] 
  &&  [| (i < 211) |]
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (IntArray.full h_pre_bucks 211 lh )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  (((h_pre_bucks + (i * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (sll buck li )
  **  ((&((buck)  # "blist" ->ₛ "key")) # Ptr  |-> buck_key)
  **  (store_string buck_key k )
|--
  [| (211 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 211) |]
.

Definition hashtbl_clear_safety_wit_6 := 
forall (h_pre: Z) (top: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (buck_key: Z) (k: (@list Z)) (li: (@list Z)) (buck: Z) (i: Z) (h_pre_bucks: Z) (lh: (@list Z)) ,
  [| (i >= 211) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (i >= 0) |] 
  &&  [| (i < 211) |]
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (IntArray.full h_pre_bucks 211 lh )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  (((h_pre_bucks + (i * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (sll buck li )
  **  ((&((buck)  # "blist" ->ₛ "key")) # Ptr  |-> buck_key)
  **  (store_string buck_key k )
|--
  [| False |]
.

Definition hashtbl_clear_safety_wit_7 := 
forall (h_pre: Z) (top: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (buck_key: Z) (k: (@list Z)) (li: (@list Z)) (buck: Z) (i: Z) (h_pre_bucks: Z) (lh: (@list Z)) ,
  [| (i < 211) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (i >= 0) |] 
  &&  [| (i < 211) |]
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (IntArray.full h_pre_bucks 211 lh )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  (((h_pre_bucks + (i * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (sll buck li )
  **  ((&((buck)  # "blist" ->ₛ "key")) # Ptr  |-> buck_key)
  **  (store_string buck_key k )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_clear_safety_wit_8 := 
forall (h_pre: Z) (top: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (buck_key: Z) (k: (@list Z)) (li: (@list Z)) (buck: Z) (i: Z) (h_pre_bucks: Z) (lh: (@list Z)) ,
  [| (i < 0) |] 
  &&  [| (i < 211) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (i >= 0) |] 
  &&  [| (i < 211) |]
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (IntArray.full h_pre_bucks 211 lh )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  (((h_pre_bucks + (i * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (sll buck li )
  **  ((&((buck)  # "blist" ->ₛ "key")) # Ptr  |-> buck_key)
  **  (store_string buck_key k )
|--
  [| False |]
.

Definition hashtbl_clear_safety_wit_9 := 
forall (h_pre: Z) (top: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (k: (@list Z)) (buck: Z) (i: Z) (h_pre_bucks: Z) (lh: (@list Z)) ,
  [| (buck = 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (i >= 0) |] 
  &&  [| (i < 211) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (i >= 0) |] 
  &&  [| (i < 211) |]
  &&  (store_map store_name (KP.remove_map (m1) (k)) )
  **  (store_map store_uint (PV.remove_map (m2) (buck)) )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (IntArray.full h_pre_bucks 211 lh )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (((h_pre_bucks + (i * sizeof(PTR) ) )) # Ptr  |-> buck)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_clear_safety_wit_10 := 
forall (h_pre: Z) (top: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (k: (@list Z)) (buck: Z) (i: Z) (h_pre_bucks: Z) (lh: (@list Z)) ,
  [| (buck = 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (i >= 0) |] 
  &&  [| (i < 211) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (i >= 0) |] 
  &&  [| (i < 211) |]
  &&  (store_map store_name (KP.remove_map (m1) (k)) )
  **  (store_map store_uint (PV.remove_map (m2) (buck)) )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (IntArray.full h_pre_bucks 211 lh )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (((h_pre_bucks + (i * sizeof(PTR) ) )) # Ptr  |-> 0)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition hashtbl_clear_safety_wit_11 := 
forall (h_pre: Z) (top: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (i: Z) (h_pre_bucks: Z) ,
  [| (i >= 211) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (i >= 211) |]
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_clear_safety_wit_12 := 
forall (h_pre: Z) (top: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (i: Z) ,
  [| (i >= 211) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (i >= 211) |]
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_clear_entail_wit_1 := 
forall (h_pre: Z) (top: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (lh_2: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) ,
  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh_2 b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| (map_composable m1 m2 ) |]
  &&  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  (IntArray.full &((h_pre)  # "hashtbl" ->ₛ "bucks") 211 lh_2 )
  **  (store_map store_sll b )
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
|--
  (EX (h_pre_bucks: Z)  (lh: (@list Z)) ,
  [| (map_composable m1 m2 ) |] 
  &&  [| (0 >= 211) |]
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (IntArray.full h_pre_bucks 211 lh ))
  ||
  (EX (buck_key: Z)  (k: (@list Z))  (li: (@list Z))  (buck: Z)  (h_pre_bucks_2: Z)  (lh: (@list Z)) ,
  [| (map_composable m1 m2 ) |] 
  &&  [| (0 >= 0) |] 
  &&  [| (0 < 211) |]
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks_2)
  **  (IntArray.full h_pre_bucks_2 211 lh )
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  (((h_pre_bucks_2 + (0 * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (sll buck li )
  **  ((&((buck)  # "blist" ->ₛ "key")) # Ptr  |-> buck_key)
  **  (store_string buck_key k ))
.

Definition hashtbl_clear_entail_wit_2 := 
forall (h_pre: Z) (top: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (k_2: (@list Z)) (buck_2: Z) (i: Z) (h_pre_bucks_3: Z) (lh_2: (@list Z)) ,
  [| (buck_2 = 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (i >= 0) |] 
  &&  [| (i < 211) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (i >= 0) |] 
  &&  [| (i < 211) |]
  &&  (store_map store_name (KP.remove_map (m1) (k_2)) )
  **  (store_map store_uint (PV.remove_map (m2) (buck_2)) )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks_3)
  **  (IntArray.full h_pre_bucks_3 211 lh_2 )
  **  (((h_pre_bucks_3 + (i * sizeof(PTR) ) )) # Ptr  |-> 0)
|--
  (EX (h_pre_bucks: Z)  (lh: (@list Z)) ,
  [| (map_composable m1 m2 ) |] 
  &&  [| ((i + 1 ) >= 211) |]
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (IntArray.full h_pre_bucks 211 lh ))
  ||
  (EX (buck_key: Z)  (k: (@list Z))  (li: (@list Z))  (buck: Z)  (h_pre_bucks_2: Z)  (lh: (@list Z)) ,
  [| (map_composable m1 m2 ) |] 
  &&  [| ((i + 1 ) >= 0) |] 
  &&  [| ((i + 1 ) < 211) |]
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks_2)
  **  (IntArray.full h_pre_bucks_2 211 lh )
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  (((h_pre_bucks_2 + ((i + 1 ) * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (sll buck li )
  **  ((&((buck)  # "blist" ->ₛ "key")) # Ptr  |-> buck_key)
  **  (store_string buck_key k ))
.

Definition hashtbl_clear_return_wit_1 := 
forall (h_pre: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (i: Z) ,
  [| (i >= 211) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (i >= 211) |]
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> 0)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> 0)
|--
  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> 0)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> 0)
.

Definition hashtbl_clear_partial_solve_wit_1 := 
forall (h_pre: Z) (top: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) ,
  [| (map_composable m1 m2 ) |]
  &&  (store_hash_skeleton h_pre m1 )
  **  (store_map store_uint m2 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
|--
  [| (map_composable m1 m2 ) |]
  &&  (store_hash_skeleton h_pre m1 )
  **  (store_map store_uint m2 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
.

Definition hashtbl_clear_partial_solve_wit_2_pure := 
forall (h_pre: Z) (top: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (buck_key: Z) (k: (@list Z)) (li: (@list Z)) (buck: Z) (i: Z) (h_pre_bucks: Z) (lh: (@list Z)) ,
  [| (i >= 0) |] 
  &&  [| (i < 211) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (i >= 0) |] 
  &&  [| (i < 211) |]
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (IntArray.full h_pre_bucks 211 lh )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  (((h_pre_bucks + (i * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (sll buck li )
  **  ((&((buck)  # "blist" ->ₛ "key")) # Ptr  |-> buck_key)
  **  (store_string buck_key k )
|--
  [| (map_composable m1 m2 ) |]
.

Definition hashtbl_clear_partial_solve_wit_2_aux := 
forall (h_pre: Z) (top: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (buck_key: Z) (k: (@list Z)) (li: (@list Z)) (buck: Z) (i: Z) (h_pre_bucks: Z) (lh: (@list Z)) ,
  [| (i >= 0) |] 
  &&  [| (i < 211) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (i >= 0) |] 
  &&  [| (i < 211) |]
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (IntArray.full h_pre_bucks 211 lh )
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  (((h_pre_bucks + (i * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (sll buck li )
  **  ((&((buck)  # "blist" ->ₛ "key")) # Ptr  |-> buck_key)
  **  (store_string buck_key k )
|--
  [| (map_composable m1 m2 ) |] 
  &&  [| (i >= 0) |] 
  &&  [| (i < 211) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (i >= 0) |] 
  &&  [| (i < 211) |]
  &&  (sll buck li )
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  ((&((buck)  # "blist" ->ₛ "key")) # Ptr  |-> buck_key)
  **  (store_string buck_key k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (IntArray.full h_pre_bucks 211 lh )
  **  (((h_pre_bucks + (i * sizeof(PTR) ) )) # Ptr  |-> buck)
.

Definition hashtbl_clear_partial_solve_wit_2 := hashtbl_clear_partial_solve_wit_2_pure -> hashtbl_clear_partial_solve_wit_2_aux.

Definition hashtbl_clear_partial_solve_wit_3 := 
forall (h_pre: Z) (top: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (i: Z) (h_pre_bucks: Z) (lh: (@list Z)) ,
  [| (i >= 211) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (i >= 211) |]
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (IntArray.full h_pre_bucks 211 lh )
|--
  [| (i >= 211) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (i >= 211) |]
  &&  (IntArray.full h_pre_bucks 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
.

Definition hashtbl_clear_which_implies_wit_1 := 
forall (m1: ((@list Z) -> (@option Z))) (h: Z) ,
  (store_hash_skeleton h m1 )
|--
  EX (lh: (@list Z))  (b: (Z -> (@option (Z * (@list Z)))))  (l: (@list Z)) ,
  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  (dll &((h)  # "hashtbl" ->ₛ "top") 0 l )
  **  (IntArray.full &((h)  # "hashtbl" ->ₛ "bucks") 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m1 )
.

(*----- Function free_hashtbl -----*)

Definition free_hashtbl_return_wit_1 := 
forall (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) ,
  [| (map_composable m1 m2 ) |]
  &&  emp
|--
  TT && emp 
.

Definition free_hashtbl_partial_solve_wit_1_pure := 
forall (h_pre: Z) (top: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) ,
  [| (map_composable m1 m2 ) |]
  &&  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  (store_hash_skeleton h_pre m1 )
  **  (store_map store_uint m2 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
|--
  [| (map_composable m1 m2 ) |]
.

Definition free_hashtbl_partial_solve_wit_1_aux := 
forall (h_pre: Z) (top: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) ,
  [| (map_composable m1 m2 ) |]
  &&  (store_hash_skeleton h_pre m1 )
  **  (store_map store_uint m2 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
|--
  [| (map_composable m1 m2 ) |] 
  &&  [| (map_composable m1 m2 ) |]
  &&  (store_hash_skeleton h_pre m1 )
  **  (store_map store_uint m2 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
.

Definition free_hashtbl_partial_solve_wit_1 := free_hashtbl_partial_solve_wit_1_pure -> free_hashtbl_partial_solve_wit_1_aux.

Definition free_hashtbl_partial_solve_wit_2 := 
forall (h_pre: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) ,
  [| (map_composable m1 m2 ) |]
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> 0)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> 0)
|--
  [| (map_composable m1 m2 ) |]
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> 0)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> 0)
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include hashtbl_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_hashtbl_findref_safety_wit_1 : hashtbl_findref_safety_wit_1.
Axiom proof_of_hashtbl_findref_safety_wit_2 : hashtbl_findref_safety_wit_2.
Axiom proof_of_hashtbl_findref_safety_wit_3 : hashtbl_findref_safety_wit_3.
Axiom proof_of_hashtbl_findref_safety_wit_4 : hashtbl_findref_safety_wit_4.
Axiom proof_of_hashtbl_findref_safety_wit_5 : hashtbl_findref_safety_wit_5.
Axiom proof_of_hashtbl_findref_safety_wit_6 : hashtbl_findref_safety_wit_6.
Axiom proof_of_hashtbl_findref_entail_wit_1 : hashtbl_findref_entail_wit_1.
Axiom proof_of_hashtbl_findref_entail_wit_2_1 : hashtbl_findref_entail_wit_2_1.
Axiom proof_of_hashtbl_findref_entail_wit_2_2 : hashtbl_findref_entail_wit_2_2.
Axiom proof_of_hashtbl_findref_entail_wit_3_1 : hashtbl_findref_entail_wit_3_1.
Axiom proof_of_hashtbl_findref_entail_wit_3_2 : hashtbl_findref_entail_wit_3_2.
Axiom proof_of_hashtbl_findref_entail_wit_4 : hashtbl_findref_entail_wit_4.
Axiom proof_of_hashtbl_findref_return_wit_1 : hashtbl_findref_return_wit_1.
Axiom proof_of_hashtbl_findref_return_wit_2 : hashtbl_findref_return_wit_2.
Axiom proof_of_hashtbl_findref_partial_solve_wit_1 : hashtbl_findref_partial_solve_wit_1.
Axiom proof_of_hashtbl_findref_partial_solve_wit_2 : hashtbl_findref_partial_solve_wit_2.
Axiom proof_of_hashtbl_findref_partial_solve_wit_3 : hashtbl_findref_partial_solve_wit_3.
Axiom proof_of_hashtbl_findref_which_implies_wit_1 : hashtbl_findref_which_implies_wit_1.
Axiom proof_of_hashtbl_remove_safety_wit_1 : hashtbl_remove_safety_wit_1.
Axiom proof_of_hashtbl_remove_safety_wit_2 : hashtbl_remove_safety_wit_2.
Axiom proof_of_hashtbl_remove_safety_wit_3 : hashtbl_remove_safety_wit_3.
Axiom proof_of_hashtbl_remove_safety_wit_4 : hashtbl_remove_safety_wit_4.
Axiom proof_of_hashtbl_remove_safety_wit_5 : hashtbl_remove_safety_wit_5.
Axiom proof_of_hashtbl_remove_safety_wit_6 : hashtbl_remove_safety_wit_6.
Axiom proof_of_hashtbl_remove_safety_wit_7 : hashtbl_remove_safety_wit_7.
Axiom proof_of_hashtbl_remove_safety_wit_8 : hashtbl_remove_safety_wit_8.
Axiom proof_of_hashtbl_remove_safety_wit_9 : hashtbl_remove_safety_wit_9.
Axiom proof_of_hashtbl_remove_safety_wit_10 : hashtbl_remove_safety_wit_10.
Axiom proof_of_hashtbl_remove_safety_wit_11 : hashtbl_remove_safety_wit_11.
Axiom proof_of_hashtbl_remove_safety_wit_12 : hashtbl_remove_safety_wit_12.
Axiom proof_of_hashtbl_remove_safety_wit_13 : hashtbl_remove_safety_wit_13.
Axiom proof_of_hashtbl_remove_safety_wit_14 : hashtbl_remove_safety_wit_14.
Axiom proof_of_hashtbl_remove_safety_wit_15 : hashtbl_remove_safety_wit_15.
Axiom proof_of_hashtbl_remove_safety_wit_16 : hashtbl_remove_safety_wit_16.
Axiom proof_of_hashtbl_remove_safety_wit_17 : hashtbl_remove_safety_wit_17.
Axiom proof_of_hashtbl_remove_safety_wit_18 : hashtbl_remove_safety_wit_18.
Axiom proof_of_hashtbl_remove_safety_wit_19 : hashtbl_remove_safety_wit_19.
Axiom proof_of_hashtbl_remove_safety_wit_20 : hashtbl_remove_safety_wit_20.
Axiom proof_of_hashtbl_remove_safety_wit_21 : hashtbl_remove_safety_wit_21.
Axiom proof_of_hashtbl_remove_entail_wit_1 : hashtbl_remove_entail_wit_1.
Axiom proof_of_hashtbl_remove_entail_wit_2_1 : hashtbl_remove_entail_wit_2_1.
Axiom proof_of_hashtbl_remove_entail_wit_2_2 : hashtbl_remove_entail_wit_2_2.
Axiom proof_of_hashtbl_remove_entail_wit_3_1 : hashtbl_remove_entail_wit_3_1.
Axiom proof_of_hashtbl_remove_entail_wit_3_2 : hashtbl_remove_entail_wit_3_2.
Axiom proof_of_hashtbl_remove_entail_wit_4 : hashtbl_remove_entail_wit_4.
Axiom proof_of_hashtbl_remove_return_wit_1 : hashtbl_remove_return_wit_1.
Axiom proof_of_hashtbl_remove_return_wit_2 : hashtbl_remove_return_wit_2.
Axiom proof_of_hashtbl_remove_return_wit_3 : hashtbl_remove_return_wit_3.
Axiom proof_of_hashtbl_remove_return_wit_4 : hashtbl_remove_return_wit_4.
Axiom proof_of_hashtbl_remove_return_wit_5 : hashtbl_remove_return_wit_5.
Axiom proof_of_hashtbl_remove_return_wit_6 : hashtbl_remove_return_wit_6.
Axiom proof_of_hashtbl_remove_return_wit_7 : hashtbl_remove_return_wit_7.
Axiom proof_of_hashtbl_remove_return_wit_8 : hashtbl_remove_return_wit_8.
Axiom proof_of_hashtbl_remove_return_wit_9 : hashtbl_remove_return_wit_9.
Axiom proof_of_hashtbl_remove_partial_solve_wit_1 : hashtbl_remove_partial_solve_wit_1.
Axiom proof_of_hashtbl_remove_partial_solve_wit_2 : hashtbl_remove_partial_solve_wit_2.
Axiom proof_of_hashtbl_remove_partial_solve_wit_3 : hashtbl_remove_partial_solve_wit_3.
Axiom proof_of_hashtbl_remove_partial_solve_wit_4 : hashtbl_remove_partial_solve_wit_4.
Axiom proof_of_hashtbl_remove_partial_solve_wit_5 : hashtbl_remove_partial_solve_wit_5.
Axiom proof_of_hashtbl_remove_partial_solve_wit_6 : hashtbl_remove_partial_solve_wit_6.
Axiom proof_of_hashtbl_remove_partial_solve_wit_7 : hashtbl_remove_partial_solve_wit_7.
Axiom proof_of_hashtbl_remove_partial_solve_wit_8 : hashtbl_remove_partial_solve_wit_8.
Axiom proof_of_hashtbl_remove_partial_solve_wit_9 : hashtbl_remove_partial_solve_wit_9.
Axiom proof_of_hashtbl_remove_partial_solve_wit_10 : hashtbl_remove_partial_solve_wit_10.
Axiom proof_of_hashtbl_remove_partial_solve_wit_11 : hashtbl_remove_partial_solve_wit_11.
Axiom proof_of_hashtbl_remove_which_implies_wit_1 : hashtbl_remove_which_implies_wit_1.
Axiom proof_of_hashtbl_free_blist_safety_wit_1 : hashtbl_free_blist_safety_wit_1.
Axiom proof_of_hashtbl_free_blist_return_wit_1 : hashtbl_free_blist_return_wit_1.
Axiom proof_of_hashtbl_free_blist_return_wit_2 : hashtbl_free_blist_return_wit_2.
Axiom proof_of_hashtbl_free_blist_partial_solve_wit_1 : hashtbl_free_blist_partial_solve_wit_1.
Axiom proof_of_hashtbl_free_blist_partial_solve_wit_2_pure : hashtbl_free_blist_partial_solve_wit_2_pure.
Axiom proof_of_hashtbl_free_blist_partial_solve_wit_2 : hashtbl_free_blist_partial_solve_wit_2.
Axiom proof_of_hashtbl_free_blist_partial_solve_wit_3_pure : hashtbl_free_blist_partial_solve_wit_3_pure.
Axiom proof_of_hashtbl_free_blist_partial_solve_wit_3 : hashtbl_free_blist_partial_solve_wit_3.
Axiom proof_of_hashtbl_free_blist_partial_solve_wit_4 : hashtbl_free_blist_partial_solve_wit_4.
Axiom proof_of_hashtbl_free_blist_which_implies_wit_1 : hashtbl_free_blist_which_implies_wit_1.
Axiom proof_of_hashtbl_clear_safety_wit_1 : hashtbl_clear_safety_wit_1.
Axiom proof_of_hashtbl_clear_safety_wit_2 : hashtbl_clear_safety_wit_2.
Axiom proof_of_hashtbl_clear_safety_wit_3 : hashtbl_clear_safety_wit_3.
Axiom proof_of_hashtbl_clear_safety_wit_4 : hashtbl_clear_safety_wit_4.
Axiom proof_of_hashtbl_clear_safety_wit_5 : hashtbl_clear_safety_wit_5.
Axiom proof_of_hashtbl_clear_safety_wit_6 : hashtbl_clear_safety_wit_6.
Axiom proof_of_hashtbl_clear_safety_wit_7 : hashtbl_clear_safety_wit_7.
Axiom proof_of_hashtbl_clear_safety_wit_8 : hashtbl_clear_safety_wit_8.
Axiom proof_of_hashtbl_clear_safety_wit_9 : hashtbl_clear_safety_wit_9.
Axiom proof_of_hashtbl_clear_safety_wit_10 : hashtbl_clear_safety_wit_10.
Axiom proof_of_hashtbl_clear_safety_wit_11 : hashtbl_clear_safety_wit_11.
Axiom proof_of_hashtbl_clear_safety_wit_12 : hashtbl_clear_safety_wit_12.
Axiom proof_of_hashtbl_clear_entail_wit_1 : hashtbl_clear_entail_wit_1.
Axiom proof_of_hashtbl_clear_entail_wit_2 : hashtbl_clear_entail_wit_2.
Axiom proof_of_hashtbl_clear_return_wit_1 : hashtbl_clear_return_wit_1.
Axiom proof_of_hashtbl_clear_partial_solve_wit_1 : hashtbl_clear_partial_solve_wit_1.
Axiom proof_of_hashtbl_clear_partial_solve_wit_2_pure : hashtbl_clear_partial_solve_wit_2_pure.
Axiom proof_of_hashtbl_clear_partial_solve_wit_2 : hashtbl_clear_partial_solve_wit_2.
Axiom proof_of_hashtbl_clear_partial_solve_wit_3 : hashtbl_clear_partial_solve_wit_3.
Axiom proof_of_hashtbl_clear_which_implies_wit_1 : hashtbl_clear_which_implies_wit_1.
Axiom proof_of_free_hashtbl_return_wit_1 : free_hashtbl_return_wit_1.
Axiom proof_of_free_hashtbl_partial_solve_wit_1_pure : free_hashtbl_partial_solve_wit_1_pure.
Axiom proof_of_free_hashtbl_partial_solve_wit_1 : free_hashtbl_partial_solve_wit_1.
Axiom proof_of_free_hashtbl_partial_solve_wit_2 : free_hashtbl_partial_solve_wit_2.

End VC_Correct.
