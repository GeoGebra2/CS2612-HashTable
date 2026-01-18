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
Require Import common_strategy_goal.
Require Import common_strategy_proof.
Require Import hashtbl_strategy_goal.
Require Import hashtbl_strategy_proof.
From SimpleC.EE Require Import ptr_array_strategy_goal.
From SimpleC.EE Require Import ptr_array_strategy_proof.
Require Import hashtbl_strategy_goal.
Require Import hashtbl_strategy_proof.

(*----- Function hashtbl_findref -----*)

Definition hashtbl_findref_safety_wit_1 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (h_callee_bucks: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (retval: Z) ,
  [| (retval = (hash_string_coq (k))) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |]
  &&  (store_string key_pre k )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_callee_bucks)
  **  (PtrArray.full h_callee_bucks 211 lh )
  **  (store_map store_sll b0 )
  **  (store_map store_name m )
  **  ((( &( "i" ) )) # Ptr  |->_)
  **  ((( &( "ind" ) )) # UInt  |->_)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
|--
  [| (211 <> 0) |]
.

Definition hashtbl_findref_safety_wit_2 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (h_callee_bucks: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (retval: Z) ,
  [| (retval = (hash_string_coq (k))) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |]
  &&  (store_string key_pre k )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_callee_bucks)
  **  (PtrArray.full h_callee_bucks 211 lh )
  **  (store_map store_sll b0 )
  **  (store_map store_name m )
  **  ((( &( "i" ) )) # Ptr  |->_)
  **  ((( &( "ind" ) )) # UInt  |->_)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
|--
  [| (211 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 211) |]
.

Definition hashtbl_findref_safety_wit_3 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (i_v: Z) (h_bucks: Z) (i: Z) (l_prev: (@list Z)) (l_res: (@list Z)) (l0: (@list Z)) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) ,
  [| (ind = ((hash_string_coq (k)) % ( 211 ) )) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (not_key k l_prev m ) |]
  &&  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "i" ) )) # Ptr  |-> i)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllbseg (h_bucks + (ind * sizeof(PTR) ) ) i l_prev )
  **  ((i) # Ptr  |-> i_v)
  **  (sll i_v l_res )
  **  (store_map_missing_i store_sll b0 ind )
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
  **  (store_string key_pre k )
  **  (store_map store_name m )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_findref_safety_wit_4 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (i_v: Z) (h_bucks: Z) (i: Z) (l_prev: (@list Z)) (l_res: (@list Z)) (l0: (@list Z)) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (i_v_key: Z) (i_v_next: Z) (l_resres: (@list Z)) (k_list_current: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (key_pre <> i_v_key) |] 
  &&  [| (k <> k_list_current) |] 
  &&  [| (i_v <> 0) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l_prev) (l_res))))))) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| ((m (k_list_current)) = (Some (i_v))) |] 
  &&  [| (l_res = (cons (i_v) (l_resres))) |] 
  &&  [| (i_v <> 0) |] 
  &&  [| (ind = ((hash_string_coq (k)) % ( 211 ) )) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (not_key k l_prev m ) |]
  &&  (store_string key_pre k )
  **  (store_string i_v_key k_list_current )
  **  ((( &( "i" ) )) # Ptr  |-> i)
  **  ((i) # Ptr  |-> i_v)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllbseg (h_bucks + (ind * sizeof(PTR) ) ) i l_prev )
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  (sll i_v_next l_resres )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  (store_map_missing_i store_name m k_list_current )
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  (store_map_missing_i store_sll b0 ind )
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
|--
  [| False |]
.

Definition hashtbl_findref_safety_wit_5 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (i_v: Z) (h_bucks: Z) (i: Z) (l_prev: (@list Z)) (l_res: (@list Z)) (l0: (@list Z)) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (i_v_key: Z) (i_v_next: Z) (l_resres: (@list Z)) (k_list_current: (@list Z)) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (key_pre = i_v_key) |] 
  &&  [| (k = k_list_current) |] 
  &&  [| (i_v <> 0) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l_prev) (l_res))))))) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| ((m (k_list_current)) = (Some (i_v))) |] 
  &&  [| (l_res = (cons (i_v) (l_resres))) |] 
  &&  [| (i_v <> 0) |] 
  &&  [| (ind = ((hash_string_coq (k)) % ( 211 ) )) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (not_key k l_prev m ) |]
  &&  (store_string key_pre k )
  **  (store_string i_v_key k_list_current )
  **  ((( &( "i" ) )) # Ptr  |-> i)
  **  ((i) # Ptr  |-> i_v)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllbseg (h_bucks + (ind * sizeof(PTR) ) ) i l_prev )
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  (sll i_v_next l_resres )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  (store_map_missing_i store_name m k_list_current )
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  (store_map_missing_i store_sll b0 ind )
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
|--
  [| False |]
.

Definition hashtbl_findref_safety_wit_6 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (i_v: Z) (h_bucks: Z) (i: Z) (l_prev: (@list Z)) (l_res: (@list Z)) (l0: (@list Z)) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) ,
  [| (i_v = 0) |] 
  &&  [| (ind = ((hash_string_coq (k)) % ( 211 ) )) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (not_key k l_prev m ) |]
  &&  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "i" ) )) # Ptr  |-> i)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllbseg (h_bucks + (ind * sizeof(PTR) ) ) i l_prev )
  **  ((i) # Ptr  |-> i_v)
  **  (sll i_v l_res )
  **  (store_map_missing_i store_sll b0 ind )
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
  **  (store_string key_pre k )
  **  (store_map store_name m )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_findref_entail_wit_1 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (h_callee_bucks: Z) (lh_2: (@list Z)) (b0_2: (Z -> (@option (Z * (@list Z))))) (l_2: (@list Z)) (retval: Z) ,
  [| (retval = (hash_string_coq (k))) |] 
  &&  [| (contain_all_addrs m l_2 ) |] 
  &&  [| (repr_all_heads lh_2 b0_2 ) |] 
  &&  [| (contain_all_correct_addrs m b0_2 ) |]
  &&  (store_string key_pre k )
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l_2 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_callee_bucks)
  **  (PtrArray.full h_callee_bucks 211 lh_2 )
  **  (store_map store_sll b0_2 )
  **  (store_map store_name m )
|--
  EX (i_v: Z)  (h_bucks: Z)  (l_prev: (@list Z))  (l_res: (@list Z))  (l0: (@list Z))  (lh: (@list Z))  (b0: (Z -> (@option (Z * (@list Z)))))  (l: (@list Z)) ,
  [| ((retval % ( 211 ) ) = ((hash_string_coq (k)) % ( 211 ) )) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= (retval % ( 211 ) )) |] 
  &&  [| ((retval % ( 211 ) ) < 211) |] 
  &&  [| ((b0 ((retval % ( 211 ) ))) = (Some ((pair ((Znth ((retval % ( 211 ) )) (lh) (0))) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (not_key k l_prev m ) |]
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllbseg (h_bucks + ((retval % ( 211 ) ) * sizeof(PTR) ) ) (h_callee_bucks + ((retval % ( 211 ) ) * sizeof(PTR) ) ) l_prev )
  **  (((h_callee_bucks + ((retval % ( 211 ) ) * sizeof(PTR) ) )) # Ptr  |-> i_v)
  **  (sll i_v l_res )
  **  (store_map_missing_i store_sll b0 (retval % ( 211 ) ) )
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  (PtrArray.missing_i h_bucks (retval % ( 211 ) ) 0 211 lh )
  **  (store_string key_pre k )
  **  (store_map store_name m )
.

Definition hashtbl_findref_entail_wit_2_1 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (i_v: Z) (h_bucks: Z) (i: Z) (l_prev: (@list Z)) (l_res: (@list Z)) (l0: (@list Z)) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (i_v_key: Z) (i_v_next: Z) (l_resres: (@list Z)) (k_list_current: (@list Z)) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (key_pre <> i_v_key) |] 
  &&  [| (k <> k_list_current) |] 
  &&  [| (i_v <> 0) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l_prev) (l_res))))))) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| ((m (k_list_current)) = (Some (i_v))) |] 
  &&  [| (l_res = (cons (i_v) (l_resres))) |] 
  &&  [| (i_v <> 0) |] 
  &&  [| (ind = ((hash_string_coq (k)) % ( 211 ) )) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (not_key k l_prev m ) |]
  &&  (store_string key_pre k )
  **  (store_string i_v_key k_list_current )
  **  ((i) # Ptr  |-> i_v)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllbseg (h_bucks + (ind * sizeof(PTR) ) ) i l_prev )
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  (sll i_v_next l_resres )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  (store_map_missing_i store_name m k_list_current )
  **  (store_map_missing_i store_sll b0 ind )
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
|--
  EX (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (key_pre = i_v_key) |] 
  &&  [| (k = k_list_current) |] 
  &&  [| (i_v <> 0) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l_prev) (l_res))))))) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| ((m (k_list_current)) = (Some (i_v))) |] 
  &&  [| (l_res = (cons (i_v) (l_resres))) |] 
  &&  [| (i_v <> 0) |] 
  &&  [| (ind = ((hash_string_coq (k)) % ( 211 ) )) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (not_key k l_prev m ) |]
  &&  (store_string key_pre k )
  **  (store_string i_v_key k_list_current )
  **  ((i) # Ptr  |-> i_v)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllbseg (h_bucks + (ind * sizeof(PTR) ) ) i l_prev )
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  (sll i_v_next l_resres )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  (store_map_missing_i store_name m k_list_current )
  **  (store_map_missing_i store_sll b0 ind )
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
.

Definition hashtbl_findref_entail_wit_2_2 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (i_v: Z) (h_bucks: Z) (i: Z) (l_prev: (@list Z)) (l_res: (@list Z)) (l0: (@list Z)) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (i_v_key: Z) (i_v_next: Z) (l_resres: (@list Z)) (k_list_current: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (key_pre = i_v_key) |] 
  &&  [| (k = k_list_current) |] 
  &&  [| (i_v <> 0) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l_prev) (l_res))))))) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| ((m (k_list_current)) = (Some (i_v))) |] 
  &&  [| (l_res = (cons (i_v) (l_resres))) |] 
  &&  [| (i_v <> 0) |] 
  &&  [| (ind = ((hash_string_coq (k)) % ( 211 ) )) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (not_key k l_prev m ) |]
  &&  (store_string key_pre k )
  **  (store_string i_v_key k_list_current )
  **  ((i) # Ptr  |-> i_v)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllbseg (h_bucks + (ind * sizeof(PTR) ) ) i l_prev )
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  (sll i_v_next l_resres )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  (store_map_missing_i store_name m k_list_current )
  **  (store_map_missing_i store_sll b0 ind )
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
|--
  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (key_pre = i_v_key) |] 
  &&  [| (k = k_list_current) |] 
  &&  [| (i_v <> 0) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l_prev) (l_res))))))) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| ((m (k_list_current)) = (Some (i_v))) |] 
  &&  [| (l_res = (cons (i_v) (l_resres))) |] 
  &&  [| (i_v <> 0) |] 
  &&  [| (ind = ((hash_string_coq (k)) % ( 211 ) )) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (not_key k l_prev m ) |]
  &&  (store_string key_pre k )
  **  (store_string i_v_key k_list_current )
  **  ((i) # Ptr  |-> i_v)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllbseg (h_bucks + (ind * sizeof(PTR) ) ) i l_prev )
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  (sll i_v_next l_resres )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  (store_map_missing_i store_name m k_list_current )
  **  (store_map_missing_i store_sll b0 ind )
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
.

Definition hashtbl_findref_entail_wit_3_1 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (i_v: Z) (h_bucks: Z) (i: Z) (l_prev: (@list Z)) (l_res: (@list Z)) (l0: (@list Z)) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (i_v_key: Z) (i_v_next: Z) (l_resres: (@list Z)) (k_list_current: (@list Z)) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (key_pre <> i_v_key) |] 
  &&  [| (k <> k_list_current) |] 
  &&  [| (i_v <> 0) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l_prev) (l_res))))))) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| ((m (k_list_current)) = (Some (i_v))) |] 
  &&  [| (l_res = (cons (i_v) (l_resres))) |] 
  &&  [| (i_v <> 0) |] 
  &&  [| (ind = ((hash_string_coq (k)) % ( 211 ) )) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (not_key k l_prev m ) |]
  &&  (store_string key_pre k )
  **  (store_string i_v_key k_list_current )
  **  ((i) # Ptr  |-> i_v)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllbseg (h_bucks + (ind * sizeof(PTR) ) ) i l_prev )
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  (sll i_v_next l_resres )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  (store_map_missing_i store_name m k_list_current )
  **  (store_map_missing_i store_sll b0 ind )
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
|--
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (key_pre <> i_v_key) |] 
  &&  [| (k <> k_list_current) |] 
  &&  [| (i_v <> 0) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l_prev) (l_res))))))) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| ((m (k_list_current)) = (Some (i_v))) |] 
  &&  [| (l_res = (cons (i_v) (l_resres))) |] 
  &&  [| (i_v <> 0) |] 
  &&  [| (ind = ((hash_string_coq (k)) % ( 211 ) )) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (not_key k l_prev m ) |]
  &&  (store_string key_pre k )
  **  (store_string i_v_key k_list_current )
  **  ((i) # Ptr  |-> i_v)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllbseg (h_bucks + (ind * sizeof(PTR) ) ) i l_prev )
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  (sll i_v_next l_resres )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  (store_map_missing_i store_name m k_list_current )
  **  (store_map_missing_i store_sll b0 ind )
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
.

Definition hashtbl_findref_entail_wit_3_2 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (i_v: Z) (h_bucks: Z) (i: Z) (l_prev: (@list Z)) (l_res: (@list Z)) (l0: (@list Z)) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (i_v_key: Z) (i_v_next: Z) (l_resres: (@list Z)) (k_list_current: (@list Z)) (retval_2: Z) ,
  [| (retval_2 = 0) |] 
  &&  [| (retval_2 = 1) |] 
  &&  [| (key_pre = i_v_key) |] 
  &&  [| (k = k_list_current) |] 
  &&  [| (i_v <> 0) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l_prev) (l_res))))))) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| ((m (k_list_current)) = (Some (i_v))) |] 
  &&  [| (l_res = (cons (i_v) (l_resres))) |] 
  &&  [| (i_v <> 0) |] 
  &&  [| (ind = ((hash_string_coq (k)) % ( 211 ) )) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (not_key k l_prev m ) |]
  &&  (store_string key_pre k )
  **  (store_string i_v_key k_list_current )
  **  ((i) # Ptr  |-> i_v)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllbseg (h_bucks + (ind * sizeof(PTR) ) ) i l_prev )
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  (sll i_v_next l_resres )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  (store_map_missing_i store_name m k_list_current )
  **  (store_map_missing_i store_sll b0 ind )
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
|--
  EX (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (key_pre <> i_v_key) |] 
  &&  [| (k <> k_list_current) |] 
  &&  [| (i_v <> 0) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l_prev) (l_res))))))) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| ((m (k_list_current)) = (Some (i_v))) |] 
  &&  [| (l_res = (cons (i_v) (l_resres))) |] 
  &&  [| (i_v <> 0) |] 
  &&  [| (ind = ((hash_string_coq (k)) % ( 211 ) )) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (not_key k l_prev m ) |]
  &&  (store_string key_pre k )
  **  (store_string i_v_key k_list_current )
  **  ((i) # Ptr  |-> i_v)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllbseg (h_bucks + (ind * sizeof(PTR) ) ) i l_prev )
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  (sll i_v_next l_resres )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  (store_map_missing_i store_name m k_list_current )
  **  (store_map_missing_i store_sll b0 ind )
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
.

Definition hashtbl_findref_entail_wit_4 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (i_v_2: Z) (h_bucks_2: Z) (i: Z) (l_prev_2: (@list Z)) (l_res_2: (@list Z)) (l0_2: (@list Z)) (lh_2: (@list Z)) (b0_2: (Z -> (@option (Z * (@list Z))))) (l_2: (@list Z)) (ind: Z) (i_v_key: Z) (i_v_next: Z) (l_resres: (@list Z)) (k_list_current: (@list Z)) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (key_pre <> i_v_key) |] 
  &&  [| (k <> k_list_current) |] 
  &&  [| (i_v_2 <> 0) |] 
  &&  [| (repr_all_heads lh_2 b0_2 ) |] 
  &&  [| ((b0_2 (ind)) = (Some ((pair ((Znth (ind) (lh_2) (0))) ((app (l_prev_2) (l_res_2))))))) |] 
  &&  [| (contain_all_correct_addrs m b0_2 ) |] 
  &&  [| ((m (k_list_current)) = (Some (i_v_2))) |] 
  &&  [| (l_res_2 = (cons (i_v_2) (l_resres))) |] 
  &&  [| (i_v_2 <> 0) |] 
  &&  [| (ind = ((hash_string_coq (k)) % ( 211 ) )) |] 
  &&  [| (contain_all_addrs m l_2 ) |] 
  &&  [| (repr_all_heads lh_2 b0_2 ) |] 
  &&  [| (contain_all_correct_addrs m b0_2 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0_2 (ind)) = (Some ((pair ((Znth (ind) (lh_2) (0))) (l0_2))))) |] 
  &&  [| (l0_2 = (app (l_prev_2) (l_res_2))) |] 
  &&  [| (not_key k l_prev_2 m ) |]
  &&  (store_string key_pre k )
  **  (store_string i_v_key k_list_current )
  **  ((i) # Ptr  |-> i_v_2)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks_2)
  **  (sllbseg (h_bucks_2 + (ind * sizeof(PTR) ) ) i l_prev_2 )
  **  ((&((i_v_2)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  (sll i_v_next l_resres )
  **  ((&((i_v_2)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  (store_map_missing_i store_name m k_list_current )
  **  (store_map_missing_i store_sll b0_2 ind )
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l_2 )
  **  (PtrArray.missing_i h_bucks_2 ind 0 211 lh_2 )
|--
  EX (i_v: Z)  (h_bucks: Z)  (l_prev: (@list Z))  (l_res: (@list Z))  (l0: (@list Z))  (lh: (@list Z))  (b0: (Z -> (@option (Z * (@list Z)))))  (l: (@list Z)) ,
  [| (ind = ((hash_string_coq (k)) % ( 211 ) )) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (not_key k l_prev m ) |]
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllbseg (h_bucks + (ind * sizeof(PTR) ) ) &((i_v_2)  # "blist" ->ₛ "next") l_prev )
  **  ((&((i_v_2)  # "blist" ->ₛ "next")) # Ptr  |-> i_v)
  **  (sll i_v l_res )
  **  (store_map_missing_i store_sll b0 ind )
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
  **  (store_string key_pre k )
  **  (store_map store_name m )
.

Definition hashtbl_findref_return_wit_1 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (i_v: Z) (h_bucks: Z) (i: Z) (l_prev: (@list Z)) (l_res: (@list Z)) (l0: (@list Z)) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (i_v_key: Z) (i_v_next: Z) (l_resres: (@list Z)) (k_list_current: (@list Z)) (retval: Z) (lh_2: (@list Z)) ,
  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (key_pre = i_v_key) |] 
  &&  [| (k = k_list_current) |] 
  &&  [| (i_v <> 0) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l_prev) (l_res))))))) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| ((m (k_list_current)) = (Some (i_v))) |] 
  &&  [| (l_res = (cons (i_v) (l_resres))) |] 
  &&  [| (i_v <> 0) |] 
  &&  [| (ind = ((hash_string_coq (k)) % ( 211 ) )) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (not_key k l_prev m ) |]
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> i_v)
  **  (sllbseg &(((Znth (ind) (lh_2) (0)))  # "blist" ->ₛ "next") i l_prev )
  **  (store_string key_pre k )
  **  (store_string i_v_key k_list_current )
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> (Znth (ind) (lh_2) (0)))
  **  (sll i_v_next l_resres )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  (store_map_missing_i store_name m k_list_current )
  **  (store_map_missing_i store_sll b0 ind )
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
|--
  ([| ((m (k)) = None) |] 
  &&  [| (&((i_v)  # "blist" ->ₛ "val") = 0) |]
  &&  (store_hash_skeleton h_pre m )
  **  (store_string key_pre k ))
  ||
  (EX (p: Z) ,
  [| ((m (k)) = (Some (p))) |] 
  &&  [| (&((i_v)  # "blist" ->ₛ "val") = &((p)  # "blist" ->ₛ "val")) |]
  &&  (store_hash_skeleton h_pre m )
  **  (store_string key_pre k ))
.

Definition hashtbl_findref_return_wit_2 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (i_v: Z) (h_bucks: Z) (i: Z) (l_prev: (@list Z)) (l_res: (@list Z)) (l0: (@list Z)) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) ,
  [| (i_v = 0) |] 
  &&  [| (ind = ((hash_string_coq (k)) % ( 211 ) )) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (not_key k l_prev m ) |]
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllbseg (h_bucks + (ind * sizeof(PTR) ) ) i l_prev )
  **  ((i) # Ptr  |-> i_v)
  **  (sll i_v l_res )
  **  (store_map_missing_i store_sll b0 ind )
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
  **  (store_string key_pre k )
  **  (store_map store_name m )
|--
  ([| ((m (k)) = None) |] 
  &&  [| (0 = 0) |]
  &&  (store_hash_skeleton h_pre m )
  **  (store_string key_pre k ))
  ||
  (EX (p: Z) ,
  [| ((m (k)) = (Some (p))) |] 
  &&  [| (0 = &((p)  # "blist" ->ₛ "val")) |]
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
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (h_callee_bucks: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) ,
  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |]
  &&  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_callee_bucks)
  **  (PtrArray.full h_callee_bucks 211 lh )
  **  (store_map store_sll b0 )
  **  (store_map store_name m )
  **  (store_string key_pre k )
|--
  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |]
  &&  (store_string key_pre k )
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_callee_bucks)
  **  (PtrArray.full h_callee_bucks 211 lh )
  **  (store_map store_sll b0 )
  **  (store_map store_name m )
.

Definition hashtbl_findref_partial_solve_wit_3_pure := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (i_v: Z) (h_bucks: Z) (i: Z) (l_prev: (@list Z)) (l_res: (@list Z)) (l0: (@list Z)) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) ,
  [| (i_v <> 0) |] 
  &&  [| (ind = ((hash_string_coq (k)) % ( 211 ) )) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (not_key k l_prev m ) |]
  &&  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "i" ) )) # Ptr  |-> i)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllbseg (h_bucks + (ind * sizeof(PTR) ) ) i l_prev )
  **  ((i) # Ptr  |-> i_v)
  **  (sll i_v l_res )
  **  (store_map_missing_i store_sll b0 ind )
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
  **  (store_string key_pre k )
  **  (store_map store_name m )
|--
  [| (i_v <> 0) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l_prev) (l_res))))))) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| ((app (l_prev) (l_res)) = (app (l_prev) (l_res))) |]
.

Definition hashtbl_findref_partial_solve_wit_3_aux := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (i_v: Z) (h_bucks: Z) (i: Z) (l_prev: (@list Z)) (l_res: (@list Z)) (l0: (@list Z)) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) ,
  [| (i_v <> 0) |] 
  &&  [| (ind = ((hash_string_coq (k)) % ( 211 ) )) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (not_key k l_prev m ) |]
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllbseg (h_bucks + (ind * sizeof(PTR) ) ) i l_prev )
  **  ((i) # Ptr  |-> i_v)
  **  (sll i_v l_res )
  **  (store_map_missing_i store_sll b0 ind )
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
  **  (store_string key_pre k )
  **  (store_map store_name m )
|--
  [| (i_v <> 0) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l_prev) (l_res))))))) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| ((app (l_prev) (l_res)) = (app (l_prev) (l_res))) |] 
  &&  [| (i_v <> 0) |] 
  &&  [| (ind = ((hash_string_coq (k)) % ( 211 ) )) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (not_key k l_prev m ) |]
  &&  ((i) # Ptr  |-> i_v)
  **  (store_map store_name m )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllbseg (h_bucks + (ind * sizeof(PTR) ) ) i l_prev )
  **  (sll i_v l_res )
  **  (store_map_missing_i store_sll b0 ind )
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
  **  (store_string key_pre k )
.

Definition hashtbl_findref_partial_solve_wit_3 := hashtbl_findref_partial_solve_wit_3_pure -> hashtbl_findref_partial_solve_wit_3_aux.

Definition hashtbl_findref_partial_solve_wit_4 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (i_v: Z) (h_bucks: Z) (i: Z) (l_prev: (@list Z)) (l_res: (@list Z)) (l0: (@list Z)) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (i_v_key: Z) (i_v_next: Z) (l_resres: (@list Z)) (k_list_current: (@list Z)) ,
  [| (i_v <> 0) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l_prev) (l_res))))))) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| ((m (k_list_current)) = (Some (i_v))) |] 
  &&  [| ((app (l_prev) (l_res)) = (app (l_prev) (l_res))) |] 
  &&  [| (l_res = (cons (i_v) (l_resres))) |] 
  &&  [| (i_v <> 0) |] 
  &&  [| (ind = ((hash_string_coq (k)) % ( 211 ) )) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (not_key k l_prev m ) |]
  &&  ((i) # Ptr  |-> i_v)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllbseg (h_bucks + (ind * sizeof(PTR) ) ) i l_prev )
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  (sll i_v_next l_resres )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  (store_string i_v_key k_list_current )
  **  (store_map_missing_i store_name m k_list_current )
  **  (store_map_missing_i store_sll b0 ind )
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
  **  (store_string key_pre k )
|--
  [| (i_v <> 0) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l_prev) (l_res))))))) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| ((m (k_list_current)) = (Some (i_v))) |] 
  &&  [| (l_res = (cons (i_v) (l_resres))) |] 
  &&  [| (i_v <> 0) |] 
  &&  [| (ind = ((hash_string_coq (k)) % ( 211 ) )) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (not_key k l_prev m ) |]
  &&  (store_string key_pre k )
  **  (store_string i_v_key k_list_current )
  **  ((i) # Ptr  |-> i_v)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllbseg (h_bucks + (ind * sizeof(PTR) ) ) i l_prev )
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  (sll i_v_next l_resres )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  (store_map_missing_i store_name m k_list_current )
  **  (store_map_missing_i store_sll b0 ind )
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
.

Definition hashtbl_findref_partial_solve_wit_5_pure := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (i_v: Z) (h_bucks: Z) (i: Z) (l_prev: (@list Z)) (l_res: (@list Z)) (l0: (@list Z)) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (i_v_key: Z) (i_v_next: Z) (l_resres: (@list Z)) (k_list_current: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (key_pre = i_v_key) |] 
  &&  [| (k = k_list_current) |] 
  &&  [| (i_v <> 0) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l_prev) (l_res))))))) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| ((m (k_list_current)) = (Some (i_v))) |] 
  &&  [| (l_res = (cons (i_v) (l_resres))) |] 
  &&  [| (i_v <> 0) |] 
  &&  [| (ind = ((hash_string_coq (k)) % ( 211 ) )) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (not_key k l_prev m ) |]
  &&  ((( &( "b" ) )) # Ptr  |-> i_v)
  **  (store_string key_pre k )
  **  (store_string i_v_key k_list_current )
  **  ((( &( "i" ) )) # Ptr  |-> i)
  **  ((i) # Ptr  |-> i_v_next)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllbseg (h_bucks + (ind * sizeof(PTR) ) ) i l_prev )
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  (sll i_v_next l_resres )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  (store_map_missing_i store_name m k_list_current )
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  (store_map_missing_i store_sll b0 ind )
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
|--
  [| (i_v_next <> 0) |]
.

Definition hashtbl_findref_partial_solve_wit_5_aux := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (i_v: Z) (h_bucks: Z) (i: Z) (l_prev: (@list Z)) (l_res: (@list Z)) (l0: (@list Z)) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (i_v_key: Z) (i_v_next: Z) (l_resres: (@list Z)) (k_list_current: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (key_pre = i_v_key) |] 
  &&  [| (k = k_list_current) |] 
  &&  [| (i_v <> 0) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l_prev) (l_res))))))) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| ((m (k_list_current)) = (Some (i_v))) |] 
  &&  [| (l_res = (cons (i_v) (l_resres))) |] 
  &&  [| (i_v <> 0) |] 
  &&  [| (ind = ((hash_string_coq (k)) % ( 211 ) )) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (not_key k l_prev m ) |]
  &&  (store_string key_pre k )
  **  (store_string i_v_key k_list_current )
  **  ((i) # Ptr  |-> i_v_next)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllbseg (h_bucks + (ind * sizeof(PTR) ) ) i l_prev )
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  (sll i_v_next l_resres )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  (store_map_missing_i store_name m k_list_current )
  **  (store_map_missing_i store_sll b0 ind )
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
|--
  [| (i_v_next <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (key_pre = i_v_key) |] 
  &&  [| (k = k_list_current) |] 
  &&  [| (i_v <> 0) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l_prev) (l_res))))))) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| ((m (k_list_current)) = (Some (i_v))) |] 
  &&  [| (l_res = (cons (i_v) (l_resres))) |] 
  &&  [| (i_v <> 0) |] 
  &&  [| (ind = ((hash_string_coq (k)) % ( 211 ) )) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (not_key k l_prev m ) |]
  &&  ((i) # Ptr  |-> i_v_next)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllbseg (h_bucks + (ind * sizeof(PTR) ) ) i l_prev )
  **  (store_string key_pre k )
  **  (store_string i_v_key k_list_current )
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  (sll i_v_next l_resres )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  (store_map_missing_i store_name m k_list_current )
  **  (store_map_missing_i store_sll b0 ind )
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
.

Definition hashtbl_findref_partial_solve_wit_5 := hashtbl_findref_partial_solve_wit_5_pure -> hashtbl_findref_partial_solve_wit_5_aux.

Definition hashtbl_findref_which_implies_wit_1 := 
forall (h_pre: Z) (m: ((@list Z) -> (@option Z))) ,
  (store_hash_skeleton h_pre m )
|--
  EX (h_pre_bucks: Z)  (lh: (@list Z))  (b0: (Z -> (@option (Z * (@list Z)))))  (l: (@list Z)) ,
  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |]
  &&  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (PtrArray.full h_pre_bucks 211 lh )
  **  (store_map store_sll b0 )
  **  (store_map store_name m )
.

Definition hashtbl_findref_which_implies_wit_2 := 
forall (m: ((@list Z) -> (@option Z))) (lh: (@list Z)) (l_prev: (@list Z)) (l_res: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l0: (@list Z)) (i: Z) (i_v: Z) (ind: Z) (h: Z) (h_bucks: Z) ,
  [| (i_v <> 0) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0))))) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |]
  &&  ((i) # Ptr  |-> i_v)
  **  (store_map store_name m )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllbseg (h_bucks + (ind * sizeof(PTR) ) ) i l_prev )
  **  (sll i_v l_res )
|--
  EX (i_v_key: Z)  (i_v_next: Z)  (l_resres: (@list Z))  (k_list_current: (@list Z)) ,
  [| (i_v <> 0) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0))))) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| ((m (k_list_current)) = (Some (i_v))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l_res = (cons (i_v) (l_resres))) |]
  &&  ((i) # Ptr  |-> i_v)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllbseg (h_bucks + (ind * sizeof(PTR) ) ) i l_prev )
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  (sll i_v_next l_resres )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  (store_string i_v_key k_list_current )
  **  (store_map_missing_i store_name m k_list_current )
.

Definition hashtbl_findref_which_implies_wit_3 := 
forall (l_prev: (@list Z)) (i: Z) (i_v: Z) (ind: Z) (h: Z) (h_bucks: Z) ,
  [| (i_v <> 0) |]
  &&  ((i) # Ptr  |-> i_v)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllbseg (h_bucks + (ind * sizeof(PTR) ) ) i l_prev )
|--
  EX (lh: (@list Z)) ,
  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> (Znth (ind) (lh) (0)))
  **  (sllbseg &(((Znth (ind) (lh) (0)))  # "blist" ->ₛ "next") i l_prev )
.

(*----- Function hashtbl_remove -----*)

Definition hashtbl_remove_safety_wit_1 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (h_bucks: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (retval: Z) ,
  [| (retval = (hash_string_coq (k))) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| (map_composable m1 m2 ) |]
  &&  (store_string key_pre k )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (PtrArray.full h_bucks 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m1 )
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
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (h_bucks: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (retval: Z) ,
  [| (retval = (hash_string_coq (k))) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| (map_composable m1 m2 ) |]
  &&  (store_string key_pre k )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (PtrArray.full h_bucks 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m1 )
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
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (val: Z) (itv_next: Z) (h_top: Z) (itv_down_up: Z) (itv_up_down: Z) (itv_down: Z) (itv_up: Z) (itv_key: Z) (k_list: (@list Z)) (removed: Z) (h_pre_bucks: Z) (l_res: (@list Z)) (buck: Z) (itv: Z) (it: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (dl_up: (@list Z)) (dl_down: (@list Z)) (ind: Z) (l_prev: (@list Z)) ,
  [| (not_key k l_prev m1 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up) (dl_down)) ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> itv)
  **  (store_map_missing_i store_sll b ind )
  **  (sllseg buck itv l_prev )
  **  (sll itv l_res )
  **  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_pre_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") it 0 &((itv)  # "blist" ->ₛ "up") dl_up )
  **  (dll it &((itv)  # "blist" ->ₛ "up") dl_down )
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key)
  **  (store_string itv_key k_list )
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_up) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_down) # Ptr  |->_)
  **  ((&((itv_up)  # "blist" ->ₛ "down")) # Ptr  |-> itv_up_down)
  **  ((itv_up_down) # Ptr  |->_)
  **  ((&((itv_down)  # "blist" ->ₛ "up")) # Ptr  |-> itv_down_up)
  **  ((itv_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  ((h_top) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> itv_next)
  **  ((itv_next) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map store_uint m2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_remove_safety_wit_4 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (val: Z) (itv_next: Z) (h_top: Z) (itv_down_up: Z) (itv_up_down: Z) (itv_down: Z) (itv_up: Z) (itv_key: Z) (k_list: (@list Z)) (removed: Z) (h_pre_bucks: Z) (l_res: (@list Z)) (buck: Z) (itv: Z) (it: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (dl_up: (@list Z)) (dl_down: (@list Z)) (ind: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (key_pre <> itv_key) |] 
  &&  [| (k <> k_list) |] 
  &&  [| (itv <> 0) |] 
  &&  [| (not_key k l_prev m1 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up) (dl_down)) ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  (store_string key_pre k )
  **  (store_string itv_key k_list )
  **  ((( &( "b" ) )) # Ptr  |-> itv)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> itv)
  **  (store_map_missing_i store_sll b ind )
  **  (sllseg buck itv l_prev )
  **  (sll itv l_res )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_pre_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") it 0 &((itv)  # "blist" ->ₛ "up") dl_up )
  **  (dll it &((itv)  # "blist" ->ₛ "up") dl_down )
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_up) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_down) # Ptr  |->_)
  **  ((&((itv_up)  # "blist" ->ₛ "down")) # Ptr  |-> itv_up_down)
  **  ((itv_up_down) # Ptr  |->_)
  **  ((&((itv_down)  # "blist" ->ₛ "up")) # Ptr  |-> itv_down_up)
  **  ((itv_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  ((h_top) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> itv_next)
  **  ((itv_next) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map store_uint m2 )
|--
  [| False |]
.

Definition hashtbl_remove_safety_wit_5 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (val: Z) (itv_next: Z) (h_top: Z) (itv_down_up: Z) (itv_up_down: Z) (itv_down: Z) (itv_up: Z) (itv_key: Z) (k_list: (@list Z)) (removed: Z) (h_pre_bucks: Z) (l_res: (@list Z)) (buck: Z) (itv: Z) (it: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (dl_up: (@list Z)) (dl_down: (@list Z)) (ind: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (key_pre = itv_key) |] 
  &&  [| (k = k_list) |] 
  &&  [| (itv <> 0) |] 
  &&  [| (not_key k l_prev m1 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up) (dl_down)) ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  (store_string key_pre k )
  **  (store_string itv_key k_list )
  **  ((( &( "b" ) )) # Ptr  |-> itv)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> itv)
  **  (store_map_missing_i store_sll b ind )
  **  (sllseg buck itv l_prev )
  **  (sll itv l_res )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_pre_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") it 0 &((itv)  # "blist" ->ₛ "up") dl_up )
  **  (dll it &((itv)  # "blist" ->ₛ "up") dl_down )
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_up) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_down) # Ptr  |->_)
  **  ((&((itv_up)  # "blist" ->ₛ "down")) # Ptr  |-> itv_up_down)
  **  ((itv_up_down) # Ptr  |->_)
  **  ((&((itv_down)  # "blist" ->ₛ "up")) # Ptr  |-> itv_down_up)
  **  ((itv_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  ((h_top) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> itv_next)
  **  ((itv_next) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map store_uint m2 )
|--
  [| False |]
.

Definition hashtbl_remove_safety_wit_6 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (val: Z) (itv_next: Z) (h_top: Z) (itv_down_up: Z) (itv_up_down: Z) (itv_down: Z) (itv_up: Z) (itv_key: Z) (k_list: (@list Z)) (removed: Z) (h_pre_bucks: Z) (l_res: (@list Z)) (buck: Z) (itv: Z) (it: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (dl_up: (@list Z)) (dl_down: (@list Z)) (ind: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (h_top = itv) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (key_pre = itv_key) |] 
  &&  [| (k = k_list) |] 
  &&  [| (itv <> 0) |] 
  &&  [| (not_key k l_prev m1 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up) (dl_down)) ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  (store_string key_pre k )
  **  (store_string itv_key k_list )
  **  ((( &( "b" ) )) # Ptr  |-> itv)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> itv)
  **  (store_map_missing_i store_sll b ind )
  **  (sllseg buck itv l_prev )
  **  (sll itv l_res )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_pre_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") it 0 &((itv)  # "blist" ->ₛ "up") dl_up )
  **  (dll it &((itv)  # "blist" ->ₛ "up") dl_down )
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_up) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_down) # Ptr  |->_)
  **  ((&((itv_up)  # "blist" ->ₛ "down")) # Ptr  |-> itv_up_down)
  **  ((itv_up_down) # Ptr  |->_)
  **  ((&((itv_down)  # "blist" ->ₛ "up")) # Ptr  |-> itv_down_up)
  **  ((itv_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> itv_down)
  **  ((h_top) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> itv_next)
  **  ((itv_next) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map store_uint m2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_remove_safety_wit_7 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (val: Z) (itv_next: Z) (h_top: Z) (itv_down_up: Z) (itv_up_down: Z) (itv_down: Z) (itv_up: Z) (itv_key: Z) (k_list: (@list Z)) (removed: Z) (h_pre_bucks: Z) (l_res: (@list Z)) (buck: Z) (itv: Z) (it: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (dl_up: (@list Z)) (dl_down: (@list Z)) (ind: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (h_top <> itv) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (key_pre = itv_key) |] 
  &&  [| (k = k_list) |] 
  &&  [| (itv <> 0) |] 
  &&  [| (not_key k l_prev m1 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up) (dl_down)) ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  (store_string key_pre k )
  **  (store_string itv_key k_list )
  **  ((( &( "b" ) )) # Ptr  |-> itv)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> itv)
  **  (store_map_missing_i store_sll b ind )
  **  (sllseg buck itv l_prev )
  **  (sll itv l_res )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_pre_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") it 0 &((itv)  # "blist" ->ₛ "up") dl_up )
  **  (dll it &((itv)  # "blist" ->ₛ "up") dl_down )
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_up) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_down) # Ptr  |->_)
  **  ((&((itv_up)  # "blist" ->ₛ "down")) # Ptr  |-> itv_up_down)
  **  ((itv_up_down) # Ptr  |->_)
  **  ((&((itv_down)  # "blist" ->ₛ "up")) # Ptr  |-> itv_down_up)
  **  ((itv_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  ((h_top) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> itv_next)
  **  ((itv_next) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map store_uint m2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_remove_safety_wit_8 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (val: Z) (itv_next: Z) (h_top: Z) (itv_down_up: Z) (itv_up_down: Z) (itv_down: Z) (itv_up: Z) (itv_key: Z) (k_list: (@list Z)) (removed: Z) (h_pre_bucks: Z) (l_res: (@list Z)) (buck: Z) (itv: Z) (it: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (dl_up: (@list Z)) (dl_down: (@list Z)) (ind: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (itv_up <> 0) |] 
  &&  [| (h_top <> itv) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (key_pre = itv_key) |] 
  &&  [| (k = k_list) |] 
  &&  [| (itv <> 0) |] 
  &&  [| (not_key k l_prev m1 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up) (dl_down)) ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  (store_string key_pre k )
  **  (store_string itv_key k_list )
  **  ((( &( "b" ) )) # Ptr  |-> itv)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> itv)
  **  (store_map_missing_i store_sll b ind )
  **  (sllseg buck itv l_prev )
  **  (sll itv l_res )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_pre_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") it 0 &((itv)  # "blist" ->ₛ "up") dl_up )
  **  (dll it &((itv)  # "blist" ->ₛ "up") dl_down )
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_up) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_down) # Ptr  |->_)
  **  ((&((itv_up)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_up_down) # Ptr  |->_)
  **  ((&((itv_down)  # "blist" ->ₛ "up")) # Ptr  |-> itv_down_up)
  **  ((itv_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  ((h_top) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> itv_next)
  **  ((itv_next) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map store_uint m2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_remove_safety_wit_9 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (val: Z) (itv_next: Z) (h_top: Z) (itv_down_up: Z) (itv_up_down: Z) (itv_down: Z) (itv_up: Z) (itv_key: Z) (k_list: (@list Z)) (removed: Z) (h_pre_bucks: Z) (l_res: (@list Z)) (buck: Z) (itv: Z) (it: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (dl_up: (@list Z)) (dl_down: (@list Z)) (ind: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (itv_up <> 0) |] 
  &&  [| (h_top = itv) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (key_pre = itv_key) |] 
  &&  [| (k = k_list) |] 
  &&  [| (itv <> 0) |] 
  &&  [| (not_key k l_prev m1 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up) (dl_down)) ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  (store_string key_pre k )
  **  (store_string itv_key k_list )
  **  ((( &( "b" ) )) # Ptr  |-> itv)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> itv)
  **  (store_map_missing_i store_sll b ind )
  **  (sllseg buck itv l_prev )
  **  (sll itv l_res )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_pre_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") it 0 &((itv)  # "blist" ->ₛ "up") dl_up )
  **  (dll it &((itv)  # "blist" ->ₛ "up") dl_down )
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_up) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_down) # Ptr  |->_)
  **  ((&((itv_up)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_up_down) # Ptr  |->_)
  **  ((&((itv_down)  # "blist" ->ₛ "up")) # Ptr  |-> itv_down_up)
  **  ((itv_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> itv_down)
  **  ((h_top) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> itv_next)
  **  ((itv_next) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map store_uint m2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_remove_safety_wit_10 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (val: Z) (itv_next: Z) (h_top: Z) (itv_down_up: Z) (itv_up_down: Z) (itv_down: Z) (itv_up: Z) (itv_key: Z) (k_list: (@list Z)) (removed: Z) (h_pre_bucks: Z) (l_res: (@list Z)) (buck: Z) (itv: Z) (it: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (dl_up: (@list Z)) (dl_down: (@list Z)) (ind: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (itv_up = 0) |] 
  &&  [| (h_top = itv) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (key_pre = itv_key) |] 
  &&  [| (k = k_list) |] 
  &&  [| (itv <> 0) |] 
  &&  [| (not_key k l_prev m1 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up) (dl_down)) ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  (store_string key_pre k )
  **  (store_string itv_key k_list )
  **  ((( &( "b" ) )) # Ptr  |-> itv)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> itv)
  **  (store_map_missing_i store_sll b ind )
  **  (sllseg buck itv l_prev )
  **  (sll itv l_res )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_pre_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") it 0 &((itv)  # "blist" ->ₛ "up") dl_up )
  **  (dll it &((itv)  # "blist" ->ₛ "up") dl_down )
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_up) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_down) # Ptr  |->_)
  **  ((&((itv_up)  # "blist" ->ₛ "down")) # Ptr  |-> itv_up_down)
  **  ((itv_up_down) # Ptr  |->_)
  **  ((&((itv_down)  # "blist" ->ₛ "up")) # Ptr  |-> itv_down_up)
  **  ((itv_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> itv_down)
  **  ((h_top) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> itv_next)
  **  ((itv_next) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map store_uint m2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_remove_safety_wit_11 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (val: Z) (itv_next: Z) (h_top: Z) (itv_down_up: Z) (itv_up_down: Z) (itv_down: Z) (itv_up: Z) (itv_key: Z) (k_list: (@list Z)) (removed: Z) (h_pre_bucks: Z) (l_res: (@list Z)) (buck: Z) (itv: Z) (it: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (dl_up: (@list Z)) (dl_down: (@list Z)) (ind: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (itv_up = 0) |] 
  &&  [| (h_top <> itv) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (key_pre = itv_key) |] 
  &&  [| (k = k_list) |] 
  &&  [| (itv <> 0) |] 
  &&  [| (not_key k l_prev m1 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up) (dl_down)) ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  (store_string key_pre k )
  **  (store_string itv_key k_list )
  **  ((( &( "b" ) )) # Ptr  |-> itv)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> itv)
  **  (store_map_missing_i store_sll b ind )
  **  (sllseg buck itv l_prev )
  **  (sll itv l_res )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_pre_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") it 0 &((itv)  # "blist" ->ₛ "up") dl_up )
  **  (dll it &((itv)  # "blist" ->ₛ "up") dl_down )
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_up) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_down) # Ptr  |->_)
  **  ((&((itv_up)  # "blist" ->ₛ "down")) # Ptr  |-> itv_up_down)
  **  ((itv_up_down) # Ptr  |->_)
  **  ((&((itv_down)  # "blist" ->ₛ "up")) # Ptr  |-> itv_down_up)
  **  ((itv_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  ((h_top) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> itv_next)
  **  ((itv_next) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map store_uint m2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_remove_safety_wit_12 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (val: Z) (itv_next: Z) (h_top: Z) (itv_down_up: Z) (itv_up_down: Z) (itv_down: Z) (itv_up: Z) (itv_key: Z) (k_list: (@list Z)) (removed: Z) (h_pre_bucks: Z) (l_res: (@list Z)) (buck: Z) (itv: Z) (it: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (dl_up: (@list Z)) (dl_down: (@list Z)) (ind: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (itv_down = 0) |] 
  &&  [| (itv_up = 0) |] 
  &&  [| (h_top <> itv) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (key_pre = itv_key) |] 
  &&  [| (k = k_list) |] 
  &&  [| (itv <> 0) |] 
  &&  [| (not_key k l_prev m1 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up) (dl_down)) ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  ((( &( "res" ) )) # UInt  |-> val)
  **  (store_string key_pre k )
  **  (store_string itv_key k_list )
  **  ((( &( "b" ) )) # Ptr  |-> itv)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> itv_next)
  **  (store_map_missing_i store_sll b ind )
  **  (sllseg buck itv l_prev )
  **  (sll itv l_res )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_pre_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") it 0 &((itv)  # "blist" ->ₛ "up") dl_up )
  **  (dll it &((itv)  # "blist" ->ₛ "up") dl_down )
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_up) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_down) # Ptr  |->_)
  **  ((&((itv_up)  # "blist" ->ₛ "down")) # Ptr  |-> itv_up_down)
  **  ((itv_up_down) # Ptr  |->_)
  **  ((&((itv_down)  # "blist" ->ₛ "up")) # Ptr  |-> itv_down_up)
  **  ((itv_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  ((h_top) # Ptr  |->_)
  **  ((itv_next) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map store_uint m2 )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition hashtbl_remove_safety_wit_13 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (val: Z) (itv_next: Z) (h_top: Z) (itv_down_up: Z) (itv_up_down: Z) (itv_down: Z) (itv_up: Z) (itv_key: Z) (k_list: (@list Z)) (removed: Z) (h_pre_bucks: Z) (l_res: (@list Z)) (buck: Z) (itv: Z) (it: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (dl_up: (@list Z)) (dl_down: (@list Z)) (ind: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (itv_down = 0) |] 
  &&  [| (itv_up = 0) |] 
  &&  [| (h_top = itv) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (key_pre = itv_key) |] 
  &&  [| (k = k_list) |] 
  &&  [| (itv <> 0) |] 
  &&  [| (not_key k l_prev m1 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up) (dl_down)) ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  ((( &( "res" ) )) # UInt  |-> val)
  **  (store_string key_pre k )
  **  (store_string itv_key k_list )
  **  ((( &( "b" ) )) # Ptr  |-> itv)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> itv_next)
  **  (store_map_missing_i store_sll b ind )
  **  (sllseg buck itv l_prev )
  **  (sll itv l_res )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_pre_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") it 0 &((itv)  # "blist" ->ₛ "up") dl_up )
  **  (dll it &((itv)  # "blist" ->ₛ "up") dl_down )
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_up) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_down) # Ptr  |->_)
  **  ((&((itv_up)  # "blist" ->ₛ "down")) # Ptr  |-> itv_up_down)
  **  ((itv_up_down) # Ptr  |->_)
  **  ((&((itv_down)  # "blist" ->ₛ "up")) # Ptr  |-> itv_down_up)
  **  ((itv_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> itv_down)
  **  ((h_top) # Ptr  |->_)
  **  ((itv_next) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map store_uint m2 )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition hashtbl_remove_safety_wit_14 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (val: Z) (itv_next: Z) (h_top: Z) (itv_down_up: Z) (itv_up_down: Z) (itv_down: Z) (itv_up: Z) (itv_key: Z) (k_list: (@list Z)) (removed: Z) (h_pre_bucks: Z) (l_res: (@list Z)) (buck: Z) (itv: Z) (it: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (dl_up: (@list Z)) (dl_down: (@list Z)) (ind: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (itv_down = 0) |] 
  &&  [| (itv_up <> 0) |] 
  &&  [| (h_top = itv) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (key_pre = itv_key) |] 
  &&  [| (k = k_list) |] 
  &&  [| (itv <> 0) |] 
  &&  [| (not_key k l_prev m1 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up) (dl_down)) ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  ((( &( "res" ) )) # UInt  |-> val)
  **  (store_string key_pre k )
  **  (store_string itv_key k_list )
  **  ((( &( "b" ) )) # Ptr  |-> itv)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> itv_next)
  **  (store_map_missing_i store_sll b ind )
  **  (sllseg buck itv l_prev )
  **  (sll itv l_res )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_pre_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") it 0 &((itv)  # "blist" ->ₛ "up") dl_up )
  **  (dll it &((itv)  # "blist" ->ₛ "up") dl_down )
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_up) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_down) # Ptr  |->_)
  **  ((&((itv_up)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_up_down) # Ptr  |->_)
  **  ((&((itv_down)  # "blist" ->ₛ "up")) # Ptr  |-> itv_down_up)
  **  ((itv_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> itv_down)
  **  ((h_top) # Ptr  |->_)
  **  ((itv_next) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map store_uint m2 )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition hashtbl_remove_safety_wit_15 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (val: Z) (itv_next: Z) (h_top: Z) (itv_down_up: Z) (itv_up_down: Z) (itv_down: Z) (itv_up: Z) (itv_key: Z) (k_list: (@list Z)) (removed: Z) (h_pre_bucks: Z) (l_res: (@list Z)) (buck: Z) (itv: Z) (it: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (dl_up: (@list Z)) (dl_down: (@list Z)) (ind: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (itv_down = 0) |] 
  &&  [| (itv_up <> 0) |] 
  &&  [| (h_top <> itv) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (key_pre = itv_key) |] 
  &&  [| (k = k_list) |] 
  &&  [| (itv <> 0) |] 
  &&  [| (not_key k l_prev m1 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up) (dl_down)) ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  ((( &( "res" ) )) # UInt  |-> val)
  **  (store_string key_pre k )
  **  (store_string itv_key k_list )
  **  ((( &( "b" ) )) # Ptr  |-> itv)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> itv_next)
  **  (store_map_missing_i store_sll b ind )
  **  (sllseg buck itv l_prev )
  **  (sll itv l_res )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_pre_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") it 0 &((itv)  # "blist" ->ₛ "up") dl_up )
  **  (dll it &((itv)  # "blist" ->ₛ "up") dl_down )
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_up) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_down) # Ptr  |->_)
  **  ((&((itv_up)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_up_down) # Ptr  |->_)
  **  ((&((itv_down)  # "blist" ->ₛ "up")) # Ptr  |-> itv_down_up)
  **  ((itv_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  ((h_top) # Ptr  |->_)
  **  ((itv_next) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map store_uint m2 )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition hashtbl_remove_safety_wit_16 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (val: Z) (itv_next: Z) (h_top: Z) (itv_down_up: Z) (itv_up_down: Z) (itv_down: Z) (itv_up: Z) (itv_key: Z) (k_list: (@list Z)) (removed: Z) (h_pre_bucks: Z) (l_res: (@list Z)) (buck: Z) (itv: Z) (it: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (dl_up: (@list Z)) (dl_down: (@list Z)) (ind: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (itv_down <> 0) |] 
  &&  [| (itv_up <> 0) |] 
  &&  [| (h_top <> itv) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (key_pre = itv_key) |] 
  &&  [| (k = k_list) |] 
  &&  [| (itv <> 0) |] 
  &&  [| (not_key k l_prev m1 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up) (dl_down)) ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  ((( &( "res" ) )) # UInt  |-> val)
  **  (store_string key_pre k )
  **  (store_string itv_key k_list )
  **  ((( &( "b" ) )) # Ptr  |-> itv)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> itv_next)
  **  (store_map_missing_i store_sll b ind )
  **  (sllseg buck itv l_prev )
  **  (sll itv l_res )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_pre_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") it 0 &((itv)  # "blist" ->ₛ "up") dl_up )
  **  (dll it &((itv)  # "blist" ->ₛ "up") dl_down )
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_up) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_down) # Ptr  |->_)
  **  ((&((itv_up)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_up_down) # Ptr  |->_)
  **  ((&((itv_down)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  ((h_top) # Ptr  |->_)
  **  ((itv_next) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map store_uint m2 )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition hashtbl_remove_safety_wit_17 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (val: Z) (itv_next: Z) (h_top: Z) (itv_down_up: Z) (itv_up_down: Z) (itv_down: Z) (itv_up: Z) (itv_key: Z) (k_list: (@list Z)) (removed: Z) (h_pre_bucks: Z) (l_res: (@list Z)) (buck: Z) (itv: Z) (it: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (dl_up: (@list Z)) (dl_down: (@list Z)) (ind: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (itv_down <> 0) |] 
  &&  [| (itv_up <> 0) |] 
  &&  [| (h_top = itv) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (key_pre = itv_key) |] 
  &&  [| (k = k_list) |] 
  &&  [| (itv <> 0) |] 
  &&  [| (not_key k l_prev m1 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up) (dl_down)) ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  ((( &( "res" ) )) # UInt  |-> val)
  **  (store_string key_pre k )
  **  (store_string itv_key k_list )
  **  ((( &( "b" ) )) # Ptr  |-> itv)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> itv_next)
  **  (store_map_missing_i store_sll b ind )
  **  (sllseg buck itv l_prev )
  **  (sll itv l_res )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_pre_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") it 0 &((itv)  # "blist" ->ₛ "up") dl_up )
  **  (dll it &((itv)  # "blist" ->ₛ "up") dl_down )
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_up) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_down) # Ptr  |->_)
  **  ((&((itv_up)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_up_down) # Ptr  |->_)
  **  ((&((itv_down)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> itv_down)
  **  ((h_top) # Ptr  |->_)
  **  ((itv_next) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map store_uint m2 )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition hashtbl_remove_safety_wit_18 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (val: Z) (itv_next: Z) (h_top: Z) (itv_down_up: Z) (itv_up_down: Z) (itv_down: Z) (itv_up: Z) (itv_key: Z) (k_list: (@list Z)) (removed: Z) (h_pre_bucks: Z) (l_res: (@list Z)) (buck: Z) (itv: Z) (it: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (dl_up: (@list Z)) (dl_down: (@list Z)) (ind: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (itv_down <> 0) |] 
  &&  [| (itv_up = 0) |] 
  &&  [| (h_top = itv) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (key_pre = itv_key) |] 
  &&  [| (k = k_list) |] 
  &&  [| (itv <> 0) |] 
  &&  [| (not_key k l_prev m1 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up) (dl_down)) ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  ((( &( "res" ) )) # UInt  |-> val)
  **  (store_string key_pre k )
  **  (store_string itv_key k_list )
  **  ((( &( "b" ) )) # Ptr  |-> itv)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> itv_next)
  **  (store_map_missing_i store_sll b ind )
  **  (sllseg buck itv l_prev )
  **  (sll itv l_res )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_pre_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") it 0 &((itv)  # "blist" ->ₛ "up") dl_up )
  **  (dll it &((itv)  # "blist" ->ₛ "up") dl_down )
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_up) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_down) # Ptr  |->_)
  **  ((&((itv_up)  # "blist" ->ₛ "down")) # Ptr  |-> itv_up_down)
  **  ((itv_up_down) # Ptr  |->_)
  **  ((&((itv_down)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> itv_down)
  **  ((h_top) # Ptr  |->_)
  **  ((itv_next) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map store_uint m2 )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition hashtbl_remove_safety_wit_19 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (val: Z) (itv_next: Z) (h_top: Z) (itv_down_up: Z) (itv_up_down: Z) (itv_down: Z) (itv_up: Z) (itv_key: Z) (k_list: (@list Z)) (removed: Z) (h_pre_bucks: Z) (l_res: (@list Z)) (buck: Z) (itv: Z) (it: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (dl_up: (@list Z)) (dl_down: (@list Z)) (ind: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (itv_down <> 0) |] 
  &&  [| (itv_up = 0) |] 
  &&  [| (h_top <> itv) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (key_pre = itv_key) |] 
  &&  [| (k = k_list) |] 
  &&  [| (itv <> 0) |] 
  &&  [| (not_key k l_prev m1 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up) (dl_down)) ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  ((( &( "res" ) )) # UInt  |-> val)
  **  (store_string key_pre k )
  **  (store_string itv_key k_list )
  **  ((( &( "b" ) )) # Ptr  |-> itv)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> itv_next)
  **  (store_map_missing_i store_sll b ind )
  **  (sllseg buck itv l_prev )
  **  (sll itv l_res )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_pre_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") it 0 &((itv)  # "blist" ->ₛ "up") dl_up )
  **  (dll it &((itv)  # "blist" ->ₛ "up") dl_down )
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_up) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_down) # Ptr  |->_)
  **  ((&((itv_up)  # "blist" ->ₛ "down")) # Ptr  |-> itv_up_down)
  **  ((itv_up_down) # Ptr  |->_)
  **  ((&((itv_down)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  ((h_top) # Ptr  |->_)
  **  ((itv_next) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map store_uint m2 )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition hashtbl_remove_safety_wit_20 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (val: Z) (itv_next: Z) (h_top: Z) (itv_down_up: Z) (itv_up_down: Z) (itv_down: Z) (itv_up: Z) (itv_key: Z) (k_list: (@list Z)) (removed: Z) (h_pre_bucks: Z) (l_res: (@list Z)) (buck: Z) (itv: Z) (it: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (dl_up: (@list Z)) (dl_down: (@list Z)) (ind: Z) (l_prev: (@list Z)) ,
  [| (itv = 0) |] 
  &&  [| (not_key k l_prev m1 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up) (dl_down)) ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> itv)
  **  (store_map_missing_i store_sll b ind )
  **  (sllseg buck itv l_prev )
  **  (sll itv l_res )
  **  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_pre_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") it 0 &((itv)  # "blist" ->ₛ "up") dl_up )
  **  (dll it &((itv)  # "blist" ->ₛ "up") dl_down )
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key)
  **  (store_string itv_key k_list )
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_up) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_down) # Ptr  |->_)
  **  ((&((itv_up)  # "blist" ->ₛ "down")) # Ptr  |-> itv_up_down)
  **  ((itv_up_down) # Ptr  |->_)
  **  ((&((itv_down)  # "blist" ->ₛ "up")) # Ptr  |-> itv_down_up)
  **  ((itv_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  ((h_top) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> itv_next)
  **  ((itv_next) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map store_uint m2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_remove_safety_wit_21 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (val: Z) (itv_next: Z) (h_top: Z) (itv_down_up: Z) (itv_up_down: Z) (itv_down: Z) (itv_up: Z) (itv_key: Z) (k_list: (@list Z)) (removed: Z) (h_pre_bucks: Z) (l_res: (@list Z)) (buck: Z) (itv: Z) (it: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (dl_up: (@list Z)) (dl_down: (@list Z)) (ind: Z) (l_prev: (@list Z)) ,
  [| (itv = 0) |] 
  &&  [| (not_key k l_prev m1 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up) (dl_down)) ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> itv)
  **  (store_map_missing_i store_sll b ind )
  **  (sllseg buck itv l_prev )
  **  (sll itv l_res )
  **  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_pre_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") it 0 &((itv)  # "blist" ->ₛ "up") dl_up )
  **  (dll it &((itv)  # "blist" ->ₛ "up") dl_down )
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |-> 0)
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key)
  **  (store_string itv_key k_list )
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_up) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_down) # Ptr  |->_)
  **  ((&((itv_up)  # "blist" ->ₛ "down")) # Ptr  |-> itv_up_down)
  **  ((itv_up_down) # Ptr  |->_)
  **  ((&((itv_down)  # "blist" ->ₛ "up")) # Ptr  |-> itv_down_up)
  **  ((itv_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  ((h_top) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> itv_next)
  **  ((itv_next) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map store_uint m2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_remove_entail_wit_1 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (h_bucks: Z) (lh_2: (@list Z)) (b_2: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (retval: Z) ,
  [| (retval = (hash_string_coq (k))) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh_2 b_2 ) |] 
  &&  [| (contain_all_correct_addrs m1 b_2 ) |] 
  &&  [| (map_composable m1 m2 ) |]
  &&  (store_string key_pre k )
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (PtrArray.full h_bucks 211 lh_2 )
  **  (store_map store_sll b_2 )
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  ((removed_pre) # Int  |->_)
|--
  EX (val: Z)  (itv_next: Z)  (h_top: Z)  (itv_down_up: Z)  (itv_up_down: Z)  (itv_down: Z)  (itv_up: Z)  (itv_key: Z)  (k_list: (@list Z))  (h_pre_bucks: Z)  (l_res: (@list Z))  (buck: Z)  (itv: Z)  (lh: (@list Z))  (b: (Z -> (@option (Z * (@list Z)))))  (dl_up: (@list Z))  (dl_down: (@list Z))  (l_prev: (@list Z)) ,
  [| (not_key k l_prev m1 ) |] 
  &&  [| (0 <= (retval % ( 211 ) )) |] 
  &&  [| ((retval % ( 211 ) ) < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up) (dl_down)) ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  (((h_bucks + ((retval % ( 211 ) ) * sizeof(PTR) ) )) # Ptr  |-> itv)
  **  (store_map_missing_i store_sll b (retval % ( 211 ) ) )
  **  (sllseg buck itv l_prev )
  **  (sll itv l_res )
  **  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_pre_bucks + ((retval % ( 211 ) ) * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (PtrArray.missing_i h_pre_bucks (retval % ( 211 ) ) 0 211 lh )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") (h_bucks + ((retval % ( 211 ) ) * sizeof(PTR) ) ) 0 &((itv)  # "blist" ->ₛ "up") dl_up )
  **  (dll (h_bucks + ((retval % ( 211 ) ) * sizeof(PTR) ) ) &((itv)  # "blist" ->ₛ "up") dl_down )
  **  ((removed_pre) # Int  |->_)
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key)
  **  (store_string itv_key k_list )
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_up) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_down) # Ptr  |->_)
  **  ((&((itv_up)  # "blist" ->ₛ "down")) # Ptr  |-> itv_up_down)
  **  ((itv_up_down) # Ptr  |->_)
  **  ((&((itv_down)  # "blist" ->ₛ "up")) # Ptr  |-> itv_down_up)
  **  ((itv_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  ((h_top) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> itv_next)
  **  ((itv_next) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map store_uint m2 )
.

Definition hashtbl_remove_entail_wit_2_1 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (val: Z) (itv_next: Z) (h_top: Z) (itv_down_up: Z) (itv_up_down: Z) (itv_down: Z) (itv_up: Z) (itv_key: Z) (k_list: (@list Z)) (removed: Z) (h_pre_bucks: Z) (l_res: (@list Z)) (buck: Z) (itv: Z) (it: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (dl_up: (@list Z)) (dl_down: (@list Z)) (ind: Z) (l_prev: (@list Z)) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (key_pre <> itv_key) |] 
  &&  [| (k <> k_list) |] 
  &&  [| (itv <> 0) |] 
  &&  [| (not_key k l_prev m1 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up) (dl_down)) ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  (store_string key_pre k )
  **  (store_string itv_key k_list )
  **  ((it) # Ptr  |-> itv)
  **  (store_map_missing_i store_sll b ind )
  **  (sllseg buck itv l_prev )
  **  (sll itv l_res )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_pre_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") it 0 &((itv)  # "blist" ->ₛ "up") dl_up )
  **  (dll it &((itv)  # "blist" ->ₛ "up") dl_down )
  **  ((removed) # Int  |->_)
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_up) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_down) # Ptr  |->_)
  **  ((&((itv_up)  # "blist" ->ₛ "down")) # Ptr  |-> itv_up_down)
  **  ((itv_up_down) # Ptr  |->_)
  **  ((&((itv_down)  # "blist" ->ₛ "up")) # Ptr  |-> itv_down_up)
  **  ((itv_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  ((h_top) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> itv_next)
  **  ((itv_next) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map store_uint m2 )
|--
  EX (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (key_pre = itv_key) |] 
  &&  [| (k = k_list) |] 
  &&  [| (itv <> 0) |] 
  &&  [| (not_key k l_prev m1 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up) (dl_down)) ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  (store_string key_pre k )
  **  (store_string itv_key k_list )
  **  ((it) # Ptr  |-> itv)
  **  (store_map_missing_i store_sll b ind )
  **  (sllseg buck itv l_prev )
  **  (sll itv l_res )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_pre_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") it 0 &((itv)  # "blist" ->ₛ "up") dl_up )
  **  (dll it &((itv)  # "blist" ->ₛ "up") dl_down )
  **  ((removed) # Int  |->_)
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_up) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_down) # Ptr  |->_)
  **  ((&((itv_up)  # "blist" ->ₛ "down")) # Ptr  |-> itv_up_down)
  **  ((itv_up_down) # Ptr  |->_)
  **  ((&((itv_down)  # "blist" ->ₛ "up")) # Ptr  |-> itv_down_up)
  **  ((itv_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  ((h_top) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> itv_next)
  **  ((itv_next) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map store_uint m2 )
.

Definition hashtbl_remove_entail_wit_2_2 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (val: Z) (itv_next: Z) (h_top: Z) (itv_down_up: Z) (itv_up_down: Z) (itv_down: Z) (itv_up: Z) (itv_key: Z) (k_list: (@list Z)) (removed: Z) (h_pre_bucks: Z) (l_res: (@list Z)) (buck: Z) (itv: Z) (it: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (dl_up: (@list Z)) (dl_down: (@list Z)) (ind: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (key_pre = itv_key) |] 
  &&  [| (k = k_list) |] 
  &&  [| (itv <> 0) |] 
  &&  [| (not_key k l_prev m1 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up) (dl_down)) ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  (store_string key_pre k )
  **  (store_string itv_key k_list )
  **  ((it) # Ptr  |-> itv)
  **  (store_map_missing_i store_sll b ind )
  **  (sllseg buck itv l_prev )
  **  (sll itv l_res )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_pre_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") it 0 &((itv)  # "blist" ->ₛ "up") dl_up )
  **  (dll it &((itv)  # "blist" ->ₛ "up") dl_down )
  **  ((removed) # Int  |->_)
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_up) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_down) # Ptr  |->_)
  **  ((&((itv_up)  # "blist" ->ₛ "down")) # Ptr  |-> itv_up_down)
  **  ((itv_up_down) # Ptr  |->_)
  **  ((&((itv_down)  # "blist" ->ₛ "up")) # Ptr  |-> itv_down_up)
  **  ((itv_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  ((h_top) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> itv_next)
  **  ((itv_next) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map store_uint m2 )
|--
  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (key_pre = itv_key) |] 
  &&  [| (k = k_list) |] 
  &&  [| (itv <> 0) |] 
  &&  [| (not_key k l_prev m1 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up) (dl_down)) ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  (store_string key_pre k )
  **  (store_string itv_key k_list )
  **  ((it) # Ptr  |-> itv)
  **  (store_map_missing_i store_sll b ind )
  **  (sllseg buck itv l_prev )
  **  (sll itv l_res )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_pre_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") it 0 &((itv)  # "blist" ->ₛ "up") dl_up )
  **  (dll it &((itv)  # "blist" ->ₛ "up") dl_down )
  **  ((removed) # Int  |->_)
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_up) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_down) # Ptr  |->_)
  **  ((&((itv_up)  # "blist" ->ₛ "down")) # Ptr  |-> itv_up_down)
  **  ((itv_up_down) # Ptr  |->_)
  **  ((&((itv_down)  # "blist" ->ₛ "up")) # Ptr  |-> itv_down_up)
  **  ((itv_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  ((h_top) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> itv_next)
  **  ((itv_next) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map store_uint m2 )
.

Definition hashtbl_remove_entail_wit_3_1 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (val: Z) (itv_next: Z) (h_top: Z) (itv_down_up: Z) (itv_up_down: Z) (itv_down: Z) (itv_up: Z) (itv_key: Z) (k_list: (@list Z)) (removed: Z) (h_pre_bucks: Z) (l_res: (@list Z)) (buck: Z) (itv: Z) (it: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (dl_up: (@list Z)) (dl_down: (@list Z)) (ind: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (key_pre <> itv_key) |] 
  &&  [| (k <> k_list) |] 
  &&  [| (itv <> 0) |] 
  &&  [| (not_key k l_prev m1 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up) (dl_down)) ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  (store_string key_pre k )
  **  (store_string itv_key k_list )
  **  ((it) # Ptr  |-> itv)
  **  (store_map_missing_i store_sll b ind )
  **  (sllseg buck itv l_prev )
  **  (sll itv l_res )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_pre_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") it 0 &((itv)  # "blist" ->ₛ "up") dl_up )
  **  (dll it &((itv)  # "blist" ->ₛ "up") dl_down )
  **  ((removed) # Int  |->_)
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_up) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_down) # Ptr  |->_)
  **  ((&((itv_up)  # "blist" ->ₛ "down")) # Ptr  |-> itv_up_down)
  **  ((itv_up_down) # Ptr  |->_)
  **  ((&((itv_down)  # "blist" ->ₛ "up")) # Ptr  |-> itv_down_up)
  **  ((itv_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  ((h_top) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> itv_next)
  **  ((itv_next) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map store_uint m2 )
|--
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (key_pre <> itv_key) |] 
  &&  [| (k <> k_list) |] 
  &&  [| (itv <> 0) |] 
  &&  [| (not_key k l_prev m1 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up) (dl_down)) ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  (store_string key_pre k )
  **  (store_string itv_key k_list )
  **  ((it) # Ptr  |-> itv)
  **  (store_map_missing_i store_sll b ind )
  **  (sllseg buck itv l_prev )
  **  (sll itv l_res )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_pre_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") it 0 &((itv)  # "blist" ->ₛ "up") dl_up )
  **  (dll it &((itv)  # "blist" ->ₛ "up") dl_down )
  **  ((removed) # Int  |->_)
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_up) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_down) # Ptr  |->_)
  **  ((&((itv_up)  # "blist" ->ₛ "down")) # Ptr  |-> itv_up_down)
  **  ((itv_up_down) # Ptr  |->_)
  **  ((&((itv_down)  # "blist" ->ₛ "up")) # Ptr  |-> itv_down_up)
  **  ((itv_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  ((h_top) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> itv_next)
  **  ((itv_next) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map store_uint m2 )
.

Definition hashtbl_remove_entail_wit_3_2 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (val: Z) (itv_next: Z) (h_top: Z) (itv_down_up: Z) (itv_up_down: Z) (itv_down: Z) (itv_up: Z) (itv_key: Z) (k_list: (@list Z)) (removed: Z) (h_pre_bucks: Z) (l_res: (@list Z)) (buck: Z) (itv: Z) (it: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (dl_up: (@list Z)) (dl_down: (@list Z)) (ind: Z) (l_prev: (@list Z)) (retval_2: Z) ,
  [| (retval_2 = 0) |] 
  &&  [| (retval_2 = 1) |] 
  &&  [| (key_pre = itv_key) |] 
  &&  [| (k = k_list) |] 
  &&  [| (itv <> 0) |] 
  &&  [| (not_key k l_prev m1 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up) (dl_down)) ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  (store_string key_pre k )
  **  (store_string itv_key k_list )
  **  ((it) # Ptr  |-> itv)
  **  (store_map_missing_i store_sll b ind )
  **  (sllseg buck itv l_prev )
  **  (sll itv l_res )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_pre_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") it 0 &((itv)  # "blist" ->ₛ "up") dl_up )
  **  (dll it &((itv)  # "blist" ->ₛ "up") dl_down )
  **  ((removed) # Int  |->_)
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_up) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_down) # Ptr  |->_)
  **  ((&((itv_up)  # "blist" ->ₛ "down")) # Ptr  |-> itv_up_down)
  **  ((itv_up_down) # Ptr  |->_)
  **  ((&((itv_down)  # "blist" ->ₛ "up")) # Ptr  |-> itv_down_up)
  **  ((itv_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  ((h_top) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> itv_next)
  **  ((itv_next) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map store_uint m2 )
|--
  EX (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (key_pre <> itv_key) |] 
  &&  [| (k <> k_list) |] 
  &&  [| (itv <> 0) |] 
  &&  [| (not_key k l_prev m1 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up) (dl_down)) ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  (store_string key_pre k )
  **  (store_string itv_key k_list )
  **  ((it) # Ptr  |-> itv)
  **  (store_map_missing_i store_sll b ind )
  **  (sllseg buck itv l_prev )
  **  (sll itv l_res )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_pre_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") it 0 &((itv)  # "blist" ->ₛ "up") dl_up )
  **  (dll it &((itv)  # "blist" ->ₛ "up") dl_down )
  **  ((removed) # Int  |->_)
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_up) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_down) # Ptr  |->_)
  **  ((&((itv_up)  # "blist" ->ₛ "down")) # Ptr  |-> itv_up_down)
  **  ((itv_up_down) # Ptr  |->_)
  **  ((&((itv_down)  # "blist" ->ₛ "up")) # Ptr  |-> itv_down_up)
  **  ((itv_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  ((h_top) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> itv_next)
  **  ((itv_next) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map store_uint m2 )
.

Definition hashtbl_remove_entail_wit_4 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (val_2: Z) (itv_next_2: Z) (h_top_2: Z) (itv_down_up_2: Z) (itv_up_down_2: Z) (itv_down_2: Z) (itv_up_2: Z) (itv_key_2: Z) (k_list_2: (@list Z)) (removed: Z) (h_pre_bucks_2: Z) (l_res_2: (@list Z)) (buck_2: Z) (itv_2: Z) (it: Z) (lh_2: (@list Z)) (b_2: (Z -> (@option (Z * (@list Z))))) (dl_up_2: (@list Z)) (dl_down_2: (@list Z)) (ind: Z) (l_prev_2: (@list Z)) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (key_pre <> itv_key_2) |] 
  &&  [| (k <> k_list_2) |] 
  &&  [| (itv_2 <> 0) |] 
  &&  [| (not_key k l_prev_2 m1 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up_2) (dl_down_2)) ) |] 
  &&  [| (repr_all_heads lh_2 b_2 ) |] 
  &&  [| (contain_all_correct_addrs m1 b_2 ) |]
  &&  (store_string key_pre k )
  **  (store_string itv_key_2 k_list_2 )
  **  ((it) # Ptr  |-> itv_2)
  **  (store_map_missing_i store_sll b_2 ind )
  **  (sllseg buck_2 itv_2 l_prev_2 )
  **  (sll itv_2 l_res_2 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks_2)
  **  (((h_pre_bucks_2 + (ind * sizeof(PTR) ) )) # Ptr  |-> buck_2)
  **  (PtrArray.missing_i h_pre_bucks_2 ind 0 211 lh_2 )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") it 0 &((itv_2)  # "blist" ->ₛ "up") dl_up_2 )
  **  (dll it &((itv_2)  # "blist" ->ₛ "up") dl_down_2 )
  **  ((removed) # Int  |->_)
  **  ((&((itv_2)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key_2)
  **  ((&((itv_2)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up_2)
  **  ((itv_up_2) # Ptr  |->_)
  **  ((&((itv_2)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down_2)
  **  ((itv_down_2) # Ptr  |->_)
  **  ((&((itv_up_2)  # "blist" ->ₛ "down")) # Ptr  |-> itv_up_down_2)
  **  ((itv_up_down_2) # Ptr  |->_)
  **  ((&((itv_down_2)  # "blist" ->ₛ "up")) # Ptr  |-> itv_down_up_2)
  **  ((itv_down_up_2) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top_2)
  **  ((h_top_2) # Ptr  |->_)
  **  ((&((itv_2)  # "blist" ->ₛ "next")) # Ptr  |-> itv_next_2)
  **  ((itv_next_2) # Ptr  |->_)
  **  ((&((itv_2)  # "blist" ->ₛ "val")) # UInt  |-> val_2)
  **  (store_map store_uint m2 )
|--
  EX (val: Z)  (itv_next: Z)  (h_top: Z)  (itv_down_up: Z)  (itv_up_down: Z)  (itv_down: Z)  (itv_up: Z)  (itv_key: Z)  (k_list: (@list Z))  (h_pre_bucks: Z)  (l_res: (@list Z))  (buck: Z)  (itv: Z)  (lh: (@list Z))  (b: (Z -> (@option (Z * (@list Z)))))  (dl_up: (@list Z))  (dl_down: (@list Z))  (l_prev: (@list Z)) ,
  [| (not_key k l_prev m1 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up) (dl_down)) ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  ((&((itv_2)  # "blist" ->ₛ "next")) # Ptr  |-> itv)
  **  (store_map_missing_i store_sll b ind )
  **  (sllseg buck itv l_prev )
  **  (sll itv l_res )
  **  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_pre_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") &((itv_2)  # "blist" ->ₛ "next") 0 &((itv)  # "blist" ->ₛ "up") dl_up )
  **  (dll &((itv_2)  # "blist" ->ₛ "next") &((itv)  # "blist" ->ₛ "up") dl_down )
  **  ((removed) # Int  |->_)
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key)
  **  (store_string itv_key k_list )
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_up) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_down) # Ptr  |->_)
  **  ((&((itv_up)  # "blist" ->ₛ "down")) # Ptr  |-> itv_up_down)
  **  ((itv_up_down) # Ptr  |->_)
  **  ((&((itv_down)  # "blist" ->ₛ "up")) # Ptr  |-> itv_down_up)
  **  ((itv_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  ((h_top) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> itv_next)
  **  ((itv_next) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map store_uint m2 )
.

Definition hashtbl_remove_return_wit_1 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (val: Z) (itv_next: Z) (h_top: Z) (itv_down_up: Z) (itv_up_down: Z) (itv_down: Z) (itv_up: Z) (itv_key: Z) (k_list: (@list Z)) (removed: Z) (h_pre_bucks: Z) (l_res: (@list Z)) (buck: Z) (itv: Z) (it: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (dl_up: (@list Z)) (dl_down: (@list Z)) (ind: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (itv_down <> 0) |] 
  &&  [| (itv_up = 0) |] 
  &&  [| (h_top <> itv) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (key_pre = itv_key) |] 
  &&  [| (k = k_list) |] 
  &&  [| (itv <> 0) |] 
  &&  [| (not_key k l_prev m1 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up) (dl_down)) ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  (store_string key_pre k )
  **  (store_string itv_key k_list )
  **  ((it) # Ptr  |-> itv_next)
  **  (store_map_missing_i store_sll b ind )
  **  (sllseg buck itv l_prev )
  **  (sll itv l_res )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_pre_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") it 0 &((itv)  # "blist" ->ₛ "up") dl_up )
  **  (dll it &((itv)  # "blist" ->ₛ "up") dl_down )
  **  ((removed) # Int  |-> 1)
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_up) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_down) # Ptr  |->_)
  **  ((&((itv_up)  # "blist" ->ₛ "down")) # Ptr  |-> itv_up_down)
  **  ((itv_up_down) # Ptr  |->_)
  **  ((&((itv_down)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  ((h_top) # Ptr  |->_)
  **  ((itv_next) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map store_uint m2 )
|--
  (EX (v: Z)  (p_next: Z)  (h_pre_top: Z)  (p_down_up: Z)  (p_up_down: Z)  (p_down: Z)  (p_up: Z)  (key: Z)  (p: Z) ,
  [| ((m1 (k)) = None) |] 
  &&  [| (val = 0) |]
  &&  (store_hash_skeleton h_pre m1 )
  **  (store_string key_pre k )
  **  ((&((p)  # "blist" ->ₛ "key")) # Ptr  |-> key)
  **  ((&((p)  # "blist" ->ₛ "up")) # Ptr  |-> p_up)
  **  ((p_up) # Ptr  |->_)
  **  ((&((p)  # "blist" ->ₛ "down")) # Ptr  |-> p_down)
  **  ((p_down) # Ptr  |->_)
  **  ((&((p_up)  # "blist" ->ₛ "down")) # Ptr  |-> p_up_down)
  **  ((p_up_down) # Ptr  |->_)
  **  ((&((p_down)  # "blist" ->ₛ "up")) # Ptr  |-> p_down_up)
  **  ((p_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_pre_top)
  **  ((h_pre_top) # Ptr  |->_)
  **  ((&((p)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  ((p_next) # Ptr  |->_)
  **  ((&((p)  # "blist" ->ₛ "val")) # UInt  |-> v)
  **  ((removed_pre) # Int  |-> 0)
  **  (store_map store_uint m2 ))
  ||
  (EX (p_next_2: Z)  (h_pre_top_2: Z)  (p_down_up_2: Z)  (p_up_down_2: Z)  (p_down_2: Z)  (p_up_2: Z)  (key0: Z)  (v_2: Z)  (p_2: Z) ,
  [| ((m1 (k)) = (Some (&((p_2)  # "blist" ->ₛ "val")))) |] 
  &&  [| ((m2 (&((p_2)  # "blist" ->ₛ "val"))) = (Some (v_2))) |] 
  &&  [| (val = v_2) |]
  &&  (store_hash_skeleton h_pre m1 )
  **  (store_string key_pre k )
  **  ((removed_pre) # Int  |-> 1)
  **  (store_map store_uint m2 )
  **  ((&((p_2)  # "blist" ->ₛ "key")) # Ptr  |-> key0)
  **  (store_string key0 k )
  **  ((&((p_2)  # "blist" ->ₛ "up")) # Ptr  |-> p_up_2)
  **  ((p_up_2) # Ptr  |->_)
  **  ((&((p_2)  # "blist" ->ₛ "down")) # Ptr  |-> p_down_2)
  **  ((p_down_2) # Ptr  |->_)
  **  ((&((p_up_2)  # "blist" ->ₛ "down")) # Ptr  |-> p_up_down_2)
  **  ((p_up_down_2) # Ptr  |->_)
  **  ((&((p_down_2)  # "blist" ->ₛ "up")) # Ptr  |-> p_down_up_2)
  **  ((p_down_up_2) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_pre_top_2)
  **  ((h_pre_top_2) # Ptr  |->_)
  **  ((&((p_2)  # "blist" ->ₛ "next")) # Ptr  |-> p_next_2)
  **  ((p_next_2) # Ptr  |->_)
  **  ((&((p_2)  # "blist" ->ₛ "val")) # UInt  |-> v_2))
.

Definition hashtbl_remove_return_wit_2 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (val: Z) (itv_next: Z) (h_top: Z) (itv_down_up: Z) (itv_up_down: Z) (itv_down: Z) (itv_up: Z) (itv_key: Z) (k_list: (@list Z)) (removed: Z) (h_pre_bucks: Z) (l_res: (@list Z)) (buck: Z) (itv: Z) (it: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (dl_up: (@list Z)) (dl_down: (@list Z)) (ind: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (itv_down <> 0) |] 
  &&  [| (itv_up = 0) |] 
  &&  [| (h_top = itv) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (key_pre = itv_key) |] 
  &&  [| (k = k_list) |] 
  &&  [| (itv <> 0) |] 
  &&  [| (not_key k l_prev m1 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up) (dl_down)) ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  (store_string key_pre k )
  **  (store_string itv_key k_list )
  **  ((it) # Ptr  |-> itv_next)
  **  (store_map_missing_i store_sll b ind )
  **  (sllseg buck itv l_prev )
  **  (sll itv l_res )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_pre_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") it 0 &((itv)  # "blist" ->ₛ "up") dl_up )
  **  (dll it &((itv)  # "blist" ->ₛ "up") dl_down )
  **  ((removed) # Int  |-> 1)
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_up) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_down) # Ptr  |->_)
  **  ((&((itv_up)  # "blist" ->ₛ "down")) # Ptr  |-> itv_up_down)
  **  ((itv_up_down) # Ptr  |->_)
  **  ((&((itv_down)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> itv_down)
  **  ((h_top) # Ptr  |->_)
  **  ((itv_next) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map store_uint m2 )
|--
  (EX (v: Z)  (p_next: Z)  (h_pre_top: Z)  (p_down_up: Z)  (p_up_down: Z)  (p_down: Z)  (p_up: Z)  (key: Z)  (p: Z) ,
  [| ((m1 (k)) = None) |] 
  &&  [| (val = 0) |]
  &&  (store_hash_skeleton h_pre m1 )
  **  (store_string key_pre k )
  **  ((&((p)  # "blist" ->ₛ "key")) # Ptr  |-> key)
  **  ((&((p)  # "blist" ->ₛ "up")) # Ptr  |-> p_up)
  **  ((p_up) # Ptr  |->_)
  **  ((&((p)  # "blist" ->ₛ "down")) # Ptr  |-> p_down)
  **  ((p_down) # Ptr  |->_)
  **  ((&((p_up)  # "blist" ->ₛ "down")) # Ptr  |-> p_up_down)
  **  ((p_up_down) # Ptr  |->_)
  **  ((&((p_down)  # "blist" ->ₛ "up")) # Ptr  |-> p_down_up)
  **  ((p_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_pre_top)
  **  ((h_pre_top) # Ptr  |->_)
  **  ((&((p)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  ((p_next) # Ptr  |->_)
  **  ((&((p)  # "blist" ->ₛ "val")) # UInt  |-> v)
  **  ((removed_pre) # Int  |-> 0)
  **  (store_map store_uint m2 ))
  ||
  (EX (p_next_2: Z)  (h_pre_top_2: Z)  (p_down_up_2: Z)  (p_up_down_2: Z)  (p_down_2: Z)  (p_up_2: Z)  (key0: Z)  (v_2: Z)  (p_2: Z) ,
  [| ((m1 (k)) = (Some (&((p_2)  # "blist" ->ₛ "val")))) |] 
  &&  [| ((m2 (&((p_2)  # "blist" ->ₛ "val"))) = (Some (v_2))) |] 
  &&  [| (val = v_2) |]
  &&  (store_hash_skeleton h_pre m1 )
  **  (store_string key_pre k )
  **  ((removed_pre) # Int  |-> 1)
  **  (store_map store_uint m2 )
  **  ((&((p_2)  # "blist" ->ₛ "key")) # Ptr  |-> key0)
  **  (store_string key0 k )
  **  ((&((p_2)  # "blist" ->ₛ "up")) # Ptr  |-> p_up_2)
  **  ((p_up_2) # Ptr  |->_)
  **  ((&((p_2)  # "blist" ->ₛ "down")) # Ptr  |-> p_down_2)
  **  ((p_down_2) # Ptr  |->_)
  **  ((&((p_up_2)  # "blist" ->ₛ "down")) # Ptr  |-> p_up_down_2)
  **  ((p_up_down_2) # Ptr  |->_)
  **  ((&((p_down_2)  # "blist" ->ₛ "up")) # Ptr  |-> p_down_up_2)
  **  ((p_down_up_2) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_pre_top_2)
  **  ((h_pre_top_2) # Ptr  |->_)
  **  ((&((p_2)  # "blist" ->ₛ "next")) # Ptr  |-> p_next_2)
  **  ((p_next_2) # Ptr  |->_)
  **  ((&((p_2)  # "blist" ->ₛ "val")) # UInt  |-> v_2))
.

Definition hashtbl_remove_return_wit_3 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (val: Z) (itv_next: Z) (h_top: Z) (itv_down_up: Z) (itv_up_down: Z) (itv_down: Z) (itv_up: Z) (itv_key: Z) (k_list: (@list Z)) (removed: Z) (h_pre_bucks: Z) (l_res: (@list Z)) (buck: Z) (itv: Z) (it: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (dl_up: (@list Z)) (dl_down: (@list Z)) (ind: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (itv_down <> 0) |] 
  &&  [| (itv_up <> 0) |] 
  &&  [| (h_top = itv) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (key_pre = itv_key) |] 
  &&  [| (k = k_list) |] 
  &&  [| (itv <> 0) |] 
  &&  [| (not_key k l_prev m1 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up) (dl_down)) ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  (store_string key_pre k )
  **  (store_string itv_key k_list )
  **  ((it) # Ptr  |-> itv_next)
  **  (store_map_missing_i store_sll b ind )
  **  (sllseg buck itv l_prev )
  **  (sll itv l_res )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_pre_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") it 0 &((itv)  # "blist" ->ₛ "up") dl_up )
  **  (dll it &((itv)  # "blist" ->ₛ "up") dl_down )
  **  ((removed) # Int  |-> 1)
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_up) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_down) # Ptr  |->_)
  **  ((&((itv_up)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_up_down) # Ptr  |->_)
  **  ((&((itv_down)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> itv_down)
  **  ((h_top) # Ptr  |->_)
  **  ((itv_next) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map store_uint m2 )
|--
  (EX (v: Z)  (p_next: Z)  (h_pre_top: Z)  (p_down_up: Z)  (p_up_down: Z)  (p_down: Z)  (p_up: Z)  (key: Z)  (p: Z) ,
  [| ((m1 (k)) = None) |] 
  &&  [| (val = 0) |]
  &&  (store_hash_skeleton h_pre m1 )
  **  (store_string key_pre k )
  **  ((&((p)  # "blist" ->ₛ "key")) # Ptr  |-> key)
  **  ((&((p)  # "blist" ->ₛ "up")) # Ptr  |-> p_up)
  **  ((p_up) # Ptr  |->_)
  **  ((&((p)  # "blist" ->ₛ "down")) # Ptr  |-> p_down)
  **  ((p_down) # Ptr  |->_)
  **  ((&((p_up)  # "blist" ->ₛ "down")) # Ptr  |-> p_up_down)
  **  ((p_up_down) # Ptr  |->_)
  **  ((&((p_down)  # "blist" ->ₛ "up")) # Ptr  |-> p_down_up)
  **  ((p_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_pre_top)
  **  ((h_pre_top) # Ptr  |->_)
  **  ((&((p)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  ((p_next) # Ptr  |->_)
  **  ((&((p)  # "blist" ->ₛ "val")) # UInt  |-> v)
  **  ((removed_pre) # Int  |-> 0)
  **  (store_map store_uint m2 ))
  ||
  (EX (p_next_2: Z)  (h_pre_top_2: Z)  (p_down_up_2: Z)  (p_up_down_2: Z)  (p_down_2: Z)  (p_up_2: Z)  (key0: Z)  (v_2: Z)  (p_2: Z) ,
  [| ((m1 (k)) = (Some (&((p_2)  # "blist" ->ₛ "val")))) |] 
  &&  [| ((m2 (&((p_2)  # "blist" ->ₛ "val"))) = (Some (v_2))) |] 
  &&  [| (val = v_2) |]
  &&  (store_hash_skeleton h_pre m1 )
  **  (store_string key_pre k )
  **  ((removed_pre) # Int  |-> 1)
  **  (store_map store_uint m2 )
  **  ((&((p_2)  # "blist" ->ₛ "key")) # Ptr  |-> key0)
  **  (store_string key0 k )
  **  ((&((p_2)  # "blist" ->ₛ "up")) # Ptr  |-> p_up_2)
  **  ((p_up_2) # Ptr  |->_)
  **  ((&((p_2)  # "blist" ->ₛ "down")) # Ptr  |-> p_down_2)
  **  ((p_down_2) # Ptr  |->_)
  **  ((&((p_up_2)  # "blist" ->ₛ "down")) # Ptr  |-> p_up_down_2)
  **  ((p_up_down_2) # Ptr  |->_)
  **  ((&((p_down_2)  # "blist" ->ₛ "up")) # Ptr  |-> p_down_up_2)
  **  ((p_down_up_2) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_pre_top_2)
  **  ((h_pre_top_2) # Ptr  |->_)
  **  ((&((p_2)  # "blist" ->ₛ "next")) # Ptr  |-> p_next_2)
  **  ((p_next_2) # Ptr  |->_)
  **  ((&((p_2)  # "blist" ->ₛ "val")) # UInt  |-> v_2))
.

Definition hashtbl_remove_return_wit_4 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (val: Z) (itv_next: Z) (h_top: Z) (itv_down_up: Z) (itv_up_down: Z) (itv_down: Z) (itv_up: Z) (itv_key: Z) (k_list: (@list Z)) (removed: Z) (h_pre_bucks: Z) (l_res: (@list Z)) (buck: Z) (itv: Z) (it: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (dl_up: (@list Z)) (dl_down: (@list Z)) (ind: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (itv_down <> 0) |] 
  &&  [| (itv_up <> 0) |] 
  &&  [| (h_top <> itv) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (key_pre = itv_key) |] 
  &&  [| (k = k_list) |] 
  &&  [| (itv <> 0) |] 
  &&  [| (not_key k l_prev m1 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up) (dl_down)) ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  (store_string key_pre k )
  **  (store_string itv_key k_list )
  **  ((it) # Ptr  |-> itv_next)
  **  (store_map_missing_i store_sll b ind )
  **  (sllseg buck itv l_prev )
  **  (sll itv l_res )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_pre_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") it 0 &((itv)  # "blist" ->ₛ "up") dl_up )
  **  (dll it &((itv)  # "blist" ->ₛ "up") dl_down )
  **  ((removed) # Int  |-> 1)
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_up) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_down) # Ptr  |->_)
  **  ((&((itv_up)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_up_down) # Ptr  |->_)
  **  ((&((itv_down)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  ((h_top) # Ptr  |->_)
  **  ((itv_next) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map store_uint m2 )
|--
  (EX (v: Z)  (p_next: Z)  (h_pre_top: Z)  (p_down_up: Z)  (p_up_down: Z)  (p_down: Z)  (p_up: Z)  (key: Z)  (p: Z) ,
  [| ((m1 (k)) = None) |] 
  &&  [| (val = 0) |]
  &&  (store_hash_skeleton h_pre m1 )
  **  (store_string key_pre k )
  **  ((&((p)  # "blist" ->ₛ "key")) # Ptr  |-> key)
  **  ((&((p)  # "blist" ->ₛ "up")) # Ptr  |-> p_up)
  **  ((p_up) # Ptr  |->_)
  **  ((&((p)  # "blist" ->ₛ "down")) # Ptr  |-> p_down)
  **  ((p_down) # Ptr  |->_)
  **  ((&((p_up)  # "blist" ->ₛ "down")) # Ptr  |-> p_up_down)
  **  ((p_up_down) # Ptr  |->_)
  **  ((&((p_down)  # "blist" ->ₛ "up")) # Ptr  |-> p_down_up)
  **  ((p_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_pre_top)
  **  ((h_pre_top) # Ptr  |->_)
  **  ((&((p)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  ((p_next) # Ptr  |->_)
  **  ((&((p)  # "blist" ->ₛ "val")) # UInt  |-> v)
  **  ((removed_pre) # Int  |-> 0)
  **  (store_map store_uint m2 ))
  ||
  (EX (p_next_2: Z)  (h_pre_top_2: Z)  (p_down_up_2: Z)  (p_up_down_2: Z)  (p_down_2: Z)  (p_up_2: Z)  (key0: Z)  (v_2: Z)  (p_2: Z) ,
  [| ((m1 (k)) = (Some (&((p_2)  # "blist" ->ₛ "val")))) |] 
  &&  [| ((m2 (&((p_2)  # "blist" ->ₛ "val"))) = (Some (v_2))) |] 
  &&  [| (val = v_2) |]
  &&  (store_hash_skeleton h_pre m1 )
  **  (store_string key_pre k )
  **  ((removed_pre) # Int  |-> 1)
  **  (store_map store_uint m2 )
  **  ((&((p_2)  # "blist" ->ₛ "key")) # Ptr  |-> key0)
  **  (store_string key0 k )
  **  ((&((p_2)  # "blist" ->ₛ "up")) # Ptr  |-> p_up_2)
  **  ((p_up_2) # Ptr  |->_)
  **  ((&((p_2)  # "blist" ->ₛ "down")) # Ptr  |-> p_down_2)
  **  ((p_down_2) # Ptr  |->_)
  **  ((&((p_up_2)  # "blist" ->ₛ "down")) # Ptr  |-> p_up_down_2)
  **  ((p_up_down_2) # Ptr  |->_)
  **  ((&((p_down_2)  # "blist" ->ₛ "up")) # Ptr  |-> p_down_up_2)
  **  ((p_down_up_2) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_pre_top_2)
  **  ((h_pre_top_2) # Ptr  |->_)
  **  ((&((p_2)  # "blist" ->ₛ "next")) # Ptr  |-> p_next_2)
  **  ((p_next_2) # Ptr  |->_)
  **  ((&((p_2)  # "blist" ->ₛ "val")) # UInt  |-> v_2))
.

Definition hashtbl_remove_return_wit_5 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (val: Z) (itv_next: Z) (h_top: Z) (itv_down_up: Z) (itv_up_down: Z) (itv_down: Z) (itv_up: Z) (itv_key: Z) (k_list: (@list Z)) (removed: Z) (h_pre_bucks: Z) (l_res: (@list Z)) (buck: Z) (itv: Z) (it: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (dl_up: (@list Z)) (dl_down: (@list Z)) (ind: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (itv_down = 0) |] 
  &&  [| (itv_up <> 0) |] 
  &&  [| (h_top <> itv) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (key_pre = itv_key) |] 
  &&  [| (k = k_list) |] 
  &&  [| (itv <> 0) |] 
  &&  [| (not_key k l_prev m1 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up) (dl_down)) ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  (store_string key_pre k )
  **  (store_string itv_key k_list )
  **  ((it) # Ptr  |-> itv_next)
  **  (store_map_missing_i store_sll b ind )
  **  (sllseg buck itv l_prev )
  **  (sll itv l_res )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_pre_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") it 0 &((itv)  # "blist" ->ₛ "up") dl_up )
  **  (dll it &((itv)  # "blist" ->ₛ "up") dl_down )
  **  ((removed) # Int  |-> 1)
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_up) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_down) # Ptr  |->_)
  **  ((&((itv_up)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_up_down) # Ptr  |->_)
  **  ((&((itv_down)  # "blist" ->ₛ "up")) # Ptr  |-> itv_down_up)
  **  ((itv_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  ((h_top) # Ptr  |->_)
  **  ((itv_next) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map store_uint m2 )
|--
  (EX (v: Z)  (p_next: Z)  (h_pre_top: Z)  (p_down_up: Z)  (p_up_down: Z)  (p_down: Z)  (p_up: Z)  (key: Z)  (p: Z) ,
  [| ((m1 (k)) = None) |] 
  &&  [| (val = 0) |]
  &&  (store_hash_skeleton h_pre m1 )
  **  (store_string key_pre k )
  **  ((&((p)  # "blist" ->ₛ "key")) # Ptr  |-> key)
  **  ((&((p)  # "blist" ->ₛ "up")) # Ptr  |-> p_up)
  **  ((p_up) # Ptr  |->_)
  **  ((&((p)  # "blist" ->ₛ "down")) # Ptr  |-> p_down)
  **  ((p_down) # Ptr  |->_)
  **  ((&((p_up)  # "blist" ->ₛ "down")) # Ptr  |-> p_up_down)
  **  ((p_up_down) # Ptr  |->_)
  **  ((&((p_down)  # "blist" ->ₛ "up")) # Ptr  |-> p_down_up)
  **  ((p_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_pre_top)
  **  ((h_pre_top) # Ptr  |->_)
  **  ((&((p)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  ((p_next) # Ptr  |->_)
  **  ((&((p)  # "blist" ->ₛ "val")) # UInt  |-> v)
  **  ((removed_pre) # Int  |-> 0)
  **  (store_map store_uint m2 ))
  ||
  (EX (p_next_2: Z)  (h_pre_top_2: Z)  (p_down_up_2: Z)  (p_up_down_2: Z)  (p_down_2: Z)  (p_up_2: Z)  (key0: Z)  (v_2: Z)  (p_2: Z) ,
  [| ((m1 (k)) = (Some (&((p_2)  # "blist" ->ₛ "val")))) |] 
  &&  [| ((m2 (&((p_2)  # "blist" ->ₛ "val"))) = (Some (v_2))) |] 
  &&  [| (val = v_2) |]
  &&  (store_hash_skeleton h_pre m1 )
  **  (store_string key_pre k )
  **  ((removed_pre) # Int  |-> 1)
  **  (store_map store_uint m2 )
  **  ((&((p_2)  # "blist" ->ₛ "key")) # Ptr  |-> key0)
  **  (store_string key0 k )
  **  ((&((p_2)  # "blist" ->ₛ "up")) # Ptr  |-> p_up_2)
  **  ((p_up_2) # Ptr  |->_)
  **  ((&((p_2)  # "blist" ->ₛ "down")) # Ptr  |-> p_down_2)
  **  ((p_down_2) # Ptr  |->_)
  **  ((&((p_up_2)  # "blist" ->ₛ "down")) # Ptr  |-> p_up_down_2)
  **  ((p_up_down_2) # Ptr  |->_)
  **  ((&((p_down_2)  # "blist" ->ₛ "up")) # Ptr  |-> p_down_up_2)
  **  ((p_down_up_2) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_pre_top_2)
  **  ((h_pre_top_2) # Ptr  |->_)
  **  ((&((p_2)  # "blist" ->ₛ "next")) # Ptr  |-> p_next_2)
  **  ((p_next_2) # Ptr  |->_)
  **  ((&((p_2)  # "blist" ->ₛ "val")) # UInt  |-> v_2))
.

Definition hashtbl_remove_return_wit_6 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (val: Z) (itv_next: Z) (h_top: Z) (itv_down_up: Z) (itv_up_down: Z) (itv_down: Z) (itv_up: Z) (itv_key: Z) (k_list: (@list Z)) (removed: Z) (h_pre_bucks: Z) (l_res: (@list Z)) (buck: Z) (itv: Z) (it: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (dl_up: (@list Z)) (dl_down: (@list Z)) (ind: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (itv_down = 0) |] 
  &&  [| (itv_up <> 0) |] 
  &&  [| (h_top = itv) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (key_pre = itv_key) |] 
  &&  [| (k = k_list) |] 
  &&  [| (itv <> 0) |] 
  &&  [| (not_key k l_prev m1 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up) (dl_down)) ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  (store_string key_pre k )
  **  (store_string itv_key k_list )
  **  ((it) # Ptr  |-> itv_next)
  **  (store_map_missing_i store_sll b ind )
  **  (sllseg buck itv l_prev )
  **  (sll itv l_res )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_pre_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") it 0 &((itv)  # "blist" ->ₛ "up") dl_up )
  **  (dll it &((itv)  # "blist" ->ₛ "up") dl_down )
  **  ((removed) # Int  |-> 1)
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_up) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_down) # Ptr  |->_)
  **  ((&((itv_up)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_up_down) # Ptr  |->_)
  **  ((&((itv_down)  # "blist" ->ₛ "up")) # Ptr  |-> itv_down_up)
  **  ((itv_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> itv_down)
  **  ((h_top) # Ptr  |->_)
  **  ((itv_next) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map store_uint m2 )
|--
  (EX (v: Z)  (p_next: Z)  (h_pre_top: Z)  (p_down_up: Z)  (p_up_down: Z)  (p_down: Z)  (p_up: Z)  (key: Z)  (p: Z) ,
  [| ((m1 (k)) = None) |] 
  &&  [| (val = 0) |]
  &&  (store_hash_skeleton h_pre m1 )
  **  (store_string key_pre k )
  **  ((&((p)  # "blist" ->ₛ "key")) # Ptr  |-> key)
  **  ((&((p)  # "blist" ->ₛ "up")) # Ptr  |-> p_up)
  **  ((p_up) # Ptr  |->_)
  **  ((&((p)  # "blist" ->ₛ "down")) # Ptr  |-> p_down)
  **  ((p_down) # Ptr  |->_)
  **  ((&((p_up)  # "blist" ->ₛ "down")) # Ptr  |-> p_up_down)
  **  ((p_up_down) # Ptr  |->_)
  **  ((&((p_down)  # "blist" ->ₛ "up")) # Ptr  |-> p_down_up)
  **  ((p_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_pre_top)
  **  ((h_pre_top) # Ptr  |->_)
  **  ((&((p)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  ((p_next) # Ptr  |->_)
  **  ((&((p)  # "blist" ->ₛ "val")) # UInt  |-> v)
  **  ((removed_pre) # Int  |-> 0)
  **  (store_map store_uint m2 ))
  ||
  (EX (p_next_2: Z)  (h_pre_top_2: Z)  (p_down_up_2: Z)  (p_up_down_2: Z)  (p_down_2: Z)  (p_up_2: Z)  (key0: Z)  (v_2: Z)  (p_2: Z) ,
  [| ((m1 (k)) = (Some (&((p_2)  # "blist" ->ₛ "val")))) |] 
  &&  [| ((m2 (&((p_2)  # "blist" ->ₛ "val"))) = (Some (v_2))) |] 
  &&  [| (val = v_2) |]
  &&  (store_hash_skeleton h_pre m1 )
  **  (store_string key_pre k )
  **  ((removed_pre) # Int  |-> 1)
  **  (store_map store_uint m2 )
  **  ((&((p_2)  # "blist" ->ₛ "key")) # Ptr  |-> key0)
  **  (store_string key0 k )
  **  ((&((p_2)  # "blist" ->ₛ "up")) # Ptr  |-> p_up_2)
  **  ((p_up_2) # Ptr  |->_)
  **  ((&((p_2)  # "blist" ->ₛ "down")) # Ptr  |-> p_down_2)
  **  ((p_down_2) # Ptr  |->_)
  **  ((&((p_up_2)  # "blist" ->ₛ "down")) # Ptr  |-> p_up_down_2)
  **  ((p_up_down_2) # Ptr  |->_)
  **  ((&((p_down_2)  # "blist" ->ₛ "up")) # Ptr  |-> p_down_up_2)
  **  ((p_down_up_2) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_pre_top_2)
  **  ((h_pre_top_2) # Ptr  |->_)
  **  ((&((p_2)  # "blist" ->ₛ "next")) # Ptr  |-> p_next_2)
  **  ((p_next_2) # Ptr  |->_)
  **  ((&((p_2)  # "blist" ->ₛ "val")) # UInt  |-> v_2))
.

Definition hashtbl_remove_return_wit_7 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (val: Z) (itv_next: Z) (h_top: Z) (itv_down_up: Z) (itv_up_down: Z) (itv_down: Z) (itv_up: Z) (itv_key: Z) (k_list: (@list Z)) (removed: Z) (h_pre_bucks: Z) (l_res: (@list Z)) (buck: Z) (itv: Z) (it: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (dl_up: (@list Z)) (dl_down: (@list Z)) (ind: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (itv_down = 0) |] 
  &&  [| (itv_up = 0) |] 
  &&  [| (h_top = itv) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (key_pre = itv_key) |] 
  &&  [| (k = k_list) |] 
  &&  [| (itv <> 0) |] 
  &&  [| (not_key k l_prev m1 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up) (dl_down)) ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  (store_string key_pre k )
  **  (store_string itv_key k_list )
  **  ((it) # Ptr  |-> itv_next)
  **  (store_map_missing_i store_sll b ind )
  **  (sllseg buck itv l_prev )
  **  (sll itv l_res )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_pre_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") it 0 &((itv)  # "blist" ->ₛ "up") dl_up )
  **  (dll it &((itv)  # "blist" ->ₛ "up") dl_down )
  **  ((removed) # Int  |-> 1)
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_up) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_down) # Ptr  |->_)
  **  ((&((itv_up)  # "blist" ->ₛ "down")) # Ptr  |-> itv_up_down)
  **  ((itv_up_down) # Ptr  |->_)
  **  ((&((itv_down)  # "blist" ->ₛ "up")) # Ptr  |-> itv_down_up)
  **  ((itv_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> itv_down)
  **  ((h_top) # Ptr  |->_)
  **  ((itv_next) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map store_uint m2 )
|--
  (EX (v: Z)  (p_next: Z)  (h_pre_top: Z)  (p_down_up: Z)  (p_up_down: Z)  (p_down: Z)  (p_up: Z)  (key: Z)  (p: Z) ,
  [| ((m1 (k)) = None) |] 
  &&  [| (val = 0) |]
  &&  (store_hash_skeleton h_pre m1 )
  **  (store_string key_pre k )
  **  ((&((p)  # "blist" ->ₛ "key")) # Ptr  |-> key)
  **  ((&((p)  # "blist" ->ₛ "up")) # Ptr  |-> p_up)
  **  ((p_up) # Ptr  |->_)
  **  ((&((p)  # "blist" ->ₛ "down")) # Ptr  |-> p_down)
  **  ((p_down) # Ptr  |->_)
  **  ((&((p_up)  # "blist" ->ₛ "down")) # Ptr  |-> p_up_down)
  **  ((p_up_down) # Ptr  |->_)
  **  ((&((p_down)  # "blist" ->ₛ "up")) # Ptr  |-> p_down_up)
  **  ((p_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_pre_top)
  **  ((h_pre_top) # Ptr  |->_)
  **  ((&((p)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  ((p_next) # Ptr  |->_)
  **  ((&((p)  # "blist" ->ₛ "val")) # UInt  |-> v)
  **  ((removed_pre) # Int  |-> 0)
  **  (store_map store_uint m2 ))
  ||
  (EX (p_next_2: Z)  (h_pre_top_2: Z)  (p_down_up_2: Z)  (p_up_down_2: Z)  (p_down_2: Z)  (p_up_2: Z)  (key0: Z)  (v_2: Z)  (p_2: Z) ,
  [| ((m1 (k)) = (Some (&((p_2)  # "blist" ->ₛ "val")))) |] 
  &&  [| ((m2 (&((p_2)  # "blist" ->ₛ "val"))) = (Some (v_2))) |] 
  &&  [| (val = v_2) |]
  &&  (store_hash_skeleton h_pre m1 )
  **  (store_string key_pre k )
  **  ((removed_pre) # Int  |-> 1)
  **  (store_map store_uint m2 )
  **  ((&((p_2)  # "blist" ->ₛ "key")) # Ptr  |-> key0)
  **  (store_string key0 k )
  **  ((&((p_2)  # "blist" ->ₛ "up")) # Ptr  |-> p_up_2)
  **  ((p_up_2) # Ptr  |->_)
  **  ((&((p_2)  # "blist" ->ₛ "down")) # Ptr  |-> p_down_2)
  **  ((p_down_2) # Ptr  |->_)
  **  ((&((p_up_2)  # "blist" ->ₛ "down")) # Ptr  |-> p_up_down_2)
  **  ((p_up_down_2) # Ptr  |->_)
  **  ((&((p_down_2)  # "blist" ->ₛ "up")) # Ptr  |-> p_down_up_2)
  **  ((p_down_up_2) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_pre_top_2)
  **  ((h_pre_top_2) # Ptr  |->_)
  **  ((&((p_2)  # "blist" ->ₛ "next")) # Ptr  |-> p_next_2)
  **  ((p_next_2) # Ptr  |->_)
  **  ((&((p_2)  # "blist" ->ₛ "val")) # UInt  |-> v_2))
.

Definition hashtbl_remove_return_wit_8 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (val: Z) (itv_next: Z) (h_top: Z) (itv_down_up: Z) (itv_up_down: Z) (itv_down: Z) (itv_up: Z) (itv_key: Z) (k_list: (@list Z)) (removed: Z) (h_pre_bucks: Z) (l_res: (@list Z)) (buck: Z) (itv: Z) (it: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (dl_up: (@list Z)) (dl_down: (@list Z)) (ind: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (itv_down = 0) |] 
  &&  [| (itv_up = 0) |] 
  &&  [| (h_top <> itv) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (key_pre = itv_key) |] 
  &&  [| (k = k_list) |] 
  &&  [| (itv <> 0) |] 
  &&  [| (not_key k l_prev m1 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up) (dl_down)) ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  (store_string key_pre k )
  **  (store_string itv_key k_list )
  **  ((it) # Ptr  |-> itv_next)
  **  (store_map_missing_i store_sll b ind )
  **  (sllseg buck itv l_prev )
  **  (sll itv l_res )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_pre_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") it 0 &((itv)  # "blist" ->ₛ "up") dl_up )
  **  (dll it &((itv)  # "blist" ->ₛ "up") dl_down )
  **  ((removed) # Int  |-> 1)
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_up) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_down) # Ptr  |->_)
  **  ((&((itv_up)  # "blist" ->ₛ "down")) # Ptr  |-> itv_up_down)
  **  ((itv_up_down) # Ptr  |->_)
  **  ((&((itv_down)  # "blist" ->ₛ "up")) # Ptr  |-> itv_down_up)
  **  ((itv_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  ((h_top) # Ptr  |->_)
  **  ((itv_next) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map store_uint m2 )
|--
  (EX (v: Z)  (p_next: Z)  (h_pre_top: Z)  (p_down_up: Z)  (p_up_down: Z)  (p_down: Z)  (p_up: Z)  (key: Z)  (p: Z) ,
  [| ((m1 (k)) = None) |] 
  &&  [| (val = 0) |]
  &&  (store_hash_skeleton h_pre m1 )
  **  (store_string key_pre k )
  **  ((&((p)  # "blist" ->ₛ "key")) # Ptr  |-> key)
  **  ((&((p)  # "blist" ->ₛ "up")) # Ptr  |-> p_up)
  **  ((p_up) # Ptr  |->_)
  **  ((&((p)  # "blist" ->ₛ "down")) # Ptr  |-> p_down)
  **  ((p_down) # Ptr  |->_)
  **  ((&((p_up)  # "blist" ->ₛ "down")) # Ptr  |-> p_up_down)
  **  ((p_up_down) # Ptr  |->_)
  **  ((&((p_down)  # "blist" ->ₛ "up")) # Ptr  |-> p_down_up)
  **  ((p_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_pre_top)
  **  ((h_pre_top) # Ptr  |->_)
  **  ((&((p)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  ((p_next) # Ptr  |->_)
  **  ((&((p)  # "blist" ->ₛ "val")) # UInt  |-> v)
  **  ((removed_pre) # Int  |-> 0)
  **  (store_map store_uint m2 ))
  ||
  (EX (p_next_2: Z)  (h_pre_top_2: Z)  (p_down_up_2: Z)  (p_up_down_2: Z)  (p_down_2: Z)  (p_up_2: Z)  (key0: Z)  (v_2: Z)  (p_2: Z) ,
  [| ((m1 (k)) = (Some (&((p_2)  # "blist" ->ₛ "val")))) |] 
  &&  [| ((m2 (&((p_2)  # "blist" ->ₛ "val"))) = (Some (v_2))) |] 
  &&  [| (val = v_2) |]
  &&  (store_hash_skeleton h_pre m1 )
  **  (store_string key_pre k )
  **  ((removed_pre) # Int  |-> 1)
  **  (store_map store_uint m2 )
  **  ((&((p_2)  # "blist" ->ₛ "key")) # Ptr  |-> key0)
  **  (store_string key0 k )
  **  ((&((p_2)  # "blist" ->ₛ "up")) # Ptr  |-> p_up_2)
  **  ((p_up_2) # Ptr  |->_)
  **  ((&((p_2)  # "blist" ->ₛ "down")) # Ptr  |-> p_down_2)
  **  ((p_down_2) # Ptr  |->_)
  **  ((&((p_up_2)  # "blist" ->ₛ "down")) # Ptr  |-> p_up_down_2)
  **  ((p_up_down_2) # Ptr  |->_)
  **  ((&((p_down_2)  # "blist" ->ₛ "up")) # Ptr  |-> p_down_up_2)
  **  ((p_down_up_2) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_pre_top_2)
  **  ((h_pre_top_2) # Ptr  |->_)
  **  ((&((p_2)  # "blist" ->ₛ "next")) # Ptr  |-> p_next_2)
  **  ((p_next_2) # Ptr  |->_)
  **  ((&((p_2)  # "blist" ->ₛ "val")) # UInt  |-> v_2))
.

Definition hashtbl_remove_return_wit_9 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (val: Z) (itv_next: Z) (h_top: Z) (itv_down_up: Z) (itv_up_down: Z) (itv_down: Z) (itv_up: Z) (itv_key: Z) (k_list: (@list Z)) (removed: Z) (h_pre_bucks: Z) (l_res: (@list Z)) (buck: Z) (itv: Z) (it: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (dl_up: (@list Z)) (dl_down: (@list Z)) (ind: Z) (l_prev: (@list Z)) ,
  [| (itv = 0) |] 
  &&  [| (not_key k l_prev m1 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up) (dl_down)) ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  ((it) # Ptr  |-> itv)
  **  (store_map_missing_i store_sll b ind )
  **  (sllseg buck itv l_prev )
  **  (sll itv l_res )
  **  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_pre_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") it 0 &((itv)  # "blist" ->ₛ "up") dl_up )
  **  (dll it &((itv)  # "blist" ->ₛ "up") dl_down )
  **  ((removed) # Int  |-> 0)
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key)
  **  (store_string itv_key k_list )
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_up) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_down) # Ptr  |->_)
  **  ((&((itv_up)  # "blist" ->ₛ "down")) # Ptr  |-> itv_up_down)
  **  ((itv_up_down) # Ptr  |->_)
  **  ((&((itv_down)  # "blist" ->ₛ "up")) # Ptr  |-> itv_down_up)
  **  ((itv_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  ((h_top) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> itv_next)
  **  ((itv_next) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map store_uint m2 )
|--
  (EX (v: Z)  (p_next: Z)  (h_pre_top: Z)  (p_down_up: Z)  (p_up_down: Z)  (p_down: Z)  (p_up: Z)  (key: Z)  (p: Z) ,
  [| ((m1 (k)) = None) |] 
  &&  [| (0 = 0) |]
  &&  (store_hash_skeleton h_pre m1 )
  **  (store_string key_pre k )
  **  ((&((p)  # "blist" ->ₛ "key")) # Ptr  |-> key)
  **  ((&((p)  # "blist" ->ₛ "up")) # Ptr  |-> p_up)
  **  ((p_up) # Ptr  |->_)
  **  ((&((p)  # "blist" ->ₛ "down")) # Ptr  |-> p_down)
  **  ((p_down) # Ptr  |->_)
  **  ((&((p_up)  # "blist" ->ₛ "down")) # Ptr  |-> p_up_down)
  **  ((p_up_down) # Ptr  |->_)
  **  ((&((p_down)  # "blist" ->ₛ "up")) # Ptr  |-> p_down_up)
  **  ((p_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_pre_top)
  **  ((h_pre_top) # Ptr  |->_)
  **  ((&((p)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  ((p_next) # Ptr  |->_)
  **  ((&((p)  # "blist" ->ₛ "val")) # UInt  |-> v)
  **  ((removed_pre) # Int  |-> 0)
  **  (store_map store_uint m2 ))
  ||
  (EX (p_next_2: Z)  (h_pre_top_2: Z)  (p_down_up_2: Z)  (p_up_down_2: Z)  (p_down_2: Z)  (p_up_2: Z)  (key0: Z)  (v_2: Z)  (p_2: Z) ,
  [| ((m1 (k)) = (Some (&((p_2)  # "blist" ->ₛ "val")))) |] 
  &&  [| ((m2 (&((p_2)  # "blist" ->ₛ "val"))) = (Some (v_2))) |] 
  &&  [| (0 = v_2) |]
  &&  (store_hash_skeleton h_pre m1 )
  **  (store_string key_pre k )
  **  ((removed_pre) # Int  |-> 1)
  **  (store_map store_uint m2 )
  **  ((&((p_2)  # "blist" ->ₛ "key")) # Ptr  |-> key0)
  **  (store_string key0 k )
  **  ((&((p_2)  # "blist" ->ₛ "up")) # Ptr  |-> p_up_2)
  **  ((p_up_2) # Ptr  |->_)
  **  ((&((p_2)  # "blist" ->ₛ "down")) # Ptr  |-> p_down_2)
  **  ((p_down_2) # Ptr  |->_)
  **  ((&((p_up_2)  # "blist" ->ₛ "down")) # Ptr  |-> p_up_down_2)
  **  ((p_up_down_2) # Ptr  |->_)
  **  ((&((p_down_2)  # "blist" ->ₛ "up")) # Ptr  |-> p_down_up_2)
  **  ((p_down_up_2) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_pre_top_2)
  **  ((h_pre_top_2) # Ptr  |->_)
  **  ((&((p_2)  # "blist" ->ₛ "next")) # Ptr  |-> p_next_2)
  **  ((p_next_2) # Ptr  |->_)
  **  ((&((p_2)  # "blist" ->ₛ "val")) # UInt  |-> v_2))
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
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (h_bucks: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) ,
  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| (map_composable m1 m2 ) |]
  &&  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (PtrArray.full h_bucks 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m1 )
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
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (PtrArray.full h_bucks 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  ((removed_pre) # Int  |->_)
.

Definition hashtbl_remove_partial_solve_wit_3 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (val: Z) (itv_next: Z) (h_top: Z) (itv_down_up: Z) (itv_up_down: Z) (itv_down: Z) (itv_up: Z) (itv_key: Z) (k_list: (@list Z)) (removed: Z) (h_pre_bucks: Z) (l_res: (@list Z)) (buck: Z) (itv: Z) (it: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (dl_up: (@list Z)) (dl_down: (@list Z)) (ind: Z) (l_prev: (@list Z)) ,
  [| (itv <> 0) |] 
  &&  [| (not_key k l_prev m1 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up) (dl_down)) ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  ((it) # Ptr  |-> itv)
  **  (store_map_missing_i store_sll b ind )
  **  (sllseg buck itv l_prev )
  **  (sll itv l_res )
  **  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_pre_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") it 0 &((itv)  # "blist" ->ₛ "up") dl_up )
  **  (dll it &((itv)  # "blist" ->ₛ "up") dl_down )
  **  ((removed) # Int  |->_)
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key)
  **  (store_string itv_key k_list )
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_up) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_down) # Ptr  |->_)
  **  ((&((itv_up)  # "blist" ->ₛ "down")) # Ptr  |-> itv_up_down)
  **  ((itv_up_down) # Ptr  |->_)
  **  ((&((itv_down)  # "blist" ->ₛ "up")) # Ptr  |-> itv_down_up)
  **  ((itv_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  ((h_top) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> itv_next)
  **  ((itv_next) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map store_uint m2 )
|--
  [| (itv <> 0) |] 
  &&  [| (not_key k l_prev m1 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up) (dl_down)) ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  (store_string key_pre k )
  **  (store_string itv_key k_list )
  **  ((it) # Ptr  |-> itv)
  **  (store_map_missing_i store_sll b ind )
  **  (sllseg buck itv l_prev )
  **  (sll itv l_res )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_pre_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") it 0 &((itv)  # "blist" ->ₛ "up") dl_up )
  **  (dll it &((itv)  # "blist" ->ₛ "up") dl_down )
  **  ((removed) # Int  |->_)
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_up) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_down) # Ptr  |->_)
  **  ((&((itv_up)  # "blist" ->ₛ "down")) # Ptr  |-> itv_up_down)
  **  ((itv_up_down) # Ptr  |->_)
  **  ((&((itv_down)  # "blist" ->ₛ "up")) # Ptr  |-> itv_down_up)
  **  ((itv_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  ((h_top) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> itv_next)
  **  ((itv_next) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map store_uint m2 )
.

Definition hashtbl_remove_partial_solve_wit_4 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (val: Z) (itv_next: Z) (h_top: Z) (itv_down_up: Z) (itv_up_down: Z) (itv_down: Z) (itv_up: Z) (itv_key: Z) (k_list: (@list Z)) (removed: Z) (h_pre_bucks: Z) (l_res: (@list Z)) (buck: Z) (itv: Z) (it: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (dl_up: (@list Z)) (dl_down: (@list Z)) (ind: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (itv_down <> 0) |] 
  &&  [| (itv_up = 0) |] 
  &&  [| (h_top <> itv) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (key_pre = itv_key) |] 
  &&  [| (k = k_list) |] 
  &&  [| (itv <> 0) |] 
  &&  [| (not_key k l_prev m1 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up) (dl_down)) ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  (store_string key_pre k )
  **  (store_string itv_key k_list )
  **  ((it) # Ptr  |-> itv_next)
  **  (store_map_missing_i store_sll b ind )
  **  (sllseg buck itv l_prev )
  **  (sll itv l_res )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_pre_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") it 0 &((itv)  # "blist" ->ₛ "up") dl_up )
  **  (dll it &((itv)  # "blist" ->ₛ "up") dl_down )
  **  ((removed) # Int  |->_)
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_up) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_down) # Ptr  |->_)
  **  ((&((itv_up)  # "blist" ->ₛ "down")) # Ptr  |-> itv_up_down)
  **  ((itv_up_down) # Ptr  |->_)
  **  ((&((itv_down)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  ((h_top) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> itv_next)
  **  ((itv_next) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map store_uint m2 )
|--
  [| (itv_down <> 0) |] 
  &&  [| (itv_up = 0) |] 
  &&  [| (h_top <> itv) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (key_pre = itv_key) |] 
  &&  [| (k = k_list) |] 
  &&  [| (itv <> 0) |] 
  &&  [| (not_key k l_prev m1 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up) (dl_down)) ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |->_)
  **  (store_string key_pre k )
  **  (store_string itv_key k_list )
  **  ((it) # Ptr  |-> itv_next)
  **  (store_map_missing_i store_sll b ind )
  **  (sllseg buck itv l_prev )
  **  (sll itv l_res )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_pre_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") it 0 &((itv)  # "blist" ->ₛ "up") dl_up )
  **  (dll it &((itv)  # "blist" ->ₛ "up") dl_down )
  **  ((removed) # Int  |->_)
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_up) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_down) # Ptr  |->_)
  **  ((&((itv_up)  # "blist" ->ₛ "down")) # Ptr  |-> itv_up_down)
  **  ((itv_up_down) # Ptr  |->_)
  **  ((&((itv_down)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  ((h_top) # Ptr  |->_)
  **  ((itv_next) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map store_uint m2 )
.

Definition hashtbl_remove_partial_solve_wit_5 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (val: Z) (itv_next: Z) (h_top: Z) (itv_down_up: Z) (itv_up_down: Z) (itv_down: Z) (itv_up: Z) (itv_key: Z) (k_list: (@list Z)) (removed: Z) (h_pre_bucks: Z) (l_res: (@list Z)) (buck: Z) (itv: Z) (it: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (dl_up: (@list Z)) (dl_down: (@list Z)) (ind: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (itv_down <> 0) |] 
  &&  [| (itv_up = 0) |] 
  &&  [| (h_top = itv) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (key_pre = itv_key) |] 
  &&  [| (k = k_list) |] 
  &&  [| (itv <> 0) |] 
  &&  [| (not_key k l_prev m1 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up) (dl_down)) ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  (store_string key_pre k )
  **  (store_string itv_key k_list )
  **  ((it) # Ptr  |-> itv_next)
  **  (store_map_missing_i store_sll b ind )
  **  (sllseg buck itv l_prev )
  **  (sll itv l_res )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_pre_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") it 0 &((itv)  # "blist" ->ₛ "up") dl_up )
  **  (dll it &((itv)  # "blist" ->ₛ "up") dl_down )
  **  ((removed) # Int  |->_)
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_up) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_down) # Ptr  |->_)
  **  ((&((itv_up)  # "blist" ->ₛ "down")) # Ptr  |-> itv_up_down)
  **  ((itv_up_down) # Ptr  |->_)
  **  ((&((itv_down)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> itv_down)
  **  ((h_top) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> itv_next)
  **  ((itv_next) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map store_uint m2 )
|--
  [| (itv_down <> 0) |] 
  &&  [| (itv_up = 0) |] 
  &&  [| (h_top = itv) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (key_pre = itv_key) |] 
  &&  [| (k = k_list) |] 
  &&  [| (itv <> 0) |] 
  &&  [| (not_key k l_prev m1 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up) (dl_down)) ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |->_)
  **  (store_string key_pre k )
  **  (store_string itv_key k_list )
  **  ((it) # Ptr  |-> itv_next)
  **  (store_map_missing_i store_sll b ind )
  **  (sllseg buck itv l_prev )
  **  (sll itv l_res )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_pre_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") it 0 &((itv)  # "blist" ->ₛ "up") dl_up )
  **  (dll it &((itv)  # "blist" ->ₛ "up") dl_down )
  **  ((removed) # Int  |->_)
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_up) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_down) # Ptr  |->_)
  **  ((&((itv_up)  # "blist" ->ₛ "down")) # Ptr  |-> itv_up_down)
  **  ((itv_up_down) # Ptr  |->_)
  **  ((&((itv_down)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> itv_down)
  **  ((h_top) # Ptr  |->_)
  **  ((itv_next) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map store_uint m2 )
.

Definition hashtbl_remove_partial_solve_wit_6 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (val: Z) (itv_next: Z) (h_top: Z) (itv_down_up: Z) (itv_up_down: Z) (itv_down: Z) (itv_up: Z) (itv_key: Z) (k_list: (@list Z)) (removed: Z) (h_pre_bucks: Z) (l_res: (@list Z)) (buck: Z) (itv: Z) (it: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (dl_up: (@list Z)) (dl_down: (@list Z)) (ind: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (itv_down <> 0) |] 
  &&  [| (itv_up <> 0) |] 
  &&  [| (h_top = itv) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (key_pre = itv_key) |] 
  &&  [| (k = k_list) |] 
  &&  [| (itv <> 0) |] 
  &&  [| (not_key k l_prev m1 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up) (dl_down)) ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  (store_string key_pre k )
  **  (store_string itv_key k_list )
  **  ((it) # Ptr  |-> itv_next)
  **  (store_map_missing_i store_sll b ind )
  **  (sllseg buck itv l_prev )
  **  (sll itv l_res )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_pre_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") it 0 &((itv)  # "blist" ->ₛ "up") dl_up )
  **  (dll it &((itv)  # "blist" ->ₛ "up") dl_down )
  **  ((removed) # Int  |->_)
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_up) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_down) # Ptr  |->_)
  **  ((&((itv_up)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_up_down) # Ptr  |->_)
  **  ((&((itv_down)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> itv_down)
  **  ((h_top) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> itv_next)
  **  ((itv_next) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map store_uint m2 )
|--
  [| (itv_down <> 0) |] 
  &&  [| (itv_up <> 0) |] 
  &&  [| (h_top = itv) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (key_pre = itv_key) |] 
  &&  [| (k = k_list) |] 
  &&  [| (itv <> 0) |] 
  &&  [| (not_key k l_prev m1 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up) (dl_down)) ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |->_)
  **  (store_string key_pre k )
  **  (store_string itv_key k_list )
  **  ((it) # Ptr  |-> itv_next)
  **  (store_map_missing_i store_sll b ind )
  **  (sllseg buck itv l_prev )
  **  (sll itv l_res )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_pre_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") it 0 &((itv)  # "blist" ->ₛ "up") dl_up )
  **  (dll it &((itv)  # "blist" ->ₛ "up") dl_down )
  **  ((removed) # Int  |->_)
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_up) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_down) # Ptr  |->_)
  **  ((&((itv_up)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_up_down) # Ptr  |->_)
  **  ((&((itv_down)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> itv_down)
  **  ((h_top) # Ptr  |->_)
  **  ((itv_next) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map store_uint m2 )
.

Definition hashtbl_remove_partial_solve_wit_7 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (val: Z) (itv_next: Z) (h_top: Z) (itv_down_up: Z) (itv_up_down: Z) (itv_down: Z) (itv_up: Z) (itv_key: Z) (k_list: (@list Z)) (removed: Z) (h_pre_bucks: Z) (l_res: (@list Z)) (buck: Z) (itv: Z) (it: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (dl_up: (@list Z)) (dl_down: (@list Z)) (ind: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (itv_down <> 0) |] 
  &&  [| (itv_up <> 0) |] 
  &&  [| (h_top <> itv) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (key_pre = itv_key) |] 
  &&  [| (k = k_list) |] 
  &&  [| (itv <> 0) |] 
  &&  [| (not_key k l_prev m1 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up) (dl_down)) ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  (store_string key_pre k )
  **  (store_string itv_key k_list )
  **  ((it) # Ptr  |-> itv_next)
  **  (store_map_missing_i store_sll b ind )
  **  (sllseg buck itv l_prev )
  **  (sll itv l_res )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_pre_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") it 0 &((itv)  # "blist" ->ₛ "up") dl_up )
  **  (dll it &((itv)  # "blist" ->ₛ "up") dl_down )
  **  ((removed) # Int  |->_)
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_up) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_down) # Ptr  |->_)
  **  ((&((itv_up)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_up_down) # Ptr  |->_)
  **  ((&((itv_down)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  ((h_top) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> itv_next)
  **  ((itv_next) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map store_uint m2 )
|--
  [| (itv_down <> 0) |] 
  &&  [| (itv_up <> 0) |] 
  &&  [| (h_top <> itv) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (key_pre = itv_key) |] 
  &&  [| (k = k_list) |] 
  &&  [| (itv <> 0) |] 
  &&  [| (not_key k l_prev m1 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up) (dl_down)) ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |->_)
  **  (store_string key_pre k )
  **  (store_string itv_key k_list )
  **  ((it) # Ptr  |-> itv_next)
  **  (store_map_missing_i store_sll b ind )
  **  (sllseg buck itv l_prev )
  **  (sll itv l_res )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_pre_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") it 0 &((itv)  # "blist" ->ₛ "up") dl_up )
  **  (dll it &((itv)  # "blist" ->ₛ "up") dl_down )
  **  ((removed) # Int  |->_)
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_up) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_down) # Ptr  |->_)
  **  ((&((itv_up)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_up_down) # Ptr  |->_)
  **  ((&((itv_down)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  ((h_top) # Ptr  |->_)
  **  ((itv_next) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map store_uint m2 )
.

Definition hashtbl_remove_partial_solve_wit_8 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (val: Z) (itv_next: Z) (h_top: Z) (itv_down_up: Z) (itv_up_down: Z) (itv_down: Z) (itv_up: Z) (itv_key: Z) (k_list: (@list Z)) (removed: Z) (h_pre_bucks: Z) (l_res: (@list Z)) (buck: Z) (itv: Z) (it: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (dl_up: (@list Z)) (dl_down: (@list Z)) (ind: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (itv_down = 0) |] 
  &&  [| (itv_up <> 0) |] 
  &&  [| (h_top <> itv) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (key_pre = itv_key) |] 
  &&  [| (k = k_list) |] 
  &&  [| (itv <> 0) |] 
  &&  [| (not_key k l_prev m1 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up) (dl_down)) ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  (store_string key_pre k )
  **  (store_string itv_key k_list )
  **  ((it) # Ptr  |-> itv_next)
  **  (store_map_missing_i store_sll b ind )
  **  (sllseg buck itv l_prev )
  **  (sll itv l_res )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_pre_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") it 0 &((itv)  # "blist" ->ₛ "up") dl_up )
  **  (dll it &((itv)  # "blist" ->ₛ "up") dl_down )
  **  ((removed) # Int  |->_)
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_up) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_down) # Ptr  |->_)
  **  ((&((itv_up)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_up_down) # Ptr  |->_)
  **  ((&((itv_down)  # "blist" ->ₛ "up")) # Ptr  |-> itv_down_up)
  **  ((itv_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  ((h_top) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> itv_next)
  **  ((itv_next) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map store_uint m2 )
|--
  [| (itv_down = 0) |] 
  &&  [| (itv_up <> 0) |] 
  &&  [| (h_top <> itv) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (key_pre = itv_key) |] 
  &&  [| (k = k_list) |] 
  &&  [| (itv <> 0) |] 
  &&  [| (not_key k l_prev m1 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up) (dl_down)) ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |->_)
  **  (store_string key_pre k )
  **  (store_string itv_key k_list )
  **  ((it) # Ptr  |-> itv_next)
  **  (store_map_missing_i store_sll b ind )
  **  (sllseg buck itv l_prev )
  **  (sll itv l_res )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_pre_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") it 0 &((itv)  # "blist" ->ₛ "up") dl_up )
  **  (dll it &((itv)  # "blist" ->ₛ "up") dl_down )
  **  ((removed) # Int  |->_)
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_up) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_down) # Ptr  |->_)
  **  ((&((itv_up)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_up_down) # Ptr  |->_)
  **  ((&((itv_down)  # "blist" ->ₛ "up")) # Ptr  |-> itv_down_up)
  **  ((itv_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  ((h_top) # Ptr  |->_)
  **  ((itv_next) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map store_uint m2 )
.

Definition hashtbl_remove_partial_solve_wit_9 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (val: Z) (itv_next: Z) (h_top: Z) (itv_down_up: Z) (itv_up_down: Z) (itv_down: Z) (itv_up: Z) (itv_key: Z) (k_list: (@list Z)) (removed: Z) (h_pre_bucks: Z) (l_res: (@list Z)) (buck: Z) (itv: Z) (it: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (dl_up: (@list Z)) (dl_down: (@list Z)) (ind: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (itv_down = 0) |] 
  &&  [| (itv_up <> 0) |] 
  &&  [| (h_top = itv) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (key_pre = itv_key) |] 
  &&  [| (k = k_list) |] 
  &&  [| (itv <> 0) |] 
  &&  [| (not_key k l_prev m1 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up) (dl_down)) ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  (store_string key_pre k )
  **  (store_string itv_key k_list )
  **  ((it) # Ptr  |-> itv_next)
  **  (store_map_missing_i store_sll b ind )
  **  (sllseg buck itv l_prev )
  **  (sll itv l_res )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_pre_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") it 0 &((itv)  # "blist" ->ₛ "up") dl_up )
  **  (dll it &((itv)  # "blist" ->ₛ "up") dl_down )
  **  ((removed) # Int  |->_)
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_up) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_down) # Ptr  |->_)
  **  ((&((itv_up)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_up_down) # Ptr  |->_)
  **  ((&((itv_down)  # "blist" ->ₛ "up")) # Ptr  |-> itv_down_up)
  **  ((itv_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> itv_down)
  **  ((h_top) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> itv_next)
  **  ((itv_next) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map store_uint m2 )
|--
  [| (itv_down = 0) |] 
  &&  [| (itv_up <> 0) |] 
  &&  [| (h_top = itv) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (key_pre = itv_key) |] 
  &&  [| (k = k_list) |] 
  &&  [| (itv <> 0) |] 
  &&  [| (not_key k l_prev m1 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up) (dl_down)) ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |->_)
  **  (store_string key_pre k )
  **  (store_string itv_key k_list )
  **  ((it) # Ptr  |-> itv_next)
  **  (store_map_missing_i store_sll b ind )
  **  (sllseg buck itv l_prev )
  **  (sll itv l_res )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_pre_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") it 0 &((itv)  # "blist" ->ₛ "up") dl_up )
  **  (dll it &((itv)  # "blist" ->ₛ "up") dl_down )
  **  ((removed) # Int  |->_)
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_up) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_down) # Ptr  |->_)
  **  ((&((itv_up)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_up_down) # Ptr  |->_)
  **  ((&((itv_down)  # "blist" ->ₛ "up")) # Ptr  |-> itv_down_up)
  **  ((itv_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> itv_down)
  **  ((h_top) # Ptr  |->_)
  **  ((itv_next) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map store_uint m2 )
.

Definition hashtbl_remove_partial_solve_wit_10 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (val: Z) (itv_next: Z) (h_top: Z) (itv_down_up: Z) (itv_up_down: Z) (itv_down: Z) (itv_up: Z) (itv_key: Z) (k_list: (@list Z)) (removed: Z) (h_pre_bucks: Z) (l_res: (@list Z)) (buck: Z) (itv: Z) (it: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (dl_up: (@list Z)) (dl_down: (@list Z)) (ind: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (itv_down = 0) |] 
  &&  [| (itv_up = 0) |] 
  &&  [| (h_top = itv) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (key_pre = itv_key) |] 
  &&  [| (k = k_list) |] 
  &&  [| (itv <> 0) |] 
  &&  [| (not_key k l_prev m1 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up) (dl_down)) ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  (store_string key_pre k )
  **  (store_string itv_key k_list )
  **  ((it) # Ptr  |-> itv_next)
  **  (store_map_missing_i store_sll b ind )
  **  (sllseg buck itv l_prev )
  **  (sll itv l_res )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_pre_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") it 0 &((itv)  # "blist" ->ₛ "up") dl_up )
  **  (dll it &((itv)  # "blist" ->ₛ "up") dl_down )
  **  ((removed) # Int  |->_)
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_up) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_down) # Ptr  |->_)
  **  ((&((itv_up)  # "blist" ->ₛ "down")) # Ptr  |-> itv_up_down)
  **  ((itv_up_down) # Ptr  |->_)
  **  ((&((itv_down)  # "blist" ->ₛ "up")) # Ptr  |-> itv_down_up)
  **  ((itv_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> itv_down)
  **  ((h_top) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> itv_next)
  **  ((itv_next) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map store_uint m2 )
|--
  [| (itv_down = 0) |] 
  &&  [| (itv_up = 0) |] 
  &&  [| (h_top = itv) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (key_pre = itv_key) |] 
  &&  [| (k = k_list) |] 
  &&  [| (itv <> 0) |] 
  &&  [| (not_key k l_prev m1 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up) (dl_down)) ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |->_)
  **  (store_string key_pre k )
  **  (store_string itv_key k_list )
  **  ((it) # Ptr  |-> itv_next)
  **  (store_map_missing_i store_sll b ind )
  **  (sllseg buck itv l_prev )
  **  (sll itv l_res )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_pre_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") it 0 &((itv)  # "blist" ->ₛ "up") dl_up )
  **  (dll it &((itv)  # "blist" ->ₛ "up") dl_down )
  **  ((removed) # Int  |->_)
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_up) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_down) # Ptr  |->_)
  **  ((&((itv_up)  # "blist" ->ₛ "down")) # Ptr  |-> itv_up_down)
  **  ((itv_up_down) # Ptr  |->_)
  **  ((&((itv_down)  # "blist" ->ₛ "up")) # Ptr  |-> itv_down_up)
  **  ((itv_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> itv_down)
  **  ((h_top) # Ptr  |->_)
  **  ((itv_next) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map store_uint m2 )
.

Definition hashtbl_remove_partial_solve_wit_11 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (val: Z) (itv_next: Z) (h_top: Z) (itv_down_up: Z) (itv_up_down: Z) (itv_down: Z) (itv_up: Z) (itv_key: Z) (k_list: (@list Z)) (removed: Z) (h_pre_bucks: Z) (l_res: (@list Z)) (buck: Z) (itv: Z) (it: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (dl_up: (@list Z)) (dl_down: (@list Z)) (ind: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (itv_down = 0) |] 
  &&  [| (itv_up = 0) |] 
  &&  [| (h_top <> itv) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (key_pre = itv_key) |] 
  &&  [| (k = k_list) |] 
  &&  [| (itv <> 0) |] 
  &&  [| (not_key k l_prev m1 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up) (dl_down)) ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  (store_string key_pre k )
  **  (store_string itv_key k_list )
  **  ((it) # Ptr  |-> itv_next)
  **  (store_map_missing_i store_sll b ind )
  **  (sllseg buck itv l_prev )
  **  (sll itv l_res )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_pre_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") it 0 &((itv)  # "blist" ->ₛ "up") dl_up )
  **  (dll it &((itv)  # "blist" ->ₛ "up") dl_down )
  **  ((removed) # Int  |->_)
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_up) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_down) # Ptr  |->_)
  **  ((&((itv_up)  # "blist" ->ₛ "down")) # Ptr  |-> itv_up_down)
  **  ((itv_up_down) # Ptr  |->_)
  **  ((&((itv_down)  # "blist" ->ₛ "up")) # Ptr  |-> itv_down_up)
  **  ((itv_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  ((h_top) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> itv_next)
  **  ((itv_next) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map store_uint m2 )
|--
  [| (itv_down = 0) |] 
  &&  [| (itv_up = 0) |] 
  &&  [| (h_top <> itv) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (key_pre = itv_key) |] 
  &&  [| (k = k_list) |] 
  &&  [| (itv <> 0) |] 
  &&  [| (not_key k l_prev m1 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 (app (dl_up) (dl_down)) ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |->_)
  **  (store_string key_pre k )
  **  (store_string itv_key k_list )
  **  ((it) # Ptr  |-> itv_next)
  **  (store_map_missing_i store_sll b ind )
  **  (sllseg buck itv l_prev )
  **  (sll itv l_res )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_pre_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1 )
  **  (dllseg &((h_pre)  # "hashtbl" ->ₛ "top") it 0 &((itv)  # "blist" ->ₛ "up") dl_up )
  **  (dll it &((itv)  # "blist" ->ₛ "up") dl_down )
  **  ((removed) # Int  |->_)
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> itv_key)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> itv_up)
  **  ((itv_up) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> itv_down)
  **  ((itv_down) # Ptr  |->_)
  **  ((&((itv_up)  # "blist" ->ₛ "down")) # Ptr  |-> itv_up_down)
  **  ((itv_up_down) # Ptr  |->_)
  **  ((&((itv_down)  # "blist" ->ₛ "up")) # Ptr  |-> itv_down_up)
  **  ((itv_down_up) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  ((h_top) # Ptr  |->_)
  **  ((itv_next) # Ptr  |->_)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map store_uint m2 )
.

Definition hashtbl_remove_which_implies_wit_1 := 
forall (m1: ((@list Z) -> (@option Z))) (h: Z) ,
  (store_hash_skeleton h m1 )
|--
  EX (h_bucks: Z)  (lh: (@list Z))  (b: (Z -> (@option (Z * (@list Z)))))  (l: (@list Z)) ,
  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  (dll &((h)  # "hashtbl" ->ₛ "top") 0 l )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (PtrArray.full h_bucks 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m1 )
.

(*----- Function hashtbl_free_blist -----*)

Definition hashtbl_free_blist_safety_wit_1 := 
forall (bl_pre: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (l: (@list Z)) ,
  [| (map_composable m1 m2 ) |]
  &&  ((( &( "bl" ) )) # Ptr  |-> bl_pre)
  **  (sll bl_pre l )
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_free_blist_return_wit_1 := 
forall (bl_pre: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) ,
  [| (map_composable m1 m2 ) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (bl_pre <> 0) |] 
  &&  [| (map_composable m1 m2 ) |]
  &&  (store_map store_name m1 )
  **  (store_map store_uint m2 )
|--
  [| (map_composable m1 m2 ) |]
  &&  (store_map store_name m1 )
  **  (store_map store_uint m2 )
.

Definition hashtbl_free_blist_return_wit_2 := 
forall (bl_pre: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (l: (@list Z)) ,
  [| (bl_pre = 0) |] 
  &&  [| (map_composable m1 m2 ) |]
  &&  (sll bl_pre l )
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
|--
  [| (map_composable m1 m2 ) |]
  &&  (store_map store_name m1 )
  **  (store_map store_uint m2 )
.

Definition hashtbl_free_blist_partial_solve_wit_1_pure := 
forall (bl_pre: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (l: (@list Z)) ,
  [| (bl_pre <> 0) |] 
  &&  [| (map_composable m1 m2 ) |]
  &&  ((( &( "bl" ) )) # Ptr  |-> bl_pre)
  **  (sll bl_pre l )
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
|--
  [| (bl_pre <> 0) |]
.

Definition hashtbl_free_blist_partial_solve_wit_1_aux := 
forall (bl_pre: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (l: (@list Z)) ,
  [| (bl_pre <> 0) |] 
  &&  [| (map_composable m1 m2 ) |]
  &&  (sll bl_pre l )
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
|--
  [| (bl_pre <> 0) |] 
  &&  [| (bl_pre <> 0) |] 
  &&  [| (map_composable m1 m2 ) |]
  &&  (sll bl_pre l )
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
.

Definition hashtbl_free_blist_partial_solve_wit_1 := hashtbl_free_blist_partial_solve_wit_1_pure -> hashtbl_free_blist_partial_solve_wit_1_aux.

Definition hashtbl_free_blist_partial_solve_wit_2_pure := 
forall (bl_pre: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (bl_key: Z) (k1: (@list Z)) (bl_next: Z) (l1: (@list Z)) ,
  [| (bl_pre <> 0) |] 
  &&  [| (map_composable m1 m2 ) |]
  &&  ((( &( "bl" ) )) # Ptr  |-> bl_pre)
  **  ((&((bl_pre)  # "blist" ->ₛ "next")) # Ptr  |-> bl_next)
  **  (sll bl_next l1 )
  **  ((&((bl_pre)  # "blist" ->ₛ "key")) # Ptr  |-> bl_key)
  **  (store_string bl_key k1 )
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
|--
  [| (map_composable m1 m2 ) |]
.

Definition hashtbl_free_blist_partial_solve_wit_2_aux := 
forall (bl_pre: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (bl_key: Z) (k1: (@list Z)) (bl_next: Z) (l1: (@list Z)) ,
  [| (bl_pre <> 0) |] 
  &&  [| (map_composable m1 m2 ) |]
  &&  ((&((bl_pre)  # "blist" ->ₛ "next")) # Ptr  |-> bl_next)
  **  (sll bl_next l1 )
  **  ((&((bl_pre)  # "blist" ->ₛ "key")) # Ptr  |-> bl_key)
  **  (store_string bl_key k1 )
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
|--
  [| (map_composable m1 m2 ) |] 
  &&  [| (bl_pre <> 0) |] 
  &&  [| (map_composable m1 m2 ) |]
  &&  (sll bl_next l1 )
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  ((&((bl_pre)  # "blist" ->ₛ "next")) # Ptr  |-> bl_next)
  **  ((&((bl_pre)  # "blist" ->ₛ "key")) # Ptr  |-> bl_key)
  **  (store_string bl_key k1 )
.

Definition hashtbl_free_blist_partial_solve_wit_2 := hashtbl_free_blist_partial_solve_wit_2_pure -> hashtbl_free_blist_partial_solve_wit_2_aux.

Definition hashtbl_free_blist_partial_solve_wit_3_pure := 
forall (bl_pre: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (bl_key: Z) (k1: (@list Z)) (bl_next: Z) ,
  [| (map_composable m1 m2 ) |] 
  &&  [| (bl_pre <> 0) |] 
  &&  [| (map_composable m1 m2 ) |]
  &&  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  ((( &( "bl" ) )) # Ptr  |-> bl_pre)
  **  ((&((bl_pre)  # "blist" ->ₛ "next")) # Ptr  |-> bl_next)
  **  ((&((bl_pre)  # "blist" ->ₛ "key")) # Ptr  |-> bl_key)
  **  (store_string bl_key k1 )
|--
  [| (map_composable m1 m2 ) |]
.

Definition hashtbl_free_blist_partial_solve_wit_3_aux := 
forall (bl_pre: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (bl_key: Z) (k1: (@list Z)) (bl_next: Z) ,
  [| (map_composable m1 m2 ) |] 
  &&  [| (bl_pre <> 0) |] 
  &&  [| (map_composable m1 m2 ) |]
  &&  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  ((&((bl_pre)  # "blist" ->ₛ "next")) # Ptr  |-> bl_next)
  **  ((&((bl_pre)  # "blist" ->ₛ "key")) # Ptr  |-> bl_key)
  **  (store_string bl_key k1 )
|--
  [| (map_composable m1 m2 ) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (bl_pre <> 0) |] 
  &&  [| (map_composable m1 m2 ) |]
  &&  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  (store_string bl_key k1 )
  **  ((&((bl_pre)  # "blist" ->ₛ "key")) # Ptr  |-> bl_key)
  **  ((&((bl_pre)  # "blist" ->ₛ "next")) # Ptr  |-> bl_next)
.

Definition hashtbl_free_blist_partial_solve_wit_3 := hashtbl_free_blist_partial_solve_wit_3_pure -> hashtbl_free_blist_partial_solve_wit_3_aux.

Definition hashtbl_free_blist_partial_solve_wit_4 := 
forall (bl_pre: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (bl_next: Z) ,
  [| (map_composable m1 m2 ) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (bl_pre <> 0) |] 
  &&  [| (map_composable m1 m2 ) |]
  &&  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  ((&((bl_pre)  # "blist" ->ₛ "next")) # Ptr  |-> bl_next)
|--
  [| (map_composable m1 m2 ) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (bl_pre <> 0) |] 
  &&  [| (map_composable m1 m2 ) |]
  &&  ((&((bl_pre)  # "blist" ->ₛ "next")) # Ptr  |->_)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
.

Definition hashtbl_free_blist_which_implies_wit_1 := 
forall (l: (@list Z)) (bl: Z) ,
  [| (bl <> 0) |]
  &&  (sll bl l )
|--
  EX (bl_key: Z)  (k1: (@list Z))  (bl_next: Z)  (l1: (@list Z)) ,
  ((&((bl)  # "blist" ->ₛ "next")) # Ptr  |-> bl_next)
  **  (sll bl_next l1 )
  **  ((&((bl)  # "blist" ->ₛ "key")) # Ptr  |-> bl_key)
  **  (store_string bl_key k1 )
.

(*----- Function hashtbl_clear -----*)

Definition hashtbl_clear_safety_wit_1 := 
forall (h_pre: Z) (top: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (h_bucks: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) ,
  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| (map_composable m1 m2 ) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (PtrArray.full h_bucks 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_clear_safety_wit_2 := 
forall (h_pre: Z) (top: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (h_bucks: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) ,
  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| (map_composable m1 m2 ) |]
  &&  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (PtrArray.full h_bucks 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_clear_safety_wit_3 := 
forall (h_pre: Z) (top: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (h_pre_bucks: Z) (i: Z) (l: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) ,
  [| (map_composable m1 m2 ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (i >= 211) |]
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (PtrArray.full h_pre_bucks 211 lh )
|--
  [| (211 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 211) |]
.

Definition hashtbl_clear_safety_wit_4 := 
forall (h_pre: Z) (top: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (h_pre_bucks: Z) (i: Z) (l: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) ,
  [| (i < 211) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (i >= 211) |]
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (PtrArray.full h_pre_bucks 211 lh )
|--
  [| False |]
.

Definition hashtbl_clear_safety_wit_5 := 
forall (h_pre: Z) (top: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (li: (@list Z)) (buck_i: Z) (h_pre_bucks: Z) (i: Z) (l: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) ,
  [| (map_composable m1 m2 ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (i >= 0) |] 
  &&  [| (i < 211) |]
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (PtrArray.missing_i h_pre_bucks i 0 211 lh )
  **  (store_map_missing_first_i_Z store_sll b i )
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  (((h_pre_bucks + (i * sizeof(PTR) ) )) # Ptr  |-> buck_i)
  **  (sll buck_i li )
|--
  [| (211 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 211) |]
.

Definition hashtbl_clear_safety_wit_6 := 
forall (h_pre: Z) (top: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (li: (@list Z)) (buck_i: Z) (h_pre_bucks: Z) (i: Z) (l: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) ,
  [| (i >= 211) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (i >= 0) |] 
  &&  [| (i < 211) |]
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (PtrArray.missing_i h_pre_bucks i 0 211 lh )
  **  (store_map_missing_first_i_Z store_sll b i )
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  (((h_pre_bucks + (i * sizeof(PTR) ) )) # Ptr  |-> buck_i)
  **  (sll buck_i li )
|--
  [| False |]
.

Definition hashtbl_clear_safety_wit_7 := 
forall (h_pre: Z) (top: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (li: (@list Z)) (buck_i: Z) (h_pre_bucks: Z) (i: Z) (l: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) ,
  [| (i < 211) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (i >= 0) |] 
  &&  [| (i < 211) |]
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (PtrArray.missing_i h_pre_bucks i 0 211 lh )
  **  (store_map_missing_first_i_Z store_sll b i )
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  (((h_pre_bucks + (i * sizeof(PTR) ) )) # Ptr  |-> buck_i)
  **  (sll buck_i li )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_clear_safety_wit_8 := 
forall (h_pre: Z) (top: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (li: (@list Z)) (buck_i: Z) (h_pre_bucks: Z) (i: Z) (l: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) ,
  [| (i < 0) |] 
  &&  [| (i < 211) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (i >= 0) |] 
  &&  [| (i < 211) |]
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (PtrArray.missing_i h_pre_bucks i 0 211 lh )
  **  (store_map_missing_first_i_Z store_sll b i )
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  (((h_pre_bucks + (i * sizeof(PTR) ) )) # Ptr  |-> buck_i)
  **  (sll buck_i li )
|--
  [| False |]
.

Definition hashtbl_clear_safety_wit_9 := 
forall (h_pre: Z) (top: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (buck_i: Z) (h_pre_bucks: Z) (i: Z) (l: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) ,
  [| (map_composable m1 m2 ) |] 
  &&  [| (i >= 0) |] 
  &&  [| (i < 211) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (i >= 0) |] 
  &&  [| (i < 211) |]
  &&  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (PtrArray.missing_i h_pre_bucks i 0 211 lh )
  **  (store_map_missing_first_i_Z store_sll b i )
  **  (((h_pre_bucks + (i * sizeof(PTR) ) )) # Ptr  |-> buck_i)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_clear_safety_wit_10 := 
forall (h_pre: Z) (top: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (h_pre_bucks: Z) (i: Z) (l: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) ,
  [| (map_composable m1 m2 ) |] 
  &&  [| (i >= 0) |] 
  &&  [| (i < 211) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (i >= 0) |] 
  &&  [| (i < 211) |]
  &&  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (PtrArray.missing_i h_pre_bucks i 0 211 lh )
  **  (store_map_missing_first_i_Z store_sll b i )
  **  (((h_pre_bucks + (i * sizeof(PTR) ) )) # Ptr  |-> 0)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition hashtbl_clear_safety_wit_11 := 
forall (h_pre: Z) (top: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (h_pre_bucks: Z) (i: Z) (l: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) ,
  [| (i >= 211) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (i >= 211) |]
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_clear_safety_wit_12 := 
forall (h_pre: Z) (top: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (i: Z) (l: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) ,
  [| (i >= 211) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (i >= 211) |]
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> 0)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_clear_entail_wit_1 := 
forall (h_pre: Z) (top: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (h_bucks: Z) (lh_2: (@list Z)) (b_2: (Z -> (@option (Z * (@list Z))))) (l_2: (@list Z)) ,
  [| (contain_all_addrs m1 l_2 ) |] 
  &&  [| (repr_all_heads lh_2 b_2 ) |] 
  &&  [| (repr_all_heads lh_2 b_2 ) |] 
  &&  [| (contain_all_correct_addrs m1 b_2 ) |] 
  &&  [| (map_composable m1 m2 ) |]
  &&  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l_2 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (PtrArray.full h_bucks 211 lh_2 )
  **  (store_map store_sll b_2 )
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
|--
  (EX (h_pre_bucks: Z)  (l: (@list Z))  (lh: (@list Z))  (b: (Z -> (@option (Z * (@list Z))))) ,
  [| (map_composable m1 m2 ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (0 >= 211) |]
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (PtrArray.full h_pre_bucks 211 lh ))
  ||
  (EX (li: (@list Z))  (buck_i: Z)  (h_pre_bucks_2: Z)  (l: (@list Z))  (lh: (@list Z))  (b: (Z -> (@option (Z * (@list Z))))) ,
  [| (map_composable m1 m2 ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (0 >= 0) |] 
  &&  [| (0 < 211) |]
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks_2)
  **  (PtrArray.missing_i h_pre_bucks_2 0 0 211 lh )
  **  (store_map_missing_first_i_Z store_sll b 0 )
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  (((h_pre_bucks_2 + (0 * sizeof(PTR) ) )) # Ptr  |-> buck_i)
  **  (sll buck_i li ))
.

Definition hashtbl_clear_entail_wit_2 := 
forall (h_pre: Z) (top: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (h_pre_bucks_3: Z) (i: Z) (l_2: (@list Z)) (lh_2: (@list Z)) (b_2: (Z -> (@option (Z * (@list Z))))) ,
  [| (map_composable m1 m2 ) |] 
  &&  [| (i >= 0) |] 
  &&  [| (i < 211) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (repr_all_heads lh_2 b_2 ) |] 
  &&  [| (i >= 0) |] 
  &&  [| (i < 211) |]
  &&  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l_2 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks_3)
  **  (PtrArray.missing_i h_pre_bucks_3 i 0 211 lh_2 )
  **  (store_map_missing_first_i_Z store_sll b_2 i )
  **  (((h_pre_bucks_3 + (i * sizeof(PTR) ) )) # Ptr  |-> 0)
|--
  (EX (h_pre_bucks: Z)  (l: (@list Z))  (lh: (@list Z))  (b: (Z -> (@option (Z * (@list Z))))) ,
  [| (map_composable m1 m2 ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| ((i + 1 ) >= 211) |]
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (PtrArray.full h_pre_bucks 211 lh ))
  ||
  (EX (li: (@list Z))  (buck_i: Z)  (h_pre_bucks_2: Z)  (l: (@list Z))  (lh: (@list Z))  (b: (Z -> (@option (Z * (@list Z))))) ,
  [| (map_composable m1 m2 ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| ((i + 1 ) >= 0) |] 
  &&  [| ((i + 1 ) < 211) |]
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks_2)
  **  (PtrArray.missing_i h_pre_bucks_2 (i + 1 ) 0 211 lh )
  **  (store_map_missing_first_i_Z store_sll b (i + 1 ) )
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  (((h_pre_bucks_2 + ((i + 1 ) * sizeof(PTR) ) )) # Ptr  |-> buck_i)
  **  (sll buck_i li ))
.

Definition hashtbl_clear_return_wit_1 := 
forall (h_pre: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (i: Z) (l_2: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) ,
  [| (i >= 211) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (i >= 211) |]
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> 0)
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l_2 )
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> 0)
|--
  EX (l: (@list Z)) ,
  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> 0)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> 0)
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
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
forall (h_pre: Z) (top: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (li: (@list Z)) (buck_i: Z) (h_pre_bucks: Z) (i: Z) (l: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) ,
  [| (i >= 0) |] 
  &&  [| (i < 211) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (i >= 0) |] 
  &&  [| (i < 211) |]
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (PtrArray.missing_i h_pre_bucks i 0 211 lh )
  **  (store_map_missing_first_i_Z store_sll b i )
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  (((h_pre_bucks + (i * sizeof(PTR) ) )) # Ptr  |-> buck_i)
  **  (sll buck_i li )
|--
  [| (map_composable m1 m2 ) |]
.

Definition hashtbl_clear_partial_solve_wit_2_aux := 
forall (h_pre: Z) (top: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (li: (@list Z)) (buck_i: Z) (h_pre_bucks: Z) (i: Z) (l: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) ,
  [| (i >= 0) |] 
  &&  [| (i < 211) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (i >= 0) |] 
  &&  [| (i < 211) |]
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (PtrArray.missing_i h_pre_bucks i 0 211 lh )
  **  (store_map_missing_first_i_Z store_sll b i )
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  (((h_pre_bucks + (i * sizeof(PTR) ) )) # Ptr  |-> buck_i)
  **  (sll buck_i li )
|--
  [| (map_composable m1 m2 ) |] 
  &&  [| (i >= 0) |] 
  &&  [| (i < 211) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (i >= 0) |] 
  &&  [| (i < 211) |]
  &&  (sll buck_i li )
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (PtrArray.missing_i h_pre_bucks i 0 211 lh )
  **  (store_map_missing_first_i_Z store_sll b i )
  **  (((h_pre_bucks + (i * sizeof(PTR) ) )) # Ptr  |-> buck_i)
.

Definition hashtbl_clear_partial_solve_wit_2 := hashtbl_clear_partial_solve_wit_2_pure -> hashtbl_clear_partial_solve_wit_2_aux.

Definition hashtbl_clear_partial_solve_wit_3 := 
forall (h_pre: Z) (top: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (h_pre_bucks: Z) (i: Z) (l: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) ,
  [| (i >= 211) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (i >= 211) |]
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (PtrArray.full h_pre_bucks 211 lh )
|--
  [| (i >= 211) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (i >= 211) |]
  &&  (PtrArray.full h_pre_bucks 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
.

Definition hashtbl_clear_which_implies_wit_1 := 
forall (m1: ((@list Z) -> (@option Z))) (h: Z) ,
  (store_hash_skeleton h m1 )
|--
  EX (h_bucks: Z)  (lh: (@list Z))  (b: (Z -> (@option (Z * (@list Z)))))  (l: (@list Z)) ,
  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  (dll &((h)  # "hashtbl" ->ₛ "top") 0 l )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (PtrArray.full h_bucks 211 lh )
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
forall (h_pre: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (l: (@list Z)) ,
  [| (map_composable m1 m2 ) |]
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> 0)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> 0)
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
|--
  [| (map_composable m1 m2 ) |]
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> 0)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> 0)
  **  (dll &((h_pre)  # "hashtbl" ->ₛ "top") 0 l )
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include hashtbl_Strategy_Correct.
Include ptr_array_Strategy_Correct.

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
Axiom proof_of_hashtbl_findref_partial_solve_wit_3_pure : hashtbl_findref_partial_solve_wit_3_pure.
Axiom proof_of_hashtbl_findref_partial_solve_wit_3 : hashtbl_findref_partial_solve_wit_3.
Axiom proof_of_hashtbl_findref_partial_solve_wit_4 : hashtbl_findref_partial_solve_wit_4.
Axiom proof_of_hashtbl_findref_partial_solve_wit_5_pure : hashtbl_findref_partial_solve_wit_5_pure.
Axiom proof_of_hashtbl_findref_partial_solve_wit_5 : hashtbl_findref_partial_solve_wit_5.
Axiom proof_of_hashtbl_findref_which_implies_wit_1 : hashtbl_findref_which_implies_wit_1.
Axiom proof_of_hashtbl_findref_which_implies_wit_2 : hashtbl_findref_which_implies_wit_2.
Axiom proof_of_hashtbl_findref_which_implies_wit_3 : hashtbl_findref_which_implies_wit_3.
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
Axiom proof_of_hashtbl_free_blist_partial_solve_wit_1_pure : hashtbl_free_blist_partial_solve_wit_1_pure.
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
