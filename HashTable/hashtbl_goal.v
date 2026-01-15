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
From SimpleC.EE Require Import ptr_array_strategy_goal.
From SimpleC.EE Require Import ptr_array_strategy_proof.
From SimpleC.EE Require Import array_shape_strategy_goal.
From SimpleC.EE Require Import array_shape_strategy_proof.

(*----- Function hashtbl_findref -----*)

Definition hashtbl_findref_safety_wit_1 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (h_bucks: Z) (h_top: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (retval: Z) ,
  [| (retval = (hash_string_coq (k))) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |]
  &&  (store_string key_pre k )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (PtrArray.full h_bucks 211 lh )
  **  (store_map store_sll b0 )
  **  (store_map store_name m )
  **  ((( &( "i" ) )) # Ptr  |->_)
  **  ((( &( "ind" ) )) # UInt  |->_)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
|--
  [| (211 <> 0) |]
.

Definition hashtbl_findref_safety_wit_2 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (h_bucks: Z) (h_top: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (retval: Z) ,
  [| (retval = (hash_string_coq (k))) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |]
  &&  (store_string key_pre k )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (PtrArray.full h_bucks 211 lh )
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
forall (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (h_top: Z) (k_list_current: (@list Z)) (key_addr: Z) (l_resres: (@list Z)) (p_current: Z) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (i: Z) (key: Z) (l_prev: (@list Z)) (buck: Z) (l0: (@list Z)) (ind: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) ,
  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair (buck) (l0))))) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l_res = (cons (p_current) (l_resres))) |]
  &&  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "i" ) )) # Ptr  |-> i)
  **  ((i) # Ptr  |-> p_current)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (sllseg buck p_current l_prev )
  **  ((&((p_current)  # "blist" ->ₛ "key")) # Ptr  |-> key_addr)
  **  (store_string key_addr k_list_current )
  **  (sll p_current l_res )
  **  (store_map store_sll b0 )
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
  **  (store_string key k )
  **  (store_map store_name m )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_findref_safety_wit_4 := 
forall (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (h_bucks: Z) (h_top: Z) (h: Z) (l_res: (@list Z)) (i_v: Z) (i: Z) (key: Z) (l_prev: (@list Z)) (buck: Z) (l0: (@list Z)) (ind: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) ,
  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair (buck) (l0))))) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (i_v = 0) |] 
  &&  [| (l_res = nil) |]
  &&  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "i" ) )) # Ptr  |-> i)
  **  ((i) # Ptr  |-> i_v)
  **  (store_map store_sll b0 )
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
  **  (store_string key k )
  **  (store_map store_name m )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_findref_safety_wit_5 := 
forall (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (h_bucks: Z) (h_top: Z) (h: Z) (l_res: (@list Z)) (i_v: Z) (i: Z) (key: Z) (l_prev: (@list Z)) (buck: Z) (l0: (@list Z)) (ind: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) ,
  [| (i_v <> 0) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair (buck) (l0))))) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (i_v = 0) |] 
  &&  [| (l_res = nil) |]
  &&  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "i" ) )) # Ptr  |-> i)
  **  ((i) # Ptr  |-> i_v)
  **  (store_map store_sll b0 )
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
  **  (store_string key k )
  **  (store_map store_name m )
|--
  [| False |]
.

Definition hashtbl_findref_safety_wit_6 := 
forall (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (h_top: Z) (k_list_current: (@list Z)) (key_addr: Z) (l_resres: (@list Z)) (p_current: Z) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (i: Z) (key: Z) (l_prev: (@list Z)) (buck: Z) (l0: (@list Z)) (ind: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (k <> k_list_current) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair (buck) (l0))))) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l_res = (cons (p_current) (l_resres))) |]
  &&  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "i" ) )) # Ptr  |-> i)
  **  ((i) # Ptr  |-> p_current)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (sllseg buck p_current l_prev )
  **  ((&((p_current)  # "blist" ->ₛ "key")) # Ptr  |-> key_addr)
  **  (sll p_current l_res )
  **  (store_map store_sll b0 )
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
  **  (store_map store_name m )
|--
  [| False |]
.

Definition hashtbl_findref_safety_wit_7 := 
forall (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (h_top: Z) (k_list_current: (@list Z)) (key_addr: Z) (l_resres: (@list Z)) (p_current: Z) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (i: Z) (key: Z) (l_prev: (@list Z)) (buck: Z) (l0: (@list Z)) (ind: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list_current) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair (buck) (l0))))) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l_res = (cons (p_current) (l_resres))) |]
  &&  (store_string key k )
  **  (store_string key_addr k_list_current )
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "i" ) )) # Ptr  |-> i)
  **  ((i) # Ptr  |-> p_current)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (sllseg buck p_current l_prev )
  **  ((&((p_current)  # "blist" ->ₛ "key")) # Ptr  |-> key_addr)
  **  (sll p_current l_res )
  **  (store_map store_sll b0 )
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
  **  (store_map store_name m )
|--
  [| False |]
.

Definition hashtbl_findref_safety_wit_8 := 
forall (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (h_top: Z) (k_list_current: (@list Z)) (key_addr: Z) (l_resres: (@list Z)) (p_current: Z) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (i: Z) (key: Z) (l_prev: (@list Z)) (buck: Z) (l0: (@list Z)) (ind: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) ,
  [| (p_current = 0) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair (buck) (l0))))) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l_res = (cons (p_current) (l_resres))) |]
  &&  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "i" ) )) # Ptr  |-> i)
  **  ((i) # Ptr  |-> p_current)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (sllseg buck p_current l_prev )
  **  ((&((p_current)  # "blist" ->ₛ "key")) # Ptr  |-> key_addr)
  **  (store_string key_addr k_list_current )
  **  (sll p_current l_res )
  **  (store_map store_sll b0 )
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
  **  (store_string key k )
  **  (store_map store_name m )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_findref_safety_wit_9 := 
forall (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (h_bucks: Z) (h_top: Z) (h: Z) (l_res: (@list Z)) (i_v: Z) (i: Z) (key: Z) (l_prev: (@list Z)) (buck: Z) (l0: (@list Z)) (ind: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) ,
  [| (i_v = 0) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair (buck) (l0))))) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (i_v = 0) |] 
  &&  [| (l_res = nil) |]
  &&  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "i" ) )) # Ptr  |-> i)
  **  ((i) # Ptr  |-> i_v)
  **  (store_map store_sll b0 )
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
  **  (store_string key k )
  **  (store_map store_name m )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_findref_entail_wit_1 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (h_bucks: Z) (h_top_3: Z) (lh_2: (@list Z)) (b0_2: (Z -> (@option (Z * (@list Z))))) (l_2: (@list Z)) (retval: Z) ,
  [| (retval = (hash_string_coq (k))) |] 
  &&  [| (contain_all_addrs m l_2 ) |] 
  &&  [| (repr_all_heads lh_2 b0_2 ) |] 
  &&  [| (contain_all_correct_addrs m b0_2 ) |]
  &&  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top_3)
  **  (dll h_top_3 0 l_2 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (PtrArray.full h_bucks 211 lh_2 )
  **  (store_map store_sll b0_2 )
  **  (store_map store_name m )
|--
  (EX (h_top: Z)  (k_list_current: (@list Z))  (key_addr: Z)  (l_resres: (@list Z))  (p_current: Z)  (l_res: (@list Z))  (h_bucks_2: Z)  (l_prev: (@list Z))  (buck: Z)  (l0: (@list Z))  (lh: (@list Z))  (b0: (Z -> (@option (Z * (@list Z)))))  (l: (@list Z)) ,
  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= (retval % ( 211 ) )) |] 
  &&  [| ((retval % ( 211 ) ) < 211) |] 
  &&  [| ((b0 ((retval % ( 211 ) ))) = (Some ((pair (buck) (l0))))) |] 
  &&  [| (not_key key_pre l_prev ) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l_res = (cons (p_current) (l_resres))) |]
  &&  (((h_bucks + ((retval % ( 211 ) ) * sizeof(PTR) ) )) # Ptr  |-> p_current)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks_2)
  **  (((h_bucks_2 + ((retval % ( 211 ) ) * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (sllseg buck p_current l_prev )
  **  ((&((p_current)  # "blist" ->ₛ "key")) # Ptr  |-> key_addr)
  **  (store_string key_addr k_list_current )
  **  (sll p_current l_res )
  **  (store_map store_sll b0 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
  **  (PtrArray.missing_i h_bucks_2 (retval % ( 211 ) ) 0 211 lh )
  **  (store_string key_pre k )
  **  (store_map store_name m ))
  ||
  (EX (h_bucks_3: Z)  (h_top_2: Z)  (l_res: (@list Z))  (i_v: Z)  (l_prev: (@list Z))  (buck: Z)  (l0: (@list Z))  (lh: (@list Z))  (b0: (Z -> (@option (Z * (@list Z)))))  (l: (@list Z)) ,
  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= (retval % ( 211 ) )) |] 
  &&  [| ((retval % ( 211 ) ) < 211) |] 
  &&  [| ((b0 ((retval % ( 211 ) ))) = (Some ((pair (buck) (l0))))) |] 
  &&  [| (not_key key_pre l_prev ) |] 
  &&  [| (i_v = 0) |] 
  &&  [| (l_res = nil) |]
  &&  (((h_bucks + ((retval % ( 211 ) ) * sizeof(PTR) ) )) # Ptr  |-> i_v)
  **  (store_map store_sll b0 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top_2)
  **  (dll h_top_2 0 l )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks_3)
  **  (PtrArray.missing_i h_bucks_3 (retval % ( 211 ) ) 0 211 lh )
  **  (store_string key_pre k )
  **  (store_map store_name m ))
.

Definition hashtbl_findref_entail_wit_2_1 := 
forall (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (h_top: Z) (k_list_current: (@list Z)) (key_addr: Z) (l_resres: (@list Z)) (p_current: Z) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (i: Z) (key: Z) (l_prev: (@list Z)) (buck: Z) (l0: (@list Z)) (ind: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list_current) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair (buck) (l0))))) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l_res = (cons (p_current) (l_resres))) |]
  &&  (store_string key k )
  **  (store_string key_addr k_list_current )
  **  ((i) # Ptr  |-> p_current)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (sllseg buck p_current l_prev )
  **  ((&((p_current)  # "blist" ->ₛ "key")) # Ptr  |-> key_addr)
  **  (sll p_current l_res )
  **  (store_map store_sll b0 )
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
  **  (store_map store_name m )
|--
  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list_current) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair (buck) (l0))))) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l_res = (cons (p_current) (l_resres))) |]
  &&  (store_string key k )
  **  (store_string key_addr k_list_current )
  **  ((i) # Ptr  |-> p_current)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (sllseg buck p_current l_prev )
  **  ((&((p_current)  # "blist" ->ₛ "key")) # Ptr  |-> key_addr)
  **  (sll p_current l_res )
  **  (store_map store_sll b0 )
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
  **  (store_map store_name m )
.

Definition hashtbl_findref_entail_wit_2_2 := 
forall (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (h_top: Z) (k_list_current: (@list Z)) (key_addr: Z) (l_resres: (@list Z)) (p_current: Z) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (i: Z) (key: Z) (l_prev: (@list Z)) (buck: Z) (l0: (@list Z)) (ind: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (k <> k_list_current) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair (buck) (l0))))) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l_res = (cons (p_current) (l_resres))) |]
  &&  ((i) # Ptr  |-> p_current)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (sllseg buck p_current l_prev )
  **  ((&((p_current)  # "blist" ->ₛ "key")) # Ptr  |-> key_addr)
  **  (sll p_current l_res )
  **  (store_map store_sll b0 )
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
  **  (store_map store_name m )
|--
  EX (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list_current) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair (buck) (l0))))) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l_res = (cons (p_current) (l_resres))) |]
  &&  (store_string key k )
  **  (store_string key_addr k_list_current )
  **  ((i) # Ptr  |-> p_current)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (sllseg buck p_current l_prev )
  **  ((&((p_current)  # "blist" ->ₛ "key")) # Ptr  |-> key_addr)
  **  (sll p_current l_res )
  **  (store_map store_sll b0 )
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
  **  (store_map store_name m )
.

Definition hashtbl_findref_entail_wit_3_1 := 
forall (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (h_top: Z) (k_list_current: (@list Z)) (key_addr: Z) (l_resres: (@list Z)) (p_current: Z) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (i: Z) (key: Z) (l_prev: (@list Z)) (buck: Z) (l0: (@list Z)) (ind: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (retval_2: Z) ,
  [| (retval_2 = 0) |] 
  &&  [| (retval_2 = 1) |] 
  &&  [| (k = k_list_current) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair (buck) (l0))))) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l_res = (cons (p_current) (l_resres))) |]
  &&  (store_string key k )
  **  (store_string key_addr k_list_current )
  **  ((i) # Ptr  |-> p_current)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (sllseg buck p_current l_prev )
  **  ((&((p_current)  # "blist" ->ₛ "key")) # Ptr  |-> key_addr)
  **  (sll p_current l_res )
  **  (store_map store_sll b0 )
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
  **  (store_map store_name m )
|--
  EX (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (k <> k_list_current) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair (buck) (l0))))) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l_res = (cons (p_current) (l_resres))) |]
  &&  ((i) # Ptr  |-> p_current)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (sllseg buck p_current l_prev )
  **  ((&((p_current)  # "blist" ->ₛ "key")) # Ptr  |-> key_addr)
  **  (sll p_current l_res )
  **  (store_map store_sll b0 )
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
  **  (store_map store_name m )
.

Definition hashtbl_findref_entail_wit_3_2 := 
forall (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (h_top: Z) (k_list_current: (@list Z)) (key_addr: Z) (l_resres: (@list Z)) (p_current: Z) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (i: Z) (key: Z) (l_prev: (@list Z)) (buck: Z) (l0: (@list Z)) (ind: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (k <> k_list_current) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair (buck) (l0))))) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l_res = (cons (p_current) (l_resres))) |]
  &&  ((i) # Ptr  |-> p_current)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (sllseg buck p_current l_prev )
  **  ((&((p_current)  # "blist" ->ₛ "key")) # Ptr  |-> key_addr)
  **  (sll p_current l_res )
  **  (store_map store_sll b0 )
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
  **  (store_map store_name m )
|--
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (k <> k_list_current) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair (buck) (l0))))) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l_res = (cons (p_current) (l_resres))) |]
  &&  ((i) # Ptr  |-> p_current)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (sllseg buck p_current l_prev )
  **  ((&((p_current)  # "blist" ->ₛ "key")) # Ptr  |-> key_addr)
  **  (sll p_current l_res )
  **  (store_map store_sll b0 )
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
  **  (store_map store_name m )
.

Definition hashtbl_findref_entail_wit_4 := 
forall (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (h_top_3: Z) (k_list_current_2: (@list Z)) (key_addr_2: Z) (l_resres_2: (@list Z)) (p_current_2: Z) (l_res_2: (@list Z)) (h_bucks_3: Z) (h: Z) (i: Z) (key: Z) (l_prev_2: (@list Z)) (buck_2: Z) (l0_2: (@list Z)) (ind: Z) (lh_2: (@list Z)) (b0_2: (Z -> (@option (Z * (@list Z))))) (l_2: (@list Z)) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (k <> k_list_current_2) |] 
  &&  [| (p_current_2 <> 0) |] 
  &&  [| (contain_all_addrs m l_2 ) |] 
  &&  [| (repr_all_heads lh_2 b0_2 ) |] 
  &&  [| (contain_all_correct_addrs m b0_2 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0_2 (ind)) = (Some ((pair (buck_2) (l0_2))))) |] 
  &&  [| (not_key key l_prev_2 ) |] 
  &&  [| (p_current_2 <> 0) |] 
  &&  [| (l0_2 = (app (l_prev_2) (l_res_2))) |] 
  &&  [| (l_res_2 = (cons (p_current_2) (l_resres_2))) |]
  &&  ((i) # Ptr  |-> p_current_2)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks_3)
  **  (((h_bucks_3 + (ind * sizeof(PTR) ) )) # Ptr  |-> buck_2)
  **  (sllseg buck_2 p_current_2 l_prev_2 )
  **  ((&((p_current_2)  # "blist" ->ₛ "key")) # Ptr  |-> key_addr_2)
  **  (sll p_current_2 l_res_2 )
  **  (store_map store_sll b0_2 )
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top_3)
  **  (dll h_top_3 0 l_2 )
  **  (PtrArray.missing_i h_bucks_3 ind 0 211 lh_2 )
  **  (store_map store_name m )
|--
  (EX (h_top: Z)  (k_list_current: (@list Z))  (key_addr: Z)  (l_resres: (@list Z))  (p_current: Z)  (l_res: (@list Z))  (h_bucks: Z)  (l_prev: (@list Z))  (buck: Z)  (l0: (@list Z))  (lh: (@list Z))  (b0: (Z -> (@option (Z * (@list Z)))))  (l: (@list Z)) ,
  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair (buck) (l0))))) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l_res = (cons (p_current) (l_resres))) |]
  &&  ((&((p_current_2)  # "blist" ->ₛ "next")) # Ptr  |-> p_current)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (sllseg buck p_current l_prev )
  **  ((&((p_current)  # "blist" ->ₛ "key")) # Ptr  |-> key_addr)
  **  (store_string key_addr k_list_current )
  **  (sll p_current l_res )
  **  (store_map store_sll b0 )
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
  **  (store_string key k )
  **  (store_map store_name m ))
  ||
  (EX (h_bucks_2: Z)  (h_top_2: Z)  (l_res: (@list Z))  (i_v: Z)  (l_prev: (@list Z))  (buck: Z)  (l0: (@list Z))  (lh: (@list Z))  (b0: (Z -> (@option (Z * (@list Z)))))  (l: (@list Z)) ,
  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair (buck) (l0))))) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (i_v = 0) |] 
  &&  [| (l_res = nil) |]
  &&  ((&((p_current_2)  # "blist" ->ₛ "next")) # Ptr  |-> i_v)
  **  (store_map store_sll b0 )
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top_2)
  **  (dll h_top_2 0 l )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks_2)
  **  (PtrArray.missing_i h_bucks_2 ind 0 211 lh )
  **  (store_string key k )
  **  (store_map store_name m ))
.

Definition hashtbl_findref_return_wit_1 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (h_top: Z) (k_list_current: (@list Z)) (key_addr: Z) (l_resres: (@list Z)) (p_current: Z) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (i: Z) (key: Z) (l_prev: (@list Z)) (buck: Z) (l0: (@list Z)) (ind: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (retval: Z) (x: Z) (l0_2: (@list Z)) (y: Z) ,
  [| (p_current = x) |] 
  &&  [| (l_res = (cons (x) (l0_2))) |] 
  &&  [| (p_current = x) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list_current) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair (buck) (l0))))) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l_res = (cons (p_current) (l_resres))) |]
  &&  ((&((p_current)  # "blist" ->ₛ "next")) # Ptr  |-> buck)
  **  (sll y l0_2 )
  **  (store_string key k )
  **  (store_string key_addr k_list_current )
  **  ((i) # Ptr  |-> y)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> p_current)
  **  (sllseg buck p_current l_prev )
  **  ((&((p_current)  # "blist" ->ₛ "key")) # Ptr  |-> key_addr)
  **  (store_map store_sll b0 )
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
  **  (store_map store_name m )
|--
  ([| ((m (k)) = None) |] 
  &&  [| (&((p_current)  # "blist" ->ₛ "val") = 0) |]
  &&  (store_hash_skeleton h_pre m )
  **  (store_string key_pre k ))
  ||
  (EX (p: Z) ,
  [| ((m (k)) = (Some (p))) |] 
  &&  [| (&((p_current)  # "blist" ->ₛ "val") = p) |]
  &&  (store_hash_skeleton h_pre m )
  **  (store_string key_pre k ))
.

Definition hashtbl_findref_return_wit_2 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (h_top: Z) (k_list_current: (@list Z)) (key_addr: Z) (l_resres: (@list Z)) (p_current: Z) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (i: Z) (key: Z) (l_prev: (@list Z)) (buck: Z) (l0: (@list Z)) (ind: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) ,
  [| (p_current = 0) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair (buck) (l0))))) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l_res = (cons (p_current) (l_resres))) |]
  &&  ((i) # Ptr  |-> p_current)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (sllseg buck p_current l_prev )
  **  ((&((p_current)  # "blist" ->ₛ "key")) # Ptr  |-> key_addr)
  **  (store_string key_addr k_list_current )
  **  (sll p_current l_res )
  **  (store_map store_sll b0 )
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
  **  (store_string key k )
  **  (store_map store_name m )
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

Definition hashtbl_findref_return_wit_3 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (h_bucks: Z) (h_top: Z) (h: Z) (l_res: (@list Z)) (i_v: Z) (i: Z) (key: Z) (l_prev: (@list Z)) (buck: Z) (l0: (@list Z)) (ind: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) ,
  [| (i_v = 0) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair (buck) (l0))))) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (i_v = 0) |] 
  &&  [| (l_res = nil) |]
  &&  ((i) # Ptr  |-> i_v)
  **  (store_map store_sll b0 )
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
  **  (store_string key k )
  **  (store_map store_name m )
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
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (h_bucks: Z) (h_top: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) ,
  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |]
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (PtrArray.full h_bucks 211 lh )
  **  (store_map store_sll b0 )
  **  (store_map store_name m )
  **  (store_string key_pre k )
|--
  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |]
  &&  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (PtrArray.full h_bucks 211 lh )
  **  (store_map store_sll b0 )
  **  (store_map store_name m )
.

Definition hashtbl_findref_partial_solve_wit_3 := 
forall (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (h_top: Z) (k_list_current: (@list Z)) (key_addr: Z) (l_resres: (@list Z)) (p_current: Z) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (i: Z) (key: Z) (l_prev: (@list Z)) (buck: Z) (l0: (@list Z)) (ind: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) ,
  [| (p_current <> 0) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair (buck) (l0))))) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l_res = (cons (p_current) (l_resres))) |]
  &&  ((i) # Ptr  |-> p_current)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (sllseg buck p_current l_prev )
  **  ((&((p_current)  # "blist" ->ₛ "key")) # Ptr  |-> key_addr)
  **  (store_string key_addr k_list_current )
  **  (sll p_current l_res )
  **  (store_map store_sll b0 )
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
  **  (store_string key k )
  **  (store_map store_name m )
|--
  [| (p_current <> 0) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair (buck) (l0))))) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l_res = (cons (p_current) (l_resres))) |]
  &&  (store_string key k )
  **  (store_string key_addr k_list_current )
  **  ((i) # Ptr  |-> p_current)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (sllseg buck p_current l_prev )
  **  ((&((p_current)  # "blist" ->ₛ "key")) # Ptr  |-> key_addr)
  **  (sll p_current l_res )
  **  (store_map store_sll b0 )
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
  **  (store_map store_name m )
.

Definition hashtbl_findref_partial_solve_wit_4 := 
forall (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (h_top: Z) (k_list_current: (@list Z)) (key_addr: Z) (l_resres: (@list Z)) (p_current: Z) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (i: Z) (key: Z) (l_prev: (@list Z)) (buck: Z) (l0: (@list Z)) (ind: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list_current) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair (buck) (l0))))) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l_res = (cons (p_current) (l_resres))) |]
  &&  (store_string key k )
  **  (store_string key_addr k_list_current )
  **  ((i) # Ptr  |-> p_current)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (sllseg buck p_current l_prev )
  **  ((&((p_current)  # "blist" ->ₛ "key")) # Ptr  |-> key_addr)
  **  (sll p_current l_res )
  **  (store_map store_sll b0 )
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
  **  (store_map store_name m )
|--
  EX (y: Z)  (l0_2: (@list Z))  (x: Z) ,
  [| (p_current = x) |] 
  &&  [| (l_res = (cons (x) (l0_2))) |] 
  &&  [| (p_current = x) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list_current) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair (buck) (l0))))) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l_res = (cons (p_current) (l_resres))) |]
  &&  ((&((p_current)  # "blist" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y l0_2 )
  **  (store_string key k )
  **  (store_string key_addr k_list_current )
  **  ((i) # Ptr  |-> p_current)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (sllseg buck p_current l_prev )
  **  ((&((p_current)  # "blist" ->ₛ "key")) # Ptr  |-> key_addr)
  **  (store_map store_sll b0 )
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
  **  (store_map store_name m )
.

Definition hashtbl_findref_which_implies_wit_1 := 
forall (m: ((@list Z) -> (@option Z))) (h: Z) ,
  (store_hash_skeleton h m )
|--
  EX (h_bucks: Z)  (h_top: Z)  (lh: (@list Z))  (b0: (Z -> (@option (Z * (@list Z)))))  (l: (@list Z)) ,
  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |]
  &&  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (PtrArray.full h_bucks 211 lh )
  **  (store_map store_sll b0 )
  **  (store_map store_name m )
.

(*----- Function hashtbl_remove -----*)

Definition hashtbl_remove_safety_wit_1 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (h_bucks: Z) (h_top: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (retval: Z) ,
  [| (retval = (hash_string_coq (k))) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| (map_composable m1 m2 ) |]
  &&  (store_string key_pre k )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
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
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (h_bucks: Z) (h_top: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (retval: Z) ,
  [| (retval = (hash_string_coq (k))) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| (map_composable m1 m2 ) |]
  &&  (store_string key_pre k )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
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
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (k0: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) ,
  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  (sll it_v l_res )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  (store_string k0 k_list )
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  (store_string key k )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_remove_safety_wit_4 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (k0: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (k <> k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  ((( &( "b" ) )) # Ptr  |-> it_v)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  (sll it_v l_res )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
|--
  [| False |]
.

Definition hashtbl_remove_safety_wit_5 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (k0: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  (store_string key k )
  **  (store_string k0 k_list )
  **  ((( &( "b" ) )) # Ptr  |-> it_v)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  (sll it_v l_res )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
|--
  [| False |]
.

Definition hashtbl_remove_safety_wit_6 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (k0: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  (store_string key k )
  **  (store_string k0 k_list )
  **  ((( &( "b" ) )) # Ptr  |-> it_v)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  (sll it_v l_res )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_remove_safety_wit_7 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (k0: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  (store_string key k )
  **  (store_string k0 k_list )
  **  ((( &( "b" ) )) # Ptr  |-> it_v)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  (sll it_v l_res )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_remove_safety_wit_8 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (k0: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (it_v_up <> 0) |] 
  &&  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  (store_string key k )
  **  (store_string k0 k_list )
  **  ((( &( "b" ) )) # Ptr  |-> it_v)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  (sll it_v l_res )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_remove_safety_wit_9 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (k0: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (it_v_up <> 0) |] 
  &&  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  (store_string key k )
  **  (store_string k0 k_list )
  **  ((( &( "b" ) )) # Ptr  |-> it_v)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  (sll it_v l_res )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_remove_safety_wit_10 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (k0: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (it_v_up = 0) |] 
  &&  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  (store_string key k )
  **  (store_string k0 k_list )
  **  ((( &( "b" ) )) # Ptr  |-> it_v)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  (sll it_v l_res )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_remove_safety_wit_11 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (k0: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (it_v_up = 0) |] 
  &&  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  (store_string key k )
  **  (store_string k0 k_list )
  **  ((( &( "b" ) )) # Ptr  |-> it_v)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  (sll it_v l_res )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_remove_safety_wit_12 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) (z: Z) (l0_2: (@list Z)) (x: Z) (l0_3: (@list Z)) (y: Z) ,
  [| (map_composable m1 m2 ) |] 
  &&  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_3))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (dl_up = (cons (h_top) (l0_2))) |] 
  &&  [| (it_v_down <> 0) |] 
  &&  [| (it_v_up = 0) |] 
  &&  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  (store_map store_name (KP.remove_map (m1) (k_list)) )
  **  (store_map store_uint (PV.remove_map (m2) (it_v)) )
  **  ((( &( "res" ) )) # UInt  |-> val)
  **  (sll y l0_3 )
  **  (dllseg z it_v h_top it_v_up l0_2 )
  **  ((&((h_top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((&((h_top)  # "blist" ->ₛ "down")) # Ptr  |-> z)
  **  (store_string key k )
  **  ((( &( "b" ) )) # Ptr  |-> it_v)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> y)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition hashtbl_remove_safety_wit_13 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) (x: Z) (l0_2: (@list Z)) (y: Z) ,
  [| (map_composable m1 m2 ) |] 
  &&  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_2))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (it_v_down <> 0) |] 
  &&  [| (it_v_up = 0) |] 
  &&  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  (store_map store_name (KP.remove_map (m1) (k_list)) )
  **  (store_map store_uint (PV.remove_map (m2) (it_v)) )
  **  ((( &( "res" ) )) # UInt  |-> val)
  **  (sll y l0_2 )
  **  (store_string key k )
  **  ((( &( "b" ) )) # Ptr  |-> it_v)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> y)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition hashtbl_remove_safety_wit_14 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) (x: Z) (l0_2: (@list Z)) (y: Z) ,
  [| (map_composable m1 m2 ) |] 
  &&  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_2))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (it_v_down <> 0) |] 
  &&  [| (it_v_up <> 0) |] 
  &&  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  (store_map store_name (KP.remove_map (m1) (k_list)) )
  **  (store_map store_uint (PV.remove_map (m2) (it_v)) )
  **  ((( &( "res" ) )) # UInt  |-> val)
  **  (sll y l0_2 )
  **  (store_string key k )
  **  ((( &( "b" ) )) # Ptr  |-> it_v)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> y)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition hashtbl_remove_safety_wit_15 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) (z: Z) (l0_2: (@list Z)) (x: Z) (l0_3: (@list Z)) (y: Z) ,
  [| (map_composable m1 m2 ) |] 
  &&  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_3))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (dl_up = (cons (h_top) (l0_2))) |] 
  &&  [| (it_v_down <> 0) |] 
  &&  [| (it_v_up <> 0) |] 
  &&  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  (store_map store_name (KP.remove_map (m1) (k_list)) )
  **  (store_map store_uint (PV.remove_map (m2) (it_v)) )
  **  ((( &( "res" ) )) # UInt  |-> val)
  **  (sll y l0_3 )
  **  (dllseg z it_v h_top it_v_up l0_2 )
  **  ((&((h_top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((&((h_top)  # "blist" ->ₛ "down")) # Ptr  |-> z)
  **  (store_string key k )
  **  ((( &( "b" ) )) # Ptr  |-> it_v)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> y)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition hashtbl_remove_safety_wit_16 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) (z: Z) (l0_2: (@list Z)) (x: Z) (l0_3: (@list Z)) (y: Z) ,
  [| (map_composable m1 m2 ) |] 
  &&  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_3))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (dl_up = (cons (h_top) (l0_2))) |] 
  &&  [| (it_v_down = 0) |] 
  &&  [| (it_v_up <> 0) |] 
  &&  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  (store_map store_name (KP.remove_map (m1) (k_list)) )
  **  (store_map store_uint (PV.remove_map (m2) (it_v)) )
  **  ((( &( "res" ) )) # UInt  |-> val)
  **  (sll y l0_3 )
  **  (dllseg z it_v h_top it_v_up l0_2 )
  **  ((&((h_top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((&((h_top)  # "blist" ->ₛ "down")) # Ptr  |-> z)
  **  (store_string key k )
  **  ((( &( "b" ) )) # Ptr  |-> it_v)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> y)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition hashtbl_remove_safety_wit_17 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) (x: Z) (l0_2: (@list Z)) (y: Z) ,
  [| (map_composable m1 m2 ) |] 
  &&  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_2))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (it_v_down = 0) |] 
  &&  [| (it_v_up <> 0) |] 
  &&  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  (store_map store_name (KP.remove_map (m1) (k_list)) )
  **  (store_map store_uint (PV.remove_map (m2) (it_v)) )
  **  ((( &( "res" ) )) # UInt  |-> val)
  **  (sll y l0_2 )
  **  (store_string key k )
  **  ((( &( "b" ) )) # Ptr  |-> it_v)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> y)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition hashtbl_remove_safety_wit_18 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) (x: Z) (l0_2: (@list Z)) (y: Z) ,
  [| (map_composable m1 m2 ) |] 
  &&  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_2))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (it_v_down = 0) |] 
  &&  [| (it_v_up = 0) |] 
  &&  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  (store_map store_name (KP.remove_map (m1) (k_list)) )
  **  (store_map store_uint (PV.remove_map (m2) (it_v)) )
  **  ((( &( "res" ) )) # UInt  |-> val)
  **  (sll y l0_2 )
  **  (store_string key k )
  **  ((( &( "b" ) )) # Ptr  |-> it_v)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> y)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition hashtbl_remove_safety_wit_19 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) (z: Z) (l0_2: (@list Z)) (x: Z) (l0_3: (@list Z)) (y: Z) ,
  [| (map_composable m1 m2 ) |] 
  &&  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_3))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (dl_up = (cons (h_top) (l0_2))) |] 
  &&  [| (it_v_down = 0) |] 
  &&  [| (it_v_up = 0) |] 
  &&  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  (store_map store_name (KP.remove_map (m1) (k_list)) )
  **  (store_map store_uint (PV.remove_map (m2) (it_v)) )
  **  ((( &( "res" ) )) # UInt  |-> val)
  **  (sll y l0_3 )
  **  (dllseg z it_v h_top it_v_up l0_2 )
  **  ((&((h_top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((&((h_top)  # "blist" ->ₛ "down")) # Ptr  |-> z)
  **  (store_string key k )
  **  ((( &( "b" ) )) # Ptr  |-> it_v)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> y)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition hashtbl_remove_safety_wit_20 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (k0: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) ,
  [| (it_v = 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  (sll it_v l_res )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  (store_string k0 k_list )
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  (store_string key k )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_remove_safety_wit_21 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (k0: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) ,
  [| (it_v = 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  (sll it_v l_res )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  (store_string k0 k_list )
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |-> 0)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  (store_string key k )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_remove_entail_wit_1 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (h_bucks: Z) (h_top_2: Z) (lh_2: (@list Z)) (b_2: (Z -> (@option (Z * (@list Z))))) (l_2: (@list Z)) (retval: Z) ,
  [| (retval = (hash_string_coq (k))) |] 
  &&  [| (contain_all_addrs m1 l_2 ) |] 
  &&  [| (repr_all_heads lh_2 b_2 ) |] 
  &&  [| (contain_all_correct_addrs m1 b_2 ) |] 
  &&  [| (map_composable m1 m2 ) |]
  &&  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top_2)
  **  (dll h_top_2 0 l_2 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (PtrArray.full h_bucks 211 lh_2 )
  **  (store_map store_sll b_2 )
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  ((removed_pre) # Int  |->_)
|--
  EX (k0: Z)  (val: Z)  (it_v_down_up: Z)  (it_v_down: Z)  (it_v_up_down: Z)  (h_top: Z)  (it_v_up: Z)  (buck: Z)  (it_v: Z)  (k_list: (@list Z))  (dl_up: (@list Z))  (dl_down: (@list Z))  (l_res: (@list Z))  (h_bucks_2: Z)  (l0: (@list Z))  (lh: (@list Z))  (b: (Z -> (@option (Z * (@list Z)))))  (l: (@list Z))  (l_prev: (@list Z)) ,
  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key_pre l_prev ) |] 
  &&  [| (0 <= (retval % ( 211 ) )) |] 
  &&  [| ((retval % ( 211 ) ) < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b ((retval % ( 211 ) ))) = (Some ((pair ((h_bucks_2 + ((retval % ( 211 ) ) * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks_2)
  **  (((h_bucks + ((retval % ( 211 ) ) * sizeof(PTR) ) )) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  (sll it_v l_res )
  **  (((h_bucks_2 + ((retval % ( 211 ) ) * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  (store_string k0 k_list )
  **  ((removed_pre) # Int  |->_)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  (store_string key_pre k )
.

Definition hashtbl_remove_entail_wit_2_1 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (k0: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  (store_string key k )
  **  (store_string k0 k_list )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  (sll it_v l_res )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
|--
  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  (store_string key k )
  **  (store_string k0 k_list )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  (sll it_v l_res )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
.

Definition hashtbl_remove_entail_wit_2_2 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (k0: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (k <> k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  (sll it_v l_res )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
|--
  EX (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  (store_string key k )
  **  (store_string k0 k_list )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  (sll it_v l_res )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
.

Definition hashtbl_remove_entail_wit_3_1 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (k0: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval_2: Z) ,
  [| (retval_2 = 0) |] 
  &&  [| (retval_2 = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  (store_string key k )
  **  (store_string k0 k_list )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  (sll it_v l_res )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
|--
  EX (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (k <> k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  (sll it_v l_res )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
.

Definition hashtbl_remove_entail_wit_3_2 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (k0: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (k <> k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  (sll it_v l_res )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
|--
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (k <> k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  (sll it_v l_res )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
.

Definition hashtbl_remove_entail_wit_4 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (k0_2: Z) (val_2: Z) (it_v_down_up_2: Z) (it_v_down_2: Z) (it_v_up_down_2: Z) (h_top_2: Z) (it_v_up_2: Z) (buck_2: Z) (it_v_2: Z) (it: Z) (k_list_2: (@list Z)) (dl_up_2: (@list Z)) (dl_down_2: (@list Z)) (l_res_2: (@list Z)) (h_bucks_2: Z) (h: Z) (l0_2: (@list Z)) (lh_2: (@list Z)) (b_2: (Z -> (@option (Z * (@list Z))))) (l_2: (@list Z)) (ind: Z) (key: Z) (l_prev_2: (@list Z)) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (k <> k_list_2) |] 
  &&  [| (it_v_2 <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev_2 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l_2 ) |] 
  &&  [| (repr_all_heads lh_2 b_2 ) |] 
  &&  [| (contain_all_correct_addrs m1 b_2 ) |] 
  &&  [| ((b_2 (ind)) = (Some ((pair ((h_bucks_2 + (ind * sizeof(PTR) ) )) (l0_2))))) |] 
  &&  [| (l0_2 = (app (l_prev_2) (l_res_2))) |] 
  &&  [| (l_2 = (app (dl_up_2) (dl_down_2))) |] 
  &&  [| ((m1 (k_list_2)) = (Some (&((it_v_2)  # "blist" ->ₛ "val")))) |]
  &&  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks_2)
  **  ((it) # Ptr  |-> it_v_2)
  **  (sllseg buck_2 it_v_2 l_prev_2 )
  **  (sll it_v_2 l_res_2 )
  **  (((h_bucks_2 + (ind * sizeof(PTR) ) )) # Ptr  |-> buck_2)
  **  ((&((it_v_2)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up_2)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top_2)
  **  (dllseg h_top_2 it_v_2 0 it_v_up_2 dl_up_2 )
  **  (dll it_v_2 it_v_up_2 dl_down_2 )
  **  ((&((it_v_up_2)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down_2)
  **  ((it_v_up_down_2) # Ptr  |-> it_v_2)
  **  ((&((it_v_2)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down_2)
  **  ((&((it_v_down_2)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up_2)
  **  ((it_v_down_up_2) # Ptr  |-> it_v_2)
  **  ((&((it_v_2)  # "blist" ->ₛ "val")) # UInt  |-> val_2)
  **  ((&((it_v_2)  # "blist" ->ₛ "key")) # Ptr  |-> k0_2)
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
|--
  EX (k0: Z)  (val: Z)  (it_v_down_up: Z)  (it_v_down: Z)  (it_v_up_down: Z)  (h_top: Z)  (it_v_up: Z)  (buck: Z)  (it_v: Z)  (k_list: (@list Z))  (dl_up: (@list Z))  (dl_down: (@list Z))  (l_res: (@list Z))  (h_bucks: Z)  (l0: (@list Z))  (lh: (@list Z))  (b: (Z -> (@option (Z * (@list Z)))))  (l: (@list Z))  (l_prev: (@list Z)) ,
  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((&((it_v_2)  # "blist" ->ₛ "next")) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  (sll it_v l_res )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  (store_string k0 k_list )
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  (store_string key k )
.

Definition hashtbl_remove_return_wit_1 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) (z: Z) (l0_2: (@list Z)) (x: Z) (l0_3: (@list Z)) (y: Z) ,
  [| (map_composable m1 m2 ) |] 
  &&  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_3))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (dl_up = (cons (h_top) (l0_2))) |] 
  &&  [| (it_v_down = 0) |] 
  &&  [| (it_v_up = 0) |] 
  &&  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  (store_map store_name (KP.remove_map (m1) (k_list)) )
  **  (store_map store_uint (PV.remove_map (m2) (it_v)) )
  **  (sll y l0_3 )
  **  (dllseg z it_v h_top it_v_up l0_2 )
  **  ((&((h_top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((&((h_top)  # "blist" ->ₛ "down")) # Ptr  |-> z)
  **  (store_string key k )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> y)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
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
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) (x: Z) (l0_2: (@list Z)) (y: Z) ,
  [| (map_composable m1 m2 ) |] 
  &&  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_2))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (it_v_down = 0) |] 
  &&  [| (it_v_up = 0) |] 
  &&  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  (store_map store_name (KP.remove_map (m1) (k_list)) )
  **  (store_map store_uint (PV.remove_map (m2) (it_v)) )
  **  (sll y l0_2 )
  **  (store_string key k )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> y)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
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
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) (x: Z) (l0_2: (@list Z)) (y: Z) ,
  [| (map_composable m1 m2 ) |] 
  &&  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_2))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (it_v_down = 0) |] 
  &&  [| (it_v_up <> 0) |] 
  &&  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  (store_map store_name (KP.remove_map (m1) (k_list)) )
  **  (store_map store_uint (PV.remove_map (m2) (it_v)) )
  **  (sll y l0_2 )
  **  (store_string key k )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> y)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
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
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) (z: Z) (l0_2: (@list Z)) (x: Z) (l0_3: (@list Z)) (y: Z) ,
  [| (map_composable m1 m2 ) |] 
  &&  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_3))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (dl_up = (cons (h_top) (l0_2))) |] 
  &&  [| (it_v_down = 0) |] 
  &&  [| (it_v_up <> 0) |] 
  &&  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  (store_map store_name (KP.remove_map (m1) (k_list)) )
  **  (store_map store_uint (PV.remove_map (m2) (it_v)) )
  **  (sll y l0_3 )
  **  (dllseg z it_v h_top it_v_up l0_2 )
  **  ((&((h_top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((&((h_top)  # "blist" ->ₛ "down")) # Ptr  |-> z)
  **  (store_string key k )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> y)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
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
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) (z: Z) (l0_2: (@list Z)) (x: Z) (l0_3: (@list Z)) (y: Z) ,
  [| (map_composable m1 m2 ) |] 
  &&  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_3))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (dl_up = (cons (h_top) (l0_2))) |] 
  &&  [| (it_v_down <> 0) |] 
  &&  [| (it_v_up <> 0) |] 
  &&  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  (store_map store_name (KP.remove_map (m1) (k_list)) )
  **  (store_map store_uint (PV.remove_map (m2) (it_v)) )
  **  (sll y l0_3 )
  **  (dllseg z it_v h_top it_v_up l0_2 )
  **  ((&((h_top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((&((h_top)  # "blist" ->ₛ "down")) # Ptr  |-> z)
  **  (store_string key k )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> y)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
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
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) (x: Z) (l0_2: (@list Z)) (y: Z) ,
  [| (map_composable m1 m2 ) |] 
  &&  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_2))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (it_v_down <> 0) |] 
  &&  [| (it_v_up <> 0) |] 
  &&  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  (store_map store_name (KP.remove_map (m1) (k_list)) )
  **  (store_map store_uint (PV.remove_map (m2) (it_v)) )
  **  (sll y l0_2 )
  **  (store_string key k )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> y)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
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
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) (x: Z) (l0_2: (@list Z)) (y: Z) ,
  [| (map_composable m1 m2 ) |] 
  &&  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_2))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (it_v_down <> 0) |] 
  &&  [| (it_v_up = 0) |] 
  &&  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  (store_map store_name (KP.remove_map (m1) (k_list)) )
  **  (store_map store_uint (PV.remove_map (m2) (it_v)) )
  **  (sll y l0_2 )
  **  (store_string key k )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> y)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
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
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) (z: Z) (l0_2: (@list Z)) (x: Z) (l0_3: (@list Z)) (y: Z) ,
  [| (map_composable m1 m2 ) |] 
  &&  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_3))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (dl_up = (cons (h_top) (l0_2))) |] 
  &&  [| (it_v_down <> 0) |] 
  &&  [| (it_v_up = 0) |] 
  &&  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  (store_map store_name (KP.remove_map (m1) (k_list)) )
  **  (store_map store_uint (PV.remove_map (m2) (it_v)) )
  **  (sll y l0_3 )
  **  (dllseg z it_v h_top it_v_up l0_2 )
  **  ((&((h_top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((&((h_top)  # "blist" ->ₛ "down")) # Ptr  |-> z)
  **  (store_string key k )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> y)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
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
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (k0: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) ,
  [| (it_v = 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  (sll it_v l_res )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  (store_string k0 k_list )
  **  ((removed) # Int  |-> 0)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  (store_string key k )
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
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (h_bucks: Z) (h_top: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) ,
  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| (map_composable m1 m2 ) |]
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
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
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (PtrArray.full h_bucks 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  ((removed_pre) # Int  |->_)
.

Definition hashtbl_remove_partial_solve_wit_3 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (k0: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) ,
  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  (sll it_v l_res )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  (store_string k0 k_list )
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  (store_string key k )
|--
  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  (store_string key k )
  **  (store_string k0 k_list )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  (sll it_v l_res )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
.

Definition hashtbl_remove_partial_solve_wit_4 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (k0: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (it_v_down <> 0) |] 
  &&  [| (it_v_up = 0) |] 
  &&  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  (store_string key k )
  **  (store_string k0 k_list )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  (sll it_v l_res )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
|--
  EX (y: Z)  (l0_3: (@list Z))  (x: Z)  (l0_2: (@list Z))  (z: Z) ,
  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_3))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (dl_up = (cons (h_top) (l0_2))) |] 
  &&  [| (it_v_down <> 0) |] 
  &&  [| (it_v_up = 0) |] 
  &&  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y l0_3 )
  **  (dllseg z it_v h_top it_v_up l0_2 )
  **  ((&((h_top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((&((h_top)  # "blist" ->ₛ "down")) # Ptr  |-> z)
  **  (store_string key k )
  **  (store_string k0 k_list )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
.

Definition hashtbl_remove_partial_solve_wit_5 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (k0: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (it_v_down <> 0) |] 
  &&  [| (it_v_up = 0) |] 
  &&  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  (store_string key k )
  **  (store_string k0 k_list )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  (sll it_v l_res )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
|--
  EX (y: Z)  (l0_2: (@list Z))  (x: Z) ,
  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_2))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (it_v_down <> 0) |] 
  &&  [| (it_v_up = 0) |] 
  &&  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y l0_2 )
  **  (store_string key k )
  **  (store_string k0 k_list )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
.

Definition hashtbl_remove_partial_solve_wit_6 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (k0: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (it_v_down <> 0) |] 
  &&  [| (it_v_up <> 0) |] 
  &&  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  (store_string key k )
  **  (store_string k0 k_list )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  (sll it_v l_res )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
|--
  EX (y: Z)  (l0_2: (@list Z))  (x: Z) ,
  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_2))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (it_v_down <> 0) |] 
  &&  [| (it_v_up <> 0) |] 
  &&  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y l0_2 )
  **  (store_string key k )
  **  (store_string k0 k_list )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
.

Definition hashtbl_remove_partial_solve_wit_7 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (k0: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (it_v_down <> 0) |] 
  &&  [| (it_v_up <> 0) |] 
  &&  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  (store_string key k )
  **  (store_string k0 k_list )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  (sll it_v l_res )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
|--
  EX (y: Z)  (l0_3: (@list Z))  (x: Z)  (l0_2: (@list Z))  (z: Z) ,
  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_3))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (dl_up = (cons (h_top) (l0_2))) |] 
  &&  [| (it_v_down <> 0) |] 
  &&  [| (it_v_up <> 0) |] 
  &&  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y l0_3 )
  **  (dllseg z it_v h_top it_v_up l0_2 )
  **  ((&((h_top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((&((h_top)  # "blist" ->ₛ "down")) # Ptr  |-> z)
  **  (store_string key k )
  **  (store_string k0 k_list )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
.

Definition hashtbl_remove_partial_solve_wit_8 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (k0: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (it_v_down = 0) |] 
  &&  [| (it_v_up <> 0) |] 
  &&  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  (store_string key k )
  **  (store_string k0 k_list )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  (sll it_v l_res )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
|--
  EX (y: Z)  (l0_3: (@list Z))  (x: Z)  (l0_2: (@list Z))  (z: Z) ,
  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_3))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (dl_up = (cons (h_top) (l0_2))) |] 
  &&  [| (it_v_down = 0) |] 
  &&  [| (it_v_up <> 0) |] 
  &&  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y l0_3 )
  **  (dllseg z it_v h_top it_v_up l0_2 )
  **  ((&((h_top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((&((h_top)  # "blist" ->ₛ "down")) # Ptr  |-> z)
  **  (store_string key k )
  **  (store_string k0 k_list )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
.

Definition hashtbl_remove_partial_solve_wit_9 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (k0: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (it_v_down = 0) |] 
  &&  [| (it_v_up <> 0) |] 
  &&  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  (store_string key k )
  **  (store_string k0 k_list )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  (sll it_v l_res )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
|--
  EX (y: Z)  (l0_2: (@list Z))  (x: Z) ,
  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_2))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (it_v_down = 0) |] 
  &&  [| (it_v_up <> 0) |] 
  &&  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y l0_2 )
  **  (store_string key k )
  **  (store_string k0 k_list )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
.

Definition hashtbl_remove_partial_solve_wit_10 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (k0: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (it_v_down = 0) |] 
  &&  [| (it_v_up = 0) |] 
  &&  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  (store_string key k )
  **  (store_string k0 k_list )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  (sll it_v l_res )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
|--
  EX (y: Z)  (l0_2: (@list Z))  (x: Z) ,
  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_2))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (it_v_down = 0) |] 
  &&  [| (it_v_up = 0) |] 
  &&  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y l0_2 )
  **  (store_string key k )
  **  (store_string k0 k_list )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
.

Definition hashtbl_remove_partial_solve_wit_11 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (k0: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) ,
  [| (it_v_down = 0) |] 
  &&  [| (it_v_up = 0) |] 
  &&  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  (store_string key k )
  **  (store_string k0 k_list )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  (sll it_v l_res )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
|--
  EX (y: Z)  (l0_3: (@list Z))  (x: Z)  (l0_2: (@list Z))  (z: Z) ,
  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_3))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (dl_up = (cons (h_top) (l0_2))) |] 
  &&  [| (it_v_down = 0) |] 
  &&  [| (it_v_up = 0) |] 
  &&  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y l0_3 )
  **  (dllseg z it_v h_top it_v_up l0_2 )
  **  ((&((h_top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((&((h_top)  # "blist" ->ₛ "down")) # Ptr  |-> z)
  **  (store_string key k )
  **  (store_string k0 k_list )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> it_v)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
.

Definition hashtbl_remove_partial_solve_wit_12_pure := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (k0: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) (z: Z) (l0_2: (@list Z)) (x: Z) (l0_3: (@list Z)) (y: Z) ,
  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_3))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (dl_up = (cons (h_top) (l0_2))) |] 
  &&  [| (it_v_down <> 0) |] 
  &&  [| (it_v_up = 0) |] 
  &&  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  ((( &( "res" ) )) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y l0_3 )
  **  (dllseg z it_v h_top it_v_up l0_2 )
  **  ((&((h_top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((&((h_top)  # "blist" ->ₛ "down")) # Ptr  |-> z)
  **  (store_string key k )
  **  (store_string k0 k_list )
  **  ((( &( "b" ) )) # Ptr  |-> it_v)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> y)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
|--
  [| (map_composable m1 m2 ) |]
.

Definition hashtbl_remove_partial_solve_wit_12_aux := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (k0: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) (z: Z) (l0_2: (@list Z)) (x: Z) (l0_3: (@list Z)) (y: Z) ,
  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_3))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (dl_up = (cons (h_top) (l0_2))) |] 
  &&  [| (it_v_down <> 0) |] 
  &&  [| (it_v_up = 0) |] 
  &&  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y l0_3 )
  **  (dllseg z it_v h_top it_v_up l0_2 )
  **  ((&((h_top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((&((h_top)  # "blist" ->ₛ "down")) # Ptr  |-> z)
  **  (store_string key k )
  **  (store_string k0 k_list )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> y)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
|--
  [| (map_composable m1 m2 ) |] 
  &&  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_3))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (dl_up = (cons (h_top) (l0_2))) |] 
  &&  [| (it_v_down <> 0) |] 
  &&  [| (it_v_up = 0) |] 
  &&  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  (store_string k0 k_list )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y l0_3 )
  **  (dllseg z it_v h_top it_v_up l0_2 )
  **  ((&((h_top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((&((h_top)  # "blist" ->ₛ "down")) # Ptr  |-> z)
  **  (store_string key k )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> y)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((removed) # Int  |->_)
.

Definition hashtbl_remove_partial_solve_wit_12 := hashtbl_remove_partial_solve_wit_12_pure -> hashtbl_remove_partial_solve_wit_12_aux.

Definition hashtbl_remove_partial_solve_wit_13_pure := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (k0: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) (x: Z) (l0_2: (@list Z)) (y: Z) ,
  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_2))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (it_v_down <> 0) |] 
  &&  [| (it_v_up = 0) |] 
  &&  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  ((( &( "res" ) )) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y l0_2 )
  **  (store_string key k )
  **  (store_string k0 k_list )
  **  ((( &( "b" ) )) # Ptr  |-> it_v)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> y)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
|--
  [| (map_composable m1 m2 ) |]
.

Definition hashtbl_remove_partial_solve_wit_13_aux := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (k0: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) (x: Z) (l0_2: (@list Z)) (y: Z) ,
  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_2))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (it_v_down <> 0) |] 
  &&  [| (it_v_up = 0) |] 
  &&  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y l0_2 )
  **  (store_string key k )
  **  (store_string k0 k_list )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> y)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
|--
  [| (map_composable m1 m2 ) |] 
  &&  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_2))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (it_v_down <> 0) |] 
  &&  [| (it_v_up = 0) |] 
  &&  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  (store_string k0 k_list )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y l0_2 )
  **  (store_string key k )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> y)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((removed) # Int  |->_)
.

Definition hashtbl_remove_partial_solve_wit_13 := hashtbl_remove_partial_solve_wit_13_pure -> hashtbl_remove_partial_solve_wit_13_aux.

Definition hashtbl_remove_partial_solve_wit_14_pure := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (k0: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) (x: Z) (l0_2: (@list Z)) (y: Z) ,
  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_2))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (it_v_down <> 0) |] 
  &&  [| (it_v_up <> 0) |] 
  &&  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  ((( &( "res" ) )) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y l0_2 )
  **  (store_string key k )
  **  (store_string k0 k_list )
  **  ((( &( "b" ) )) # Ptr  |-> it_v)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> y)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
|--
  [| (map_composable m1 m2 ) |]
.

Definition hashtbl_remove_partial_solve_wit_14_aux := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (k0: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) (x: Z) (l0_2: (@list Z)) (y: Z) ,
  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_2))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (it_v_down <> 0) |] 
  &&  [| (it_v_up <> 0) |] 
  &&  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y l0_2 )
  **  (store_string key k )
  **  (store_string k0 k_list )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> y)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
|--
  [| (map_composable m1 m2 ) |] 
  &&  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_2))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (it_v_down <> 0) |] 
  &&  [| (it_v_up <> 0) |] 
  &&  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  (store_string k0 k_list )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y l0_2 )
  **  (store_string key k )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> y)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((removed) # Int  |->_)
.

Definition hashtbl_remove_partial_solve_wit_14 := hashtbl_remove_partial_solve_wit_14_pure -> hashtbl_remove_partial_solve_wit_14_aux.

Definition hashtbl_remove_partial_solve_wit_15_pure := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (k0: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) (z: Z) (l0_2: (@list Z)) (x: Z) (l0_3: (@list Z)) (y: Z) ,
  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_3))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (dl_up = (cons (h_top) (l0_2))) |] 
  &&  [| (it_v_down <> 0) |] 
  &&  [| (it_v_up <> 0) |] 
  &&  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  ((( &( "res" ) )) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y l0_3 )
  **  (dllseg z it_v h_top it_v_up l0_2 )
  **  ((&((h_top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((&((h_top)  # "blist" ->ₛ "down")) # Ptr  |-> z)
  **  (store_string key k )
  **  (store_string k0 k_list )
  **  ((( &( "b" ) )) # Ptr  |-> it_v)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> y)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
|--
  [| (map_composable m1 m2 ) |]
.

Definition hashtbl_remove_partial_solve_wit_15_aux := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (k0: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) (z: Z) (l0_2: (@list Z)) (x: Z) (l0_3: (@list Z)) (y: Z) ,
  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_3))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (dl_up = (cons (h_top) (l0_2))) |] 
  &&  [| (it_v_down <> 0) |] 
  &&  [| (it_v_up <> 0) |] 
  &&  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y l0_3 )
  **  (dllseg z it_v h_top it_v_up l0_2 )
  **  ((&((h_top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((&((h_top)  # "blist" ->ₛ "down")) # Ptr  |-> z)
  **  (store_string key k )
  **  (store_string k0 k_list )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> y)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
|--
  [| (map_composable m1 m2 ) |] 
  &&  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_3))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (dl_up = (cons (h_top) (l0_2))) |] 
  &&  [| (it_v_down <> 0) |] 
  &&  [| (it_v_up <> 0) |] 
  &&  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  (store_string k0 k_list )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y l0_3 )
  **  (dllseg z it_v h_top it_v_up l0_2 )
  **  ((&((h_top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((&((h_top)  # "blist" ->ₛ "down")) # Ptr  |-> z)
  **  (store_string key k )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> y)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((removed) # Int  |->_)
.

Definition hashtbl_remove_partial_solve_wit_15 := hashtbl_remove_partial_solve_wit_15_pure -> hashtbl_remove_partial_solve_wit_15_aux.

Definition hashtbl_remove_partial_solve_wit_16_pure := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (k0: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) (z: Z) (l0_2: (@list Z)) (x: Z) (l0_3: (@list Z)) (y: Z) ,
  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_3))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (dl_up = (cons (h_top) (l0_2))) |] 
  &&  [| (it_v_down = 0) |] 
  &&  [| (it_v_up <> 0) |] 
  &&  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  ((( &( "res" ) )) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y l0_3 )
  **  (dllseg z it_v h_top it_v_up l0_2 )
  **  ((&((h_top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((&((h_top)  # "blist" ->ₛ "down")) # Ptr  |-> z)
  **  (store_string key k )
  **  (store_string k0 k_list )
  **  ((( &( "b" ) )) # Ptr  |-> it_v)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> y)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
|--
  [| (map_composable m1 m2 ) |]
.

Definition hashtbl_remove_partial_solve_wit_16_aux := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (k0: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) (z: Z) (l0_2: (@list Z)) (x: Z) (l0_3: (@list Z)) (y: Z) ,
  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_3))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (dl_up = (cons (h_top) (l0_2))) |] 
  &&  [| (it_v_down = 0) |] 
  &&  [| (it_v_up <> 0) |] 
  &&  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y l0_3 )
  **  (dllseg z it_v h_top it_v_up l0_2 )
  **  ((&((h_top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((&((h_top)  # "blist" ->ₛ "down")) # Ptr  |-> z)
  **  (store_string key k )
  **  (store_string k0 k_list )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> y)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
|--
  [| (map_composable m1 m2 ) |] 
  &&  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_3))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (dl_up = (cons (h_top) (l0_2))) |] 
  &&  [| (it_v_down = 0) |] 
  &&  [| (it_v_up <> 0) |] 
  &&  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  (store_string k0 k_list )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y l0_3 )
  **  (dllseg z it_v h_top it_v_up l0_2 )
  **  ((&((h_top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((&((h_top)  # "blist" ->ₛ "down")) # Ptr  |-> z)
  **  (store_string key k )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> y)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((removed) # Int  |->_)
.

Definition hashtbl_remove_partial_solve_wit_16 := hashtbl_remove_partial_solve_wit_16_pure -> hashtbl_remove_partial_solve_wit_16_aux.

Definition hashtbl_remove_partial_solve_wit_17_pure := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (k0: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) (x: Z) (l0_2: (@list Z)) (y: Z) ,
  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_2))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (it_v_down = 0) |] 
  &&  [| (it_v_up <> 0) |] 
  &&  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  ((( &( "res" ) )) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y l0_2 )
  **  (store_string key k )
  **  (store_string k0 k_list )
  **  ((( &( "b" ) )) # Ptr  |-> it_v)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> y)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
|--
  [| (map_composable m1 m2 ) |]
.

Definition hashtbl_remove_partial_solve_wit_17_aux := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (k0: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) (x: Z) (l0_2: (@list Z)) (y: Z) ,
  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_2))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (it_v_down = 0) |] 
  &&  [| (it_v_up <> 0) |] 
  &&  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y l0_2 )
  **  (store_string key k )
  **  (store_string k0 k_list )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> y)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
|--
  [| (map_composable m1 m2 ) |] 
  &&  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_2))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (it_v_down = 0) |] 
  &&  [| (it_v_up <> 0) |] 
  &&  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  (store_string k0 k_list )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y l0_2 )
  **  (store_string key k )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> y)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((removed) # Int  |->_)
.

Definition hashtbl_remove_partial_solve_wit_17 := hashtbl_remove_partial_solve_wit_17_pure -> hashtbl_remove_partial_solve_wit_17_aux.

Definition hashtbl_remove_partial_solve_wit_18_pure := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (k0: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) (x: Z) (l0_2: (@list Z)) (y: Z) ,
  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_2))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (it_v_down = 0) |] 
  &&  [| (it_v_up = 0) |] 
  &&  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  ((( &( "res" ) )) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y l0_2 )
  **  (store_string key k )
  **  (store_string k0 k_list )
  **  ((( &( "b" ) )) # Ptr  |-> it_v)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> y)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
|--
  [| (map_composable m1 m2 ) |]
.

Definition hashtbl_remove_partial_solve_wit_18_aux := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (k0: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) (x: Z) (l0_2: (@list Z)) (y: Z) ,
  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_2))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (it_v_down = 0) |] 
  &&  [| (it_v_up = 0) |] 
  &&  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y l0_2 )
  **  (store_string key k )
  **  (store_string k0 k_list )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> y)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
|--
  [| (map_composable m1 m2 ) |] 
  &&  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_2))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (it_v_down = 0) |] 
  &&  [| (it_v_up = 0) |] 
  &&  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  (store_string k0 k_list )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y l0_2 )
  **  (store_string key k )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> y)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((removed) # Int  |->_)
.

Definition hashtbl_remove_partial_solve_wit_18 := hashtbl_remove_partial_solve_wit_18_pure -> hashtbl_remove_partial_solve_wit_18_aux.

Definition hashtbl_remove_partial_solve_wit_19_pure := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (k0: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) (z: Z) (l0_2: (@list Z)) (x: Z) (l0_3: (@list Z)) (y: Z) ,
  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_3))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (dl_up = (cons (h_top) (l0_2))) |] 
  &&  [| (it_v_down = 0) |] 
  &&  [| (it_v_up = 0) |] 
  &&  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  ((( &( "res" ) )) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y l0_3 )
  **  (dllseg z it_v h_top it_v_up l0_2 )
  **  ((&((h_top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((&((h_top)  # "blist" ->ₛ "down")) # Ptr  |-> z)
  **  (store_string key k )
  **  (store_string k0 k_list )
  **  ((( &( "b" ) )) # Ptr  |-> it_v)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> y)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((( &( "removed" ) )) # Ptr  |-> removed)
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
|--
  [| (map_composable m1 m2 ) |]
.

Definition hashtbl_remove_partial_solve_wit_19_aux := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (k0: Z) (val: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) (z: Z) (l0_2: (@list Z)) (x: Z) (l0_3: (@list Z)) (y: Z) ,
  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_3))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (dl_up = (cons (h_top) (l0_2))) |] 
  &&  [| (it_v_down = 0) |] 
  &&  [| (it_v_up = 0) |] 
  &&  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y l0_3 )
  **  (dllseg z it_v h_top it_v_up l0_2 )
  **  ((&((h_top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((&((h_top)  # "blist" ->ₛ "down")) # Ptr  |-> z)
  **  (store_string key k )
  **  (store_string k0 k_list )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> y)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((removed) # Int  |->_)
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
|--
  [| (map_composable m1 m2 ) |] 
  &&  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_3))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (dl_up = (cons (h_top) (l0_2))) |] 
  &&  [| (it_v_down = 0) |] 
  &&  [| (it_v_up = 0) |] 
  &&  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  (store_string k0 k_list )
  **  ((&((it_v)  # "blist" ->ₛ "key")) # Ptr  |-> k0)
  **  ((&((it_v)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y l0_3 )
  **  (dllseg z it_v h_top it_v_up l0_2 )
  **  ((&((h_top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((&((h_top)  # "blist" ->ₛ "down")) # Ptr  |-> z)
  **  (store_string key k )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> y)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((removed) # Int  |->_)
.

Definition hashtbl_remove_partial_solve_wit_19 := hashtbl_remove_partial_solve_wit_19_pure -> hashtbl_remove_partial_solve_wit_19_aux.

Definition hashtbl_remove_partial_solve_wit_20 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) (z: Z) (l0_2: (@list Z)) (x: Z) (l0_3: (@list Z)) (y: Z) ,
  [| (map_composable m1 m2 ) |] 
  &&  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_3))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (dl_up = (cons (h_top) (l0_2))) |] 
  &&  [| (it_v_down = 0) |] 
  &&  [| (it_v_up = 0) |] 
  &&  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  (store_map store_name (KP.remove_map (m1) (k_list)) )
  **  (store_map store_uint (PV.remove_map (m2) (it_v)) )
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y l0_3 )
  **  (dllseg z it_v h_top it_v_up l0_2 )
  **  ((&((h_top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((&((h_top)  # "blist" ->ₛ "down")) # Ptr  |-> z)
  **  (store_string key k )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> y)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((removed) # Int  |->_)
|--
  [| (map_composable m1 m2 ) |] 
  &&  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_3))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (dl_up = (cons (h_top) (l0_2))) |] 
  &&  [| (it_v_down = 0) |] 
  &&  [| (it_v_up = 0) |] 
  &&  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |->_)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |->_)
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |->_)
  **  (store_map store_name (KP.remove_map (m1) (k_list)) )
  **  (store_map store_uint (PV.remove_map (m2) (it_v)) )
  **  (sll y l0_3 )
  **  (dllseg z it_v h_top it_v_up l0_2 )
  **  ((&((h_top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((&((h_top)  # "blist" ->ₛ "down")) # Ptr  |-> z)
  **  (store_string key k )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> y)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((removed) # Int  |->_)
.

Definition hashtbl_remove_partial_solve_wit_21 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) (x: Z) (l0_2: (@list Z)) (y: Z) ,
  [| (map_composable m1 m2 ) |] 
  &&  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_2))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (it_v_down = 0) |] 
  &&  [| (it_v_up = 0) |] 
  &&  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  (store_map store_name (KP.remove_map (m1) (k_list)) )
  **  (store_map store_uint (PV.remove_map (m2) (it_v)) )
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y l0_2 )
  **  (store_string key k )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> y)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((removed) # Int  |->_)
|--
  [| (map_composable m1 m2 ) |] 
  &&  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_2))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (it_v_down = 0) |] 
  &&  [| (it_v_up = 0) |] 
  &&  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |->_)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |->_)
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |->_)
  **  (store_map store_name (KP.remove_map (m1) (k_list)) )
  **  (store_map store_uint (PV.remove_map (m2) (it_v)) )
  **  (sll y l0_2 )
  **  (store_string key k )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> y)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((removed) # Int  |->_)
.

Definition hashtbl_remove_partial_solve_wit_22 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) (x: Z) (l0_2: (@list Z)) (y: Z) ,
  [| (map_composable m1 m2 ) |] 
  &&  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_2))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (it_v_down = 0) |] 
  &&  [| (it_v_up <> 0) |] 
  &&  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  (store_map store_name (KP.remove_map (m1) (k_list)) )
  **  (store_map store_uint (PV.remove_map (m2) (it_v)) )
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y l0_2 )
  **  (store_string key k )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> y)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((removed) # Int  |->_)
|--
  [| (map_composable m1 m2 ) |] 
  &&  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_2))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (it_v_down = 0) |] 
  &&  [| (it_v_up <> 0) |] 
  &&  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |->_)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |->_)
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |->_)
  **  (store_map store_name (KP.remove_map (m1) (k_list)) )
  **  (store_map store_uint (PV.remove_map (m2) (it_v)) )
  **  (sll y l0_2 )
  **  (store_string key k )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> y)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((removed) # Int  |->_)
.

Definition hashtbl_remove_partial_solve_wit_23 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) (z: Z) (l0_2: (@list Z)) (x: Z) (l0_3: (@list Z)) (y: Z) ,
  [| (map_composable m1 m2 ) |] 
  &&  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_3))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (dl_up = (cons (h_top) (l0_2))) |] 
  &&  [| (it_v_down = 0) |] 
  &&  [| (it_v_up <> 0) |] 
  &&  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  (store_map store_name (KP.remove_map (m1) (k_list)) )
  **  (store_map store_uint (PV.remove_map (m2) (it_v)) )
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y l0_3 )
  **  (dllseg z it_v h_top it_v_up l0_2 )
  **  ((&((h_top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((&((h_top)  # "blist" ->ₛ "down")) # Ptr  |-> z)
  **  (store_string key k )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> y)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((removed) # Int  |->_)
|--
  [| (map_composable m1 m2 ) |] 
  &&  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_3))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (dl_up = (cons (h_top) (l0_2))) |] 
  &&  [| (it_v_down = 0) |] 
  &&  [| (it_v_up <> 0) |] 
  &&  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |->_)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |->_)
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |->_)
  **  (store_map store_name (KP.remove_map (m1) (k_list)) )
  **  (store_map store_uint (PV.remove_map (m2) (it_v)) )
  **  (sll y l0_3 )
  **  (dllseg z it_v h_top it_v_up l0_2 )
  **  ((&((h_top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((&((h_top)  # "blist" ->ₛ "down")) # Ptr  |-> z)
  **  (store_string key k )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> y)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_down_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((removed) # Int  |->_)
.

Definition hashtbl_remove_partial_solve_wit_24 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) (z: Z) (l0_2: (@list Z)) (x: Z) (l0_3: (@list Z)) (y: Z) ,
  [| (map_composable m1 m2 ) |] 
  &&  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_3))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (dl_up = (cons (h_top) (l0_2))) |] 
  &&  [| (it_v_down <> 0) |] 
  &&  [| (it_v_up <> 0) |] 
  &&  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  (store_map store_name (KP.remove_map (m1) (k_list)) )
  **  (store_map store_uint (PV.remove_map (m2) (it_v)) )
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y l0_3 )
  **  (dllseg z it_v h_top it_v_up l0_2 )
  **  ((&((h_top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((&((h_top)  # "blist" ->ₛ "down")) # Ptr  |-> z)
  **  (store_string key k )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> y)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((removed) # Int  |->_)
|--
  [| (map_composable m1 m2 ) |] 
  &&  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_3))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (dl_up = (cons (h_top) (l0_2))) |] 
  &&  [| (it_v_down <> 0) |] 
  &&  [| (it_v_up <> 0) |] 
  &&  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |->_)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |->_)
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |->_)
  **  (store_map store_name (KP.remove_map (m1) (k_list)) )
  **  (store_map store_uint (PV.remove_map (m2) (it_v)) )
  **  (sll y l0_3 )
  **  (dllseg z it_v h_top it_v_up l0_2 )
  **  ((&((h_top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((&((h_top)  # "blist" ->ₛ "down")) # Ptr  |-> z)
  **  (store_string key k )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> y)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((removed) # Int  |->_)
.

Definition hashtbl_remove_partial_solve_wit_25 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) (x: Z) (l0_2: (@list Z)) (y: Z) ,
  [| (map_composable m1 m2 ) |] 
  &&  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_2))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (it_v_down <> 0) |] 
  &&  [| (it_v_up <> 0) |] 
  &&  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  (store_map store_name (KP.remove_map (m1) (k_list)) )
  **  (store_map store_uint (PV.remove_map (m2) (it_v)) )
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y l0_2 )
  **  (store_string key k )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> y)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((removed) # Int  |->_)
|--
  [| (map_composable m1 m2 ) |] 
  &&  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_2))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (it_v_down <> 0) |] 
  &&  [| (it_v_up <> 0) |] 
  &&  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |->_)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |->_)
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |->_)
  **  (store_map store_name (KP.remove_map (m1) (k_list)) )
  **  (store_map store_uint (PV.remove_map (m2) (it_v)) )
  **  (sll y l0_2 )
  **  (store_string key k )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> y)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((removed) # Int  |->_)
.

Definition hashtbl_remove_partial_solve_wit_26 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) (x: Z) (l0_2: (@list Z)) (y: Z) ,
  [| (map_composable m1 m2 ) |] 
  &&  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_2))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (it_v_down <> 0) |] 
  &&  [| (it_v_up = 0) |] 
  &&  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  (store_map store_name (KP.remove_map (m1) (k_list)) )
  **  (store_map store_uint (PV.remove_map (m2) (it_v)) )
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y l0_2 )
  **  (store_string key k )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> y)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((removed) # Int  |->_)
|--
  [| (map_composable m1 m2 ) |] 
  &&  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_2))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (it_v_down <> 0) |] 
  &&  [| (it_v_up = 0) |] 
  &&  [| (h_top = it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |->_)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |->_)
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |->_)
  **  (store_map store_name (KP.remove_map (m1) (k_list)) )
  **  (store_map store_uint (PV.remove_map (m2) (it_v)) )
  **  (sll y l0_2 )
  **  (store_string key k )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> y)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> it_v_down)
  **  (dllseg h_top it_v 0 it_v_up dl_up )
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((removed) # Int  |->_)
.

Definition hashtbl_remove_partial_solve_wit_27 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (removed: Z) (it_v_down_up: Z) (it_v_down: Z) (it_v_up_down: Z) (h_top: Z) (it_v_up: Z) (buck: Z) (it_v: Z) (it: Z) (k_list: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (l_res: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (ind: Z) (key: Z) (l_prev: (@list Z)) (retval: Z) (z: Z) (l0_2: (@list Z)) (x: Z) (l0_3: (@list Z)) (y: Z) ,
  [| (map_composable m1 m2 ) |] 
  &&  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_3))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (dl_up = (cons (h_top) (l0_2))) |] 
  &&  [| (it_v_down <> 0) |] 
  &&  [| (it_v_up = 0) |] 
  &&  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  (store_map store_name (KP.remove_map (m1) (k_list)) )
  **  (store_map store_uint (PV.remove_map (m2) (it_v)) )
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y l0_3 )
  **  (dllseg z it_v h_top it_v_up l0_2 )
  **  ((&((h_top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((&((h_top)  # "blist" ->ₛ "down")) # Ptr  |-> z)
  **  (store_string key k )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> y)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_down)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((removed) # Int  |->_)
|--
  [| (map_composable m1 m2 ) |] 
  &&  [| (it_v = x) |] 
  &&  [| (l_res = (cons (x) (l0_3))) |] 
  &&  [| (it_v = x) |] 
  &&  [| (dl_up = (cons (h_top) (l0_2))) |] 
  &&  [| (it_v_down <> 0) |] 
  &&  [| (it_v_up = 0) |] 
  &&  [| (h_top <> it_v) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list) |] 
  &&  [| (it_v <> 0) |] 
  &&  [| (map_composable m1 m2 ) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((b (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (l = (app (dl_up) (dl_down))) |] 
  &&  [| ((m1 (k_list)) = (Some (&((it_v)  # "blist" ->ₛ "val")))) |]
  &&  ((&((it_v)  # "blist" ->ₛ "up")) # Ptr  |->_)
  **  ((&((it_v)  # "blist" ->ₛ "down")) # Ptr  |->_)
  **  ((&((it_v)  # "blist" ->ₛ "next")) # Ptr  |->_)
  **  (store_map store_name (KP.remove_map (m1) (k_list)) )
  **  (store_map store_uint (PV.remove_map (m2) (it_v)) )
  **  (sll y l0_3 )
  **  (dllseg z it_v h_top it_v_up l0_2 )
  **  ((&((h_top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((&((h_top)  # "blist" ->ₛ "down")) # Ptr  |-> z)
  **  (store_string key k )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((it) # Ptr  |-> y)
  **  (sllseg buck it_v l_prev )
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll it_v it_v_up dl_down )
  **  ((&((it_v_up)  # "blist" ->ₛ "down")) # Ptr  |-> it_v_up_down)
  **  ((it_v_up_down) # Ptr  |-> it_v)
  **  ((&((it_v_down)  # "blist" ->ₛ "up")) # Ptr  |-> it_v_up)
  **  ((it_v_down_up) # Ptr  |-> it_v)
  **  ((removed) # Int  |->_)
.

Definition hashtbl_remove_which_implies_wit_1 := 
forall (m1: ((@list Z) -> (@option Z))) (h: Z) ,
  (store_hash_skeleton h m1 )
|--
  EX (h_bucks: Z)  (h_top: Z)  (lh: (@list Z))  (b: (Z -> (@option (Z * (@list Z)))))  (l: (@list Z)) ,
  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (PtrArray.full h_bucks 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m1 )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.
Include ptr_array_Strategy_Correct.

Axiom proof_of_hashtbl_findref_safety_wit_1 : hashtbl_findref_safety_wit_1.
Axiom proof_of_hashtbl_findref_safety_wit_2 : hashtbl_findref_safety_wit_2.
Axiom proof_of_hashtbl_findref_safety_wit_3 : hashtbl_findref_safety_wit_3.
Axiom proof_of_hashtbl_findref_safety_wit_4 : hashtbl_findref_safety_wit_4.
Axiom proof_of_hashtbl_findref_safety_wit_5 : hashtbl_findref_safety_wit_5.
Axiom proof_of_hashtbl_findref_safety_wit_6 : hashtbl_findref_safety_wit_6.
Axiom proof_of_hashtbl_findref_safety_wit_7 : hashtbl_findref_safety_wit_7.
Axiom proof_of_hashtbl_findref_safety_wit_8 : hashtbl_findref_safety_wit_8.
Axiom proof_of_hashtbl_findref_safety_wit_9 : hashtbl_findref_safety_wit_9.
Axiom proof_of_hashtbl_findref_entail_wit_1 : hashtbl_findref_entail_wit_1.
Axiom proof_of_hashtbl_findref_entail_wit_2_1 : hashtbl_findref_entail_wit_2_1.
Axiom proof_of_hashtbl_findref_entail_wit_2_2 : hashtbl_findref_entail_wit_2_2.
Axiom proof_of_hashtbl_findref_entail_wit_3_1 : hashtbl_findref_entail_wit_3_1.
Axiom proof_of_hashtbl_findref_entail_wit_3_2 : hashtbl_findref_entail_wit_3_2.
Axiom proof_of_hashtbl_findref_entail_wit_4 : hashtbl_findref_entail_wit_4.
Axiom proof_of_hashtbl_findref_return_wit_1 : hashtbl_findref_return_wit_1.
Axiom proof_of_hashtbl_findref_return_wit_2 : hashtbl_findref_return_wit_2.
Axiom proof_of_hashtbl_findref_return_wit_3 : hashtbl_findref_return_wit_3.
Axiom proof_of_hashtbl_findref_partial_solve_wit_1 : hashtbl_findref_partial_solve_wit_1.
Axiom proof_of_hashtbl_findref_partial_solve_wit_2 : hashtbl_findref_partial_solve_wit_2.
Axiom proof_of_hashtbl_findref_partial_solve_wit_3 : hashtbl_findref_partial_solve_wit_3.
Axiom proof_of_hashtbl_findref_partial_solve_wit_4 : hashtbl_findref_partial_solve_wit_4.
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
Axiom proof_of_hashtbl_remove_partial_solve_wit_12_pure : hashtbl_remove_partial_solve_wit_12_pure.
Axiom proof_of_hashtbl_remove_partial_solve_wit_12 : hashtbl_remove_partial_solve_wit_12.
Axiom proof_of_hashtbl_remove_partial_solve_wit_13_pure : hashtbl_remove_partial_solve_wit_13_pure.
Axiom proof_of_hashtbl_remove_partial_solve_wit_13 : hashtbl_remove_partial_solve_wit_13.
Axiom proof_of_hashtbl_remove_partial_solve_wit_14_pure : hashtbl_remove_partial_solve_wit_14_pure.
Axiom proof_of_hashtbl_remove_partial_solve_wit_14 : hashtbl_remove_partial_solve_wit_14.
Axiom proof_of_hashtbl_remove_partial_solve_wit_15_pure : hashtbl_remove_partial_solve_wit_15_pure.
Axiom proof_of_hashtbl_remove_partial_solve_wit_15 : hashtbl_remove_partial_solve_wit_15.
Axiom proof_of_hashtbl_remove_partial_solve_wit_16_pure : hashtbl_remove_partial_solve_wit_16_pure.
Axiom proof_of_hashtbl_remove_partial_solve_wit_16 : hashtbl_remove_partial_solve_wit_16.
Axiom proof_of_hashtbl_remove_partial_solve_wit_17_pure : hashtbl_remove_partial_solve_wit_17_pure.
Axiom proof_of_hashtbl_remove_partial_solve_wit_17 : hashtbl_remove_partial_solve_wit_17.
Axiom proof_of_hashtbl_remove_partial_solve_wit_18_pure : hashtbl_remove_partial_solve_wit_18_pure.
Axiom proof_of_hashtbl_remove_partial_solve_wit_18 : hashtbl_remove_partial_solve_wit_18.
Axiom proof_of_hashtbl_remove_partial_solve_wit_19_pure : hashtbl_remove_partial_solve_wit_19_pure.
Axiom proof_of_hashtbl_remove_partial_solve_wit_19 : hashtbl_remove_partial_solve_wit_19.
Axiom proof_of_hashtbl_remove_partial_solve_wit_20 : hashtbl_remove_partial_solve_wit_20.
Axiom proof_of_hashtbl_remove_partial_solve_wit_21 : hashtbl_remove_partial_solve_wit_21.
Axiom proof_of_hashtbl_remove_partial_solve_wit_22 : hashtbl_remove_partial_solve_wit_22.
Axiom proof_of_hashtbl_remove_partial_solve_wit_23 : hashtbl_remove_partial_solve_wit_23.
Axiom proof_of_hashtbl_remove_partial_solve_wit_24 : hashtbl_remove_partial_solve_wit_24.
Axiom proof_of_hashtbl_remove_partial_solve_wit_25 : hashtbl_remove_partial_solve_wit_25.
Axiom proof_of_hashtbl_remove_partial_solve_wit_26 : hashtbl_remove_partial_solve_wit_26.
Axiom proof_of_hashtbl_remove_partial_solve_wit_27 : hashtbl_remove_partial_solve_wit_27.
Axiom proof_of_hashtbl_remove_which_implies_wit_1 : hashtbl_remove_which_implies_wit_1.

End VC_Correct.
