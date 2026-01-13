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
  **  (IntArray.full h_bucks 211 lh )
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
  **  (IntArray.full h_bucks 211 lh )
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
forall (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (h_top: Z) (h_bucks: Z) (h: Z) (i_v: Z) (i: Z) (buck: Z) (l_res: (@list Z)) (key: Z) (l_prev: (@list Z)) (l0: (@list Z)) (ind: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) ,
  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((ind + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (i_v = 0) |] 
  &&  [| (l_res = nil) |]
  &&  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  (((ind + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((( &( "i" ) )) # Ptr  |-> i)
  **  ((i) # Ptr  |-> i_v)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllseg (h_bucks + (ind * sizeof(PTR) ) ) i_v l_prev )
  **  (store_map store_sll b0 )
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
  **  (IntArray.full h_bucks 211 lh )
  **  (store_string key k )
  **  (store_map store_name m )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_findref_safety_wit_4 := 
forall (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (h_top: Z) (h_bucks: Z) (h: Z) (i_v: Z) (i: Z) (buck: Z) (l_res: (@list Z)) (key: Z) (l_prev: (@list Z)) (l0: (@list Z)) (ind: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) ,
  [| (i_v <> 0) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((ind + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (i_v = 0) |] 
  &&  [| (l_res = nil) |]
  &&  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  (((ind + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((( &( "i" ) )) # Ptr  |-> i)
  **  ((i) # Ptr  |-> i_v)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllseg (h_bucks + (ind * sizeof(PTR) ) ) i_v l_prev )
  **  (store_map store_sll b0 )
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
  **  (IntArray.full h_bucks 211 lh )
  **  (store_string key k )
  **  (store_map store_name m )
|--
  [| False |]
.

Definition hashtbl_findref_safety_wit_5 := 
forall (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (h_top: Z) (k_list_current: (@list Z)) (key_addr: Z) (l_resres: (@list Z)) (p_current: Z) (i: Z) (buck: Z) (l_res: (@list Z)) (key: Z) (l_prev: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (ind: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) ,
  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (l_res = (cons (p_current) (l_resres))) |]
  &&  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((( &( "i" ) )) # Ptr  |-> i)
  **  ((i) # Ptr  |-> p_current)
  **  (sllseg (ind + (ind * sizeof(PTR) ) ) p_current l_prev )
  **  ((&((p_current)  # "blist" ->ₛ "key")) # Ptr  |-> key_addr)
  **  (store_string key_addr k_list_current )
  **  (sll p_current l_res )
  **  (store_map store_sll b0 )
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
  **  (IntArray.full h_bucks 211 lh )
  **  (store_string key k )
  **  (store_map store_name m )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_findref_safety_wit_6 := 
forall (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (h_top: Z) (k_list_current: (@list Z)) (key_addr: Z) (l_resres: (@list Z)) (p_current: Z) (i: Z) (buck: Z) (l_res: (@list Z)) (key: Z) (l_prev: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (ind: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (k <> k_list_current) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (l_res = (cons (p_current) (l_resres))) |]
  &&  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((( &( "i" ) )) # Ptr  |-> i)
  **  ((i) # Ptr  |-> p_current)
  **  (sllseg (ind + (ind * sizeof(PTR) ) ) p_current l_prev )
  **  ((&((p_current)  # "blist" ->ₛ "key")) # Ptr  |-> key_addr)
  **  (sll p_current l_res )
  **  (store_map store_sll b0 )
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
  **  (IntArray.full h_bucks 211 lh )
  **  (store_map store_name m )
|--
  [| False |]
.

Definition hashtbl_findref_safety_wit_7 := 
forall (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (h_top: Z) (k_list_current: (@list Z)) (key_addr: Z) (l_resres: (@list Z)) (p_current: Z) (i: Z) (buck: Z) (l_res: (@list Z)) (key: Z) (l_prev: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (ind: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list_current) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (l_res = (cons (p_current) (l_resres))) |]
  &&  (store_string key k )
  **  (store_string key_addr k_list_current )
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((( &( "i" ) )) # Ptr  |-> i)
  **  ((i) # Ptr  |-> p_current)
  **  (sllseg (ind + (ind * sizeof(PTR) ) ) p_current l_prev )
  **  ((&((p_current)  # "blist" ->ₛ "key")) # Ptr  |-> key_addr)
  **  (sll p_current l_res )
  **  (store_map store_sll b0 )
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
  **  (IntArray.full h_bucks 211 lh )
  **  (store_map store_name m )
|--
  [| False |]
.

Definition hashtbl_findref_safety_wit_8 := 
forall (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (h_top: Z) (h_bucks: Z) (h: Z) (i_v: Z) (i: Z) (buck: Z) (l_res: (@list Z)) (key: Z) (l_prev: (@list Z)) (l0: (@list Z)) (ind: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) ,
  [| (i_v = 0) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((ind + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (i_v = 0) |] 
  &&  [| (l_res = nil) |]
  &&  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  (((ind + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((( &( "i" ) )) # Ptr  |-> i)
  **  ((i) # Ptr  |-> i_v)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllseg (h_bucks + (ind * sizeof(PTR) ) ) i_v l_prev )
  **  (store_map store_sll b0 )
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
  **  (IntArray.full h_bucks 211 lh )
  **  (store_string key k )
  **  (store_map store_name m )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_findref_safety_wit_9 := 
forall (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (h_top: Z) (k_list_current: (@list Z)) (key_addr: Z) (l_resres: (@list Z)) (p_current: Z) (i: Z) (buck: Z) (l_res: (@list Z)) (key: Z) (l_prev: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (ind: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) ,
  [| (p_current = 0) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (l_res = (cons (p_current) (l_resres))) |]
  &&  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((( &( "i" ) )) # Ptr  |-> i)
  **  ((i) # Ptr  |-> p_current)
  **  (sllseg (ind + (ind * sizeof(PTR) ) ) p_current l_prev )
  **  ((&((p_current)  # "blist" ->ₛ "key")) # Ptr  |-> key_addr)
  **  (store_string key_addr k_list_current )
  **  (sll p_current l_res )
  **  (store_map store_sll b0 )
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
  **  (IntArray.full h_bucks 211 lh )
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
  **  (IntArray.full h_bucks 211 lh_2 )
  **  (store_map store_sll b0_2 )
  **  (store_map store_name m )
|--
  (EX (h_top: Z)  (h_bucks_2: Z)  (i_v: Z)  (buck: Z)  (l_res: (@list Z))  (l_prev: (@list Z))  (l0: (@list Z))  (lh: (@list Z))  (b0: (Z -> (@option (Z * (@list Z)))))  (l: (@list Z)) ,
  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= (retval % ( 211 ) )) |] 
  &&  [| ((retval % ( 211 ) ) < 211) |] 
  &&  [| ((b0 ((retval % ( 211 ) ))) = (Some ((pair (((retval % ( 211 ) ) + ((retval % ( 211 ) ) * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (not_key key_pre l_prev ) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (i_v = 0) |] 
  &&  [| (l_res = nil) |]
  &&  ((((retval % ( 211 ) ) + ((retval % ( 211 ) ) * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (((h_bucks + ((retval % ( 211 ) ) * sizeof(PTR) ) )) # Ptr  |-> i_v)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks_2)
  **  (sllseg (h_bucks_2 + ((retval % ( 211 ) ) * sizeof(PTR) ) ) i_v l_prev )
  **  (store_map store_sll b0 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
  **  (IntArray.full h_bucks_2 211 lh )
  **  (store_string key_pre k )
  **  (store_map store_name m ))
  ||
  (EX (h_top_2: Z)  (k_list_current: (@list Z))  (key_addr: Z)  (l_resres: (@list Z))  (p_current: Z)  (buck: Z)  (l_res: (@list Z))  (l_prev: (@list Z))  (h_bucks_3: Z)  (l0: (@list Z))  (lh: (@list Z))  (b0: (Z -> (@option (Z * (@list Z)))))  (l: (@list Z)) ,
  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= (retval % ( 211 ) )) |] 
  &&  [| ((retval % ( 211 ) ) < 211) |] 
  &&  [| ((b0 ((retval % ( 211 ) ))) = (Some ((pair ((h_bucks_3 + ((retval % ( 211 ) ) * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (not_key key_pre l_prev ) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (l_res = (cons (p_current) (l_resres))) |]
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks_3)
  **  (((h_bucks_3 + ((retval % ( 211 ) ) * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  (((h_bucks + ((retval % ( 211 ) ) * sizeof(PTR) ) )) # Ptr  |-> p_current)
  **  (sllseg ((retval % ( 211 ) ) + ((retval % ( 211 ) ) * sizeof(PTR) ) ) p_current l_prev )
  **  ((&((p_current)  # "blist" ->ₛ "key")) # Ptr  |-> key_addr)
  **  (store_string key_addr k_list_current )
  **  (sll p_current l_res )
  **  (store_map store_sll b0 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top_2)
  **  (dll h_top_2 0 l )
  **  (IntArray.full h_bucks_3 211 lh )
  **  (store_string key_pre k )
  **  (store_map store_name m ))
.

Definition hashtbl_findref_entail_wit_2_1 := 
forall (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (h_top: Z) (k_list_current: (@list Z)) (key_addr: Z) (l_resres: (@list Z)) (p_current: Z) (i: Z) (buck: Z) (l_res: (@list Z)) (key: Z) (l_prev: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (ind: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list_current) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (l_res = (cons (p_current) (l_resres))) |]
  &&  (store_string key k )
  **  (store_string key_addr k_list_current )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((i) # Ptr  |-> p_current)
  **  (sllseg (ind + (ind * sizeof(PTR) ) ) p_current l_prev )
  **  ((&((p_current)  # "blist" ->ₛ "key")) # Ptr  |-> key_addr)
  **  (sll p_current l_res )
  **  (store_map store_sll b0 )
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
  **  (IntArray.full h_bucks 211 lh )
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
  &&  [| ((b0 (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (l_res = (cons (p_current) (l_resres))) |]
  &&  (store_string key k )
  **  (store_string key_addr k_list_current )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((i) # Ptr  |-> p_current)
  **  (sllseg (ind + (ind * sizeof(PTR) ) ) p_current l_prev )
  **  ((&((p_current)  # "blist" ->ₛ "key")) # Ptr  |-> key_addr)
  **  (sll p_current l_res )
  **  (store_map store_sll b0 )
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
  **  (IntArray.full h_bucks 211 lh )
  **  (store_map store_name m )
.

Definition hashtbl_findref_entail_wit_2_2 := 
forall (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (h_top: Z) (k_list_current: (@list Z)) (key_addr: Z) (l_resres: (@list Z)) (p_current: Z) (i: Z) (buck: Z) (l_res: (@list Z)) (key: Z) (l_prev: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (ind: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (k <> k_list_current) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (l_res = (cons (p_current) (l_resres))) |]
  &&  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((i) # Ptr  |-> p_current)
  **  (sllseg (ind + (ind * sizeof(PTR) ) ) p_current l_prev )
  **  ((&((p_current)  # "blist" ->ₛ "key")) # Ptr  |-> key_addr)
  **  (sll p_current l_res )
  **  (store_map store_sll b0 )
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
  **  (IntArray.full h_bucks 211 lh )
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
  &&  [| ((b0 (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (l_res = (cons (p_current) (l_resres))) |]
  &&  (store_string key k )
  **  (store_string key_addr k_list_current )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((i) # Ptr  |-> p_current)
  **  (sllseg (ind + (ind * sizeof(PTR) ) ) p_current l_prev )
  **  ((&((p_current)  # "blist" ->ₛ "key")) # Ptr  |-> key_addr)
  **  (sll p_current l_res )
  **  (store_map store_sll b0 )
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
  **  (IntArray.full h_bucks 211 lh )
  **  (store_map store_name m )
.

Definition hashtbl_findref_entail_wit_3_1 := 
forall (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (h_top: Z) (k_list_current: (@list Z)) (key_addr: Z) (l_resres: (@list Z)) (p_current: Z) (i: Z) (buck: Z) (l_res: (@list Z)) (key: Z) (l_prev: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (ind: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (retval_2: Z) ,
  [| (retval_2 = 0) |] 
  &&  [| (retval_2 = 1) |] 
  &&  [| (k = k_list_current) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (l_res = (cons (p_current) (l_resres))) |]
  &&  (store_string key k )
  **  (store_string key_addr k_list_current )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((i) # Ptr  |-> p_current)
  **  (sllseg (ind + (ind * sizeof(PTR) ) ) p_current l_prev )
  **  ((&((p_current)  # "blist" ->ₛ "key")) # Ptr  |-> key_addr)
  **  (sll p_current l_res )
  **  (store_map store_sll b0 )
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
  **  (IntArray.full h_bucks 211 lh )
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
  &&  [| ((b0 (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (l_res = (cons (p_current) (l_resres))) |]
  &&  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((i) # Ptr  |-> p_current)
  **  (sllseg (ind + (ind * sizeof(PTR) ) ) p_current l_prev )
  **  ((&((p_current)  # "blist" ->ₛ "key")) # Ptr  |-> key_addr)
  **  (sll p_current l_res )
  **  (store_map store_sll b0 )
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
  **  (IntArray.full h_bucks 211 lh )
  **  (store_map store_name m )
.

Definition hashtbl_findref_entail_wit_3_2 := 
forall (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (h_top: Z) (k_list_current: (@list Z)) (key_addr: Z) (l_resres: (@list Z)) (p_current: Z) (i: Z) (buck: Z) (l_res: (@list Z)) (key: Z) (l_prev: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (ind: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (k <> k_list_current) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (l_res = (cons (p_current) (l_resres))) |]
  &&  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((i) # Ptr  |-> p_current)
  **  (sllseg (ind + (ind * sizeof(PTR) ) ) p_current l_prev )
  **  ((&((p_current)  # "blist" ->ₛ "key")) # Ptr  |-> key_addr)
  **  (sll p_current l_res )
  **  (store_map store_sll b0 )
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
  **  (IntArray.full h_bucks 211 lh )
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
  &&  [| ((b0 (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (l_res = (cons (p_current) (l_resres))) |]
  &&  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((i) # Ptr  |-> p_current)
  **  (sllseg (ind + (ind * sizeof(PTR) ) ) p_current l_prev )
  **  ((&((p_current)  # "blist" ->ₛ "key")) # Ptr  |-> key_addr)
  **  (sll p_current l_res )
  **  (store_map store_sll b0 )
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
  **  (IntArray.full h_bucks 211 lh )
  **  (store_map store_name m )
.

Definition hashtbl_findref_entail_wit_4 := 
forall (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (h_top_3: Z) (k_list_current_2: (@list Z)) (key_addr_2: Z) (l_resres_2: (@list Z)) (p_current: Z) (i: Z) (buck_2: Z) (l_res_2: (@list Z)) (key: Z) (l_prev_2: (@list Z)) (h_bucks_3: Z) (h: Z) (l0_2: (@list Z)) (ind: Z) (lh_2: (@list Z)) (b0_2: (Z -> (@option (Z * (@list Z))))) (l_2: (@list Z)) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (k <> k_list_current_2) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (contain_all_addrs m l_2 ) |] 
  &&  [| (repr_all_heads lh_2 b0_2 ) |] 
  &&  [| (contain_all_correct_addrs m b0_2 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0_2 (ind)) = (Some ((pair ((h_bucks_3 + (ind * sizeof(PTR) ) )) (l0_2))))) |] 
  &&  [| (not_key key l_prev_2 ) |] 
  &&  [| (l0_2 = (app (l_prev_2) (l_res_2))) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (l_res_2 = (cons (p_current) (l_resres_2))) |]
  &&  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks_3)
  **  (((h_bucks_3 + (ind * sizeof(PTR) ) )) # Ptr  |-> buck_2)
  **  ((i) # Ptr  |-> p_current)
  **  (sllseg (ind + (ind * sizeof(PTR) ) ) p_current l_prev_2 )
  **  ((&((p_current)  # "blist" ->ₛ "key")) # Ptr  |-> key_addr_2)
  **  (sll p_current l_res_2 )
  **  (store_map store_sll b0_2 )
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top_3)
  **  (dll h_top_3 0 l_2 )
  **  (IntArray.full h_bucks_3 211 lh_2 )
  **  (store_map store_name m )
|--
  (EX (h_top: Z)  (h_bucks: Z)  (i_v: Z)  (buck: Z)  (l_res: (@list Z))  (l_prev: (@list Z))  (l0: (@list Z))  (lh: (@list Z))  (b0: (Z -> (@option (Z * (@list Z)))))  (l: (@list Z)) ,
  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((ind + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (i_v = 0) |] 
  &&  [| (l_res = nil) |]
  &&  (((ind + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((p_current)  # "blist" ->ₛ "next")) # Ptr  |-> i_v)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllseg (h_bucks + (ind * sizeof(PTR) ) ) i_v l_prev )
  **  (store_map store_sll b0 )
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
  **  (IntArray.full h_bucks 211 lh )
  **  (store_string key k )
  **  (store_map store_name m ))
  ||
  (EX (h_top_2: Z)  (k_list_current: (@list Z))  (key_addr: Z)  (l_resres: (@list Z))  (p_current_2: Z)  (buck: Z)  (l_res: (@list Z))  (l_prev: (@list Z))  (h_bucks_2: Z)  (l0: (@list Z))  (lh: (@list Z))  (b0: (Z -> (@option (Z * (@list Z)))))  (l: (@list Z)) ,
  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((h_bucks_2 + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (p_current_2 <> 0) |] 
  &&  [| (l_res = (cons (p_current_2) (l_resres))) |]
  &&  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks_2)
  **  (((h_bucks_2 + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((&((p_current)  # "blist" ->ₛ "next")) # Ptr  |-> p_current_2)
  **  (sllseg (ind + (ind * sizeof(PTR) ) ) p_current_2 l_prev )
  **  ((&((p_current_2)  # "blist" ->ₛ "key")) # Ptr  |-> key_addr)
  **  (store_string key_addr k_list_current )
  **  (sll p_current_2 l_res )
  **  (store_map store_sll b0 )
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top_2)
  **  (dll h_top_2 0 l )
  **  (IntArray.full h_bucks_2 211 lh )
  **  (store_string key k )
  **  (store_map store_name m ))
.

Definition hashtbl_findref_return_wit_1 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (h_top: Z) (k_list_current: (@list Z)) (key_addr: Z) (l_resres: (@list Z)) (p_current: Z) (i: Z) (buck: Z) (l_res: (@list Z)) (key: Z) (l_prev: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (ind: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (retval: Z) (x: Z) (l0_2: (@list Z)) (y: Z) ,
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
  &&  [| ((b0 (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (l_res = (cons (p_current) (l_resres))) |]
  &&  ((&((p_current)  # "blist" ->ₛ "next")) # Ptr  |-> buck)
  **  (sll y l0_2 )
  **  (store_string key k )
  **  (store_string key_addr k_list_current )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> p_current)
  **  ((i) # Ptr  |-> y)
  **  (sllseg (ind + (ind * sizeof(PTR) ) ) p_current l_prev )
  **  ((&((p_current)  # "blist" ->ₛ "key")) # Ptr  |-> key_addr)
  **  (store_map store_sll b0 )
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
  **  (IntArray.full h_bucks 211 lh )
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
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (h_top: Z) (h_bucks: Z) (h: Z) (i_v: Z) (i: Z) (buck: Z) (l_res: (@list Z)) (key: Z) (l_prev: (@list Z)) (l0: (@list Z)) (ind: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) ,
  [| (i_v = 0) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((ind + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (i_v = 0) |] 
  &&  [| (l_res = nil) |]
  &&  (((ind + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((i) # Ptr  |-> i_v)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllseg (h_bucks + (ind * sizeof(PTR) ) ) i_v l_prev )
  **  (store_map store_sll b0 )
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
  **  (IntArray.full h_bucks 211 lh )
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
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (h_top: Z) (k_list_current: (@list Z)) (key_addr: Z) (l_resres: (@list Z)) (p_current: Z) (i: Z) (buck: Z) (l_res: (@list Z)) (key: Z) (l_prev: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (ind: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) ,
  [| (p_current = 0) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (l_res = (cons (p_current) (l_resres))) |]
  &&  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((i) # Ptr  |-> p_current)
  **  (sllseg (ind + (ind * sizeof(PTR) ) ) p_current l_prev )
  **  ((&((p_current)  # "blist" ->ₛ "key")) # Ptr  |-> key_addr)
  **  (store_string key_addr k_list_current )
  **  (sll p_current l_res )
  **  (store_map store_sll b0 )
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
  **  (IntArray.full h_bucks 211 lh )
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
  **  (IntArray.full h_bucks 211 lh )
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
  **  (IntArray.full h_bucks 211 lh )
  **  (store_map store_sll b0 )
  **  (store_map store_name m )
.

Definition hashtbl_findref_partial_solve_wit_3 := 
forall (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (h_top: Z) (k_list_current: (@list Z)) (key_addr: Z) (l_resres: (@list Z)) (p_current: Z) (i: Z) (buck: Z) (l_res: (@list Z)) (key: Z) (l_prev: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (ind: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) ,
  [| (p_current <> 0) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (l_res = (cons (p_current) (l_resres))) |]
  &&  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((i) # Ptr  |-> p_current)
  **  (sllseg (ind + (ind * sizeof(PTR) ) ) p_current l_prev )
  **  ((&((p_current)  # "blist" ->ₛ "key")) # Ptr  |-> key_addr)
  **  (store_string key_addr k_list_current )
  **  (sll p_current l_res )
  **  (store_map store_sll b0 )
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
  **  (IntArray.full h_bucks 211 lh )
  **  (store_string key k )
  **  (store_map store_name m )
|--
  [| (p_current <> 0) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (l_res = (cons (p_current) (l_resres))) |]
  &&  (store_string key k )
  **  (store_string key_addr k_list_current )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((i) # Ptr  |-> p_current)
  **  (sllseg (ind + (ind * sizeof(PTR) ) ) p_current l_prev )
  **  ((&((p_current)  # "blist" ->ₛ "key")) # Ptr  |-> key_addr)
  **  (sll p_current l_res )
  **  (store_map store_sll b0 )
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
  **  (IntArray.full h_bucks 211 lh )
  **  (store_map store_name m )
.

Definition hashtbl_findref_partial_solve_wit_4 := 
forall (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (h_top: Z) (k_list_current: (@list Z)) (key_addr: Z) (l_resres: (@list Z)) (p_current: Z) (i: Z) (buck: Z) (l_res: (@list Z)) (key: Z) (l_prev: (@list Z)) (h_bucks: Z) (h: Z) (l0: (@list Z)) (ind: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_list_current) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (contain_all_addrs m l ) |] 
  &&  [| (repr_all_heads lh b0 ) |] 
  &&  [| (contain_all_correct_addrs m b0 ) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| ((b0 (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (l_res = (cons (p_current) (l_resres))) |]
  &&  (store_string key k )
  **  (store_string key_addr k_list_current )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((i) # Ptr  |-> p_current)
  **  (sllseg (ind + (ind * sizeof(PTR) ) ) p_current l_prev )
  **  ((&((p_current)  # "blist" ->ₛ "key")) # Ptr  |-> key_addr)
  **  (sll p_current l_res )
  **  (store_map store_sll b0 )
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
  **  (IntArray.full h_bucks 211 lh )
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
  &&  [| ((b0 (ind)) = (Some ((pair ((h_bucks + (ind * sizeof(PTR) ) )) (l0))))) |] 
  &&  [| (not_key key l_prev ) |] 
  &&  [| (l0 = (app (l_prev) (l_res))) |] 
  &&  [| (p_current <> 0) |] 
  &&  [| (l_res = (cons (p_current) (l_resres))) |]
  &&  ((&((p_current)  # "blist" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y l0_2 )
  **  (store_string key k )
  **  (store_string key_addr k_list_current )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR) ) )) # Ptr  |-> buck)
  **  ((i) # Ptr  |-> p_current)
  **  (sllseg (ind + (ind * sizeof(PTR) ) ) p_current l_prev )
  **  ((&((p_current)  # "blist" ->ₛ "key")) # Ptr  |-> key_addr)
  **  (store_map store_sll b0 )
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> h_top)
  **  (dll h_top 0 l )
  **  (IntArray.full h_bucks 211 lh )
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
  **  (IntArray.full h_bucks 211 lh )
  **  (store_map store_sll b0 )
  **  (store_map store_name m )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.
Include hashtbl_Strategy_Correct.

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

End VC_Correct.
