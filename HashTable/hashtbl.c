#include "verification_stdlib.h"
#include "verification_list.h"
#include "hashtbl_def.h"
#include "../qcp-binary-democases/QCP_examples/ptr_array_def.h"
/*@ Import Coq Require Import hashtbl_lib */

/*@ Extern Coq (sll : Z -> list Z -> Assertion)
               (sllseg: Z -> Z -> list Z -> Assertion)
               (sllbseg: Z -> Z -> list Z -> Assertion)
               (dll: Z -> Z -> list Z -> Assertion)
               (dllseg: Z -> Z -> Z -> Z -> list Z -> Assertion)
               (store_string: Z -> list Z -> Assertion)
               (store_sll: Z -> (Z * list Z) -> Assertion)
               (store_name: list Z -> Z -> Assertion)
               (contain_all_addrs: (list Z -> option Z) -> list Z -> Prop)
               (repr_all_heads: list Z -> (Z -> option (Z * list Z)) -> Prop)
               (contain_all_correct_addrs: (list Z -> option Z) -> (Z -> option (Z * list Z)) -> Prop)
               (store_hash_skeleton: Z -> (list Z -> option Z) -> Assertion)
               (map_compose: (list Z -> option Z) -> (Z -> option Z) -> (Z -> option Z) -> Prop)
               (map_composable: (list Z -> option Z) -> (Z -> option Z) -> Prop)
               (empty_map: {A} {B} -> A -> option B)
               (KP::insert_map: (list Z -> option Z) -> list Z -> Z -> (list Z -> option Z))
               (KP::remove_map: (list Z -> option Z) -> list Z -> (list Z -> option Z))
               (PV::insert_map: (Z -> option Z) -> Z -> Z -> (Z -> option Z))
               (PV::remove_map: (Z -> option Z) -> Z -> (Z -> option Z))
               (KP::remove_keys: (list Z -> option Z) -> list (list Z) -> (list Z -> option Z))
               (PV::remove_addrs: (Z -> option Z) -> list Z -> (Z -> option Z))
               (store_map: {A} {B} -> (A -> B -> Assertion) -> (A -> option B) -> Assertion)
               (store_map_missing_i: {A} {B} -> (A -> B -> Assertion) -> (A -> option B) -> A -> Assertion)
               (store_map_missing_first_i_Z: {B} -> (Z -> B -> Assertion) -> (Z -> option B) -> Z -> Assertion)
               (store_hashtbl: Z -> (list Z -> option Z) -> Assertion)
               (hash_string_coq: list Z -> Z)
               (not_key: Z -> list Z -> Prop)
               (pair: {A} {B} -> A -> B -> A * B)
 */

/*@ include strategies "hashtbl.strategies" */

int NBUCK = 211;

void free_string(char *key)
/*@
  With p m1 m2 k
  Require map_composable(m1, m2) &&
          store_map(store_name, m1) *
          store_map(store_uint, m2) *
          store_string(key, k) *
          store_ptr(&(p->key), key)
  Ensure map_composable(m1, m2) &&
        store_map(store_name, m1)*
        store_map(store_uint, m2)
*/
;

void free_blist_array(struct blist **i)
/*@ With lh
  Require PtrArray::full(i, 211, lh) 
  Ensure emp
*/;

void free_blist(struct blist *b)
/*@
  Require has_ptr_permission(&(b -> next))
  Ensure emp
*/;

unsigned int hash_string(char *key)
/*@
  With k
  Require store_string(key, k)
  Ensure store_string(key, k)
          && (__return == (hash_string_coq(k)))
*/;

int string_equal(char *k1, char *k2)
/*@
  With k1_list k2_list
  Require store_string(k1, k1_list) * 
          store_string(k2, k2_list) 
  Ensure store_string(k1, k1_list) * 
           store_string(k2, k2_list) * 
           ((__return == 1 && k1 == k2 && k1_list == k2_list) ||
           (__return == 0 && k1 != k2 && k1_list != k2_list))
*/;

void free_hashtbl_struct(struct hashtbl *h)
/*@
  With l m1 m2
  Require store(&h->top, 0) *
          store(&h->bucks, 0) *
          dll(&h->top, (void*) 0, l) *
          store_map(store_name, m1) *
          store_map(store_uint, m2)
  Ensure emp
*/;

unsigned int *hashtbl_findref(struct hashtbl *h, char *key)
/*@
  With m k
  Require store_hash_skeleton(h, m) *
          store_string(key, k)
  Ensure store_hash_skeleton(h, m) *
         store_string(key, k) *
         ((exists p, m(k) == Some(p) && __return == p) ||
          (m(k) == None && __return == (void *) 0))
*/
{
  unsigned int ind;
  struct blist **i;
  /*@ store_hash_skeleton(h, m)
      which implies
        exists l lh b bucks, 
        contain_all_addrs(m, l) && 
        repr_all_heads(lh, b) && 
        contain_all_correct_addrs(m, b) && 
        dll(&h->top, (void*) 0, l) * 
        PtrArray::full(&h->bucks, 211, lh) * 
        store(&h->bucks, bucks) *
        store_map(store_sll, b)*
        store_map(store_name, m)
  */
  ind = hash_string(key) % 211;
  i = &h->bucks[ind];
  /*@ Inv Assert
      exists l_prev l_res k_list buck,
      not_key(key, l_prev) &&
      0 <= ind && ind < 211 &&
      sllseg(buck, (*i), l_prev) *
      sll((*i)->next, l_res) *
      store_string((*i)->key, k_list) *
      store_string(key, k) *
      store_map(store_name, m)*
      store(&h->bucks[ind], buck)
  */
  //Inv的最后三句是为了string_equal,*i = b->next和b->next = h->bucks[ind]不会报错
  for (; *i != (void *) 0; i = &(*i)->next){
    if (string_equal(key, (*i)->key)) {
      struct blist *b = *i;
      // LRU
      *i = b->next;
      b->next = h->bucks[ind];
      h->bucks[ind] = b;
      return &b->val;
    }
  }
  return (void *) 0;
}


unsigned int hashtbl_remove(struct hashtbl *h, char *key, int *removed)
/*@
  With m1 m2 k
  Require map_composable(m1, m2) &&
          store_hash_skeleton(h, m1) *
          store_map(store_uint, m2) *
          store_string(key, k) *
          has_int_permission(removed)
  Ensure store_hash_skeleton(h, m1) *
         store_string(key, k) *
         ((exists p v key0,
             m1(k) == Some(&(p -> val)) &&
             m2(&(p -> val)) == Some(v) && __return == v &&
             store_int(removed, 1) *
             store_map(store_uint, m2) *
             store_ptr(&(p -> key), key0) * 
             store_string(key0, k) *
             has_ptr_permission(p -> up) *
             has_ptr_permission(p -> down) *
             has_ptr_permission(p->up->down) *
             has_ptr_permission(p->down->up) *
             has_ptr_permission(h->top) *
             has_ptr_permission(p->next) *
             store_uint(&(p -> val), v)) ||
          (m1(k) == None && __return == 0 &&
           store_int(removed, 0) * store_map(store_uint, m2)))
*/
{
  unsigned int ind;
  struct blist **it;
  /*@ store_hash_skeleton(h, m1)
      which implies
        exists l lh b, 
        contain_all_addrs(m1, l) && 
        repr_all_heads(lh, b) && 
        contain_all_correct_addrs(m1, b) && 
        dll(&h->top, (void*) 0, l) * 
        PtrArray::full(h->bucks, 211, lh) * 
        store_map(store_sll, b)*
        store_map(store_name, m1)
  */
  ind = hash_string(key) % 211;
  /*@ Inv Assert
      exists l_prev l_res k_list buck dl_up dl_down val lh b itv,
      not_key(key, l_prev) &&
      0 <= ind && ind < 211 &&
      contain_all_addrs(m1, app(dl_up, dl_down)) && 
      repr_all_heads(lh, b) && 
      contain_all_correct_addrs(m1, b) && 
      (h == h@pre) &&
      (key == key@pre) &&
      store(it, itv) *
      store_map_missing_i(store_sll, b, ind) *
      sllseg(buck, itv, l_prev) *
      sll(itv, l_res) *
      store_string(key, k) *
      store(&h@pre->bucks[ind], buck) *
      PtrArray::missing_i(h@pre->bucks, ind, 0, 211, lh) *
      store_map(store_name, m1) *
      dllseg(&h->top, it, (void*) 0, &(itv->up), dl_up) *
      dll(it, &(itv->up), dl_down) *
      has_int_permission(removed) *
      store_string(itv->key, k_list) *
      has_ptr_permission(itv->up) *
      has_ptr_permission(itv->down) *
      has_ptr_permission(itv->up->down) *
      has_ptr_permission(itv->down->up) *
      has_ptr_permission(h->top) *
      has_ptr_permission(itv->next) *
      store(&(itv->val), val) *
      store_map(store_uint, m2)
  */
  for (it = &h->bucks[ind]; *it != (void *) 0; it = &(*it)->next) {
    struct blist *b = *it;
    if (string_equal(key, b->key)) {
      if (h->top == b)
        h->top = b->down;
      if (b->up != (void *) 0)
        b->up->down = b->down;
      if (b->down != (void *) 0)
        b->down->up = b->up;

      *it = b->next;
      unsigned int res = b->val;
      free_blist(b);
      *removed = 1;
      return res;
    }
  }
  *removed = 0;
  return 0;
}

void hashtbl_free_blist(struct blist *bl)
/*@
  With l m1 m2
  Require map_composable(m1, m2) &&
          sll(bl, l) *
          store_map(store_name, m1) *
          store_map(store_uint, m2) 
  Ensure (map_composable(m1, m2) &&
          store_map(store_name, m1) *
          store_map(store_uint, m2)
          )
*/
{
  if (bl != (void *) 0) {
    /*@ sll(bl, l) && bl != (void *) 0
        which implies
        exists l1 k1,
        sll(bl->next, l1) *
        store_string(bl->key, k1)
    */
    hashtbl_free_blist(bl->next);
    free_string(bl -> key);
    free_blist(bl);
  }
}

void hashtbl_clear(struct hashtbl *h)
/*@
  With m1 m2 top
  Require map_composable(m1, m2) &&
          store_hash_skeleton(h, m1) *
          store_map(store_uint, m2) *
          store(&h->top, top)
  Ensure exists l,
         store(&h->bucks, 0) * 
         store(&h->top, 0) *
         dll(&h->top, (void*) 0, l) *
         store_map(store_name, m1) *
        store_map(store_uint, m2)
*/ 
{
  /*@ store_hash_skeleton(h, m1)
      which implies
        exists lh b l, 
        contain_all_addrs(m1, l) && 
        repr_all_heads(lh, b) && 
        repr_all_heads(lh, b) &&
        contain_all_correct_addrs(m1, b) && 
        dll(&h->top, (void*) 0, l) * 
        PtrArray::full(h->bucks, 211, lh) * 
        store_map(store_sll, b)*
        store_map(store_name, m1)
  */
  int i = 0;
  /*@ Inv Assert
      exists li buck_i lh b l,
      map_composable(m1, m2) &&
      repr_all_heads(lh, b) &&
      store(&h@pre->top, top) *
      store(&h, h@pre) *
      dll(&h->top, (void*) 0, l) *
      ((i >= 0 && i < 211 &&
      PtrArray::missing_i(h@pre->bucks, i, 0, 211, lh) *
      store_map_missing_first_i_Z(store_sll, b, i) *
      store_map(store_name, m1) *
      store_map(store_uint, m2) *
      store(&h@pre->bucks[i], buck_i) *
      sll(buck_i, li)) || 
      (i >= 211 && 
      store_map(store_name, m1) *
      store_map(store_uint, m2) *
      PtrArray::full(h@pre->bucks, 211, lh)))
  */
  for (i = 0; i < 211 && i >= 0; i++) {
    hashtbl_free_blist(h->bucks[i]);
    h->bucks[i] = (void *) 0;
  }

  free_blist_array(h->bucks);
  h->bucks = (void *) 0;
  h->top = (void *) 0;
}

void free_hashtbl(struct hashtbl *h)
/*@
  With m1 m2 top
  Require map_composable(m1, m2) &&
          store_hash_skeleton(h, m1) *
          store_map(store_uint, m2) *
          store(&h->top, top)
  Ensure emp
*/
{
  hashtbl_clear(h);
  free_hashtbl_struct(h);
}
