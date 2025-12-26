#include "verification_stdlib.h"
#include "verification_list.h"
#include "hashtbl.h"
#include "../qcp-binary-democases/QCP_examples/int_array_def.h"
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
               (store_map: {A} {B} -> (A -> B -> Assertion) -> (A -> option B) -> Assertion)
               (store_hashtbl: Z -> (list Z -> option Z) -> Assertion)
               (hash_string_coq: list Z -> Z)
               (not_key: Z -> list Z -> Prop)
               (pair: {A} {B} -> A -> B -> A * B)
 */

/*@ include strategies "hashtbl.strategies" */

int NBUCK = 211;

void free_string(char *key)
/*@
  With p k m1 m2
  Require map_composable(m1, m2) &&
          store_map(store_name, m1) *
          store_map(store_uint, m2) *
          store_string(key, k) *
          store_ptr(&(p->key), key)
  Ensure map_composable(m1, m2) &&
        store_map(store_name, KP::remove_map(m1, k))*
        store_map(store_uint, PV::remove_map(m2, p))*
        store_string(key, k) *
        store_ptr(&(p->key), key)
*/
;

void free_blist_array(struct blist **i)
/*@ With lh
  Require IntArray::full(i, NBUCK, lh) 
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
  With k1_list k2_list m1
  Require store_map(store_name, m1) *
          store_string(k1, k1_list) * 
          store_string(k2, k2_list) 
  Ensure store_string(k1, k1_list) * 
           store_string(k2, k2_list) * 
           ((__return == 1 && m1(k1_list) == m1(k2_list)) ||
           (__return == 0 && m1(k1_list) != m1(k2_list)))
*/;

void free_hashtbl_struct(struct hashtbl *h)
/*@
  With m1 m2
  Require map_composable(m1, m2) &&
          has_ptr_permission(&(h->bucks)) * 
          has_ptr_permission(&(h->top)) *
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
        exists l lh b, 
        contain_all_addrs(m, l) && 
        repr_all_heads(lh, b) && 
        contain_all_correct_addrs(m, b) && 
        dll(h->top, (void*) 0, l) * 
        IntArray::full(h->bucks, 211, lh) * 
        store_map(store_sll, b)*
        store_map(store_name, m)
  */
  ind = hash_string(key) % 211;
  i = &h->bucks[ind];
  /*@ Inv Assert
      exists l_prev l_res k_list buck,
      not_key(key, l_prev) &&
      0 <= ind && ind < 211 &&
      sllseg(h->bucks[ind], (*i), l_prev) *
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
  Ensure store_hash_skeleton(h, KP::remove_map(m1, k)) *
         store_string(key, k) *
         ((exists p v key0,
             m1(k) == Some(&(p -> val)) &&
             m2(&(p -> val)) == Some(v) && __return == v &&
             store_int(removed, 1) *
             store_map(store_uint, PV::remove_map(m2, p)) *
             store_ptr(&(p -> key), key0) * store_string(key0, k) *
             has_ptr_permission(&(p -> up)) *
             has_ptr_permission(&(p -> down)) *
             has_ptr_permission(&(p -> next)) *
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
        dll(h->top, (void*) 0, l) * 
        IntArray::full(h->bucks, 211, lh) * 
        store_map(store_sll, b)*
        store_map(store_name, m1)
  */
  ind = hash_string(key) % 211;
  /*@ Inv Assert
      exists l_prev l_res k_list buck dl_up dl_down dl_mid val,
      not_key(key, l_prev) &&
      0 <= ind && ind < 211 &&
      sllseg(h->bucks[ind], (*it), l_prev) *
      sll((*it)->next, l_res) *
      store_string((*it)->key, k_list) *
      store_string(key, k) *
      store(&h->bucks[ind], buck) *
      dllseg(h->top, (*it), (void*) 0, (*it)->up, dl_up) *
      dllseg((*it)->up, (*it)->down, (*it)->up->up, (*it), dl_mid) *
      dll((*it)->down, (*it), dl_down) *
      store((*it)->up->down, (*it)) *
      store((*it)->down->up, (*it)) *
      store(&(*it)->val, val) *
      has_int_permission(removed) *
      store_map(store_name, m1)
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
  With l m k
  Require sll(bl, l) *
          store_map(store_name, m) *
          store_string(bl->key, k)
  Ensure (bl == (void *)0 && store_map(store_name, KP::remove_map(m, k)))
*/
{
  if (bl != (void *) 0) {
    /*@ sll(bl, l)
        which implies
        exists l1 k1,
        sll(bl->next, l1) *
        store_string(bl->next->key, k1)
    */
    free_blist(bl);
  }
}

void hashtbl_clear(struct hashtbl *h)
/*@
  With m1 m2
  Require map_composable(m1, m2) &&
          store_hash_skeleton(h, m1) *
          store_map(store_uint, m2)
  Ensure emp
*/ 
{
  int i;
  /*@ Inv Assert
      exists li k buck,
      sll(h->bucks[i], li) *
      store_map(store_name, m1) *
      store_string(h->bucks[i]->key, k) *
      store(&h->bucks[i], buck)
  */
  for (i = 0; i < 211; i++) {
    hashtbl_free_blist(h->bucks[i]);
    h->bucks[i] = (void *) 0;
  }

  free_blist_array(h->bucks);
  h->bucks = (void *) 0;
  h->top = (void *) 0;
}

void free_hashtbl(struct hashtbl *h)
/*@
  With m1 m2
  Require map_composable(m1, m2) &&
          store_hash_skeleton(h, m1) *
          store_map(store_uint, m2)
  Ensure emp
*/
{
  hashtbl_clear(h);
  free_hashtbl_struct(h);
}