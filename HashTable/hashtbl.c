#include "verification_stdlib.h"
#include "verification_list.h"
#include "hashtbl.h"
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
 */

int NBUCK = 211;

void free_string(char *key)
/*@
  With k m1
  Require store_map(store_name, m1) *
          store_string(key, k)
  Ensure store_map(store_name, KP::remove_map(m1, k))
*/
;

void free_blist_array(struct blist **i)
/*@
  Require exists q, data_at(i, struct blist*, q)
  Ensure emp
*/;

void free_blist(struct blist *b)
/*@
  Require exists k v,
            store_ptr(&(b -> key),k) *
            store_uint(&(b -> val), v) *
            has_ptr_permission(&(b -> next)) *
            has_ptr_permission(&(b -> up)) *
            has_ptr_permission(&(b -> down))
  Ensure emp
*/;

unsigned int hash_string(char *key)
/*@
  With k m1
  Require store_string(key, k) *
          store_map(store_name, m1)
  Ensure store_string(key, k) *
          store_map(store_name, KP::insert_map(m1, k, hash_string_coq(k)))
          && (__return == (hash_string_coq(k)))
*/;

int string_equal(char *k1, char *k2)
/*@
  With k1_list k2_list
  Require store_string(k1, k1_list) * 
            store_string(k2, k2_list) 
  Ensure store_string(k1, k1_list) * 
           store_string(k2, k2_list) * 
           ((__return == 1 && k1_list == k2_list) ||
           (__return == 0 && k1_list != k2_list))
*/;
void free_hashtbl_struct(struct hashtbl *h)
/*@
  With m_buck m_val k_list
  Require has_ptr_permission(&(h->bucks)) * 
          has_ptr_permission(&(h->top)) *
          (exists q1, data_at(h, struct hashtbl*, q1)) * 
          (exists q2, data_at(&(h->bucks), struct blist**, q2)) *
          store_hash_skeleton(h, m_buck) *
          store_map(store_uint, m_val) * 
          store_map(store_name, k_list)
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

  ind = hash_string(key) % NBUCK;
  for (i = &h->bucks[ind]; *i != (void *) 0; i = &(*i)->next)
    if (string_equal(key, (*i)->key)) {
      struct blist *b = *i;
      // LRU
      *i = b->next;
      b->next = h->bucks[ind];
      h->bucks[ind] = b;

      return &b->val;
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

  ind = hash_string(key) % NBUCK;
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
  return (void*) 0;
}

void hashtbl_free_blist(struct blist *bl)
/*@
  With l m1 m2
  Require sll(bl, l) *
          store_map(store_name, m1) *
          store_map(store_uint, m2) *
          (exists k v,
            store_ptr(&(bl -> key),k) *
            store_uint(&(bl -> val), v) *
            has_ptr_permission(&(bl -> next)) *
            has_ptr_permission(&(bl -> up)) *
            has_ptr_permission(&(bl -> down)))
  Ensure emp
*/
{ 
  if (bl != (void *) 0) {
    hashtbl_free_blist(bl->next);
    free_string(bl -> key);
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

  for (i = 0; i < NBUCK; i++) {
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