#include "verification_stdlib.h"
#include "verification_list.h"
#include "hashtbl.h"
#include "../qcp-binary-democases/QCP_examples/int_array_def.h"
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
               (store_map: {A} {B} -> (A -> B -> Assertion) -> (A -> option B) -> Assertion)
               (store_hashtbl: Z -> (list Z -> option Z) -> Assertion)
               (hash_string_coq: list Z -> Z)
               (not_key: list Z -> list Z -> (list Z -> option Z) -> Prop)
               (pair: {A} {B} -> A -> B -> A * B)
               (store_map_missing_i: {A} {B} -> (A -> B -> Assertion) -> (A -> option B) -> (A) -> Assertion)
 */

/*@ include strategies "hashtbl.strategies" */
int NBUCK = 211;

void free_string(char *key)
/*@
  With p k m1 m2 v
  Require map_composable(m1, m2) &&
          store_map(store_name, m1) *
          store_map(store_uint, m2) *
          store_string(key, k) *
          store_ptr(&(p->key), key) *
          store_uint(&(p->val), v)
  Ensure map_composable(m1, m2) &&
        store_map(store_name, KP::remove_map(m1, k))*
        store_map(store_uint, PV::remove_map(m2, p))
*/
;

void free_blist_array(struct blist **i)
/*@ With lh
  Require PtrArray::full(i, 211, lh) 
  Ensure emp
*/;

void free_blist(struct blist *b)
/*@ 
  Require has_ptr_permission(&(b -> up)) *
          has_ptr_permission(&(b -> down)) *
          has_ptr_permission(&(b -> next))
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
/*@ With k1_list k2_list
  Require store_string(k1, k1_list)*
          store_string(k2, k2_list)
  Ensure  store_string(k1, k1_list)*
          store_string(k2, k2_list) *
          ((__return == 1 && k1 == k2 && k1_list == k2_list) ||
          (__return == 0 && k1 != k2 && k1_list != k2_list))
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
        exists l lh b0, 
        contain_all_addrs(m, l) && 
        repr_all_heads(lh, b0) && 
        contain_all_correct_addrs(m, b0) && 
        dll(&h->top, (void*) 0, l) * 
        PtrArray::full(h->bucks, 211, lh) * 
        store_map(store_sll, b0)*
        store_map(store_name, m)
  */
  ind = hash_string(key) % 211;
  i = &h->bucks[ind];
  /*@ Inv Assert
      exists l l0 l_prev l_res lh b0,
      ind == hash_string_coq(k) % 211 &&
      contain_all_addrs(m, l) && 
      repr_all_heads(lh, b0) && 
      contain_all_correct_addrs(m, b0) && 
      0 <= ind && ind < 211 &&
      b0(ind) == Some(pair(Znth (ind, lh, 0),l0)) &&
      l0 == app(l_prev, l_res) &&
      not_key(k, l_prev, m) &&
      key == key@pre &&
      sllseg((Znth (ind, lh, 0)), *i, l_prev) *
      sll (*i, l_res) *
      store_map_missing_i(store_sll, b0, ind)*
      dll(&h->top, (void*) 0, l) * 
      store_ptr(&(h->bucks[ind]),(Znth (ind, lh, 0))) *
      PtrArray::missing_i( h->bucks, ind, 0, 211, lh) *
      store_string(key, k) *
      store_map(store_name, m)
  */
  for (; *i != (void *) 0; i = &(*i)->next){
    /*@ exists l0 b0 l_res l_prev lh,
        *i != 0 && 
        b0(ind) == Some(pair((Znth (ind, lh, 0)),l0))&& 
        contain_all_correct_addrs(m, b0) && 
        l0 == app(l_prev, l_res) &&
        store_map(store_name, m) *
        sllseg((Znth (ind, lh, 0)), *i, l_prev) *
        sll(*i, l_res)
    which implies
        exists p_current key_addr k_list_current l_resres p_next,
          p_current != 0 &&
          b0(ind) == Some(pair((Znth (ind, lh, 0)),l0)) &&
          contain_all_correct_addrs(m, b0) && 
          m (k_list_current) == Some (&p_current->val) &&
          l0 == app(l_prev, l_res) &&
          l_res == cons(p_current, l_resres) &&
          store_ptr(i, p_current) *
          sllseg((Znth (ind, lh, 0)), p_current, l_prev) *
          store_ptr(&(p_current->next), p_next) *
          sll(p_next, l_resres) *
          data_at(&(p_current->key), key_addr) *
          store_string(key_addr, k_list_current) *
          store_map_missing_i(store_name, m, k_list_current)
    */
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

// unsigned int hashtbl_remove(struct hashtbl *h, char *key, int *removed)
// /*@
//   With m1 m2 k
//   Require map_composable(m1, m2) &&
//           store_hash_skeleton(h, m1) *
//           store_map(store_uint, m2) *
//           store_string(key, k) *
//           has_int_permission(removed)
//   Ensure store_hash_skeleton(h, KP::remove_map(m1, k)) *
//          store_string(key, k) *
//          ((exists p v key0,
//              m1(k) == Some(&(p -> val)) &&
//              m2(&(p -> val)) == Some(v) && __return == v &&
//              store_int(removed, 1) *
//              store_map(store_uint, PV::remove_map(m2, p)) *
//              store_ptr(&(p -> key), key0) * store_string(key0, k) *
//              has_ptr_permission(&(p -> up)) *
//              has_ptr_permission(&(p -> down)) *
//              has_ptr_permission(&(p -> next)) *
//              store_uint(&(p -> val), v)) ||
//           (m1(k) == None && __return == 0 &&
//            store_int(removed, 0) * store_map(store_uint, m2)))
// */
// {
//   unsigned int ind;
//   struct blist **it;
//   /*@ store_hash_skeleton(h, m1)
//       which implies
//         exists l lh b, 
//         contain_all_addrs(m1, l) && 
//         repr_all_heads(lh, b) && 
//         contain_all_correct_addrs(m1, b) && 
//         dll(h->top, (void*) 0, l) * 
//         PtrArray::full(h->bucks, 211, lh) * 
//         store_map(store_sll, b)*
//         store_map(store_name, m1)
//   */
//   ind = hash_string(key) % 211;
//   /*@ Inv Assert
//       exists l l0 lh b l_prev l_res k_list k0 buck dl_up dl_down val,
//       map_composable(m1, m2) &&
//       not_key(key, l_prev, m2) &&
//       0 <= ind && ind < 211 &&
//       contain_all_addrs(m1, l) && 
//       repr_all_heads(lh, b) && 
//       contain_all_correct_addrs(m1, b) && 
//       b(ind) == Some(pair(&(h->bucks[ind]),l0)) &&
//       l0 == app(l_prev, l_res) &&
//       l == app(dl_up, dl_down) &&
//       m1(k_list) == Some(&(*it)->val) &&
//       sllseg(buck, (*it), l_prev) *
//       sll((*it), l_res) *
//       store(&h->bucks[ind], buck) *
//       dllseg(h->top, (*it), (void*) 0, (*it)->up, dl_up) *
//       dll((*it), (*it)->up, dl_down) *
//       store_ptr((*it)->up->down, (*it)) *
//       store_ptr((*it)->down->up, (*it)) *
//       store_uint(&(*it)->val, val) *
//       store_ptr(&(*it)->key, k0) *
//       store_string(k0, k_list) *
//       has_int_permission(removed) *
//       store_map(store_name, m1) *
//       store_map(store_uint, m2) *
//       store_string(key, k)
//   */
//   for (it = &h->bucks[ind]; *it != (void *) 0; it = &(*it)->next) {
//     struct blist *b = *it;
//     if (string_equal(key, b->key)) {
//       if (h->top == b)
//         h->top = b->down;
//       if (b->up != (void *) 0)
//         b->up->down = b->down;
//       if (b->down != (void *) 0)
//         b->down->up = b->up;

//       *it = b->next;
//       unsigned int res = b->val;
//       free_string(b->key);
//       free_blist(b);
//       *removed = 1;
//       return res;
//     }
//   }
//   *removed = 0;
//   return 0;
// }

// void hashtbl_free_blist(struct blist *bl)
// /*@
//   With l ls m1 m2 lh b h lhx k key v
//   Require map_composable(m1, m2) &&
//           contain_all_addrs(m1, l) && 
//           repr_all_heads(lh, b) && 
//           contain_all_correct_addrs(m1, b) && 
//           dll(h->top, (void*) 0, l) * 
//           sll(lhx, ls) *
//           store_map(store_name, m1) *
//           store_map(store_uint, m2) *
//           (bl == (void*) 0 ||
//           (bl != (void *) 0 &&
//           store_ptr(&(bl->key), key) *
//           store_string(key, k) *
//           store_uint(&(bl->val), v)))
//   Ensure exists l0 l_up l_down l1 ls0 ls1 k,
//           map_composable(m1, m2) &&
//           contain_all_addrs(m1, l1) && 
//           repr_all_heads(lh, b) && 
//           contain_all_correct_addrs(m1, b) && 
//           ((bl != (void *) 0 &&
//           l0 == app(l_up, l_down) &&
//           l1 == cons(bl, l_down) &&
//           l == app(l_up, l1) &&
//           ls1 == cons(bl, nil) &&
//           ls == app(ls0, ls1) &&
//           sll(lhx, ls0) *
//           dll(h->top, (void*) 0, l0) * 
//           store_map(store_name, KP::remove_map(m1, k)) *
//           store_map(store_uint, PV::remove_map(m2, bl))) ||
//           (bl == (void *) 0 && 
//           dll(h->top, (void*) 0, l) * 
//           sll(lhx, ls) *
//           store_map(store_name, m1) *
//           store_map(store_uint, m2)))
// */
// {
//   if (bl != (void *) 0) {
//     /*@ bl != 0 
//         which implies
//         exists key k v,
//         store_ptr(&(bl->key), key) *
//         store_string(key, k) *
//         store_uint(&(bl->val), v)
//     */
//     hashtbl_free_blist(bl->next);
//     free_string(bl -> key);
//     free_blist(bl);
//   }
// }

// void hashtbl_clear(struct hashtbl *h)
// /*@
//   With m1 m2
//   Require map_composable(m1, m2) &&
//           store_hash_skeleton(h, m1) *
//           store_map(store_uint, m2)
//   Ensure has_ptr_permission(&(h->bucks)) * 
//          has_ptr_permission(&(h->top)) *
//          store_map(store_name, m1) * 
//          store_map(store_uint, m2)
// */ 
// {
//   /*@ store_hash_skeleton(h, m1)
//       which implies
//         exists l lh b, 
//         contain_all_addrs(m1, l) && 
//         repr_all_heads(lh, b) && 
//         contain_all_correct_addrs(m1, b) && 
//         dll(h->top, (void*) 0, l) * 
//         PtrArray::full(h->bucks, 211, lh) * 
//         store_map(store_sll, b)*
//         store_map(store_name, m1)
//   */
//   int i;
//   /*@ Inv Assert
//       exists li k buck lh,
//       map_composable(m1, m2) &&
//       sll(buck, li) *
//       store_map(store_name, m1) *
//       store_map(store_uint, m2) *
//       store_string(buck->key, k) *
//       store(&h->bucks[i], buck) *
//       PtrArray::full(h->bucks, 211, lh) *
//       has_ptr_permission(h->top)
//   */
//   for (i = 0; i < 211; i++) {
//     hashtbl_free_blist(h->bucks[i]);
//     h->bucks[i] = (void *) 0;
//   }

//   free_blist_array(h->bucks);
//   h->bucks = (void *) 0;
//   h->top = (void *) 0;
// }

// void free_hashtbl(struct hashtbl *h)
// /*@
//   With m1 m2
//   Require map_composable(m1, m2) &&
//           store_hash_skeleton(h, m1) *
//           store_map(store_uint, m2)
//   Ensure emp
// */
// {
//   hashtbl_clear(h);
//   free_hashtbl_struct(h);
// }