#include "hashtbl.h"

void create_bucks(struct hashtbl *h) {
  int i;
  h->bucks = malloc_blist_array();
  for (i = 0; i < NBUCK; i++)
    h->bucks[i] = (void*) 0;
}

void init_hashtbl(struct hashtbl *h) {
  h->bucks = (void*) 0;
  h->top = (void*) 0;
  create_bucks(h);
}

struct hashtbl *create_hashtbl() {
  struct hashtbl *h;
  h = malloc_hashtbl();
  init_hashtbl(h);
  return h;
}

void hashtbl_add(struct hashtbl *h, char *key, unsigned int val) {
  unsigned int ind;
  struct blist *buc;
  ind = hash_string(key) % NBUCK;
  buc = malloc_blist();
  buc->key = key;
  buc->val = val;

  buc->up = (void*) 0;
  buc->down = h->top;
  if (h->top != (void*) 0)
    h->top->up = buc;
  h->top = buc;

  buc->next = h->bucks[ind];
  h->bucks[ind] = buc;
}

unsigned int hashtbl_find(struct hashtbl *h, char *key, int *valid) {
  unsigned int ind;
  struct blist **i;

  ind = hash_string(key) % NBUCK;
  for (i = &h->bucks[ind]; *i != (void*) 0; i = &(*i)->next)
    if (string_equal(key, (*i)->key)) {
      struct blist *b = *i;

      *i = b->next;
      b->next = h->bucks[ind];
      h->bucks[ind] = b;

      *valid = 1;
      return b->val;
    }
  *valid = 0;
  return 0;
}

unsigned int *hashtbl_findref(struct hashtbl *h, char *key) {
  unsigned int ind;
  struct blist **i;

  ind = hash_string(key) % NBUCK;
  for (i = &h->bucks[ind]; *i != (void*) 0; i = &(*i)->next)
    if (string_equal(key, (*i)->key)) {
      struct blist *b = *i;
      // LRU
      *i = b->next;
      b->next = h->bucks[ind];
      h->bucks[ind] = b;

      return &b->val;
    }
  return (void*) 0;
}


unsigned int hashtbl_remove(struct hashtbl *h, char *key, int *removed) {
  unsigned int ind;
  struct blist **it;

  ind = hash_string(key) % NBUCK;
  for (it = &h->bucks[ind]; *it != (void*) 0; it = &(*it)->next) {
    struct blist *b = *it;
    if (string_equal(key, b->key)) {
      if (h->top == b)
        h->top = b->down;

      if (b->up != (void*) 0)
        b->up->down = b->down;
      if (b->down != (void*) 0)
        b->down->up = b->up;

      *it = b->next;
      unsigned int res = b->val;
      free_blist(b);
      *removed = 1;
      return res;
    }
  }
  *removed = 0;
  return (void*) 0;
}

void hashtbl_free_blist(struct blist *bl) {
  if (bl != (void*) 0) {
    hashtbl_free_blist(bl->next);
    free_string(bl -> key);
    free_blist(bl);
  }
}

void hashtbl_clear(struct hashtbl *h) {
  int i;

  for (i = 0; i < NBUCK; i++) {
    hashtbl_free_blist(h->bucks[i]);
    h->bucks[i] = (void*) 0;
  }

  free_blist_array(h->bucks);
  h->bucks = (void*) 0;
  h->top = (void*) 0;
}

void free_hashtbl(struct hashtbl *h) {
  hashtbl_clear(h);
  free_hashtbl(h);
}

