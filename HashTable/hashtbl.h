
struct blist {
  char *key;
  unsigned int val;
  /* for elements with the same hash */
  struct blist *next;
  /* for traversing the whole table */
  struct blist *down;
  struct blist *up;
};

struct hashtbl {
  struct blist **bucks;
  struct blist *top;
};

unsigned int *hashtbl_findref(struct hashtbl *h, char * key);
/* do not free anything */
unsigned int hashtbl_remove(struct hashtbl *h, char * key, int *removed);
void free_hashtbl(struct hashtbl *h);

void free_blist_array(struct blist **i);
void free_blist(struct blist *b);
void free_hashtbl(struct hashtbl *h);
unsigned int hash_string(char *key);
int string_equal(char *k1, char *k2);
