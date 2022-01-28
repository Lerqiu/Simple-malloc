#include <assert.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stddef.h>
#include <unistd.h>

/*
Autor: Kamil Kasprzak 315591
Praca powstała w pełni samodzielnie bazując na materiałach przedstawianych
na wykładzie.

Idea to "Explicit Free Lists" z optymalizacjami:
https://skos.ii.uni.wroc.pl/pluginfile.php/42597/mod_resource/content/2/so21_wyklad_8b.pdf
<=> Główna idea
https://skos.ii.uni.wroc.pl/pluginfile.php/42596/mod_resource/content/3/so21_wyklad_8a.pdf
<=> optymalizacje
Oraz wskazówka przedstawiona przez wykładowcę na wykładzie (wspominająca o
częstym wykorzystaniu małych bloków do 128 bajtów)

Na początku sterty znajduje się struktura kubełków podzielona na dwa fragmenty:
1) Kubełki przechowujące bloki `log_2(wielkość obszaru)` (jest ich 25)
2) Kubełki przechowujące bloki `wielkość obszaru` (jest ich 8)

Kubełki posiadają w swojej strukturze strażników
*/

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.
 * When you hand in, remove the #define DEBUG line. */
// #define DEBUG
#ifdef DEBUG
#define debug(fmt, ...) printf("%s: " fmt "\n", __func__, __VA_ARGS__)
#define msg(...) printf(__VA_ARGS__)
#else
#define debug(fmt, ...)
#define msg(...)
#endif

#define __unused __attribute__((unused))

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* !DRIVER */

typedef uint32_t word_t; /* Heap is bascially an array of 4-byte words. */

typedef enum {
  FREE = 0,     /* Block is free */
  USED = 1,     /* Block is used */
  PREVFREE = 2, /* Previous block is free (optimized boundary tags) */
} bt_flags;

static word_t *heap_start; /* Address of the first block */
static word_t *heap_end;   /* Address past last byte of last block */
static word_t *eListStart; /* Start of buckets with elements  ~log_2 */
static word_t
  *eListStartSmall; /* Start of buckets with elements with identical size*/
static word_t *borderFreeBlock; /* Pointer to free block at end of heap */

/* --=[ boundary tag handling ]=-------------------------------------------- */

static inline size_t bt_size(word_t *bt) {
  return *bt & ~(USED | PREVFREE);
}

/* Returns address of next block. */
static inline word_t *bt_next(word_t *bt) {
  return bt + (bt_size(bt) >> 2);
}

/* Returns address of previous block. */
static inline word_t *bt_prev(word_t *bt) {
  return bt - (bt_size(bt - 1) >> 2);
}

static inline word_t bt_used(word_t *bt) {
  return *bt & USED;
}

static inline word_t bt_free(word_t *bt) {
  return !(*bt & USED);
}

/* Given boundary tag address calculate it's buddy address. */
static inline word_t *bt_footer(word_t *bt) {
  return (void *)bt + bt_size(bt) - sizeof(word_t);
}

/* Given payload pointer returns an address of boundary tag. */
static inline word_t *bt_fromptr(void *ptr) {
  return (word_t *)ptr - 1;
}

/* Creates boundary tag(s) for given block. */
static inline void bt_make(word_t *bt, size_t size, bt_flags flags) {
  *bt = size | flags;
}

/* Creates boundary tag(s) for given block. */
static inline void bt_make_free(word_t *bt, size_t size) {
  *bt = size;
  *(bt + (bt_size(bt) >> 2) - 1) = size;
}

/* Previous block free flag handling for optimized boundary tags. */
static inline bt_flags bt_get_prevfree(word_t *bt) {
  return *bt & PREVFREE;
}

static inline void bt_clr_prevfree(word_t *bt) {
  *bt &= ~PREVFREE;
}

static inline void bt_set_prevfree(word_t *bt) {
  *bt |= PREVFREE;
}

/* Returns address of payload. */
static inline void *bt_payload(word_t *bt) {
  return bt + 1;
}

/* --=[ miscellanous procedures ]=------------------------------------------ */

/* Calculates block size incl. header, footer & payload,
 * and aligns it to block boundary (ALIGNMENT). */
static inline size_t blksz(size_t size) {
  size_t header = sizeof(word_t);
  return ((header + size + 15) & ~15);
}

static void *morecore(size_t size) {
  void *ptr = mem_sbrk(size);
  if (ptr == (void *)-1)
    return NULL;
  return ptr;
}

/* --=[ explicit free lists procedures ]=--------------------------------- */

typedef enum {
  NEXT = 1, /* index to next block */
  PREV = 2, /* index to previous block */
} eList_direction;

static inline word_t *eList_getBucketBySize(word_t size) {
  if (size < 16 * 8) {
    return eListStartSmall + (8 * 2 - (size >> 3));
  }
  word_t bucket = __builtin_clz(size);
  return eListStart + (bucket << 1);
}

static inline word_t *eList_getBucket(word_t *header) {
  word_t size = bt_size(header);
  return eList_getBucketBySize(size);
}

static inline word_t eList_calculatePointer(word_t *header) {
  return ((unsigned long)header - (unsigned long)eListStart) >> 2;
}

static inline word_t *eList_get_pointer(word_t *header,
                                        eList_direction direction) {
  return header + direction;
}

static inline word_t *eList_get_elem(word_t *header,
                                     eList_direction direction) {
  return eListStart + *(header + direction);
}

static inline void eList_removeFromEList(word_t *header) {
  word_t *next = eList_get_elem(header, NEXT);
  word_t *prev = eList_get_elem(header, PREV);
  *(eList_get_pointer(prev, NEXT)) = eList_calculatePointer(next);
  *(eList_get_pointer(next, PREV)) = eList_calculatePointer(prev);
}

static inline void eList_add_toList(word_t *header) {
  word_t *first = eList_getBucket(header);

  word_t *next = eList_get_elem(first, NEXT);
  *(eList_get_pointer(header, NEXT)) = eList_calculatePointer(next);
  *(eList_get_pointer(header, PREV)) = eList_calculatePointer(first);
  *(eList_get_pointer(next, PREV)) = eList_calculatePointer(header);
  *(eList_get_pointer(first, NEXT)) = eList_calculatePointer(header);
}

/* --=[ mm_init ]=---------------------------------------------------------- */

int mm_init(void) {
  const int buckets = 32 - 4 - 3 + 8;
  // 2^32, last 4 bites are not used (addresses are aligned to 16) [28
  // buckets], 8 buckets of strict type in palce of 3 buckets of standard type
  void *ptr = morecore(ALIGNMENT - sizeof(word_t) + ALIGNMENT * 16);
  if (!ptr)
    return -1;

  heap_start = mem_sbrk(0);
  heap_end = heap_start;
  eListStart = ptr;

  word_t *w = ptr;
  eListStartSmall = w + (32 - 4 - 3) * 2;
  for (int i = 0; i < buckets; i++, w += 2) {
    *(eList_get_pointer(w, NEXT)) = eList_calculatePointer(w);
    *(eList_get_pointer(w, PREV)) = eList_calculatePointer(w);
  }

  borderFreeBlock = NULL;

  return 0;
}

/* --=[ malloc ]=----------------------------------------------------------- */

static inline word_t *find_fit(size_t reqsz) {
  word_t *bt;

  word_t *bucket = eList_getBucketBySize(reqsz);

  for (; bucket >= eListStartSmall; bucket -= 2) // Buckets with identical size
    if ((bt = eList_get_elem(bucket, PREV)) != bucket && (bt_size(bt) >= reqsz))
      return bt;

  for (; bucket >= eListStart; bucket -= 2) { // Buckets with similar size
    if ((bt = eList_get_elem(bucket, PREV)) != bucket) {
      if (bt_size(bt) >= reqsz)
        return bt;
      else if ((bt = eList_get_elem(bucket, NEXT)) != bucket &&
               bt_size(bt) >= reqsz)
        return bt;
    }
  }

  return borderFreeBlock;
}

void *malloc(size_t size) {
  word_t reqsz = blksz(size);
  word_t *bt = find_fit(reqsz);

  if (bt == borderFreeBlock)
    borderFreeBlock = NULL;

  if (bt == NULL) { // Add new free block
    morecore(reqsz);
    bt = heap_end;
    heap_end += (reqsz >> 2);
    bt_make(bt, reqsz, USED);
    return bt_payload(bt);
  }

  word_t btSize = bt_size(bt);
  if (btSize < reqsz && bt_next(bt) >= heap_end) { // Expand last free block

    word_t expand = reqsz - btSize;
    morecore(expand);
    eList_removeFromEList(bt);
    heap_end += (expand >> 2);
    bt_make(bt, reqsz, USED);
    return bt_payload(bt);
  }

  // Use standard free block
  eList_removeFromEList(bt);
  bt_make(bt, reqsz, USED);

  word_t *next = bt_next(bt);
  if (reqsz < btSize) {
    bt_make_free(next, btSize - reqsz);
    eList_add_toList(next);
  } else if (next < heap_end)
    bt_clr_prevfree(next);
  return bt_payload(bt);
}

/* --=[ free ]=------------------------------------------------------------- */

void free(void *ptr) {
  if (ptr == NULL)
    return;

  word_t *bt = bt_fromptr(ptr);
  word_t current_prevFreeFlag = bt_get_prevfree(bt);
  uint8_t prevAndNextUsed = 1;

  /*=== NEXT ===*/
  word_t *next = bt_next(bt);
  if (next < heap_end) {
    if (bt_free(next)) {
      eList_removeFromEList(next);

      word_t newSize = bt_size(bt) + bt_size(next);
      bt_make_free(bt, newSize);

      prevAndNextUsed = 0;
    } else {
      bt_set_prevfree(next);
    }
  }

  /*=== PREV ===*/
  if (current_prevFreeFlag && bt > heap_start) {
    word_t *prev = bt_prev(bt);
    eList_removeFromEList(prev);

    word_t newSize = bt_size(prev) + bt_size(bt);
    bt_make_free(prev, newSize);

    bt = prev;
    prevAndNextUsed = 0;
  }

  /*=== If surrounded by used blocks ===*/
  if (prevAndNextUsed) {
    word_t newSize = bt_size(bt);
    bt_make_free(bt, newSize);
  }

  /*=== Explicit free list pointer ===*/
  eList_add_toList(bt);

  borderFreeBlock = bt_next(bt) >= heap_end ? bt : borderFreeBlock;
}

/* --=[ realloc ]=---------------------------------------------------------- */

void *realloc(void *old_ptr, size_t size) {
  /* If size == 0 then this is just free, and we return NULL. */
  if (size == 0) {
    free(old_ptr);
    return NULL;
  }

  /* If old_ptr is NULL, then this is just malloc. */
  if (!old_ptr)
    return malloc(size);

  word_t *bt = bt_fromptr(old_ptr);
  size_t old_size = bt_size(bt);

  word_t reqsz = blksz(size);
  if (reqsz == old_size) // Already has optimal size
    return old_ptr;

  if (reqsz < old_size) { // New block can be smaller
    *bt = reqsz | (*bt & (USED | PREVFREE));
    word_t *next = bt_next(bt);
    bt_make_free(next, old_size - reqsz);

    word_t *nextOfNext = bt_next(next);
    if (nextOfNext < heap_end) {
      bt_set_prevfree(nextOfNext);

      if (bt_free(nextOfNext)) {
        eList_removeFromEList(nextOfNext);
        bt_make_free(next, bt_size(next) + bt_size(nextOfNext));
        if (nextOfNext == borderFreeBlock)
          borderFreeBlock = next;
      }
    } else {
      borderFreeBlock = next;
    }
    eList_add_toList(next);

    return bt_payload(bt);
  }

  word_t *next = bt_next(bt);

  if (bt_free(next) &&
      next < heap_end) { // This block is too small but next is free

    word_t nextSize = bt_size(next);
    if (nextSize + old_size == reqsz) {
      eList_removeFromEList(next);
      if (borderFreeBlock == next)
        borderFreeBlock = NULL;

      *bt = reqsz | (*bt & (USED | PREVFREE));
      word_t *nextOfNext = bt_next(next);
      if (nextOfNext < heap_end)
        bt_clr_prevfree(nextOfNext);
      return bt_payload(bt);
    }

    if (nextSize + old_size > reqsz) {
      eList_removeFromEList(next);
      *bt = reqsz | (*bt & (USED | PREVFREE));

      word_t *nextOfNext = bt_next(bt);
      bt_make_free(nextOfNext, nextSize + old_size - reqsz);
      eList_add_toList(nextOfNext);
      if (next == borderFreeBlock)
        borderFreeBlock = nextOfNext;

      return bt_payload(bt);
    }
  }

  if (next >= heap_end) { // Block is too small but is at end of heap
    if (morecore(reqsz - old_size) != NULL) {
      heap_end += ((reqsz - old_size) >> 2);
      *bt = reqsz | (*bt & (USED | PREVFREE));
      return bt_payload(bt);
    }
  }

  void *new_ptr = malloc(size);
  /* If malloc() fails, the original block is left untouched. */
  if (!new_ptr)
    return NULL;

  /* Copy the old data. */

  old_size -= 4; // Header data
  if (size < old_size)
    old_size = size;
  memcpy(new_ptr, old_ptr, old_size);

  /* Free the old block. */
  free(old_ptr);

  return new_ptr;
}

/* --=[ calloc ]=----------------------------------------------------------- */

void *calloc(size_t nmemb, size_t size) {
  size_t bytes = nmemb * size;
  void *new_ptr = malloc(bytes);
  if (new_ptr)
    memset(new_ptr, 0, bytes);
  return new_ptr;
}

/* --=[ mm_checkheap ]=----------------------------------------------------- */

void mm_checkheap(int verbose) {
  // In the end this function was unnecessary
}
