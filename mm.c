/*
 * mm.c - Malloc implementation using segregated fits with address-ordered
 * explicit linked lists and advanced reallocation heuristics.
 *
 * [Block Structure]
 * Each block has a 4-byte header and footer. The header contains the block
 * size, an allocation bit (LSB), and a reallocation tag (second LSB).
 * Free blocks contain pointers to their predecessor and successor in a
 * segregated free list.
 * 
 * [Allocated Block]
 * +------------------------------------------+
 * | Header (size | prev_alloc | alloc | tag) | 4 bytes
 * +------------------------------------------+
 * |                                          |
 * |                 Payload                  |
 * |                                          |
 * +------------------------------------------+
 * | Footer (size | prev_alloc | alloc)       | 4 bytes 
 * +------------------------------------------+
 *
 * [Free Block]
 * +--------------------------------------------+
 * | Header (size | prev_alloc | alloc=0 | tag) | 4 bytes
 * +--------------------------------------------+
 * | SUCC (Pointer to next free block)          | 4 bytes
 * +--------------------------------------------+
 * | PRED (Pointer to previous free block)      | 4 bytes
 * +--------------------------------------------+
 * |              Payload(unused)               | 4 bytes
 * +--------------------------------------------+
 * | Footer (size | prev_alloc | alloc=0)       | 4 bytes
 * +--------------------------------------------+
 *
 * [Free List Management]
 * Free blocks are managed using a segregated free list structure, where each
 * list holds blocks of a certain size class (powers of 2). Within each list,
 * blocks are sorted by size in descending order to approximate a best-fit policy.
 * Coalescing is performed immediately upon freeing a block or extending the heap.
 *
 * [Reallocation Strategy]
 * Reallocation is heavily optimized using a reallocation tag and a buffer.
 * - Reallocation Tag: The second LSB in a block's header. When a block is
 * reallocated, the next physical block is "tagged" as reserved. This tagged
 * block is skipped by mm_malloc, preserving it for the next potential
 * reallocation of the preceding block. This avoids costly memory moves.
 * - Reallocation Buffer: A small buffer is added to reallocated blocks to
 * absorb minor size increases without needing to resize the block immediately.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Your student ID */
    "20190328",
    /* Your full name*/
    "Joonhee Cho",
    /* Your email address */
    "sogang@sogang.ac.kr",
};

/* --- Alignment and Macro Definitions --- */
#define ALIGNMENT 8
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define WSIZE           4             /* Word and header/footer size (bytes) */
#define DSIZE           8             /* Double word size (bytes) */
#define INITCHUNKSIZE   (1 << 6)      /* Initial heap size (64 bytes) */
#define CHUNKSIZE       (1 << 12)     /* Incremental heap size (4KB) */
#define SEGLISTNUM      20            /* Number of segregated lists */
#define REALLOC_BUFFER  (1 << 7)      /* Buffer size for reallocation (128 bytes) */

/* --- Helper Macros --- */
#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define MIN(x, y) ((x) < (y) ? (x) : (y))

/* Pack a size and allocation status into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Write a value to p, preserving the reallocation tag */
#define PUT_REALLOC(p, val) (*(unsigned int *)(p) = (val) | GET_REALLOC(p))

/* Write a value to p, clearing the reallocation tag */
#define PUT_NO_REALLOC(p, val) (*(unsigned int *)(p) = (val))

/* Read block size and allocation status */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Reallocation tag operations */
#define GET_REALLOC(p) (GET(p) & 0x2)
#define SET_REALLOC(p) (PUT(p, GET(p) | 0x2))
#define REMOVE_REALLOC(p) (PUT(p, GET(p) & ~0x2))

/* Compute address of header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Compute address of next and previous physical blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Access pointers for free blocks in the segregated list */
#define PRED_PTR(bp) ((char **)(bp))
#define SUCC_PTR(bp) ((char **)((char *)(bp) + WSIZE))

#define PRED(bp) (*(char **)(bp))
#define SUCC(bp) (*(char **)((char *)(bp) + WSIZE))


/* --- Global Variables & Function Prototypes --- */
static void *segregated_free_lists[SEGLISTNUM];      /* Segregated free lists for different size classes */

static void *extend_heap(size_t size);               /* Extend the heap */
static void *coalesce(void *ptr);                    /* Coalesce free blocks */
static void *place(void *ptr, size_t asize);         /* Place a block */
static void insert_node(void *ptr, size_t size);     /* Insert a free block into the segregated list */
static void delete_node(void *ptr);                  /* Delete a free block from the segregated list */

/*
 * mm_init - Initializes the memory manager.
 */
int mm_init(void) {
    char *heap_start;

    for (int i = 0; i < SEGLISTNUM; i++) {
        segregated_free_lists[i] = NULL;
    }

    if ((long)(heap_start = mem_sbrk(WSIZE << 2)) == -1)
        return -1;

    PUT_NO_REALLOC(heap_start, 0);
    PUT_NO_REALLOC(heap_start + (1 * WSIZE), PACK(DSIZE, 1));   /* Prologue block */
    PUT_NO_REALLOC(heap_start + (2 * WSIZE), PACK(DSIZE, 1));   /* Next block */
    PUT_NO_REALLOC(heap_start + (3 * WSIZE), PACK(0, 1));       /* Epilogue block */

    /* Extend the heap */
    if (extend_heap(INITCHUNKSIZE) == NULL)
        return -1;

    return 0;
}

/*
 * extend_heap - Extends the heap with a new free block.
 */
static void *extend_heap(size_t size) {
    void *ptr;
    size_t asize = ALIGN(size);

    if ((ptr = mem_sbrk(asize)) == (void *)-1)
        return NULL;

    PUT_NO_REALLOC(HDRP(ptr), PACK(asize, 0));          /* Set header */
    PUT_NO_REALLOC(FTRP(ptr), PACK(asize, 0));          /* Set footer */
    PUT_NO_REALLOC(HDRP(NEXT_BLKP(ptr)), PACK(0, 1));   /* Set epilogue header */

    /* Insert the new free block into the segregated list */
    insert_node(ptr, asize);
    return coalesce(ptr);
}

/*
 * insert_node - Inserts a free block into the appropriate segregated list,
 * sorted by size in descending order.
 */
static void insert_node(void *ptr, size_t size) {
    int list = 0;
    void *search_ptr;
    void *insert_ptr = NULL;

    /* Find the appropriate class from the segregated list */
    while ((list < SEGLISTNUM - 1) && (size > 1)) {
        size >>= 1;
        list++;
    }

    /* Find insertion point (descending order by size) */
    search_ptr = segregated_free_lists[list];
    while ((search_ptr != NULL) && (size < GET_SIZE(HDRP(search_ptr)))) {
        insert_ptr = search_ptr;
        search_ptr = SUCC(search_ptr);
    }

    /* Insert block */
    if (search_ptr != NULL) {
        if (insert_ptr != NULL) { /* Middle */
            *SUCC_PTR(ptr) = search_ptr;
            *PRED_PTR(ptr) = insert_ptr;
            *PRED_PTR(search_ptr) = ptr;
            *SUCC_PTR(insert_ptr) = ptr;
        } else { /* Head */
            *SUCC_PTR(ptr) = search_ptr;
            *PRED_PTR(ptr) = NULL;
            *PRED_PTR(search_ptr) = ptr;
            segregated_free_lists[list] = ptr;
        }
    } else {
        if (insert_ptr != NULL) { /* Tail */
            *SUCC_PTR(ptr) = NULL;
            *PRED_PTR(ptr) = insert_ptr;
            *SUCC_PTR(insert_ptr) = ptr;
        } else { /* Empty list */
            *SUCC_PTR(ptr) = NULL;
            *PRED_PTR(ptr) = NULL;
            segregated_free_lists[list] = ptr;
        }
    }
}


/*
 * delete_node - Removes a free block from its segregated list.
 */
static void delete_node(void *ptr) {
    int list = 0;
    size_t size = GET_SIZE(HDRP(ptr));

    /* Find the appropriate class from the segregated list */
    while ((list < SEGLISTNUM - 1) && (size > 1)) {
        size >>= 1;
        list++;
    }

    /* Remove block */
    if (SUCC(ptr) != NULL) {
        if (PRED(ptr) != NULL) {
            *SUCC_PTR(PRED(ptr)) = SUCC(ptr);
            *PRED_PTR(SUCC(ptr)) = PRED(ptr);
        } else {
            *PRED_PTR(SUCC(ptr)) = NULL;
            segregated_free_lists[list] = SUCC(ptr);
        }
    } else {
        if (PRED(ptr) != NULL) {
            *SUCC_PTR(PRED(ptr)) = NULL;
        } else {
            segregated_free_lists[list] = NULL;
        }
    }
}

/*
 * coalesce - Coalesces adjacent free blocks.
 */
static void *coalesce(void *ptr) {
    unsigned int prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(ptr)));
    unsigned int next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
    size_t size = GET_SIZE(HDRP(ptr));

    if (prev_alloc && next_alloc) {                 /* Case 1: The previous block and the next block are both allocated */
        return ptr;
    } else if (prev_alloc && !next_alloc) {         /* Case 2: The next block is free */
        delete_node(ptr);
        delete_node(NEXT_BLKP(ptr));
        size += GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        PUT(HDRP(ptr), PACK(size, 0));
        PUT(FTRP(ptr), PACK(size, 0));
    } else if (!prev_alloc && next_alloc) {         /* Case 3: The previous block is free */
        delete_node(ptr);
        delete_node(PREV_BLKP(ptr));
        size += GET_SIZE(HDRP(PREV_BLKP(ptr)));
        ptr = PREV_BLKP(ptr);
        PUT(HDRP(ptr), PACK(size, 0));
        PUT(FTRP(ptr), PACK(size, 0));
    } else {                                        /* Case 4: The previous block and the next block are both free */
        delete_node(ptr);
        delete_node(PREV_BLKP(ptr));
        delete_node(NEXT_BLKP(ptr));
        size += GET_SIZE(HDRP(PREV_BLKP(ptr))) + GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        ptr = PREV_BLKP(ptr);
        PUT(HDRP(ptr), PACK(size, 0));
        PUT(FTRP(ptr), PACK(size, 0));
    }
    
    insert_node(ptr, size);
    return ptr;
}

/*
 * place - Places a block of a given size, splitting if possible.
 * Implements a back-placement strategy for larger blocks to reduce external fragmentation.
 */
static void *place(void *ptr, size_t asize) {
    size_t ptr_size = GET_SIZE(HDRP(ptr));
    size_t remainder = ptr_size - asize;

    delete_node(ptr);

    if (remainder <= (DSIZE << 1)) {
        /* If the remainder is too small, don't split. */
        PUT_REALLOC(HDRP(ptr), PACK(ptr_size, 1));
        PUT_REALLOC(FTRP(ptr), PACK(ptr_size, 1));
    } else if (asize >= 100) { 
        /* Back-placement for larger blocks */
        PUT_NO_REALLOC(HDRP(ptr), PACK(remainder, 0));
        PUT_NO_REALLOC(FTRP(ptr), PACK(remainder, 0));
        PUT_NO_REALLOC(HDRP(NEXT_BLKP(ptr)), PACK(asize, 1));
        PUT_NO_REALLOC(FTRP(NEXT_BLKP(ptr)), PACK(asize, 1));
        insert_node(ptr, remainder);
        return NEXT_BLKP(ptr);
    } else { 
        /* Front-placement */
        PUT_REALLOC(HDRP(ptr), PACK(asize, 1));
        PUT_REALLOC(FTRP(ptr), PACK(asize, 1));
        PUT_NO_REALLOC(HDRP(NEXT_BLKP(ptr)), PACK(remainder, 0));
        PUT_NO_REALLOC(FTRP(NEXT_BLKP(ptr)), PACK(remainder, 0));
        insert_node(NEXT_BLKP(ptr), remainder);
    }
    return ptr;
}

/*
 * mm_malloc - Allocates a memory block.
 */
void *mm_malloc(size_t size) {
    size_t asize;
    size_t extendsize;
    void *ptr = NULL;
    int list = 0;

    if (size == 0)
        return NULL;

    if (size <= DSIZE) {
        asize = DSIZE << 1;
    } else {
        asize = ALIGN(size + DSIZE);
    }

    size_t searchsize = asize;
    while (list < SEGLISTNUM) {
        if ((list == SEGLISTNUM - 1) || ((searchsize <= 1) && (segregated_free_lists[list] != NULL))) {
            ptr = segregated_free_lists[list];
            while ((ptr != NULL) && ((asize > GET_SIZE(HDRP(ptr))) || (GET_REALLOC(HDRP(ptr))))) {
                ptr = SUCC(ptr);
            }
            if (ptr != NULL)
                break;
        }
        searchsize >>= 1;
        list++;
    }

    if (ptr == NULL) {
        extendsize = MAX(asize, CHUNKSIZE);
        if ((ptr = extend_heap(extendsize)) == NULL)
            return NULL;
    }

    ptr = place(ptr, asize);
    return ptr;
}

/*
 * mm_free - Frees a memory block.
 */
void mm_free(void *ptr) {
    if (ptr == NULL)
        return;

    size_t size = GET_SIZE(HDRP(ptr));
    REMOVE_REALLOC(HDRP(NEXT_BLKP(ptr)));
    
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    
    insert_node(ptr, size);
    coalesce(ptr);
}

/*
 * mm_realloc - Reallocates a memory block with advanced heuristics.
 */
void *mm_realloc(void *ptr, size_t size) {
    if (ptr == NULL)
        return mm_malloc(size);
    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }

    void *new_ptr = ptr;
    size_t new_size = ALIGN(size + DSIZE);
    size_t old_size = GET_SIZE(HDRP(ptr));
    int remainder;

    /* Add buffer for future reallocations */
    if (new_size < old_size) {
        remainder = old_size - new_size;
        if (remainder < (DSIZE << 1)) {
             PUT(HDRP(ptr), PACK(old_size, 1));
             PUT(FTRP(ptr), PACK(old_size, 1));
             SET_REALLOC(HDRP(NEXT_BLKP(ptr)));
        }
        return ptr;
    }
    
    int block_buffer = GET_SIZE(HDRP(ptr)) - new_size;

    /* Allocate more space if needed */
    if (block_buffer < 0) {
        /* Check if next block is free or the end of the heap */
        if (!GET_ALLOC(HDRP(NEXT_BLKP(ptr))) || !GET_SIZE(HDRP(NEXT_BLKP(ptr)))) {
            remainder = old_size + GET_SIZE(HDRP(NEXT_BLKP(ptr))) - new_size;
            if (remainder < 0) {
                size_t extendsize = MAX(-remainder, CHUNKSIZE);
                if (extend_heap(extendsize) == NULL)
                    return NULL;
                remainder += extendsize;
            }
            
            delete_node(NEXT_BLKP(ptr));
            PUT_NO_REALLOC(HDRP(ptr), PACK(new_size + remainder, 1));
            PUT_NO_REALLOC(FTRP(ptr), PACK(new_size + remainder, 1));

        } else { /* Fallback to malloc and free */
            new_ptr = mm_malloc(new_size - DSIZE);
            memcpy(new_ptr, ptr, MIN(size, new_size) - DSIZE);
            mm_free(ptr);
        }
        block_buffer = GET_SIZE(HDRP(new_ptr)) - new_size;
    }

    /* Tag the next block if the buffer is small */
    if (block_buffer < (REALLOC_BUFFER << 1))
        SET_REALLOC(HDRP(NEXT_BLKP(new_ptr)));

    return new_ptr;
}
