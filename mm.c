/*
 * mm.c - Dynamic Memory Allocator with Advanced Reallocation and Address-Ordered Free Lists.
 *
 * [Overall Strategy]
 * 1. Segregated Free Lists:
 * - Free blocks are categorized into multiple lists based on their size.
 * - This significantly reduces the search time for a suitable block.
 *
 * 2. Address-Ordered Free List Insertion:
 * - Instead of a simple LIFO (Last-In, First-Out) policy, free blocks are inserted
 * into their respective lists in ascending order of memory address.
 * - This policy, while slightly slower on insertion, tends to reduce external
 * fragmentation over time, leading to better space utilization.
 *
 * 3. Comprehensive Realloc Optimization:
 * - The mm_realloc function is heavily optimized to minimize costly malloc/memcpy/free cycles.
 * - It checks not only the next adjacent block but also the previous block and
 * both simultaneously for potential coalescing to resize a block in-place.
 * - This is particularly effective for traces with many incremental reallocations.
 *
 * 4. First-Fit Placement Policy:
 * - Within each size class, the first block that is large enough is chosen. This
 * maintains high throughput, which is a strength of the previous implementation.
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
 * provide your information in the following struct.
 ********************************************************/
team_t team = {
    /* Your student ID */
    "20XXXXXX",
    /* Your full name*/
    "Gildong Hong",
    /* Your email address */
    "example@sogang.ac.kr",
};

/* --- Constants and Macros --- */
#define WSIZE       4
#define DSIZE       8
#define CHUNKSIZE  (1<<12)
#define LISTLIMIT   20

#define MAX(x, y) ((x) > (y)? (x) : (y))

#define PACK(size, alloc)  ((size) | (alloc))

#define GET(p)       (*(unsigned int *)(p))
#define PUT(p, val)  (*(unsigned int *)(p) = (val))

#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HDRP(bp)       ((char *)(bp) - WSIZE)
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

#define PRED_PTR(bp) (*(char **)(bp))
#define SUCC_PTR(bp) (*(char **)(bp + WSIZE))

/* --- Global Variables & Function Prototypes --- */
static void *heap_listp;
static void **segregated_free_lists;

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void insert_node(void *bp, size_t size);
static void delete_node(void *bp);

/*
 * mm_init
 */
int mm_init(void)
{
    char *heap_start;

    if ((heap_start = mem_sbrk((LISTLIMIT * DSIZE) + 4 * WSIZE)) == (void *)-1)
        return -1;
    
    segregated_free_lists = (void **)heap_start;

    for (int i = 0; i < LISTLIMIT; i++) {
        segregated_free_lists[i] = NULL;
    }
    
    heap_listp = heap_start + (LISTLIMIT * DSIZE);

    PUT(heap_listp, 0);
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));
    heap_listp += (2*WSIZE);

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

/*
 * extend_heap
 */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);
}

/*
 * mm_malloc
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0)
        return NULL;

    if (size <= DSIZE)
        asize = 2*DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize,CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}


/*
 * find_fit (First-Fit)
 */
static void *find_fit(size_t asize)
{
    void *bp;
    size_t search_size = asize;
    int list_index = 0;

    while (list_index < LISTLIMIT) {
        if ((list_index == LISTLIMIT - 1) || ((search_size <= 1) && (segregated_free_lists[list_index] != NULL))) {
            bp = segregated_free_lists[list_index];
            while (bp != NULL) {
                if (GET_SIZE(HDRP(bp)) >= asize) {
                    return bp;
                }
                bp = SUCC_PTR(bp);
            }
        }
        search_size >>= 1;
        list_index++;
    }
    return NULL;
}

/*
 * place
 */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    delete_node(bp);

    if ((csize - asize) >= (2*DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
        insert_node(bp, csize-asize);
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * mm_free
 */
void mm_free(void *bp)
{
    if (bp == 0)
        return;

    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/*
 * coalesce
 */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && !next_alloc) { // Case 2
        delete_node(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size,0));
    }
    else if (!prev_alloc && next_alloc) { // Case 3
        delete_node(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else if (!prev_alloc && !next_alloc) { // Case 4
        delete_node(PREV_BLKP(bp));
        delete_node(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    
    insert_node(bp, size);
    return bp;
}

/*
 * mm_realloc - Highly optimized realloc
 */
void *mm_realloc(void *ptr, size_t size)
{
    if (ptr == NULL) {
        return mm_malloc(size);
    }
    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }

    size_t old_size = GET_SIZE(HDRP(ptr));
    size_t new_asize;

    if (size <= DSIZE) {
        new_asize = 2 * DSIZE;
    } else {
        new_asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);
    }

    // Case 1: New size is smaller or equal.
    if (new_asize <= old_size) {
        if (old_size - new_asize >= 2 * DSIZE) {
            PUT(HDRP(ptr), PACK(new_asize, 1));
            PUT(FTRP(ptr), PACK(new_asize, 1));
            void *next_bp = NEXT_BLKP(ptr);
            PUT(HDRP(next_bp), PACK(old_size - new_asize, 0));
            PUT(FTRP(next_bp), PACK(old_size - new_asize, 0));
            coalesce(next_bp);
        }
        return ptr;
    }
    // Case 2: New size is larger.
    else {
        size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
        size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(ptr)));
        size_t next_size = GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        size_t prev_size = GET_SIZE(HDRP(PREV_BLKP(ptr)));
        
        // Opt 1: Coalesce with next block
        if (!next_alloc && (old_size + next_size) >= new_asize) {
            delete_node(NEXT_BLKP(ptr));
            size_t total_size = old_size + next_size;
             if (total_size - new_asize >= 2*DSIZE) {
                PUT(HDRP(ptr), PACK(new_asize, 1));
                PUT(FTRP(ptr), PACK(new_asize, 1));
                void *split_bp = NEXT_BLKP(ptr);
                PUT(HDRP(split_bp), PACK(total_size - new_asize, 0));
                PUT(FTRP(split_bp), PACK(total_size - new_asize, 0));
                insert_node(split_bp, total_size-new_asize);
            } else {
                PUT(HDRP(ptr), PACK(total_size, 1));
                PUT(FTRP(ptr), PACK(total_size, 1));
            }
            return ptr;
        }

        // Opt 2: Coalesce with previous block
        if (!prev_alloc && (old_size + prev_size) >= new_asize) {
            void* prev_bp = PREV_BLKP(ptr);
            delete_node(prev_bp);
            size_t total_size = old_size + prev_size;
            memmove(prev_bp, ptr, old_size - DSIZE);

            if (total_size - new_asize >= 2*DSIZE) {
                PUT(HDRP(prev_bp), PACK(new_asize, 1));
                PUT(FTRP(prev_bp), PACK(new_asize, 1));
                void* split_bp = NEXT_BLKP(prev_bp);
                PUT(HDRP(split_bp), PACK(total_size - new_asize, 0));
                PUT(FTRP(split_bp), PACK(total_size - new_asize, 0));
                insert_node(split_bp, total_size - new_asize);
            } else {
                PUT(HDRP(prev_bp), PACK(total_size, 1));
                PUT(FTRP(prev_bp), PACK(total_size, 1));
            }
            return prev_bp;
        }

        // Opt 3: Coalesce with both previous and next blocks
        if (!prev_alloc && !next_alloc && (old_size + prev_size + next_size) >= new_asize) {
            void* prev_bp = PREV_BLKP(ptr);
            void* next_bp = NEXT_BLKP(ptr);
            delete_node(prev_bp);
            delete_node(next_bp);
            size_t total_size = old_size + prev_size + next_size;
            memmove(prev_bp, ptr, old_size - DSIZE);
            
            if(total_size - new_asize >= 2*DSIZE){
                PUT(HDRP(prev_bp), PACK(new_asize, 1));
                PUT(FTRP(prev_bp), PACK(new_asize, 1));
                void* split_bp = NEXT_BLKP(prev_bp);
                PUT(HDRP(split_bp), PACK(total_size-new_asize, 0));
                PUT(FTRP(split_bp), PACK(total_size-new_asize, 0));
                insert_node(split_bp, total_size-new_asize);
            } else {
                PUT(HDRP(prev_bp), PACK(total_size, 1));
                PUT(FTRP(prev_bp), PACK(total_size, 1));
            }
            return prev_bp;
        }

        // Fallback: Malloc new block and copy data
        void *newptr = mm_malloc(size);
        if (newptr == NULL) return NULL;
        memcpy(newptr, ptr, old_size - DSIZE);
        mm_free(ptr);
        return newptr;
    }
}


/* --- Segregated List Helper Functions --- */
/*
 * insert_node - Inserts a free block into the appropriate list in address order.
 */
static void insert_node(void *bp, size_t size) {
    int list_index = 0;
    void *search_ptr = NULL;
    void *insert_prev = NULL;

    while ((list_index < LISTLIMIT - 1) && (size > 1)) {
        size >>= 1;
        list_index++;
    }

    search_ptr = segregated_free_lists[list_index];
    // Traverse the list to find the correct position to insert (address order)
    while (search_ptr != NULL && (char *)bp > (char *)search_ptr) {
        insert_prev = search_ptr;
        search_ptr = SUCC_PTR(search_ptr);
    }
    
    if (search_ptr != NULL) {
        if (insert_prev != NULL) { // Insert in the middle
            SUCC_PTR(bp) = search_ptr;
            PRED_PTR(search_ptr) = bp;
            PRED_PTR(bp) = insert_prev;
            SUCC_PTR(insert_prev) = bp;
        } else { // Insert at the head
            SUCC_PTR(bp) = search_ptr;
            PRED_PTR(search_ptr) = bp;
            PRED_PTR(bp) = NULL;
            segregated_free_lists[list_index] = bp;
        }
    } else {
        if (insert_prev != NULL) { // Insert at the tail
            SUCC_PTR(bp) = NULL;
            PRED_PTR(bp) = insert_prev;
            SUCC_PTR(insert_prev) = bp;
        } else { // Insert into an empty list
            SUCC_PTR(bp) = NULL;
            PRED_PTR(bp) = NULL;
            segregated_free_lists[list_index] = bp;
        }
    }
}

/*
 * delete_node - Removes a block from its free list.
 */
static void delete_node(void *bp) {
    size_t size = GET_SIZE(HDRP(bp));
    int list_index = 0;

    while ((list_index < LISTLIMIT - 1) && (size > 1)) {
        size >>= 1;
        list_index++;
    }

    if (SUCC_PTR(bp) != NULL) {
        if (PRED_PTR(bp) != NULL) { // Middle of the list
            PRED_PTR(SUCC_PTR(bp)) = PRED_PTR(bp);
            SUCC_PTR(PRED_PTR(bp)) = SUCC_PTR(bp);
        } else { // Head of the list
            PRED_PTR(SUCC_PTR(bp)) = NULL;
            segregated_free_lists[list_index] = SUCC_PTR(bp);
        }
    } else {
        if (PRED_PTR(bp) != NULL) { // Tail of the list
            SUCC_PTR(PRED_PTR(bp)) = NULL;
        } else { // The only element in the list
            segregated_free_lists[list_index] = NULL;
        }
    }
}
