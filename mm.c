/*
 * mm.c - Dynamic Memory Allocator with Segregated Free Lists and Heap Checker.
 *
 * [Overall Strategy]
 * 1. Segregated Free Lists & First-Fit:
 * - To optimize search time, free blocks are organized into multiple lists
 * based on size classes. The first suitable block found is used.
 * 2. Address-Ordered Free List Insertion:
 * - Free blocks are inserted into lists in ascending memory address order
 * to potentially improve fragmentation patterns.
 * 3. Comprehensive Realloc Optimization:
 * - mm_realloc is optimized to check if the block is at the end of the heap
 * for in-place expansion, or if the next adjacent block is free for coalescing, 
 * which minimizes costly data copies.
 * 4. Heap Checker (mm_checkheap):
 * - An optional debugging function to verify heap integrity.
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
    "20190328",
    /* Your full name*/
    "Joonhee Cho",
    /* Your email address */
    "sogang@sogang.ac.kr",
};

/* --- Constants and Macros --- */
#define WSIZE       4       /* Word and header/footer size (bytes) */
#define DSIZE       8       /* Double word size (bytes) */
#define CHUNKSIZE  (1<<12)  /* Extend heap by this amount (bytes) */
#define LISTLIMIT   20      /* Number of segregated free lists */

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))
#define PUT(p, val)  (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Pointers to predecessor and successor free blocks */
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
static int get_list_index(size_t size);

#ifdef DEBUG
/* Heap checker functions */
static int mm_checkheap(int verbose);
#endif

/*
 * mm_init - Initialize the malloc package.
 */
int mm_init(void)
{
    char *heap_start;

    /* Allocate memory for segregated list pointers */
    if ((heap_start = mem_sbrk((LISTLIMIT * DSIZE) + 4 * WSIZE)) == (void *)-1)
        return -1;
    
    segregated_free_lists = (void **)heap_start;

    /* Initialize segregated lists to NULL */
    for (int i = 0; i < LISTLIMIT; i++) {
        segregated_free_lists[i] = NULL;
    }
    
    heap_listp = heap_start + (LISTLIMIT * DSIZE);

    /* Prologue and Epilogue blocks setup */
    PUT(heap_listp, 0);                          /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));     /* Epilogue header */
    heap_listp += (2*WSIZE);

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;

    #ifdef DEBUG
    mm_checkheap(1);
    #endif

    return 0;
}

/*
 * extend_heap - Extend heap with a new free block.
 */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /* Initialize free block header/footer and the new epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 * Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;

    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        #ifdef DEBUG
        mm_checkheap(1);
        #endif
        return bp;
    }

    /* No fit found. Get more memory and place the block. */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);

    #ifdef DEBUG
    mm_checkheap(1);
    #endif

    return bp;
}

/*
 * find_fit (First-Fit) - Find a fit for a block with asize bytes.
 */
static void *find_fit(size_t asize)
{
    int list_index = get_list_index(asize);

    /* Search for a fit starting from the appropriate list */
    for (; list_index < LISTLIMIT; list_index++) {
        void *bp = segregated_free_lists[list_index];
        while (bp != NULL) {
            if (GET_SIZE(HDRP(bp)) >= asize) {
                return bp;
            }
            bp = SUCC_PTR(bp);
        }
    }
    return NULL; /* No fit */
}


/*
 * place - Place block of asize bytes at start of free block bp
 * and split if remainder would be at least minimum block size.
 */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    delete_node(bp);

    if ((csize - asize) >= (2 * DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
        insert_node(bp, csize - asize);
    } else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}


/*
 * mm_free - Freeing a block.
 */
void mm_free(void *bp)
{
    if (bp == 0)
        return;

    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);

    #ifdef DEBUG
    mm_checkheap(1);
    #endif
}

/*
 * coalesce - Boundary tag coalescing. Return ptr to coalesced block.
 */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && !next_alloc) { /* Case 2: Coalesce with next block */
        delete_node(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size,0));
    }
    else if (!prev_alloc && next_alloc) { /* Case 3: Coalesce with previous block */
        delete_node(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else if (!prev_alloc && !next_alloc) { /* Case 4: Coalesce with both */
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
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
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
    
    /* Case 1: New size is smaller or equal */
    if (new_asize <= old_size) {
        if (old_size - new_asize >= (2 * DSIZE)) {
            PUT(HDRP(ptr), PACK(new_asize, 1));
            PUT(FTRP(ptr), PACK(new_asize, 1));
            void *next_bp = NEXT_BLKP(ptr);
            PUT(HDRP(next_bp), PACK(old_size - new_asize, 0));
            PUT(FTRP(next_bp), PACK(old_size - new_asize, 0));
            coalesce(next_bp);
        }
        return ptr;
    }
    /* Case 2: New size is larger */
    else {
        size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
        size_t next_size = GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        
        /* Optimization 2a: Coalesce with the next free block */
        if (!next_alloc && (old_size + next_size) >= new_asize) {
            delete_node(NEXT_BLKP(ptr));
            size_t total_size = old_size + next_size;

            if (total_size - new_asize >= 2 * DSIZE) {
                PUT(HDRP(ptr), PACK(new_asize, 1));
                PUT(FTRP(ptr), PACK(new_asize, 1));
                void *split_bp = NEXT_BLKP(ptr);
                PUT(HDRP(split_bp), PACK(total_size - new_asize, 0));
                PUT(FTRP(split_bp), PACK(total_size - new_asize, 0));
                insert_node(split_bp, total_size - new_asize);
            } else {
                PUT(HDRP(ptr), PACK(total_size, 1));
                PUT(FTRP(ptr), PACK(total_size, 1));
            }
            return ptr;
        }
        /* Optimization 2b: Extend heap if block is at the end */
        else if (next_size == 0) {
            size_t extend_size = new_asize - old_size;
            if (mem_sbrk(extend_size) == (void*)-1) {
                return NULL;
            }
            PUT(HDRP(ptr), PACK(new_asize, 1));
            PUT(FTRP(ptr), PACK(new_asize, 1));
            PUT(HDRP(NEXT_BLKP(ptr)), PACK(0, 1)); /* New epilogue */
            return ptr;
        }
        /* Case 3: Fallback to malloc, memcpy, and free */
        else {
            void *newptr = mm_malloc(size);
            if (newptr == NULL) return NULL;
            memcpy(newptr, ptr, old_size - DSIZE); /* Copy old payload */
            mm_free(ptr);
            return newptr;
        }
    }
}

/* --- Segregated List Helper Functions --- */

/*
 * get_list_index - Get the index of the segregated list for a given size.
 */
static int get_list_index(size_t size) {
    int list_index = 0;
    while ((list_index < LISTLIMIT - 1) && (size > 1)) {
        size >>= 1;
        list_index++;
    }
    return list_index;
}

/*
 * insert_node - Insert a block into the appropriate segregated free list, ordered by address.
 */
static void insert_node(void *bp, size_t size) {
    int list_index = get_list_index(size);
    void *search_ptr = segregated_free_lists[list_index];
    void *insert_prev = NULL;

    /* Find position to insert (address order) */
    while (search_ptr != NULL && (char *)bp > (char *)search_ptr) {
        insert_prev = search_ptr;
        search_ptr = SUCC_PTR(search_ptr);
    }
    
    if (search_ptr != NULL) { // Insert in the middle or at the head
        if (insert_prev != NULL) { // Middle
            SUCC_PTR(bp) = search_ptr;
            PRED_PTR(search_ptr) = bp;
            PRED_PTR(bp) = insert_prev;
            SUCC_PTR(insert_prev) = bp;
        } else { // Head
            SUCC_PTR(bp) = search_ptr;
            PRED_PTR(search_ptr) = bp;
            PRED_PTR(bp) = NULL;
            segregated_free_lists[list_index] = bp;
        }
    } else { // Insert at the end or in an empty list
        if (insert_prev != NULL) { // End
            SUCC_PTR(bp) = NULL;
            PRED_PTR(bp) = insert_prev;
            SUCC_PTR(insert_prev) = bp;
        } else { // Empty list
            SUCC_PTR(bp) = NULL;
            PRED_PTR(bp) = NULL;
            segregated_free_lists[list_index] = bp;
        }
    }
}

/*
 * delete_node - Remove a block from its segregated free list.
 */
static void delete_node(void *bp) {
    size_t size = GET_SIZE(HDRP(bp));
    int list_index = get_list_index(size);

    if (SUCC_PTR(bp) != NULL) {
        if (PRED_PTR(bp) != NULL) { // Node is in the middle
            PRED_PTR(SUCC_PTR(bp)) = PRED_PTR(bp);
            SUCC_PTR(PRED_PTR(bp)) = SUCC_PTR(bp);
        } else { // Node is at the head
            PRED_PTR(SUCC_PTR(bp)) = NULL;
            segregated_free_lists[list_index] = SUCC_PTR(bp);
        }
    } else {
        if (PRED_PTR(bp) != NULL) { // Node is at the tail
            SUCC_PTR(PRED_PTR(bp)) = NULL;
        } else { // Node is the only element
            segregated_free_lists[list_index] = NULL;
        }
    }
}

#ifdef DEBUG
/* --- Heap Consistency Checker --- */
static void print_block(void *bp) {
    size_t hsize, halloc, fsize, falloc;

    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));

    if (hsize == 0) {
        printf("%p: EOL\n", bp);
        return;
    }

    printf("%p: header: [%zu:%c] footer: [%zu:%c]\n", bp,
           hsize, (halloc ? 'a' : 'f'),
           fsize, (falloc ? 'a' : 'f'));
}

/*
 * mm_checkheap - A lightweight heap checker.
 */
int mm_checkheap(int verbose) {
    char *bp;
    int free_blocks_in_heap = 0;
    int free_blocks_in_list = 0;

    if (verbose) printf("Heap (%p):\n", heap_listp);

    if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
        printf("Bad prologue header\n");

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (verbose) print_block(bp);

        if ((size_t)bp % DSIZE)
            printf("Error: %p is not doubleword aligned\n", bp);

        if (GET(HDRP(bp)) != GET(FTRP(bp)))
            printf("Error: header does not match footer\n");

        if (!GET_ALLOC(HDRP(bp)) && !GET_ALLOC(HDRP(NEXT_BLKP(bp))))
            printf("Error: contiguous free blocks %p and %p escaped coalescing\n", bp, NEXT_BLKP(bp));
        
        if (!GET_ALLOC(HDRP(bp))) {
            free_blocks_in_heap++;
        }
    }

    if (verbose) print_block(bp);
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
        printf("Bad epilogue header\n");

    for (int i = 0; i < LISTLIMIT; i++) {
        for (bp = segregated_free_lists[i]; bp != NULL; bp = SUCC_PTR(bp)) {
            free_blocks_in_list++;
            if (GET_ALLOC(HDRP(bp)))
                printf("Error: allocated block %p in free list\n", bp);
            if (SUCC_PTR(bp) != NULL && PRED_PTR(SUCC_PTR(bp)) != bp)
                printf("Error: free list pointer inconsistency at %p\n", bp);
        }
    }

    if (free_blocks_in_heap != free_blocks_in_list)
        printf("Error: free block count mismatch. Heap: %d, List: %d\n", free_blocks_in_heap, free_blocks_in_list);

    return 1;
}
#endif
