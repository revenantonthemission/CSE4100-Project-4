/*
 * mm.c - A memory allocator using a Red-Black Tree.
 *
 * This version includes a heap checker for debugging purposes.
 * To enable the heap checker, compile with the -DDEBUG flag.
 * e.g., gcc -DDEBUG -g -o mdriver mdriver.c mm.c memlib.c
 *
 * Free blocks are managed using a Red-Black Tree, ordered by block size.
 * This version is for 32-bit systems.
 *
 * *****************************************************************
 * <<< 주요 수정 사항 >>>
 * 1. rb_delete & rb_delete_fixup: Black Height 불일치 오류를 해결하기 위해
 * NULL 노드 처리 로직을 포함한 표준 R-B Tree 삭제 알고리즘으로 대폭 수정.
 * 삭제된 노드가 블랙일 경우, 대체 노드가 NULL이더라도 fixup을 수행하도록 변경.
 * 2. MIN_BLK_SIZE: 24바이트 (8바이트 정렬 준수)
 * *****************************************************************
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

/* Basic constants and macros for 32-bit */
#define WSIZE       4       /* Word and header/footer size (bytes) */
#define DSIZE       8       /* Double word size (bytes) */
#define CHUNKSIZE   (1<<12) /* Extend heap by this amount (bytes) */
/* Minimum block size must be 24 bytes (multiple of 8)
 * to hold header(4), footer(4), and 3 pointers(12) and maintain 8-byte alignment. */
#define MIN_BLK_SIZE (6 * WSIZE) 

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size, color, and allocated bit into a word */
#define PACK(size, color, alloc) ((size) | ((color)<<1) | (alloc))

/* Read and write a word at address p */
#define GET(p)      (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Read the size, allocation bit, and color bit from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
#define GET_COLOR(p) ((GET(p) & 0x2) >> 1) /* 0 for RED, 1 for BLACK */

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)    ((char *)(bp) - WSIZE)
#define FTRP(bp)    ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Red-Black Tree Macros: Block pointer 'bp' points to the payload area.
 * The first 12 bytes of the payload in a free block are used for pointers. */
#define PARENT(bp)      (*(void **)(bp))
#define LEFT_CHILD(bp)  (*(void **)(bp + WSIZE))
#define RIGHT_CHILD(bp) (*(void **)(bp + 2 * WSIZE))

/* Setters for R-B Tree pointers */
#define SET_PARENT(bp, p)      (PARENT(bp) = (p))
#define SET_LEFT_CHILD(bp, l)  (LEFT_CHILD(bp) = (l))
#define SET_RIGHT_CHILD(bp, r) (RIGHT_CHILD(bp) = (r))

/* Color operations */
#define SET_COLOR(p, color) \
    do { \
        if (p != NULL) { \
            unsigned int size = GET_SIZE(HDRP(p)); \
            unsigned int alloc = GET_ALLOC(HDRP(p)); \
            PUT(HDRP(p), PACK(size, color, alloc)); \
            PUT(FTRP(p), PACK(size, color, alloc)); \
        } \
    } while (0)

#define SET_RED(p) SET_COLOR(p, 0)
#define SET_BLACK(p) SET_COLOR(p, 1)

/* Global variables */
static void *heap_listp = NULL;
static void *rb_root = NULL;

/* Function prototypes */
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void rb_insert(void *bp);
static void rb_insert_fixup(void *bp);
static void rb_delete(void *bp);
static void rb_delete_fixup(void *x);
static void rotate_left(void *x);
static void rotate_right(void *x);
static void transplant(void *u, void *v);
static void *tree_minimum(void *x);
int mm_check(void);

/* * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;
        
    PUT(heap_listp, 0);                             /* Alignment padding */
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1, 1)); /* Prologue header */
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1, 1)); /* Prologue footer */
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1, 1));     /* Epilogue header */
    heap_listp += (2 * WSIZE);
    rb_root = NULL;

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    
    #ifdef DEBUG
        mm_check();
    #endif
    return 0;
}

/* * mm_malloc - Allocate a block.
 */
void *mm_malloc(size_t size)
{
    size_t asize;      
    size_t extendsize; 
    void *bp;

    if (size == 0) return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE + WSIZE * 3) { // Payload size that fits in min block
        asize = MIN_BLK_SIZE;
    } else {
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    }
    
    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        #ifdef DEBUG
            mm_check();
        #endif
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    #ifdef DEBUG
        mm_check();
    #endif
    return bp;
}

/*
 * mm_free - Freeing a block.
 */
void mm_free(void *bp)
{
    if (bp == NULL) return;

    size_t size = GET_SIZE(HDRP(bp));

    /* Mark the block as free, but keep its color for now until coalesce */
    PUT(HDRP(bp), PACK(size, GET_COLOR(HDRP(bp)), 0)); 
    PUT(FTRP(bp), PACK(size, GET_COLOR(HDRP(bp)), 0));
    coalesce(bp);

    #ifdef DEBUG
        mm_check();
    #endif
}

/*
 * mm_realloc - Reallocate a block to a new size.
 */
void *mm_realloc(void *ptr, size_t size)
{
    if (ptr == NULL) return mm_malloc(size);
    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }

    size_t old_size = GET_SIZE(HDRP(ptr));
    size_t new_size;

    /* Adjust new size */
    if (size <= DSIZE + WSIZE*3) {
        new_size = MIN_BLK_SIZE;
    } else {
        new_size = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    }

    /* If new size is smaller or equal, we can just return the original pointer */
    if (old_size >= new_size) {
        return ptr;
    } 
    
    /* Check if we can expand into the next block */
    void* next_block = NEXT_BLKP(ptr);
    size_t next_alloc = GET_ALLOC(HDRP(next_block));
    size_t next_size = GET_SIZE(HDRP(next_block));

    /* If next block is free and large enough, merge them */
    if (!next_alloc && (old_size + next_size) >= new_size) {
        rb_delete(next_block); // Remove the next block from free tree
        size_t total_size = old_size + next_size;
        
        // Split if necessary
        if((total_size - new_size) >= MIN_BLK_SIZE) {
            PUT(HDRP(ptr), PACK(new_size, 1, 1));
            PUT(FTRP(ptr), PACK(new_size, 1, 1));
            void* remainder = NEXT_BLKP(ptr);
            PUT(HDRP(remainder), PACK(total_size - new_size, 1, 0));
            PUT(FTRP(remainder), PACK(total_size - new_size, 1, 0));
            rb_insert(remainder);
        } else {
            PUT(HDRP(ptr), PACK(total_size, 1, 1));
            PUT(FTRP(ptr), PACK(total_size, 1, 1));
        }
        #ifdef DEBUG
            mm_check();
        #endif
        return ptr;
    }
    
    /* Fallback: allocate a new block and copy data */
    void *new_ptr = mm_malloc(size);
    if (new_ptr == NULL) return NULL;
    
    /* Copy data from old block to new block. */
    size_t copy_size = old_size - DSIZE;
    memcpy(new_ptr, ptr, copy_size);
    mm_free(ptr);
    
    #ifdef DEBUG
        mm_check();
    #endif
    return new_ptr;
}

/*
 * coalesce - Merge adjacent free blocks.
 */
static void *coalesce(void *bp)
{
    void *prev_bp = PREV_BLKP(bp);
    void *next_bp = NEXT_BLKP(bp);
    size_t prev_alloc = GET_ALLOC(FTRP(prev_bp));
    size_t next_alloc = GET_ALLOC(HDRP(next_bp));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && !next_alloc) { /* Case 2: Merge with next block */
        rb_delete(next_bp);
        size += GET_SIZE(HDRP(next_bp));
        PUT(HDRP(bp), PACK(size, 1, 0));
        PUT(FTRP(bp), PACK(size, 1, 0));
    }

    else if (!prev_alloc && next_alloc) { /* Case 3: Merge with previous block */
        rb_delete(prev_bp);
        size += GET_SIZE(HDRP(prev_bp));
        PUT(HDRP(prev_bp), PACK(size, 1, 0));
        PUT(FTRP(prev_bp), PACK(size, 1, 0));
        bp = prev_bp;
    }

    else if (!prev_alloc && !next_alloc) { /* Case 4: Merge with both */
        rb_delete(prev_bp);
        rb_delete(next_bp);
        size += GET_SIZE(HDRP(prev_bp)) + GET_SIZE(FTRP(next_bp));
        PUT(HDRP(prev_bp), PACK(size, 1, 0));
        PUT(FTRP(prev_bp), PACK(size, 1, 0));
        bp = prev_bp;
    }
    
    /* Insert the newly coalesced block into the tree */
    rb_insert(bp);
    return bp;
}

/*
 * extend_heap - Extend the heap with a new free block.
 */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if (size < MIN_BLK_SIZE) size = MIN_BLK_SIZE;

    if ((long)(bp = mem_sbrk(size)) == -1) return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 1, 0)); /* New free block header (default black) */
    PUT(FTRP(bp), PACK(size, 1, 0)); /* New free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1, 1)); /* New epilogue header */

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

/*
 * find_fit - Find the best fit for a block of a given size.
 * We search for the smallest block that is large enough.
 */
static void *find_fit(size_t asize)
{
    void *current = rb_root;
    void *best_fit = NULL;
    while (current != NULL) {
        if (GET_SIZE(HDRP(current)) >= asize) {
            best_fit = current;
            current = LEFT_CHILD(current); // Try to find a smaller block
        } else {
            current = RIGHT_CHILD(current); // Need a larger block
        }
    }
    return best_fit;
}

/*
 * place - Place a block of a given size at the beginning of a free block.
 */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    rb_delete(bp); // Remove the block from the free tree

    if ((csize - asize) >= MIN_BLK_SIZE) {
        /* Split the block */
        PUT(HDRP(bp), PACK(asize, 1, 1));
        PUT(FTRP(bp), PACK(asize, 1, 1));
        
        void *next_bp = NEXT_BLKP(bp);
        PUT(HDRP(next_bp), PACK(csize - asize, 1, 0));
        PUT(FTRP(next_bp), PACK(csize - asize, 1, 0));
        
        /* Insert the remainder directly, don't use coalesce */
        rb_insert(next_bp); 
    } else {
        /* Don't split, use the whole block */
        PUT(HDRP(bp), PACK(csize, 1, 1));
        PUT(FTRP(bp), PACK(csize, 1, 1));
    }
}


/************************************************
 * Red-Black Tree Implementation (Revised)
 ************************************************/

static void rotate_left(void *x) {
    void *y = RIGHT_CHILD(x);
    SET_RIGHT_CHILD(x, LEFT_CHILD(y));
    if (LEFT_CHILD(y) != NULL) SET_PARENT(LEFT_CHILD(y), x);
    SET_PARENT(y, PARENT(x));
    if (PARENT(x) == NULL) rb_root = y;
    else if (x == LEFT_CHILD(PARENT(x))) SET_LEFT_CHILD(PARENT(x), y);
    else SET_RIGHT_CHILD(PARENT(x), y);
    SET_LEFT_CHILD(y, x);
    SET_PARENT(x, y);
}

static void rotate_right(void *x) {
    void *y = LEFT_CHILD(x);
    SET_LEFT_CHILD(x, RIGHT_CHILD(y));
    if (RIGHT_CHILD(y) != NULL) SET_PARENT(RIGHT_CHILD(y), x);
    SET_PARENT(y, PARENT(x));
    if (PARENT(x) == NULL) rb_root = y;
    else if (x == RIGHT_CHILD(PARENT(x))) SET_RIGHT_CHILD(PARENT(x), y);
    else SET_LEFT_CHILD(PARENT(x), y);
    SET_RIGHT_CHILD(y, x);
    SET_PARENT(x, y);
}

static void rb_insert(void *z) {
    void *y = NULL;
    void *x = rb_root;
    size_t z_size = GET_SIZE(HDRP(z));

    while (x != NULL) {
        y = x;
        if (z_size < GET_SIZE(HDRP(x))) {
            x = LEFT_CHILD(x);
        } else {
            x = RIGHT_CHILD(x);
        }
    }

    SET_PARENT(z, y);
    if (y == NULL) {
        rb_root = z;
    } else if (z_size < GET_SIZE(HDRP(y))) {
        SET_LEFT_CHILD(y, z);
    } else {
        SET_RIGHT_CHILD(y, z);
    }

    SET_LEFT_CHILD(z, NULL);
    SET_RIGHT_CHILD(z, NULL);
    SET_RED(z);
    rb_insert_fixup(z);
}

static void rb_insert_fixup(void *z) {
    while (PARENT(z) != NULL && GET_COLOR(HDRP(PARENT(z))) == 0) { // Parent is RED
        void *grandparent = PARENT(PARENT(z));
        if (PARENT(z) == LEFT_CHILD(grandparent)) {
            void *uncle = RIGHT_CHILD(grandparent);
            if (uncle != NULL && GET_COLOR(HDRP(uncle)) == 0) { // Case 1: Uncle is RED
                SET_BLACK(PARENT(z));
                SET_BLACK(uncle);
                SET_RED(grandparent);
                z = grandparent;
            } else { // Uncle is BLACK
                if (z == RIGHT_CHILD(PARENT(z))) { // Case 2: z is right child
                    z = PARENT(z);
                    rotate_left(z);
                }
                // Case 3: z is left child
                grandparent = PARENT(PARENT(z)); // Re-fetch grandparent
                SET_BLACK(PARENT(z));
                SET_RED(grandparent);
                rotate_right(grandparent);
            }
        } else { // Symmetric to the 'if' part
            void *uncle = LEFT_CHILD(grandparent);
            if (uncle != NULL && GET_COLOR(HDRP(uncle)) == 0) {
                SET_BLACK(PARENT(z));
                SET_BLACK(uncle);
                SET_RED(grandparent);
                z = grandparent;
            } else {
                if (z == LEFT_CHILD(PARENT(z))) {
                    z = PARENT(z);
                    rotate_right(z);
                }
                grandparent = PARENT(PARENT(z));
                SET_BLACK(PARENT(z));
                SET_RED(grandparent);
                rotate_left(grandparent);
            }
        }
    }
    SET_BLACK(rb_root);
}

static void transplant(void *u, void *v) {
    if (PARENT(u) == NULL) {
        rb_root = v;
    } else if (u == LEFT_CHILD(PARENT(u))) {
        SET_LEFT_CHILD(PARENT(u), v);
    } else {
        SET_RIGHT_CHILD(PARENT(u), v);
    }
    if (v != NULL) {
        SET_PARENT(v, PARENT(u));
    }
}

static void *tree_minimum(void *x) {
    if (x == NULL) return NULL;
    while (LEFT_CHILD(x) != NULL) {
        x = LEFT_CHILD(x);
    }
    return x;
}

/*
 * rb_delete - More robust implementation to fix Black-Height issues.
 */
static void rb_delete(void *z) {
    if (z == NULL) return;
    
    void *x, *y;
    void *y_parent;
    int y_original_color;

    y = z;
    y_original_color = GET_COLOR(HDRP(y));

    if (LEFT_CHILD(z) == NULL) {
        x = RIGHT_CHILD(z);
        y_parent = PARENT(z);
        transplant(z, x);
    } else if (RIGHT_CHILD(z) == NULL) {
        x = LEFT_CHILD(z);
        y_parent = PARENT(z);
        transplant(z, x);
    } else {
        y = tree_minimum(RIGHT_CHILD(z));
        y_original_color = GET_COLOR(HDRP(y));
        x = RIGHT_CHILD(y);
        
        if (PARENT(y) == z) {
            y_parent = y;
            if (x != NULL) SET_PARENT(x, y);
        } else {
            y_parent = PARENT(y);
            transplant(y, x);
            SET_RIGHT_CHILD(y, RIGHT_CHILD(z));
            SET_PARENT(RIGHT_CHILD(z), y);
        }
        
        transplant(z, y);
        SET_LEFT_CHILD(y, LEFT_CHILD(z));
        SET_PARENT(LEFT_CHILD(y), y);
        SET_COLOR(y, GET_COLOR(HDRP(z)));
    }

    if (y_original_color == 1) { // Fixup is needed only if a BLACK node was removed.
        rb_delete_fixup(x);
    }
}

/*
 * rb_delete_fixup - More robust version that handles NULL 'x'
 */
static void rb_delete_fixup(void *x) {
    while (x != rb_root && (x == NULL || GET_COLOR(HDRP(x)) == 1)) {
        void* parent_x = (x != NULL) ? PARENT(x) : rb_root; // Need parent to find sibling
        if (x == LEFT_CHILD(parent_x)) {
            void *w = RIGHT_CHILD(parent_x); // w is sibling
            if (w == NULL) break; 
            
            if (GET_COLOR(HDRP(w)) == 0) { // Case 1: sibling is RED
                SET_BLACK(w);
                SET_RED(parent_x);
                rotate_left(parent_x);
                w = RIGHT_CHILD(parent_x);
            }
            if (w == NULL) break;

            if ((LEFT_CHILD(w) == NULL || GET_COLOR(HDRP(LEFT_CHILD(w))) == 1) &&
                (RIGHT_CHILD(w) == NULL || GET_COLOR(HDRP(RIGHT_CHILD(w))) == 1)) { // Case 2: sibling's children are both BLACK
                SET_RED(w);
                x = parent_x;
            } else {
                if (RIGHT_CHILD(w) == NULL || GET_COLOR(HDRP(RIGHT_CHILD(w))) == 1) { // Case 3: sibling's right child is BLACK
                    if (LEFT_CHILD(w) != NULL) SET_BLACK(LEFT_CHILD(w));
                    SET_RED(w);
                    rotate_right(w);
                    w = RIGHT_CHILD(parent_x);
                }
                if (w == NULL) break;
                // Case 4: sibling's right child is RED
                SET_COLOR(w, GET_COLOR(HDRP(parent_x)));
                SET_BLACK(parent_x);
                if (RIGHT_CHILD(w) != NULL) SET_BLACK(RIGHT_CHILD(w));
                rotate_left(parent_x);
                x = rb_root; // End loop
            }
        } else { // Symmetric case for right child
            void *w = LEFT_CHILD(parent_x);
            if (w == NULL) break;

            if (GET_COLOR(HDRP(w)) == 0) {
                SET_BLACK(w);
                SET_RED(parent_x);
                rotate_right(parent_x);
                w = LEFT_CHILD(parent_x);
            }
            if (w == NULL) break;

            if ((RIGHT_CHILD(w) == NULL || GET_COLOR(HDRP(RIGHT_CHILD(w))) == 1) &&
                (LEFT_CHILD(w) == NULL || GET_COLOR(HDRP(LEFT_CHILD(w))) == 1)) {
                SET_RED(w);
                x = parent_x;
            } else {
                if (LEFT_CHILD(w) == NULL || GET_COLOR(HDRP(LEFT_CHILD(w))) == 1) {
                    if (RIGHT_CHILD(w) != NULL) SET_BLACK(RIGHT_CHILD(w));
                    SET_RED(w);
                    rotate_left(w);
                    w = LEFT_CHILD(parent_x);
                }
                if (w == NULL) break;
                SET_COLOR(w, GET_COLOR(HDRP(parent_x)));
                SET_BLACK(parent_x);
                if (LEFT_CHILD(w) != NULL) SET_BLACK(LEFT_CHILD(w));
                rotate_right(parent_x);
                x = rb_root;
            }
        }
    }
    if (x != NULL) SET_BLACK(x);
}


/************************************************
 * Heap Checker (For Debugging)
 ************************************************/
// Functions for mm_check. No changes needed here, but kept for completeness.
static int check_rb_properties_recursive(void* node, int black_count, int* path_black_height);
static int validate_rb_tree(void);
static int is_in_free_list_recursive(void *node, void *bp);

int mm_check(void) {
    void *bp;

    // Check heap boundaries and block alignment
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if ((unsigned long)bp % DSIZE) {
            printf("Error: block %p is not doubleword aligned\n", bp);
            return 0;
        }
        if (GET(HDRP(bp)) != GET(FTRP(bp))) {
            printf("Error: header and footer of block %p do not match\n", bp);
            return 0;
        }
        // Check if free blocks are actually in the free list
        if (!GET_ALLOC(HDRP(bp))) {
            if (!is_in_free_list_recursive(rb_root, bp)) {
                printf("Error: Free block %p is not in the R-B tree.\n", bp);
                return 0;
            }
        }
    }

    // Check Red-Black tree properties
    if (!validate_rb_tree()) {
        return 0;
    }

    return 1;
}

// Recursive helper to check if bp is in the free list (R-B tree)
static int is_in_free_list_recursive(void *node, void *bp) {
    if (node == NULL) return 0;
    if (node == bp) return 1;
    
    // To handle duplicate sizes, we must check both subtrees if sizes are equal
    size_t bp_size = GET_SIZE(HDRP(bp));
    size_t node_size = GET_SIZE(HDRP(node));

    if (bp_size < node_size) {
        return is_in_free_list_recursive(LEFT_CHILD(node), bp);
    } else { // If bp_size >= node_size, check right, but also check left if sizes are equal
        if (is_in_free_list_recursive(RIGHT_CHILD(node), bp)) return 1;
        if (bp_size == node_size) {
           return is_in_free_list_recursive(LEFT_CHILD(node), bp);
        }
    }
    return 0;
}


static int validate_rb_tree() {
    if (rb_root != NULL && GET_COLOR(HDRP(rb_root)) != 1) { // Root must be BLACK
        printf("RB Tree Error: Root %p is not black\n", rb_root);
        return 0;
    }
    int black_height = -1; 
    return check_rb_properties_recursive(rb_root, 0, &black_height);
}

static int check_rb_properties_recursive(void* node, int black_count, int* path_black_height) {
    if (node == NULL) {
        black_count++; // count NIL node as black
        if (*path_black_height == -1) {
            *path_black_height = black_count;
        } else if (*path_black_height != black_count) {
            printf("RB Tree Error: Black height mismatch. Expected %d, got %d\n", *path_black_height, black_count);
            return 0;
        }
        return 1;
    }
    
    // Property 4: Red node must have black children
    if (GET_COLOR(HDRP(node)) == 0) { // is RED
        if ((LEFT_CHILD(node) != NULL && GET_COLOR(HDRP(LEFT_CHILD(node))) == 0) ||
            (RIGHT_CHILD(node) != NULL && GET_COLOR(HDRP(RIGHT_CHILD(node))) == 0)) {
            printf("RB Tree Error: Red node %p has a red child.\n", node);
            return 0;
        }
    }
    
    if (GET_COLOR(HDRP(node)) == 1) {
        black_count++;
    }

    // Check parent-child pointers consistency
    if(LEFT_CHILD(node) != NULL && PARENT(LEFT_CHILD(node)) != node) {
        printf("RB Tree Error: Parent-child mismatch at node %p\n", node);
        return 0;
    }
    if(RIGHT_CHILD(node) != NULL && PARENT(RIGHT_CHILD(node)) != node) {
        printf("RB Tree Error: Parent-child mismatch at node %p\n", node);
        return 0;
    }

    return check_rb_properties_recursive(LEFT_CHILD(node), black_count, path_black_height) &&
           check_rb_properties_recursive(RIGHT_CHILD(node), black_count, path_black_height);
}
