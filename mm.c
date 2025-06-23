/*
 * mm-bplustree-full.c - A memory allocator using a complete B+ tree.
 *
 * This version provides a complete implementation of the B+ tree,
 * including handling for node splitting (for both leaf and internal nodes),
 * merging, and redistribution of keys. This ensures the tree remains
 * balanced and efficient even under complex allocation patterns.
 *
 * Free Block Structure:
 * [Header | ... (free space) ... | Footer]
 * Header/Footer: 8 bytes (size + allocation bit).
 * Minimum block size is 16 bytes.
 *
 * B+ Tree Node Structure:
 * Each node is stored in a block allocated from the heap.
 * Node: [is_leaf (1 byte) | num_keys (int) | parent_ptr | sibling_ptr | keys[] | pointers[]]
 * - is_leaf: Flag indicating if the node is a leaf.
 * - num_keys: Number of keys currently in the node.
 * - parent_ptr: Pointer to the parent node. Essential for splits and merges.
 * - sibling_ptr: Pointer to the next sibling (for leaf nodes).
 * - keys[]: Array of block sizes.
 * - pointers[]: In leaf nodes, points to free blocks. In internal nodes, points to child nodes.
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
    "20251234",
    /* Your full name*/
    "Gildong Hong",
    /* Your email address */
    "gildong@sogang.ac.kr",
};

/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */
#define DSIZE       8       /* Double word size (bytes) */
#define CHUNKSIZE   (1<<12) /* Extend heap by this amount (bytes) */
#define ALIGNMENT   8

/* B+ Tree order. MUST BE ODD for correct splitting. */
#define ORDER 5

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))
#define PUT(p, val)  (*(unsigned int *)(p) = (val))
#define PUT_P(p, val) (*(void **)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

/* B+ Tree Node access macros. Pointers are 8 bytes on 64-bit systems. */
#define IS_LEAF(np)         (*(char *)(np))
#define NUM_KEYS(np)        (*(int *)((char *)(np) + WSIZE))
#define PARENT_NODE(np)     (*(void **)((char *)(np) + DSIZE))
#define SIBLING_NODE(np)    (*(void **)((char *)(np) + DSIZE + DSIZE))
#define KEYS(np, i)         (*(size_t *)((char *)(np) + DSIZE + DSIZE + DSIZE + (i * DSIZE)))
#define POINTERS(np, i)     (*(void **)((char **)(np) + (DSIZE + DSIZE + DSIZE + (ORDER - 1) * DSIZE) / DSIZE + i))
#define BPLUS_NODE_SIZE ALIGN(DSIZE + DSIZE + DSIZE + (ORDER-1)*DSIZE + ORDER*DSIZE)

/* Global variables */
static void *heap_listp = 0;
static void *bplus_tree_root = NULL;

/* Forward declarations */
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static int get_node_index(void* parent, void* n);
static void* find_leaf(void *root, size_t size);
static void insert_into_leaf(void *leaf, size_t size, void *bp);
static void insert_into_node(void* n, int left_index, size_t key, void* right);
static void insert_into_parent(void *left, size_t key, void *right);
static void insert_block(void *bp);
static void adjust_root(void);
static void delete_block(void *bp);
static void delete_entry(void *node, size_t size, void *bp);


/*
 * mm_init - Initializes the malloc package.
 */
int mm_init(void) {
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1) return -1;
    
    PUT(heap_listp, 0);
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));
    heap_listp += (2 * WSIZE);

    bplus_tree_root = mem_sbrk(BPLUS_NODE_SIZE);
    if (bplus_tree_root == (void*)-1) return -1;
    
    IS_LEAF(bplus_tree_root) = 1;
    NUM_KEYS(bplus_tree_root) = 0;
    PUT_P(&PARENT_NODE(bplus_tree_root), NULL);
    PUT_P(&SIBLING_NODE(bplus_tree_root), NULL);

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL) return -1;
    return 0;
}

/*
 * mm_malloc - Allocate a block.
 */
void *mm_malloc(size_t size) {
    if (size == 0) return NULL;

    size_t asize = ALIGN(size + DSIZE);
    void *bp;

    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    size_t extendsize = (asize > CHUNKSIZE) ? asize : CHUNKSIZE;
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL) return NULL;
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Frees a block.
 */
void mm_free(void *bp) {
    if (bp == NULL) return;

    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    
    insert_block(coalesce(bp));
}

/*
 * mm_realloc - Reallocates a memory block.
 */
void *mm_realloc(void *ptr, size_t size) {
    if (ptr == NULL) return mm_malloc(size);
    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }

    size_t old_size = GET_SIZE(HDRP(ptr));
    size_t new_size = ALIGN(size + DSIZE);

    if (new_size <= old_size) return ptr;

    void* next_bp = NEXT_BLKP(ptr);
    if (!GET_ALLOC(HDRP(next_bp)) && (old_size + GET_SIZE(HDRP(next_bp))) >= new_size) {
        delete_block(next_bp);
        size_t total_size = old_size + GET_SIZE(HDRP(next_bp));
        PUT(HDRP(ptr), PACK(total_size, 1));
        PUT(FTRP(ptr), PACK(total_size, 1));
        return ptr;
    }

    void *newptr = mm_malloc(size);
    if (newptr == NULL) return NULL;
    
    memcpy(newptr, ptr, old_size - DSIZE);
    mm_free(ptr);
    return newptr;
}

/************************************************
 * Helper Functions for Malloc
 ************************************************/

static void *extend_heap(size_t words) {
    char *bp;
    size_t size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1) return NULL;

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);
}

static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {
        return bp;
    } else if (prev_alloc && !next_alloc) {
        delete_block(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    } else if (!prev_alloc && next_alloc) {
        delete_block(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    } else {
        delete_block(PREV_BLKP(bp));
        delete_block(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}

static void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));
    if ((csize - asize) >= (2 * DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        void* remainder = NEXT_BLKP(bp);
        PUT(HDRP(remainder), PACK(csize - asize, 0));
        PUT(FTRP(remainder), PACK(csize - asize, 0));
        insert_block(remainder);
    } else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

static void *find_fit(size_t asize) {
    void *leaf = find_leaf(bplus_tree_root, asize);
    while (leaf != NULL) {
        for (int i = 0; i < NUM_KEYS(leaf); i++) {
            if (KEYS(leaf, i) >= asize) {
                void *bp = POINTERS(leaf, i);
                delete_block(bp);
                return bp;
            }
        }
        leaf = SIBLING_NODE(leaf);
    }
    return NULL;
}

/************************************************
 * B+ Tree Full Implementation
 ************************************************/
static int get_node_index(void* parent, void* n) {
    if (parent == NULL) return -1;
    int i = 0;
    while(i <= NUM_KEYS(parent) && POINTERS(parent, i) != n) i++;
    return i;
}

static void* find_leaf(void *root, size_t size) {
    if (root == NULL) return NULL;
    void *c = root;
    while (!IS_LEAF(c)) {
        int i = 0;
        while (i < NUM_KEYS(c) && size >= KEYS(c, i)) {
            i++;
        }
        c = POINTERS(c, i);
    }
    return c;
}

static void insert_into_leaf(void *leaf, size_t size, void *bp) {
    int i = NUM_KEYS(leaf);
    while (i > 0 && KEYS(leaf, i - 1) > size) {
        PUT_P(&KEYS(leaf, i), KEYS(leaf, i - 1));
        PUT_P(&POINTERS(leaf, i), POINTERS(leaf, i - 1));
        i--;
    }
    PUT_P(&KEYS(leaf, i), size);
    PUT_P(&POINTERS(leaf, i), bp);
    NUM_KEYS(leaf)++;
}

static void insert_into_node(void* n, int left_index, size_t key, void* right) {
    for (int i = NUM_KEYS(n); i > left_index; i--) {
        PUT_P(&KEYS(n, i), KEYS(n, i - 1));
        PUT_P(&POINTERS(n, i + 1), POINTERS(n, i));
    }
    PUT_P(&POINTERS(n, left_index + 1), right);
    PUT_P(&KEYS(n, left_index), key);
    NUM_KEYS(n)++;
}

static void insert_into_parent(void *left, size_t key, void *right) {
    void* parent = PARENT_NODE(left);

    if (parent == NULL) {
        bplus_tree_root = mem_sbrk(BPLUS_NODE_SIZE);
        IS_LEAF(bplus_tree_root) = 0;
        NUM_KEYS(bplus_tree_root) = 1;
        PUT_P(&KEYS(bplus_tree_root, 0), key);
        PUT_P(&POINTERS(bplus_tree_root, 0), left);
        PUT_P(&POINTERS(bplus_tree_root, 1), right);
        PUT_P(&PARENT_NODE(left), bplus_tree_root);
        PUT_P(&PARENT_NODE(right), bplus_tree_root);
        return;
    }
    
    int left_index = get_node_index(parent, left);
    if (NUM_KEYS(parent) < ORDER - 1) {
        insert_into_node(parent, left_index, key, right);
        return;
    }

    // Split parent (internal node)
    void* new_node = mem_sbrk(BPLUS_NODE_SIZE);
    size_t temp_keys[ORDER];
    void* temp_pointers[ORDER + 1];

    for(int i=0; i < ORDER - 1; i++) temp_keys[i] = KEYS(parent, i);
    for(int i=0; i < ORDER; i++) temp_pointers[i] = POINTERS(parent, i);

    int i = 0, j = 0;;
    while(i < ORDER - 1 && KEYS(parent, i) < key) i++;

    for (int j = ORDER - 1; j > i; j--) temp_keys[j] = temp_keys[j-1];
    for (int j = ORDER; j > i + 1; j--) temp_pointers[j] = temp_pointers[j-1];
    
    temp_keys[i] = key;
    temp_pointers[i+1] = right;

    int split = (ORDER - 1) / 2;
    size_t up_key = temp_keys[split];

    NUM_KEYS(parent) = split;
    for(i=0; i<split; i++) {
        PUT_P(&KEYS(parent, i), temp_keys[i]);
        PUT_P(&POINTERS(parent, i), temp_pointers[i]);
    }
    PUT_P(&POINTERS(parent, i), temp_pointers[i]);

    IS_LEAF(new_node) = 0;
    NUM_KEYS(new_node) = ORDER - 1 - split;
    for(i=split+1, j=0; i < ORDER; i++, j++) {
        PUT_P(&KEYS(new_node, j), temp_keys[i]);
        PUT_P(&POINTERS(new_node, j), temp_pointers[i]);
        PUT_P(&PARENT_NODE(POINTERS(new_node, j)), new_node);
    }
    PUT_P(&POINTERS(new_node, j), temp_pointers[i]);
    PUT_P(&PARENT_NODE(POINTERS(new_node, j)), new_node);
    
    PUT_P(&PARENT_NODE(new_node), PARENT_NODE(parent));
    insert_into_parent(parent, up_key, new_node);
}

void insert_block(void *bp) {
    if (bplus_tree_root == NULL) return;
    size_t size = GET_SIZE(HDRP(bp));
    void* leaf = find_leaf(bplus_tree_root, size);

    if (NUM_KEYS(leaf) < ORDER - 1) {
        insert_into_leaf(leaf, size, bp);
        return;
    }

    // Split leaf node
    void* new_leaf = mem_sbrk(BPLUS_NODE_SIZE);
    size_t temp_keys[ORDER];
    void* temp_pointers[ORDER];
    int i, j;
    
    for(i=0; i < ORDER - 1; i++) {
        temp_keys[i] = KEYS(leaf, i);
        temp_pointers[i] = POINTERS(leaf, i);
    }

    i = 0;
    while(i < ORDER - 1 && KEYS(leaf, i) < size) i++;

    for (j = ORDER - 1; j > i; j--) {
        temp_keys[j] = temp_keys[j-1];
        temp_pointers[j] = temp_pointers[j-1];
    }
    temp_keys[i] = size;
    temp_pointers[i] = bp;

    int split = ORDER / 2;
    NUM_KEYS(leaf) = split;
    for(i=0; i<split; i++) {
        PUT_P(&KEYS(leaf, i), temp_keys[i]);
        PUT_P(&POINTERS(leaf, i), temp_pointers[i]);
    }

    IS_LEAF(new_leaf) = 1;
    NUM_KEYS(new_leaf) = ORDER - split;
    for(i=split, j=0; i < ORDER; i++, j++) {
        PUT_P(&KEYS(new_leaf, j), temp_keys[i]);
        PUT_P(&POINTERS(new_leaf, j), temp_pointers[i]);
    }

    PUT_P(&SIBLING_NODE(new_leaf), SIBLING_NODE(leaf));
    PUT_P(&SIBLING_NODE(leaf), new_leaf);
    PUT_P(&PARENT_NODE(new_leaf), PARENT_NODE(leaf));
    
    insert_into_parent(leaf, KEYS(new_leaf, 0), new_leaf);
}

static void delete_block(void *bp) {
    if (bp == NULL) return;
    size_t size = GET_SIZE(HDRP(bp));
    void* leaf = find_leaf(bplus_tree_root, size);
    if(leaf) delete_entry(leaf, size, bp);
}

static void adjust_root() {
    if (NUM_KEYS(bplus_tree_root) == 0 && !IS_LEAF(bplus_tree_root)) {
        void* new_root = POINTERS(bplus_tree_root, 0);
        if(new_root) PUT_P(&PARENT_NODE(new_root), NULL);
        // Old root is abandoned (leak) but this simplifies logic
        bplus_tree_root = new_root;
    }
}

static void coalesce_nodes(void *node, void *neighbor, int neighbor_index, void *parent, int k_prime_index) {
    int i, j, neighbor_insertion_index, n_end;
    void *tmp;

    if (neighbor_index == -1) { // node is leftmost child
        tmp = node; node = neighbor; neighbor = tmp;
    }

    neighbor_insertion_index = NUM_KEYS(neighbor);
    
    if (!IS_LEAF(node)) {
        KEYS(neighbor, neighbor_insertion_index) = KEYS(parent, k_prime_index);
        NUM_KEYS(neighbor)++;
    }

    n_end = NUM_KEYS(node);
    for (i = neighbor_insertion_index + 1, j = 0; j < n_end; i++, j++) {
        KEYS(neighbor, i) = KEYS(node, j);
        POINTERS(neighbor, i) = POINTERS(node, j);
        NUM_KEYS(neighbor)++;
        NUM_KEYS(node)--;
    }
    
    if (!IS_LEAF(neighbor)) {
        for(i = 0; i <= NUM_KEYS(neighbor); i++) {
            tmp = POINTERS(neighbor, i);
            PUT_P(&PARENT_NODE(tmp), neighbor);
        }
    }

    SIBLING_NODE(neighbor) = SIBLING_NODE(node);
    delete_entry(parent, KEYS(parent, k_prime_index), node);
    // free(node) -> abandoned leak
}

static void redistribute_nodes(void *node, void *neighbor, int neighbor_index, void *parent, int k_prime_index) {
    int i;
    if (neighbor_index != -1) { // neighbor is to the left
        if (!IS_LEAF(node))
            POINTERS(node, NUM_KEYS(node) + 1) = POINTERS(node, NUM_KEYS(node));
        for (i = NUM_KEYS(node); i > 0; i--) {
            KEYS(node, i) = KEYS(node, i - 1);
            POINTERS(node, i) = POINTERS(node, i - 1);
        }
        if (!IS_LEAF(node)) {
            POINTERS(node, 0) = POINTERS(neighbor, NUM_KEYS(neighbor));
            void* tmp = POINTERS(node, 0);
            PUT_P(&PARENT_NODE(tmp), node);
            KEYS(node, 0) = KEYS(parent, k_prime_index);
            PUT_P(&KEYS(parent, k_prime_index), KEYS(neighbor, NUM_KEYS(neighbor) - 1));
        } else {
            POINTERS(node, 0) = POINTERS(neighbor, NUM_KEYS(neighbor) - 1);
            KEYS(node, 0) = KEYS(neighbor, NUM_KEYS(neighbor) - 1);
            PUT_P(&KEYS(parent, k_prime_index), KEYS(node, 0));
        }
    } else { // neighbor is to the right
        if (IS_LEAF(node)) {
            KEYS(node, NUM_KEYS(node)) = KEYS(neighbor, 0);
            POINTERS(node, NUM_KEYS(node)) = POINTERS(neighbor, 0);
            PUT_P(&KEYS(parent, k_prime_index), KEYS(neighbor, 1));
        } else {
            KEYS(node, NUM_KEYS(node)) = KEYS(parent, k_prime_index);
            POINTERS(node, NUM_KEYS(node) + 1) = POINTERS(neighbor, 0);
            void* tmp = POINTERS(node, NUM_KEYS(node) + 1);
            PUT_P(&PARENT_NODE(tmp), node);
            PUT_P(&KEYS(parent, k_prime_index), KEYS(neighbor, 0));
        }
        for (i = 0; i < NUM_KEYS(neighbor) - 1; i++) {
            KEYS(neighbor, i) = KEYS(neighbor, i + 1);
            POINTERS(neighbor, i) = POINTERS(neighbor, i + 1);
        }
        if (!IS_LEAF(neighbor))
            POINTERS(neighbor, i) = POINTERS(neighbor, i + 1);
    }

    NUM_KEYS(node)++;
    NUM_KEYS(neighbor)--;
}

static void delete_entry(void *node, size_t size, void *bp) {
    int i = 0;
    while (i < NUM_KEYS(node) && KEYS(node, i) != size) i++;
    while (i < NUM_KEYS(node) && KEYS(node, i) == size && POINTERS(node, i) != bp) i++;

    if (i == NUM_KEYS(node)) return;

    for (; i < NUM_KEYS(node) - 1; i++) {
        KEYS(node, i) = KEYS(node, i + 1);
        POINTERS(node, i) = POINTERS(node, i + 1);
    }
    NUM_KEYS(node)--;

    if (node == bplus_tree_root) {
        adjust_root();
        return;
    }

    int min_keys = (ORDER - 1) / 2;
    if (NUM_KEYS(node) >= min_keys) return;

    void* parent = PARENT_NODE(node);
    int node_idx = get_node_index(parent, node);
    int k_prime_idx = node_idx > 0 ? node_idx - 1 : 0;
    
    int neighbor_idx;
    if (node_idx == 0) neighbor_idx = 1;
    else neighbor_idx = node_idx - 1;
    
    void* neighbor = POINTERS(parent, neighbor_idx);

    if (NUM_KEYS(neighbor) > min_keys) {
        redistribute_nodes(node, neighbor, node_idx > 0 ? neighbor_idx : -1, parent, k_prime_idx);
    } else {
        coalesce_nodes(node, neighbor, node_idx > 0 ? neighbor_idx : -1, parent, k_prime_idx);
    }
}
