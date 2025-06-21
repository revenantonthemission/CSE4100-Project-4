/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>
#include <stddef.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your information in the following struct.
 ********************************************************/

// 여기에 Red-Black Tree 정의

typedef struct rb_node {
    void *key;
    struct rb_node *left;
    struct rb_node *right;
    struct rb_node *parent;
    int color;
} rb_node_t;

typedef struct rb_tree {
    rb_node_t *root;
    rb_node_t *nil;
} rb_tree_t;

team_t team = {
    /* Your student ID */
    "20190328",
    /* Your full name*/
    "Joonhee Cho",
    /* Your email address */
    "trivialife@sogang.ac.kr",
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

/* size_t is the type returned by malloc, realloc, and free */
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* $begin mallocmacros */
/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */ //line:vm:mm:beginconst
#define DSIZE       8       /* Double word size (bytes) */
#define CHUNKSIZE  (1<<12)  /* Extend heap by this amount (bytes) */  //line:vm:mm:endconst 

#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc)) //line:vm:mm:pack

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))            //line:vm:mm:get
#define PUT(p, val)  (*(unsigned int *)(p) = (val))    //line:vm:mm:put

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)                   //line:vm:mm:getsize
#define GET_ALLOC(p) (GET(p) & 0x1)                    //line:vm:mm:getalloc

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)                      //line:vm:mm:hdrp
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) //line:vm:mm:ftrp

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) //line:vm:mm:nextblkp
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) //line:vm:mm:prevblkp
/* $end mallocmacros */

/* Red-Black Tree Functions */
rb_tree_t *rb_tree_create(void);
rb_node_t *rb_tree_insert(rb_tree_t *tree, void *key);
rb_node_t *rb_tree_search(rb_tree_t *tree, void *key);
rb_node_t *rb_tree_delete(rb_tree_t *tree, void *key);
rb_node_t *minimum(rb_node_t *node, rb_tree_t *tree);
rb_node_t *maximum(rb_node_t *node, rb_tree_t *tree);

void rb_insert_fixup(rb_tree_t *tree, rb_node_t *z);
void rb_delete_fixup(rb_tree_t *tree, rb_node_t *x);
void left_rotate(rb_tree_t *tree, rb_node_t *x);
void right_rotate(rb_tree_t *tree, rb_node_t *x);
void rb_transplant(rb_tree_t *tree, rb_node_t *u, rb_node_t *v);

rb_tree_t *rb_tree_create(void) {
    rb_tree_t *tree = malloc(sizeof(rb_tree_t));
    if (!tree) return NULL;

    tree->nil = malloc(sizeof(rb_node_t));
    if (!tree->nil) {
        free(tree);
        return NULL;
    }

    tree->nil->color = 0; // Black
    tree->nil->left = NULL;
    tree->nil->right = NULL;
    tree->nil->parent = NULL;
    tree->root = tree->nil;

    return tree;
}
rb_node_t *rb_tree_insert(rb_tree_t *tree, void *key) {
    rb_node_t *new_node = malloc(sizeof(rb_node_t));
    if (!new_node) return NULL;

    new_node->key = key;
    new_node->left = tree->nil;
    new_node->right = tree->nil;
    new_node->parent = NULL;
    new_node->color = 1; // Red

    rb_node_t *y = tree->nil;
    rb_node_t *x = tree->root;

    while (x != tree->nil) {
        y = x;
        if (key < x->key)
            x = x->left;
        else
            x = x->right;
    }

    new_node->parent = y;
    if (y == tree->nil)
        tree->root = new_node; // Tree was empty
    else if (key < y->key)
        y->left = new_node;
    else
        y->right = new_node;

    rb_insert_fixup(tree, new_node);
    return new_node;
}
rb_node_t *rb_tree_search(rb_tree_t *tree, void *key) {
    rb_node_t *x = tree->root;

    while (x != tree->nil) {
        if (key == x->key)
            return x;
        else if (key < x->key)
            x = x->left;
        else
            x = x->right;
    }
    return NULL; // Not found
}
rb_node_t *rb_tree_delete(rb_tree_t *tree, void *key) {
    rb_node_t *z = rb_tree_search(tree, key);
    if (z == tree->nil) return NULL; // Not found

    rb_node_t *y = z;
    int y_original_color = y->color;
    rb_node_t *x;

    if (z->left == tree->nil) {
        x = z->right;
        rb_transplant(tree, z, z->right);
    } else if (z->right == tree->nil) {
        x = z->left;
        rb_transplant(tree, z, z->left);
    } else {
        y = minimum(z->right, tree);
        y_original_color = y->color;
        x = y->right;

        if (y->parent == z)
            x->parent = y;
        else {
            rb_transplant(tree, y, y->right);
            y->right = z->right;
            y->right->parent = y;
        }
        rb_transplant(tree, z, y);
        y->left = z->left;
        y->left->parent = y;
        y->color = z->color;
    }
    free(z);
    if (y_original_color == 0)
        rb_delete_fixup(tree, x);
    return z;
}
rb_node_t *minimum(rb_node_t *node, rb_tree_t *tree) {
    while (node->left != tree->nil) {
        node = node->left;
    }
    return node;
}
rb_node_t *maximum(rb_node_t *node, rb_tree_t *tree) {
    while (node->right != tree->nil) {
        node = node->right;
    }
    return node;
}

void rb_insert_fixup(rb_tree_t *tree, rb_node_t *z) {
    while (z->parent->color == 1) { // While z's parent is red
        if (z->parent == z->parent->parent->left) {
            rb_node_t *y = z->parent->parent->right; // Uncle
            if (y->color == 1) { // Case 1: Uncle is red
                z->parent->color = 0; // Make parent black
                y->color = 0; // Make uncle black
                z->parent->parent->color = 1; // Make grandparent red
                z = z->parent->parent; // Move up the tree
            } else {
                if (z == z->parent->right) { // Case 2: z is right child
                    z = z->parent;
                    left_rotate(tree, z);
                }
                // Case 3: z is left child
                z->parent->color = 0;
                z->parent->parent->color = 1;
                right_rotate(tree, z->parent->parent);
            }
        } else {
            rb_node_t *y = z->parent->parent->left; // Uncle
            if (y->color == 1) { // Case 1: Uncle is red
                z->parent->color = 0; // Make parent black
                y->color = 0; // Make uncle black
                z->parent->parent->color = 1; // Make grandparent red
                z = z->parent->parent; // Move up the tree
            } else {
                if (z == z->parent->left) { // Case 2: z is left child
                    z = z->parent;
                    right_rotate(tree, z);
                }
                // Case 3: z is right child
                z->parent->color = 0;
                z->parent->parent->color = 1;
                left_rotate(tree, z->parent->parent);
            }
        }
    }
    tree->root->color = 0; // Ensure root is always black
}
void rb_delete_fixup(rb_tree_t *tree, rb_node_t *x) {
    while (x != tree->root && x->color == 0) { // While x is not root and is black
        if (x == x->parent->left) {
            rb_node_t *w = x->parent->right; // Sibling
            if (w->color == 1) { // Case 1: w is red
                w->color = 0; // Make w black
                x->parent->color = 1; // Make parent red
                left_rotate(tree, x->parent);
                w = x->parent->right; // Update w
            }
            if (w->left->color == 0 && w->right->color == 0) { // Case 2: Both children are black
                w->color = 1; // Make w red
                x = x->parent; // Move up the tree
            } else {
                if (w->right->color == 0) { // Case 3: w's right child is black
                    w->left->color = 0; // Make left child black
                    w->color = 1; // Make w red
                    right_rotate(tree, w);
                    w = x->parent->right; // Update w
                }
                // Case 4: w's right child is red
                w->color = x->parent->color;
                x->parent->color = 0;
                w->right->color = 0;
                left_rotate(tree, x->parent);
                x = tree->root; // Exit loop
            }
        } else {
            rb_node_t *w = x->parent->left; // Sibling
            if (w->color == 1) { // Case 1: w is red
                w->color = 0; // Make w black
                x->parent->color = 1; // Make parent red
                right_rotate(tree, x->parent);
                w = x->parent->left; // Update w
            }
            if (w->right->color == 0 && w->left->color == 0) { // Case 2: Both children are black
                w->color = 1; // Make w red
                x = x->parent; // Move up the tree
            } else {
                if (w->left->color == 0) { // Case 3: w's left child is black
                    w->right->color = 0; // Make right child black
                    w->color = 1; // Make w red
                    left_rotate(tree, w);
                    w = x->parent->left; // Update w
                }
                // Case 4: w's left child is red
                w->color = x->parent->color;
                x->parent->color = 0;
                w->left->color = 0;
                right_rotate(tree, x->parent);
                x = tree->root; // Exit loop
            }
        }
    }
    x->color = 0; // Ensure x is black
}
void left_rotate(rb_tree_t *tree, rb_node_t *x) {
    rb_node_t *y = x->right;
    x->right = y->left;
    if (y->left != tree->nil)
        y->left->parent = x;
    y->parent = x->parent;
    if (x->parent == tree->nil)
        tree->root = y; // Update root
    else if (x == x->parent->left)
        x->parent->left = y;
    else
        x->parent->right = y;
    y->left = x;
    x->parent = y;
}
void right_rotate(rb_tree_t *tree, rb_node_t *x) {
    rb_node_t *y = x->left;
    x->left = y->right;
    if (y->right != tree->nil)
        y->right->parent = x;
    y->parent = x->parent;
    if (x->parent == tree->nil)
        tree->root = y; // Update root
    else if (x == x->parent->right)
        x->parent->right = y;
    else
        x->parent->left = y;
    y->right = x;
    x->parent = y;
}
void rb_transplant(rb_tree_t *tree, rb_node_t *u, rb_node_t *v) {
    if (u->parent == tree->nil)
        tree->root = v; // Update root
    else if (u == u->parent->left)
        u->parent->left = v;
    else
        u->parent->right = v;
    v->parent = u->parent;
}


/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    int newsize = ALIGN(size + SIZE_T_SIZE);
    void *p = mem_sbrk(newsize);
    if (p == (void *)-1)
	return NULL;
    else {
        *(size_t *)p = size;
        return (void *)((char *)p + SIZE_T_SIZE);
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{

}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}