/**
 * @file mm.c
 * @brief A 64-bit struct-based implicit free list memory allocator
 *
 * 15-213: Introduction to Computer Systems
 *
 * TODO: insert your documentation here. :)
 *
 *************************************************************************
 *
 * ADVICE FOR STUDENTS.
 * - Step 0: Please read the writeup!
 * - Step 1: Write your heap checker.
 * - Step 2: Write contracts / debugging assert statements.
 * - Good luck, and have fun!
 *
 *************************************************************************
 *
 * @author Austin Lin <allin@andrew.cmu.edu>
 */

#include <assert.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"

/* Do not change the following! */

#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* def DRIVER */

/* You can change anything from here onward */

/*
 *****************************************************************************
 * If DEBUG is defined (such as when running mdriver-dbg), these macros      *
 * are enabled. You can use them to print debugging output and to check      *
 * contracts only in debug mode.                                             *
 *                                                                           *
 * Only debugging macros with names beginning "dbg_" are allowed.            *
 * You may not define any other macros having arguments.                     *
 *****************************************************************************
 */
#ifdef DEBUG
/* When DEBUG is defined, these form aliases to useful functions */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_requires(expr) assert(expr)
#define dbg_assert(expr) assert(expr)
#define dbg_ensures(expr) assert(expr)
#define dbg_printheap(...) print_heap(__VA_ARGS__)
#else
/* When DEBUG is not defined, no code gets generated for these */
/* The sizeof() hack is used to avoid "unused variable" warnings */
#define dbg_printf(...) (sizeof(__VA_ARGS__), -1)
#define dbg_requires(expr) (sizeof(expr), 1)
#define dbg_assert(expr) (sizeof(expr), 1)
#define dbg_ensures(expr) (sizeof(expr), 1)
#define dbg_printheap(...) ((void)sizeof(__VA_ARGS__))
#endif

/* Basic constants */

typedef uint64_t word_t;

/** @brief Word and header size (bytes) */
static const size_t wsize = sizeof(word_t);

/** @brief Double word size (bytes) */
static const size_t dsize = 2 * wsize;

/** @brief Minimum block size (bytes) */
static const size_t min_block_size = dsize;

/** @brief Size of Header and 2 pointers */
static const size_t header_and_pointer_size = wsize + 2 * sizeof(void *);

/** @brief Minimum size of a free block that has a header, prev and next
 * pointers, and a footer */
static const size_t min_full_free_block_size = 32;

/**
 * TODO: explain what chunksize is
 * (Must be divisible by dsize)
 */
static const size_t chunksize = (1 << 12);

/**
 * TODO: explain what alloc_mask is
 */
static const word_t alloc_mask = 0x1;

/**
 * TODO: explain what size_mask is
 */
static const word_t size_mask = ~(word_t)0xF;

typedef struct block block_t;
typedef struct freed_block_contents {

    block_t *next;
    block_t *prev;

} freed_block_contents_t;

typedef union block_contents {
    /** @brief pointer to the free and next pointers */
    freed_block_contents_t prev_next_pointers;

    /**
     * @brief A pointer to the block payload.
     */
    char payload[0];
} block_contents_t;

/** @brief Represents the header and payload of one block in the heap */
typedef struct block {

    /** @brief Header contains size + allocation flag */
    word_t header;

    /**
     * @brief A pointer to the block payload.
     */
    block_contents_t payload_contents;

} block_t;

/* Global variables */

/** @brief Pointer to first block in the heap */
static block_t *heap_start = NULL;

/** @brief the number of free lists */
#define max_free_lists 15

/** @brief Pointer to first freed block in each seg list */
static block_t *free_lists[max_free_lists];

static const uint32_t free_list_size_limits[max_free_lists] = {
    16,   32,   48,   64,   128,   256,   512,   768,
    1024, 2048, 4096, 8192, 16384, 32768, 577536};

/*
 *****************************************************************************
 * The functions below are short wrapper functions to perform * bit
 *manipulation, pointer arithmetic, and other helper operations.        *
 *                                                                           *
 * We've given you the function header comments for the functions below * to
 *help you understand how this baseline code works.                      *
 *                                                                           *
 * Note that these function header comments are short since the functions *
 * they are describing are short as well; you will need to provide *
 * adequate details for the functions that you write yourself! *
 *****************************************************************************
 */

/*
 * ---------------------------------------------------------------------------
 *                        BEGIN SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

static void print_heap(char *msg);
static bool block_is_alligned(block_t *curr_block);
static size_t get_size(block_t *block);
static block_t *find_next(block_t *block);
static bool get_alloc(block_t *block);
static bool get_prev_alloc(block_t *block);
static word_t pack(size_t size, bool alloc, bool prev_alloc);
static bool check_header_footer(block_t *curr_block);

static block_t *get_free_list(size_t size) {
    for (int i = 0; i < max_free_lists; i++) {
        if (size <= free_list_size_limits[i]) {
            return free_lists[i];
        }
    }
    dbg_assert(size > free_list_size_limits[max_free_lists - 2]);
    return free_lists[max_free_lists - 1];
}

static int get_free_list_index(size_t size) {
    for (int i = 0; i < max_free_lists; i++) {
        if (size <= free_list_size_limits[i]) {
            return i;
        }
    }
    dbg_assert(size > free_list_size_limits[max_free_lists - 2]);
    return max_free_lists - 1;
}

static void write_free_list_start(size_t size, block_t *block) {
    for (int i = 0; i < max_free_lists; i++) {
        if (size <= free_list_size_limits[i]) {
            free_lists[i] = block;
            return;
        }
    }
    dbg_assert(size > free_list_size_limits[max_free_lists - 2]);
    free_lists[max_free_lists - 1] = block;
}

static freed_block_contents_t *get_free_block_contents(block_t *block) {
    freed_block_contents_t *prev_next_pointers =
        &(block->payload_contents.prev_next_pointers);
    return prev_next_pointers;
}

static block_t *get_prev_free_block(block_t *block) {
    if (get_size(block) < min_full_free_block_size)
        return NULL;
    freed_block_contents_t *prev_next_pointers = get_free_block_contents(block);
    return prev_next_pointers->prev;
}

static block_t *get_next_free_block(block_t *block) {
    freed_block_contents_t *prev_next_pointers = get_free_block_contents(block);
    return prev_next_pointers->next;
}

// from: https://www.cs.cmu.edu/~15122/handouts/10-linkedlist.pdf
static bool is_acyclic(block_t *free_list_start) {

    if (free_list_start == NULL)
        return true;
    block_t *h = get_next_free_block(free_list_start); // hare
    block_t *t = free_list_start;                      // tortoise
    while (h != t) {
        if (h == NULL || get_next_free_block(h) == NULL)
            return true;
        h = get_next_free_block(get_next_free_block(h));
        dbg_assert(t != NULL);
        // faster hare hits NULL quicker
        t = get_next_free_block(t);
    }
    dbg_assert(h == t);
    return false;
}

/**
 * @brief
 * TODO: fix the function
 */
static void write_next_pointer(block_t *block, block_t *next_free_block) {
    block->payload_contents.prev_next_pointers.next = next_free_block;
}

/**
 * @brief
 * TODO: fix the function
 */
static void write_prev_pointer(block_t *block, block_t *prev_free_block) {
    dbg_requires((block) != NULL);
    if (get_size(block) >= min_full_free_block_size)
        block->payload_contents.prev_next_pointers.prev = prev_free_block;
}

static void write_prev_alloc(block_t *block, bool prev_alloc) {
    dbg_requires((block) != NULL);
    size_t size = get_size(block);
    bool alloc = get_alloc(block);
    block->header = pack(size, alloc, prev_alloc);
    dbg_assert(get_prev_alloc(block) == prev_alloc);
}

static block_t *remove_free_block(block_t *block) {

    block_t *free_list_start = get_free_list(get_size(block));

    dbg_requires(block_is_alligned(block));
    block_t *prev_block = get_prev_free_block(block);
    block_t *next_block = get_next_free_block(block);

    if (prev_block != NULL) {
        write_next_pointer(prev_block, next_block);
        dbg_printheap("wrote prev_block's next pointer");
    }
    if (next_block != NULL) {
        write_prev_pointer(next_block, prev_block);
        dbg_printheap("wrote next_block's prev pointer");
    }

    if (prev_block == NULL && next_block == NULL)
        write_free_list_start(get_size(block), NULL);
    else if (block == free_list_start)
        write_free_list_start(get_size(block), next_block);

    // write_next_pointer(block, NULL);
    // write_prev_pointer(block, NULL);

    return block;
}

/**
 * @brief Returns the maximum of two integers.
 * @param[in] x
 * @param[in] y
 * @return `x` if `x > y`, and `y` otherwise.
 */
static size_t max(size_t x, size_t y) {
    return (x > y) ? x : y;
}

/**
 * @brief Rounds `size` up to next multiple of n
 * @param[in] size
 * @param[in] n
 * @return The size after rounding up
 */
static size_t round_up(size_t size, size_t n) {
    return n * ((size + (n - 1)) / n);
}

/**
 * @brief Packs the `size` and `alloc` of a block into a word suitable for
 *        use as a packed value.
 *
 * Packed values are used for both headers and footers.
 *
 * The allocation status is packed into the lowest bit of the word.
 *
 * @param[in] size The size of the block being represented
 * @param[in] alloc True if the block is allocated
 * @return The packed value
 */
static word_t pack(size_t size, bool alloc, bool prev_alloc) {
    word_t word = size;
    if (prev_alloc) {
        word |= (alloc_mask << 1); // set second bit
    }
    if (alloc) {
        word |= alloc_mask; // set first bit
    }
    return word;
}

/**
 * @brief Extracts the size represented in a packed word.
 *
 * This function simply clears the lowest 4 bits of the word, as the heap
 * is 16-byte aligned.
 *
 * @param[in] word
 * @return The size of the block represented by the word
 */
static size_t extract_size(word_t word) {
    return (word & size_mask);
}

/**
 * @brief Extracts the size of a block from its header.
 * @param[in] block
 * @return The size of the block
 */
static size_t get_size(block_t *block) {
    return extract_size(block->header);
}

/**
 * @brief Given a payload pointer, returns a pointer to the corresponding
 *        block.
 * @param[in] bp A pointer to a block's payload
 * @return The corresponding block
 */
static block_t *payload_to_header(void *bp) {
    return (block_t *)((char *)bp - offsetof(block_t, payload_contents));
}

/**
 * @brief Given a block pointer, returns a pointer to the corresponding
 *        payload.
 * @param[in] block
 * @return A pointer to the block's payload
 * @pre The block must be a valid block, not a boundary tag.
 */
static void *header_to_payload(block_t *block) {
    dbg_requires(get_size(block) != 0);
    return (void *)(&block->payload_contents);
}

/**
 * @brief Given a block pointer, returns a pointer to the corresponding
 *        footer.
 * @param[in] block
 * @return A pointer to the block's footer
 * @pre The block must be a valid block, not a boundary tag.
 */
static word_t *header_to_footer(block_t *block) {
    dbg_requires(get_size(block) != 0 &&
                 "Called header_to_footer on the epilogue block");
    return (word_t *)(((void *)&block->payload_contents) + get_size(block) -
                      dsize);
}

/**
 * @brief Given a block footer, returns a pointer to the corresponding
 *        header.
 * @param[in] footer A pointer to the block's footer
 * @return A pointer to the start of the block
 * @pre The footer must be the footer of a valid block, not a boundary tag.
 */
static block_t *footer_to_header(word_t *footer) {
    size_t size = extract_size(*footer);
    return (block_t *)((char *)footer + wsize - size);
}

static bool get_alloc(block_t *block);
/**
 * @brief Returns the payload size of a given block.
 *
 * The payload size is equal to the entire block size minus the sizes of the
 * block's header and footer.
 *
 * @param[in] block
 * @return The size of the block's payload
 */
static size_t get_payload_size(block_t *block) {
    size_t asize = get_size(block);
    if (get_alloc(block) == 0)
        return asize - dsize;
    else
        return asize - wsize;
}

/**
 * @brief Returns the allocation status of a given header value.
 *
 * This is based on the lowest bit of the header value.
 *
 * @param[in] word
 * @return The allocation status correpsonding to the word
 */
static bool extract_alloc(word_t word) {
    return (bool)(word & alloc_mask);
}

/**
 * @brief Returns the allocation status of the prevous block of given header
 * value.
 *
 * This is based on the 2nd lowest bit of the header value.
 *
 * @param[in] word
 * @return The allocation status of the previous block correpsonding to the word
 */
static bool extract_prev_alloc(word_t word) {
    return (bool)(word & (alloc_mask << 1));
}

/**
 * @brief Returns the allocation status of a block, based on its header.
 * @param[in] block
 * @return The allocation status of the block
 */
static bool get_alloc(block_t *block) {
    return extract_alloc(block->header);
}

/**
 * @brief Returns the allocation status of the previous block, based on its
 * header.
 * @param[in] block
 * @return The allocation status of the prev block
 */
static bool get_prev_alloc(block_t *block) {
    return extract_prev_alloc(block->header);
}

/**
 * @brief Writes an epilogue header at the given address.
 *
 * The epilogue header has size 0, and is marked as allocated.
 *
 * @param[out] block The location to write the epilogue header
 */
static void write_epilogue(block_t *block) {
    dbg_requires((char *)block == mem_heap_hi() - 7);
    block->header = pack(0, true, false);
}

/**
 * @brief Writes a block starting at the given address.
 *
 * This function writes both a header and footer, where the location of the
 * footer is computed in relation to the header.
 *
 * TODO: Are there any preconditions or postconditions?
 *
 * @param[out] block The location to begin writing the block header
 * @param[in] size The size of the new block
 * @param[in] alloc The allocation status of the new block
 */
static void write_block(block_t *block, size_t size, bool alloc) {
    dbg_requires(block != NULL);
    dbg_requires(size > 0);

    if (alloc == true && get_alloc(block) == false) {
        remove_free_block(block);
        // block_t *next_block = find_next(block);
        // write_prev_alloc(next_block, true);
        // dbg_assert(get_prev_alloc(next_block) == true);
        // dbg_printheap("pack");
    }

    bool prev_alloc = get_prev_alloc(block);
    block->header = pack(size, alloc, prev_alloc);

    block_t *free_list_start = get_free_list(get_size(block));

    if (alloc == false) {
        // write next and prev pointers
        word_t *footerp = header_to_footer(block);
        *footerp = block->header;
        if (free_list_start != block)
            write_next_pointer(block, free_list_start);
        else
            write_next_pointer(block, get_next_free_block(block));
        write_prev_pointer(block, NULL);
        if (free_list_start != NULL && get_alloc(free_list_start) == false &&
            free_list_start != block)
            write_prev_pointer(free_list_start, block);
        write_free_list_start(get_size(block), block);
        dbg_assert(check_header_footer(block));
    }
}

/**
 * @brief Finds the next consecutive block on the heap.
 *
 * This function accesses the next block in the "implicit list" of the heap
 * by adding the size of the block.
 *
 * @param[in] block A block in the heap
 * @return The next consecutive block on the heap
 * @pre The block is not the epilogue
 */
static block_t *find_next(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires(get_size(block) != 0 &&
                 "Called find_next on the last block in the heap");
    return (block_t *)((char *)block + get_size(block));
}

/**
 * @brief Finds the footer of the previous block on the heap.
 * @param[in] block A block in the heap
 * @return The location of the previous block's footer
 */
static word_t *find_prev_footer(block_t *block) {
    // Compute previous footer position as one word before the header
    return &(block->header) - 1;
}

/**
 * @brief Finds the previous consecutive block on the heap.
 *
 * This is the previous block in the "implicit list" of the heap.
 *
 * If the function is called on the first block in the heap, NULL will be
 * returned, since the first block in the heap has no previous block!
 *
 * The position of the previous block is found by reading the previous
 * block's footer to determine its size, then calculating the start of the
 * previous block based on its size.
 *
 * @param[in] block A block in the heap
 * @return The previous consecutive block in the heap.
 */
static block_t *find_prev(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires(get_size(block) != 0);
    word_t *footerp = find_prev_footer(block);
    size_t size = extract_size(*footerp);
    return (block_t *)((char *)block - size);
}

/**
 * @brief Prints error messages
 *
 * @param[in] error_msg - string that represents the error
 * @return nothing
 */
static void print_error(char *error_msg) {
    printf("Error: %16s \n", error_msg);
}

/**
 * @brief Checks to make sure the heap has a prologue and a epilogue
 *
 * @return true if the heap has a prologue and a epilogue
 */
bool has_epilogue_prologue() {
    // if (*(word_t *)mem_heap_lo() != pack(0, true))
    //     return false;
    // if (*(word_t *)(mem_heap_hi() - 7) != pack(0, true))
    //     return false;
    return true;
}

/**
 * @brief Checks to make sure the block is alligned
 *
 * @param[in] curr_block - pointer of the block to be tested
 * @return true if address is a multiple of 16 false otherwise
 */
static bool block_is_alligned(block_t *curr_block) {
    if ((size_t)curr_block % (size_t)8 != 0) {
        return false;
    }
    return true;
}

/**
 * @brief Checks to make sure the block is within heap boundaries
 *
 * @param[in] curr_block - pointer of the block to be tested
 * @return true if block address is witin the heap boundaries false otherwise
 */
static bool block_within_heap(block_t *curr_block) {
    if ((void *)curr_block < mem_heap_lo() ||
        (void *)curr_block > mem_heap_hi() || curr_block == NULL) {
        return false;
    }
    return true;
}

/**
 * @brief Checks to make sure the block's header and footer is valid
 *
 * @param[in] curr_block - pointer of the block to be tested
 * @return true if block is larger than min size, and header and footer are
 * consistent
 */
static bool check_header_footer(block_t *curr_block) {
    word_t header = curr_block->header;
    word_t footer = *header_to_footer(curr_block);

    if (get_alloc(curr_block) == 1)
        return true; // block is allocated and has no footer
    if (get_size(curr_block) < min_block_size) {
        dbg_printf("size: %zu", get_size(curr_block));
        print_error("Block smaller than min size.");
        return false;
    }

    /** TODO: magic number */
    if (extract_size(header) != extract_size(footer) &&
        get_size(curr_block) >= min_full_free_block_size) {
        printf(
            "Error: Block size inconsistent between header and footer: %p \n",
            curr_block);
        return false;
    }
    if (extract_alloc(header) != extract_alloc(footer)) {
        print_error("Block alloc bit inconsistent between header and footer.");
        return false;
    }
    return true;
}

static void print_heap(char *msg) {
    for (block_t *curr_block = heap_start; get_size(curr_block) > 0;
         curr_block = find_next(curr_block)) {
        if (get_alloc(curr_block) == false) {
            printf("addr: %p \t size: %zu \t prev_alloc: %d \t alloc: %d \t "
                   "prev: %p \t next: %p "
                   "\t msg: %s \n",
                   curr_block, get_size(curr_block), get_prev_alloc(curr_block),
                   get_alloc(curr_block),
                   (void *)get_prev_free_block(curr_block),
                   (void *)get_next_free_block(curr_block), msg);
        }
        if (get_alloc(curr_block) == true) {
            printf("addr: %p \t size: %zu \t prev_alloc: %d \t alloc: %d \t "
                   "next_block: %p"
                   "\t\t\t msg: %s \n",
                   curr_block, get_size(curr_block), get_prev_alloc(curr_block),
                   get_alloc(curr_block), curr_block + get_size(curr_block),
                   msg);
        }
    }
    printf("\n");
}

static void print_free_list(char *msg) {
    for (int i = 0; i < max_free_lists; i++) {

        block_t *free_list_start = free_lists[i];
        if (free_list_start != NULL) {
            block_t *block = free_list_start;
            freed_block_contents_t *prev_next_pointers =
                get_free_block_contents(block);

            for (; block != NULL; block = (prev_next_pointers->next)) {
                printf("addr: %p \t size: %zu \t alloc: %d \t prev: %p \t "
                       "next: %p "
                       "\t msg: %s \n",
                       block, get_size(block), get_alloc(block),
                       (void *)get_prev_free_block(block),
                       (void *)get_next_free_block(block), msg);
                prev_next_pointers = get_free_block_contents(block);
            }
        }
    }

    printf("\n");
}

/*
 * ---------------------------------------------------------------------------
 *                        END SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/******** The remaining content below are helper and debug routines ********/

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] block
 * @return
 */
static block_t *coalesce_block(block_t *block) {
    /*
     * TODO: delete or replace this comment once you're done.
     *
     * Before you start, it will be helpful to review the "Dynamic Memory
     * Allocation: Basic" lecture, and especially the four coalescing
     * cases that are described.
     *
     * The actual content of the function will probably involve a call to
     * find_prev(), and multiple calls to write_block(). For examples of how
     * to use write_block(), take a look at split_block().
     *
     * Please do not reference code from prior semesters for this, including
     * old versions of the 213 website. We also discourage you from looking
     * at the malloc code in CS:APP and K&R, which make heavy use of macros
     * and which we no longer consider to be good style.
     */
    dbg_requires(block != NULL);
    dbg_requires(get_size(block) != 0);
    dbg_requires(get_alloc(block) == false);

    dbg_printheap("");
    block_t *prev_block;
    if (get_size(block) >= min_full_free_block_size)
        prev_block = find_prev(block);
    block_t *next_block = find_next(block);
    size_t curr_block_size = get_size(block);

    // case 1 do not go into the for loop
    /* prev_block == block when prev_block is the prolgue block. the prologue
     * block is freed and we do not want to coalesce the prologue block with
     * block
     */
    if (curr_block_size > 0 &&
        ((get_alloc(next_block) == false) ||
         (get_prev_alloc(block) == false && prev_block != block))) {

        size_t prev_block_size;
        if (get_prev_alloc(block) ==
            false) // only get prev block size if it is freed
            prev_block_size = get_size(prev_block);
        size_t next_block_size = get_size(next_block);

        // case 2
        /* prev_block == block when prev_block is the prolgue block. the
         * prologue block is freed and we do not want to coalesce the prologue
         * block with block
         */
        if ((get_prev_alloc(block) == true ||
             (get_prev_alloc(block) == false && prev_block == block)) &&
            (get_alloc(next_block) == false && next_block != block)) {

            block_t *free_list_start =
                get_free_list(curr_block_size + next_block_size);

            if (block != free_list_start) {
                remove_free_block(block);
                dbg_printheap("remove curr block");
            }
            write_block(block, curr_block_size + next_block_size, false);
            dbg_printheap("write new block");
            remove_free_block(next_block);
            dbg_printheap("remove next block");
            dbg_printf("case 2");
        }

        // case 3
        else if ((get_prev_alloc(block) == false && prev_block != block) &&
                 (get_alloc(next_block) == true)) {

            block_t *free_list_start =
                get_free_list(curr_block_size + prev_block_size);

            if (prev_block != free_list_start) {
                remove_free_block(prev_block);
                dbg_printheap("remove prev block");
            }
            write_block(prev_block, curr_block_size + prev_block_size, false);
            dbg_printheap("write new block");

            remove_free_block(block);
            dbg_printheap("rem curr block");

            block = prev_block;
            dbg_printf("case 3");
        }

        // case 4
        else if ((get_prev_alloc(block) == false && prev_block != block) &&
                 (get_alloc(next_block) == false)) {

            remove_free_block(prev_block);
            dbg_printheap("remove block 68");

            write_block(prev_block,
                        curr_block_size + prev_block_size + next_block_size,
                        false);
            dbg_printheap("write new combined block");
            remove_free_block(next_block);
            dbg_printheap("remove next block");
            remove_free_block(block);
            dbg_printheap("remove block");

            block = prev_block;
            dbg_printf("case 4");
        }
    }

    dbg_printheap("");
    dbg_assert(check_header_footer(block));
    dbg_assert(mm_checkheap(__LINE__));
    return block;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] size
 * @return
 */
static block_t *extend_heap(size_t size) {
    void *bp;

    word_t old_epilogue = *(word_t *)(mem_heap_hi() - 7);
    size_t orig_heap_size = mem_heapsize();

    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk(size)) == (void *)-1) {
        return NULL;
    }

    /*
     * TODO: delete or replace this comment once you've thought about it.
     * Think about what bp represents. Why do we write the new block
     * starting one word BEFORE bp, but with the same size that we
     * originally requested?
     */

    // Initialize free block header/footer
    block_t *block = payload_to_header(bp);
    write_block(block, size, false);

    if (orig_heap_size >= min_block_size) // only write the prev alloc if there
                                          // are blocks in the heap
        write_prev_alloc(block, extract_prev_alloc(old_epilogue));

    // if there are no free blocks in the free list, set free_list_start to this
    // block
    block_t *free_list_start = get_free_list(get_size(block));
    if (free_list_start == NULL) {
        write_free_list_start(get_size(block), block);
    }

    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_epilogue(block_next);

    // Coalesce in case the previous block was free
    block = coalesce_block(block);

    dbg_ensures(mm_checkheap(__LINE__));
    return block;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] block
 * @param[in] asize
 */
static void split_block(block_t *block, size_t asize) {
    dbg_requires(get_alloc(block));
    /* TODO: Can you write a precondition about the value of asize? */

    size_t block_size = get_size(block);

    if ((block_size - asize) >= min_block_size) {

        block_t *block_split;
        write_block(block, asize, true);

        block_split = find_next(block);
        write_block(block_split, block_size - asize, false);
        write_prev_alloc(block_split, true);
    }

    dbg_ensures(get_alloc(block));
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] asize
 * @return
 */
static block_t *find_fit(size_t asize) {
    dbg_printheap("");
    int free_list_index = get_free_list_index(asize);
    block_t *possible_block = NULL;
    for (; free_list_index < max_free_lists; free_list_index++) {
        block_t *free_list_start = free_lists[free_list_index];
        if (free_list_start != NULL) {
            block_t *block = free_list_start;
            freed_block_contents_t *prev_next_pointers =
                get_free_block_contents(block);

            for (; block != NULL; block = (prev_next_pointers->next)) {
                if (!(get_alloc(block)) && (asize <= get_size(block))) {

                    return block; // comment this out for final

                    // if perfect fit return
                    if (get_size(block) == asize)
                        return block;

                    // the block works and there wasn't
                    // another block that works, save it
                    else if (asize <= get_size(block) &&
                             possible_block == NULL) {
                        possible_block = block;
                    }

                    // the block works and there was another
                    // block that works, return the smaller one
                    else if (get_size(block) == asize &&
                             possible_block != NULL) {
                        if (get_size(block) <= get_size(possible_block))
                            return block;
                        else
                            return possible_block;
                    }
                }
                prev_next_pointers = get_free_block_contents(block);
            }
        }
    }
    return possible_block; // no fit found return the only block that fit or
                           // null
}

/**
 * @brief checks to make sure the heap is valid
 *
 * Heap:
 * ensure heap has an epilogue and a prologue
 * ensure blocks is properly alligned to 16 bytes
 * check to make sure the block is between block boundaries
 * check to make sure headers and footers are the same
 * check to make sure coalesing is correct i.e. no free blocks next to each
 * other
 *
 * Free lists:
 * make sure free lists has no cycles
 * check to make sure there are no allocated blocks in the free list
 * check consistency of the current block's next pointer
 * ensure that the number of blocks in the free list is the same as the number
 * in the heap ensure all blocks are within the right bucket size range.
 *
 * @param[in] line
 * @return bool true if the heap is correct, false if there are problems with
 * the heap.
 */
bool mm_checkheap(int line) {

    // ensure heap has an epilogue and a prologue
    if (!has_epilogue_prologue()) {
        char *error_msg = "No prologue or epilogue.";
        print_error(error_msg);
        return false;
    }

    // sentry variable to make sure coalesing does not fail on the first block
    // in the heap
    unsigned short prev_alloc = 1;

    // tally the number of free blocks in the heap to compare to number in free
    // lists
    uint64_t num_free_heap_blocks = 0;

    for (block_t *curr_block = heap_start; get_size(curr_block) > 0;
         curr_block = find_next(curr_block)) {

        // ensure block is properly alligned to 16 bytes
        if (!block_is_alligned(curr_block)) {
            print_error("Blocks not alligned.");
            return false;
        }

        // check to make sure the block is between block boundaries
        if (!block_within_heap(curr_block)) {
            print_error("Block not within block boundaries.");
            return false;
        }

        // check to make sure headers and footers are the same
        if (!check_header_footer(curr_block)) {
            return false;
        }

        // check to make sure coalesing is correct
        // i.e. no free blocks next to each other
        if (get_alloc(curr_block) == 0 && prev_alloc == 0) {
            print_error(
                "Coalesing incorrect. Two free consecutive blocks in heap.");
            return false;
        } else
            prev_alloc = get_alloc(curr_block);

        // count free blocks in heap to compare to those in the free lists
        if ((get_alloc(curr_block) == 0))
            num_free_heap_blocks++;
    }

    // counts the number of free blocks in the heap
    uint64_t num_free_list_blocks = 0;

    // iterate through each free list
    for (int i = 0; i < max_free_lists; i++) {
        block_t *free_list_start = free_lists[i];

        // make sure free list has no cycles
        if (!is_acyclic(free_list_start)) {
            print_error("free list has cycle.");
            return false;
        }

        if (free_list_start != NULL) {

            // iterate through each block in the free list
            block_t *block = free_list_start;
            freed_block_contents_t *prev_next_pointers =
                get_free_block_contents(block);

            dbg_printheap("Check free list");
            for (; block != NULL; block = (prev_next_pointers->next)) {

                if (get_size(block) == 0) {
                    num_free_list_blocks--;
                }
                // check to make sure there are no allocated blocks in the free
                // list
                if (get_alloc(block) == 1) {
                    print_error("Free list has allocated blocks");
                    print_free_list("Free List");
                    return false;
                }

                // check consistency of the current block's next pointer
                block_t *next_block = get_next_free_block(block);
                if (get_next_free_block(block) != NULL &&
                    get_size(block) >= min_full_free_block_size) {
                    if (get_prev_free_block(next_block) != block &&
                        get_size(next_block) >= min_full_free_block_size) {
                        print_error("Block next pointer is not consitent with "
                                    "the next block's previous pointer");
                        return false;
                    }
                }

                // check consistency of the current block's  previous pointer
                block_t *prev_block = get_prev_free_block(block);
                if (get_prev_free_block(block) != NULL) {
                    if (get_next_free_block(prev_block) != block) {
                        print_error("Block prev pointer is not consitent with "
                                    "the previous block's next pointer");
                        return false;
                    }
                }

                // check that all free list pointers are between mem_heap_lo and
                // mem_heap_hi
                if ((!block_within_heap(next_block) && next_block != NULL) ||
                    (!block_within_heap(prev_block) && prev_block != NULL) ||
                    !block_within_heap(block)) {
                    print_error("Block prev pointer or next pointer points "
                                "outside of the heap");
                    return false;
                }

                // check block is in the right bucket
                if (get_free_list_index(get_size(block)) != i &&
                    get_size(block) >= min_full_free_block_size) {
                    print_free_list(""); // remove this
                    print_error("Block in incorrect bucket");
                    return false;
                }

                prev_next_pointers = get_free_block_contents(block);
                num_free_list_blocks++; // count total blocks in the free lists
                                        // to compare with total free blocks in
                                        // the heap
            }
        }
    }

    // check the number of free blocks in the heap and in the free lists are the
    // same
    if (num_free_heap_blocks != num_free_list_blocks) {
        print_error("Number of block in free list incorrect");
        return false;
    }
    return true;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @return
 */
bool mm_init(void) {
    // Create the initial empty heap
    word_t *start = (word_t *)(mem_sbrk(2 * wsize));

    if (start == (void *)-1) {
        return false;
    }

    // clear all free lists
    for (int i = 0; i < max_free_lists; i++) {
        free_lists[i] = NULL;
    }

    /*
     * TODO: delete or replace this comment once you've thought about it.
     * Think about why we need a heap prologue and epilogue. Why do
     * they correspond to a block footer and header respectively?
     */

    start[0] = pack(0, true, 0); // Heap prologue (block footer)
    start[1] = pack(0, true, 0); // Heap epilogue (block header)

    // Heap starts with first "block header", currently the epilogue
    heap_start = (block_t *)&(start[1]);

    // Extend the empty heap with a free block of chunksize bytes
    if (extend_heap(chunksize) == NULL) {
        return false;
    }

    return true;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] size
 * @return
 */
void *malloc(size_t size) {
    dbg_requires(mm_checkheap(__LINE__));

    size_t asize;      // Adjusted block size
    size_t extendsize; // Amount to extend heap if no fit is found
    block_t *block;
    void *bp = NULL;

    // Initialize heap if it isn't initialized
    if (heap_start == NULL) {
        mm_init();
    }

    // Ignore spurious request
    if (size == 0) {
        dbg_ensures(mm_checkheap(__LINE__));
        return bp;
    }

    // Adjust block size to include overhead and to meet alignment requirements
    asize = round_up(size + wsize, dsize);

    // Search the free list for a fit
    block = find_fit(asize);

    // If no fit is found, request more memory, and then and place the block
    if (block == NULL) {
        // Always request at least chunksize
        extendsize = max(asize, chunksize);
        block = extend_heap(extendsize);
        // extend_heap returns an error
        if (block == NULL) {
            return bp;
        }
    }

    // The block should be marked as free
    dbg_assert(!get_alloc(block));

    // Mark block as allocated
    size_t block_size = get_size(block);
    write_block(block, block_size, true);

    // Try to split the block if too large
    split_block(block, asize);

    // set the prev allocation bit for the next block
    block_t *next_block = find_next(block);
    write_prev_alloc(next_block, true);

    // remove_free_block(block);

    if (get_size(block) >
        header_and_pointer_size) // if block size is less than  the size of a
                                 // header plus the 2 pointers, the next block
                                 // will be overwritten
        write_next_pointer(block, NULL);
    write_prev_pointer(block, NULL);

    bp = header_to_payload(block);

    dbg_ensures(mm_checkheap(__LINE__));
    dbg_printheap("");
    return bp;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] bp
 */
void free(void *bp) {
    dbg_requires(mm_checkheap(__LINE__));

    if (bp == NULL) {
        return;
    }

    block_t *block = payload_to_header(bp);
    size_t size = get_size(block);

    // The block should be marked as allocated
    dbg_assert(get_alloc(block));

    // Mark the block as free
    write_block(block, size, false);

    // Update the prev alloc of the previous block header
    block_t *next_block = find_next(block);
    write_prev_alloc(next_block, false);

    // Try to coalesce the block with its neighbors
    block = coalesce_block(block);

    dbg_ensures(mm_checkheap(__LINE__));
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] ptr
 * @param[in] size
 * @return
 */
void *realloc(void *ptr, size_t size) {
    block_t *block = payload_to_header(ptr);
    size_t copysize;
    void *newptr;

    // If size == 0, then free block and return NULL
    if (size == 0) {
        free(ptr);
        return NULL;
    }

    // If ptr is NULL, then equivalent to malloc
    if (ptr == NULL) {
        return malloc(size);
    }

    // Otherwise, proceed with reallocation
    newptr = malloc(size);

    // If malloc fails, the original block is left untouched
    if (newptr == NULL) {
        return NULL;
    }

    // Copy the old data
    copysize = get_payload_size(block); // gets size of old payload
    if (size < copysize) {
        copysize = size;
    }
    memcpy(newptr, ptr, copysize);

    // Free the old block
    free(ptr);

    return newptr;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] elements
 * @param[in] size
 * @return
 */
void *calloc(size_t elements, size_t size) {
    void *bp;
    size_t asize = elements * size;

    if (elements == 0) {
        return NULL;
    }
    if (asize / elements != size) {
        // Multiplication overflowed
        return NULL;
    }

    bp = malloc(asize);
    if (bp == NULL) {
        return NULL;
    }

    // Initialize all bits to 0
    memset(bp, 0, asize);

    return bp;
}

/*
 *****************************************************************************
 * Do not delete the following super-secret(tm) lines!                       *
 *                                                                           *
 * 53 6f 20 79 6f 75 27 72 65 20 74 72 79 69 6e 67 20 74 6f 20               *
 *                                                                           *
 * 66 69 67 75 72 65 20 6f 75 74 20 77 68 61 74 20 74 68 65 20               *
 * 68 65 78 61 64 65 63 71 6d 41 6c 20 64 69 67 69 74 73 20 64               *
 * 6f 2e 2e 2e 20 68 61 68 61 68 61 21 20 41 53 43 49 49 20 69               *
 *                                                                           *
 * 73 6e 30 84 19 45 68 65 20 72 69 67 68 74 20 65 6e 63 6f 64               *
 * 69 6e 67 21 20 4e 69 45 27 40 64 81 1e 4d 20 74 68 6f 75 67               *
 * 68 21 20 2d 44 72 2e 20 45 76 69 6c 0a c5 7c fc 80 6e 57 0a               *
 *                                                                           *
 *****************************************************************************
 */
