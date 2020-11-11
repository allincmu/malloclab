/**
 * @file mm.c
 * @brief A 64-bit struct-based explicit segregated free list memory allocator
 *
 * 15-213: Introduction to Computer Systems
 *
 * In this allocator, the heap is separated into blocks.
 * Each block contains a header that is 8 bytes:
 *  - The first bit of the header stores the allocation status of the block. It
 *    is set if the block is allocated and unset if the the block is freed.
 *  - The second bit stores the allocation status of the previous block.
 *    Likewise, it is set if the previous block is alocated; unset if not
 *  - The third bit denotes whether the previous block is a
 *    miniblock (described below). It is set if the previous block is a
 *    miniblock and unset if not.
 *
 * There are 3 types of blocks each with different fields:
 *  1. Allocated block - Contains a header and a payload. Since we do not know
 *     the size of the payload, it is declared as a zero length array, which is
 *     a GCC compiler extension for a variable length object.
 *
 *  2. Freed Block - Freed blocks are stored in buckets of blocks of similar
 *     sizes. These buckets are implemented as doubly linked lists. The ranges
 *     of the sizes of the blocks inside each free list increases the higher up
 *     you go. This allocator contains a total of 15 segregated free lists. A
 *     pointer pointing to the start of each segregated free list is stored in a
 *     global array of length 15.
 *     A freed block contains a header. It also stores 2 pointers inside the
 *     space of the original payload: a pointer pointing to the next freed block
 *     in the segregated list and a pointer pointing to the previous freed block
 *     in the segregated list. Following the space for the payload. The freed
 *     block has a footer which is exactly the same as the header  and is useful
 *     for traversing the heap backwards.
 *
 *  3. Miniblock - A miniblock is 16 bytes in size. Because of this it only
 *     contains a header and a 8 byte payload. It can be both allocated and
 *     freed. Since a freed miniblock contains no footer, this makes traversing
 *     the heap backwards difficult. This is why the third bit of the header of
 *     the next block denotes whether the block is a miniblock so the start of
 *     the next block can be calculated. Since a miniblock is always 16 bytes.
 *
 * 1 struct is used to represent all 3 of these types of blocks. The way this is
 * achieved is by creating a union with a  struct the previous and next pointers
 * for a freed block and a 0 length array for the payload of an allocated block.
 * In this way, 1 struct can be used to represent both allocated and unallocated
 * blocks. A miniblock is also represented using this struct although the
 * previous pointer and footer is not written to avoid overwriting information
 * in subsequent blocks.
 *
 * This allocator implements the 4 functions: malloc, realloc, calloc, and free
 * according to the libc routines.
 *
 * To malloc a block, the free list corresponding to the is traversed until the
 * first block that fits is found (first fit). If no block is found in that free
 * list, the allocator moves onto the next free list. This continues until a
 * suitable block is found in the free lists. If no block is found, the heap is
 * extended to provide space for the new block. If the block that is found is
 * too big it is split into 2 smaller blocks as long as both blocks meet the 16
 * byte allignment requriement. If either of these blocks is a miniblock, the
 * miniblock status bit is set on the subsequent block.
 *
 * To free a block, the block is marked as unallocated and inserted into the
 * head of the free list corresponding to the size of the block. If there this
 * newly freed block is next to another freed block in the heap, the blocks are
 * coalesced together. This involves removing the separate blocks from their
 * free lists, rewriting the first block to be the combined size of all the
 * blocks that were coalesced together and adding the the final combined block
 * to the free list corresponding to its new size.
 *
 * The realloc and calloc functions remain unchanged from the starter code.
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
#define dbg_printfreelist(...) print_free_list(__VA_ARGS__)
#else
/* When DEBUG is not defined, no code gets generated for these */
/* The sizeof() hack is used to avoid "unused variable" warnings */
#define dbg_printf(...) (sizeof(__VA_ARGS__), -1)
#define dbg_requires(expr) (sizeof(expr), 1)
#define dbg_assert(expr) (sizeof(expr), 1)
#define dbg_ensures(expr) (sizeof(expr), 1)
#define dbg_printheap(...) ((void)sizeof(__VA_ARGS__))
#define dbg_printfreelist(...) ((void)sizeof(__VA_ARGS__))
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
 * @brief number of bytes to extend the heap
 * (Must be divisible by dsize)
 */
static const size_t chunksize = (1 << 11);

/**
 * @brief isolates the bit of the header/footer associated with whether the
 * block is allocated
 */
static const word_t alloc_mask = 0x1;

/**
 * @brief isolates the bit of the header/footer associated with whether the prev
 * block is allocated
 */
static const word_t prev_alloc_mask = 0b10;

/**
 * @brief isolates the bit of the header/footer associated with whether the prev
 * block is a miniblock
 */
static const word_t prev_miniblock_status_mask = 0b100;

/**
 * @brief isolates the bits in the header/footer that store the size of the
 * block.
 */
static const word_t size_mask = ~(word_t)0xF;

// Forward declarations for structs
typedef struct freed_block_contents freed_block_contents_t;
typedef union block_contents block_contents_t;
typedef struct block block_t;

/** @brief Represents the contents of a freed block payload.
 * A freed block payload contains prev and next pointers. */
typedef struct freed_block_contents {

    /** @brief pointers pointing to the next free and previous free blocks */
    block_t *next;
    block_t *prev;

} freed_block_contents_t;

/** @brief Represents the contents of a block payload as a union for free and
allocated blocks.
 *
 * A freed block payload contains prev and next pointers.
 * A miniblock payload contains a next pointer
 * An allocated block payload contains only a payload represented as a
 *      zero length array
 *
 */
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

/** @brief An array of the max_size limit of each seglist */
static const size_t free_list_size_limits[max_free_lists] = {
    16,   32,   48,   64,   128,   256,   512,   768,
    1024, 2048, 4096, 8192, 16384, 32768, 577536};

/*
 *****************************************************************************
 * The functions below are short wrapper functions to perform bit manipulation,
 * pointer arithmetic, and other helper operations.
 *
 * We've given you the function header comments for the functions below to help
 * you understand how this baseline code works.
 *
 * Note that these function header comments are short since the functions they
 * are describing are short as well; you will need to provide adequate details
 * for the functions that you write yourself!
 *****************************************************************************
 */

/*
 * ---------------------------------------------------------------------------
 *                        BEGIN SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/******************************
 * Helper Function prototypes
 ******************************/

/* Mathematical helper functions  */
static size_t max(size_t x, size_t y);
static size_t round_up(size_t size, size_t n);

/* These functions get the proper free list */
static block_t *get_free_list(size_t size);
static int get_free_list_index(size_t size);
static void write_free_list_start(size_t size, block_t *block);
static block_t *remove_free_block(block_t *block);

/* These functions get and set the next and prev pointers of the free blocks */
static freed_block_contents_t *get_free_block_contents(block_t *block);
static block_t *get_prev_free_block(block_t *block);
static block_t *get_next_free_block(block_t *block);
static void write_next_pointer(block_t *block, block_t *next_free_block);
static void write_prev_pointer(block_t *block, block_t *prev_free_block);

/* These functions set the header of blocks */
static word_t pack(size_t size, bool alloc, bool prev_alloc);
static void write_prev_alloc(block_t *block, bool prev_alloc);
static void write_prev_miniblock_status(block_t *block, bool miniblock);

/* These functions extract data from headers */
static size_t extract_size(word_t word);
static bool extract_alloc(word_t word);
static bool extract_prev_alloc(word_t word);
static bool extract_prev_miniblock_status(word_t word);
static bool extract_prev_miniblock_status(word_t word);

/* These functions get data stored in the header of blocks */
static size_t get_size(block_t *block);
static size_t get_payload_size(block_t *block);
static bool get_alloc(block_t *block);
static bool get_prev_alloc(block_t *block);
static bool get_prev_miniblock_status(block_t *block);

/* functions to write blocks */
static void write_epilogue(block_t *block);
static void write_block(block_t *block, size_t size, bool alloc);

/* functions to find blocks in the heap */
static block_t *find_next(block_t *block);
static word_t *find_prev_footer(block_t *block);
static block_t *find_prev(block_t *block);

/* check heap helpers */
bool has_epilogue_prologue();
static bool block_is_alligned(block_t *curr_block);
static bool block_within_heap(block_t *curr_block);
static bool check_header_footer(block_t *curr_block);
static bool is_acyclic(block_t *free_list_start);

/* These functions print out debugging info */
static void print_error(char *error_msg);
static void print_heap(char *msg);
static void print_free_list(char *msg);

/********************************
 * Begin Function Declarations
 ********************************/

/**
 * @brief gets the start of the free list for the specified block size
 * @param [in] size - size of the block
 * @return a pointer to the first block in the free list containing freed blocks
 * of similar size
 */
static block_t *get_free_list(size_t size) {
    for (int i = 0; i < max_free_lists; i++) {
        if (size <= free_list_size_limits[i]) {
            return free_lists[i];
        }
    }
    dbg_assert(size > free_list_size_limits[max_free_lists - 2]);
    // block is bigger than the second to last bucket limit so return last
    // bucket
    return free_lists[max_free_lists - 1];
}

/**
 * @brief gets the index for the free list for the specified block size
 * @param [in] size - size of the block
 * @return the index of free list containing freed blocks of similar size
 */
static int get_free_list_index(size_t size) {
    for (int i = 0; i < max_free_lists; i++) {
        if (size <= free_list_size_limits[i]) {
            return i;
        }
    }
    dbg_assert(size > free_list_size_limits[max_free_lists - 2]);
    // block is bigger than the second to last bucket limit so return last
    // bucket
    return max_free_lists - 1;
}

/**
 * @brief adds free block to the front of free list
 *
 * New free blocks are added to the front of the doubly linked list
 *
 * @param [in] size - size of the block
 * @param [in] block - the block you want to add to the list
 * @return the index of free list containing freed blocks of similar size
 */
static void write_free_list_start(size_t size, block_t *block) {
    for (int i = 0; i < max_free_lists; i++) {
        if (size <= free_list_size_limits[i]) {
            free_lists[i] = block;
            return;
        }
    }
    dbg_assert(size > free_list_size_limits[max_free_lists - 2]);
    // block is bigger than the second to last bucket limit so add to last
    // bucket
    free_lists[max_free_lists - 1] = block;
}

/**
 * @brief gets the payload for a free block containing the prev and next
 * pointers
 * @param [in] block
 * @return a struct containing the prev and next pointers to the previous and
 * next free blocks in the free list
 */
static freed_block_contents_t *get_free_block_contents(block_t *block) {
    freed_block_contents_t *prev_next_pointers =
        &(block->payload_contents.prev_next_pointers);
    return prev_next_pointers;
}

/**
 * @brief gets the previous free block in the free list
 * @param[in] block
 * @return NULL if the block is a miniblock or a pointer to the previous free
 * block
 */
static block_t *get_prev_free_block(block_t *block) {
    if (get_size(block) < min_full_free_block_size)
        return NULL;
    freed_block_contents_t *prev_next_pointers = get_free_block_contents(block);
    return prev_next_pointers->prev;
}

/**
 * @brief gets the next free block in the free list
 * @param[in] block
 * @return NULL if the block is a miniblock or a pointer to the next free block
 */
static block_t *get_next_free_block(block_t *block) {
    freed_block_contents_t *prev_next_pointers = get_free_block_contents(block);
    return prev_next_pointers->next;
}

/**
 * @brief writes the next pointer for the block
 * @param[in] block
 * @param[in] next_free_block - the next free block relative to block
 * block's next field points to next_free_block
 */
static void write_next_pointer(block_t *block, block_t *next_free_block) {
    block->payload_contents.prev_next_pointers.next = next_free_block;
}

/**
 * @brief writes the previous pointer for the block if the block is not a
 * minblock
 * @param[in] block
 * @param[in] prev_free_block - the previous free block relative to block
 * block's prev field points to prev_free_block
 */
static void write_prev_pointer(block_t *block, block_t *prev_free_block) {
    if (block == NULL)
        return;
    if (get_size(block) >= min_full_free_block_size)
        block->payload_contents.prev_next_pointers.prev = prev_free_block;
}

/**
 * @brief wrapper function to write the bit of the header associated with
 * whether the previous block in the heap is allocated This is the second bit in
 * the header
 * @param[in] block - the block that you want to write the prev_alloc bit for
 * @param[in] prev_alloc - whether the previous block in the heap is allocated
 */
static void write_prev_alloc(block_t *block, bool prev_alloc) {
    dbg_requires((block) != NULL);
    size_t size = get_size(block);
    bool alloc = get_alloc(block);
    block->header = pack(size, alloc, prev_alloc);
    dbg_assert(get_prev_alloc(block) == prev_alloc);
}

/**
 * @brief sets the third bit of the header/footer to 1 if the previous block
 * is a miniblock i.e. less than 32 bytes
 *
 * @param [in] block
 * @param [in] miniblock - bool value - 1 if miniblock; 0 if not miniblock
 */
static void write_prev_miniblock_status(block_t *block, bool miniblock) {

    size_t block_size = get_size(block);
    bool alloc = get_alloc(block);
    bool prev_alloc = get_prev_alloc(block);

    block->header = pack(block_size, alloc, prev_alloc);

    if (miniblock) {
        block->header |= prev_miniblock_status_mask;
    }
}

/**
 * @brief removes the block from the free list
 *
 * Writes the previous block's next pointer to the block after the block you are
 * trying to remove and writes the next block's previous pointer to the block
 * that comes before the block that you are trying to remove in the free list.
 *
 * @param[in] block - the block you are trying to remove
 *
 */
static block_t *remove_free_block(block_t *block) {
    dbg_requires(block_is_alligned(block));

    block_t *free_list_start = get_free_list(get_size(block));

    block_t *prev_block = get_prev_free_block(block);
    block_t *next_block = get_next_free_block(block);

    // splice the block out of the free list
    if (prev_block != NULL) {
        write_next_pointer(prev_block, next_block);
    }
    if (next_block != NULL) {
        write_prev_pointer(next_block, prev_block);
    }

    // if block is the only block in the free list we want to write
    // free_list_start to NULL
    if (prev_block == NULL && next_block == NULL && free_list_start == block) {
        // block is only item in free list
        write_free_list_start(get_size(block), NULL);
    }

    // if block is the first block in the free list but not the only block in
    // the free list we write the start of the free list as the block that comes
    // after the block we are trying to remove
    else if (block == free_list_start) {
        write_free_list_start(get_size(block), next_block);
    }

    // if the free list is a list of miniblocks, there are no previous pointers
    // so we have to traverse the list (since the blocks do not have a previous
    // pointer) until we get to the block we are trying to remove and rewrite
    // the previous block's next pointer to point to the block that comes after
    // the removed block
    else if (get_size(block) <= min_block_size) {
        // traverse list
        for (block_t *curr_block = free_list_start; curr_block != NULL;
             curr_block = get_next_free_block(curr_block)) {
            // if next block is  the removed block, we rewrite the next pointer
            // of the current block
            if (get_next_free_block(curr_block) == block) {
                write_next_pointer(curr_block, get_next_free_block(block));
                break;
            }
        }
    }

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
 * @brief Packs the `size` and `alloc` and the 'previous block's allocation
 * status' of a block into a word suitable for use as a packed value.
 *
 * Packed values are used for both headers and footers.
 *
 * The allocation status is packed into the lowest bit of the word.
 * The previous block allocation status is packed into the 2nd lowest bit of the
 * word
 *
 * @param[in] size The size of the block being represented
 * @param[in] alloc True if the block is allocated
 * @param[in] prev_alloc True if the previous block in the heap is allocated
 * @return The packed value
 */
static word_t pack(size_t size, bool alloc, bool prev_alloc) {
    word_t word = size;
    if (prev_alloc) {
        word |= prev_alloc_mask; // set second bit
    }
    if (alloc) {
        word |= alloc_mask; // set first bit
    }
    return word;
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
 * @brief Returns the allocation status of a given header value.
 *
 * This is based on the lowest bit of the header/footer value.
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
 * This is based on the 2nd lowest bit of the header/footer value.
 *
 * @param[in] word
 * @return The allocation status of the previous block correpsonding to the
 * word
 */
static bool extract_prev_alloc(word_t word) {
    return (bool)(word & (prev_alloc_mask));
}

/**
 * @brief Returns the minblock status of the prevous block of given header
 * value.
 *
 * This is based on the 3rd lowest bit of the header/footer value.
 *
 * @param[in] word
 * @return The allocation status of the previous block correpsonding to the
 * word
 */
static bool extract_prev_miniblock_status(word_t word) {
    return (bool)(word & (prev_miniblock_status_mask));
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
    if (get_alloc(block) == 0 && get_size(block) >= min_full_free_block_size)
        return asize - dsize;
    else
        // The block is allocated which means it does not have a footer or it is
        // a miniblock so it does not have a footer and the payload in both of
        // these cases is the block size minus the header size
        return asize - wsize;
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
 * @brief Returns the miniblock status of the previous block, based on its
 * header.
 * @param[in] block
 * @return The miniblock status of the prev block: true if the previous block is
 * a miniblock and 0 if not
 */
static bool get_prev_miniblock_status(block_t *block) {
    return extract_prev_miniblock_status(block->header);
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
 * @pre block is not NULL and size > 0
 *
 * @param[out] block The location to begin writing the block header
 * @param[in] size The size of the new block
 * @param[in] alloc The allocation status of the new block
 */
static void write_block(block_t *block, size_t size, bool alloc) {
    dbg_requires(block != NULL);
    dbg_requires(size > 0);

    // if we are mallocing a freed block, we remove it from the free list
    if (alloc == true && get_alloc(block) == false) {
        remove_free_block(block);
    }

    // rewrite the block header
    bool prev_alloc = get_prev_alloc(block);
    bool prev_miniblock = get_prev_miniblock_status(block);
    block->header = pack(size, alloc, prev_alloc);
    if (prev_miniblock)
        write_prev_miniblock_status(block, prev_miniblock);

    block_t *free_list_start = get_free_list(get_size(block));

    if (alloc == false) {
        // write footer
        word_t *footerp = header_to_footer(block);
        *footerp = block->header;

        // if block is not at the start of the list we add it to the front
        if (free_list_start != block) {
            write_next_pointer(block, free_list_start);
            write_prev_pointer(get_next_free_block(block), block);

            write_free_list_start(get_size(block), block);
            write_prev_pointer(block, NULL);
        }

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
 * If the function is called on the first block in the heap, it will return the
 * first block!
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
 * @brief Checks to make sure the heap has a prologue and a epilogue
 *
 * @return true if the heap has a prologue and a epilogue
 */
bool has_epilogue_prologue() {
    if (*(word_t *)mem_heap_lo() != pack(0, true, 0))
        return false;
    if (*(word_t *)(mem_heap_hi() - 7) != pack(0, true, 0))
        return false;
    return true;
}

/**
 * @brief Checks to make sure the block is alligned to 16 bytes
 *
 * @param[in] curr_block - pointer of the block to be tested
 * @return true if address is a multiple of 16 false otherwise
 */
static bool block_is_alligned(block_t *curr_block) {
    if ((size_t)curr_block % (size_t)16 != 0) {
        return false;
    }
    return true;
}

/**
 * @brief Checks to make sure the block is within heap boundaries
 *
 * @param[in] curr_block - pointer of the block to be tested
 * @return true if block address is witin the heap boundaries false
 * otherwise
 */
static bool block_within_heap(block_t *curr_block) {
    if ((void *)curr_block < mem_heap_lo() ||
        (void *)curr_block + get_size(curr_block) > mem_heap_hi() ||
        curr_block == NULL) {
        return false;
    }
    return true;
}

/**
 * @brief Checks to make sure the block's header and footer is valid
 *
 * The size is larger than the minmum size
 * Header and footers are consistent
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

    // check that the footer is consistent with the header if there is a footer
    if (extract_size(header) != extract_size(footer) &&
        get_size(curr_block) >= min_full_free_block_size) {
        printf("Error: Block size inconsistent between header and footer: "
               "%p \n",
               curr_block);
        return false;
    }
    if (extract_alloc(header) != extract_alloc(footer)) {
        print_error("Block alloc bit inconsistent between header and footer.");
        return false;
    }
    return true;
}

/**
 * @brief checks to make sure that a free list has no cycles using the tortoise
 * and the hare approach
 *
 * @param[in] - the start of the free list to be tested
 * @return - true if there are no cyles in the list; false otherwise
 * from: https://www.cs.cmu.edu/~15122/handouts/10-linkedlist.pdf
 */
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
 * @brief Prints error messages along with the blocks in the heap and the blocks
 * in each free list
 *
 * @param[in] error_msg - string that represents the error
 */
static void print_error(char *error_msg) {
    dbg_printheap("Heap");
    dbg_printfreelist("Free List");
    printf("Error: %16s \n", error_msg);
}
/**
 * @brief Prints out the contents of the heap by traversing the implicit list
 * Prints out the address, size, prev block miniblock status, prev allocation
 * status, prev and next pointers if free block, and the message.
 * @param[in] msg - string that represents debugging information
 */
static void print_heap(char *msg) {
    for (block_t *curr_block = heap_start; get_size(curr_block) > 0;
         curr_block = find_next(curr_block)) {

        // print free block
        if (get_alloc(curr_block) == false) {
            printf("addr: %p \t size: %zu \t %d %d %d \t "
                   "prev: %p \t next: %p "
                   "\t msg: %s \n",
                   curr_block, get_size(curr_block),
                   get_prev_miniblock_status(curr_block),
                   get_prev_alloc(curr_block), get_alloc(curr_block),
                   (void *)get_prev_free_block(curr_block),
                   (void *)get_next_free_block(curr_block), msg);
        }

        // print allocated block
        if (get_alloc(curr_block) == true) {
            printf("addr: %p \t size: %zu \t %d %d %d \t "
                   "next_block: %p"
                   "\t\t\t msg: %s \n",
                   curr_block, get_size(curr_block),
                   get_prev_miniblock_status(curr_block),
                   get_prev_alloc(curr_block), get_alloc(curr_block),
                   (void *)curr_block + get_size(curr_block), msg);
        }
    }
    printf("\n");
}

/**
 * @brief Prints out the contents of the each free list by traversing the next
 * pointers Prints out the address, size, allocation status, prev and next
 * pointers, and the message.
 * @param[in] msg - string that represents debugging information
 */
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

/******** The remaining content below are helper and debug routines *********/

/**
 * @brief If there are 2 or more free blocks next to each other in the heap,
 * they are combined together into a single free block
 *
 * This involves removing the separate blocks from the free lists they were
 * previously in and inserting the new coalesced free block into the approprate
 * free list according to it's size.
 *
 * If the last block to be coalesced is a miniblock, the prev block miniblock
 * status bit on the next block needs to be reset to false since the coalesced
 * block is not a miniblock
 *
 * @param[in] block
 * @return a pointer pointing to the  header of the coalesced block
 */
static block_t *coalesce_block(block_t *block) {

    dbg_requires(block != NULL);
    dbg_requires(get_size(block) != 0);
    dbg_requires(get_alloc(block) == false);

    dbg_printheap("");
    block_t *prev_block;

    // if the previous block is unallocated and a miniblock, we cannot get the
    // start of the previous block using the block's footer because there isn't
    // one so we subtract 16, the size of the miniblock, from the curr block to
    // get the start of the previous block
    if (get_prev_alloc(block) == false && get_prev_miniblock_status(block)) {
        // the miniblock is 16 bytes
        prev_block = (block_t *)((void *)block - min_block_size);
        dbg_assert(get_size(prev_block) == min_block_size);
    }
    // if the block isnt a miniblock, we can get the previous block using it's
    // footer and the find_prev function
    else if (get_prev_alloc(block) == false) {
        prev_block = find_prev(block);
    }

    block_t *next_block = find_next(block);
    size_t curr_block_size = get_size(block);

    // case 1 do not go into the for loop bc no coalesing needed.
    /* prev_block == block when prev_block is the prolgue block. the
     * prologue block is freed but we do not want to coalesce the prologue
     * block with block
     */
    if (curr_block_size > 0 &&
        ((get_alloc(next_block) == false) ||
         (get_prev_alloc(block) == false && prev_block != block))) {

        size_t prev_block_size;
        if (get_prev_alloc(block) == false)
            // only get prev block size if it is freed
            prev_block_size = get_size(prev_block);

        size_t next_block_size = get_size(next_block);

        // case 2 : coalesce curr block with next block
        /* prev_block == block when prev_block is the prolgue block. the
         * prologue block is freed and we do not want to coalesce the
         * prologue block with block
         */
        if ((get_prev_alloc(block) == true ||
             (get_prev_alloc(block) == false && prev_block == block)) &&
            (get_alloc(next_block) == false && next_block != block)) {

            // get the start of the free list that the coalesced block
            // should be placed in
            block_t *free_list_start =
                get_free_list(curr_block_size + next_block_size);

            // if the first block is not in the same bucket as the final
            // coalesced block we remove it from the free list it is in
            if (block != free_list_start) {
                remove_free_block(block);
            }

            // we always want to remove the next block from the free list it is
            // in
            remove_free_block(next_block);

            size_t coalesced_size = curr_block_size + next_block_size;

            if (next_block_size < min_full_free_block_size &&
                coalesced_size >= min_full_free_block_size) {
                // next block is a miniblock but the coalesced block is not
                // a miniblock so we want to rewrite miniblock bit on next
                // block's header
                block_t *block_after_coalesce = find_next(next_block);
                write_prev_miniblock_status(block_after_coalesce, false);
            }

            // write the coalesced block
            write_block(block, coalesced_size, false);
            dbg_printf("case 2");
        }

        // case 3: coalesce previous block, current block
        else if ((get_prev_alloc(block) == false && prev_block != block) &&
                 (get_alloc(next_block) == true)) {

            // get the start of the free list that the coalesced block
            // should be placed in
            block_t *free_list_start =
                get_free_list(curr_block_size + prev_block_size);

            // if the prev block is not the start of the bucket of the final
            // coalesced block we remove it from the free list that it is in
            if (prev_block != free_list_start) {
                remove_free_block(prev_block);
            }

            // we always remove the current block from the free list it is in
            remove_free_block(block);

            size_t coalesced_size = curr_block_size + prev_block_size;

            if (curr_block_size < min_full_free_block_size &&
                coalesced_size >= min_full_free_block_size) {
                // curr_block is a miniblock but the coalesced block is not
                // a miniblock
                // rewrite miniblock bit on next block's header
                block_t *block_after_coalesce = find_next(block);
                write_prev_miniblock_status(block_after_coalesce, false);
            }

            write_block(prev_block, coalesced_size, false);

            // set the coalesced block
            block = prev_block;
            dbg_printf("case 3");
        }

        // case 4 : coalesce previous block, current block, and next block
        else if ((get_prev_alloc(block) == false && prev_block != block) &&
                 (get_alloc(next_block) == false)) {

            // get the start of the free list that the coalesced block
            // should be placed in
            block_t *free_list_start = get_free_list(
                curr_block_size + prev_block_size + next_block_size);

            // if the prev block is not the start of the bucket of the final
            // coalesced block we remove it
            if (prev_block != free_list_start) {
                remove_free_block(prev_block);
            }

            // we always remove the current and next blocks
            remove_free_block(block);
            remove_free_block(next_block);

            size_t coalesced_size =
                curr_block_size + prev_block_size + next_block_size;

            if (next_block_size < min_full_free_block_size &&
                coalesced_size >= min_full_free_block_size) {
                // next_block is a miniblock but the coalesced block is not
                // a miniblock rewrite miniblock bit on next block's header
                block_t *block_after_coalesce = find_next(next_block);
                write_prev_miniblock_status(block_after_coalesce, false);
            }

            // write the coalesced block
            write_block(prev_block, coalesced_size, false);

            // set the coalesced block
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
 * @brief extends the heap by the specified number of bytes
 *
 * if the nubmer of bytes does not meet the 16 byte allignment requirement, it
 * is rounded up to meet the allignment requirement.
 *
 * The heap is extended by writing a unallocated block of the requested size at
 * the end of the heap and then coalescing this block with the original last
 * block in the heap if necessary.
 *
 * @param[in] size - the size to extend the heap by
 * @return the last block in the new heap
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

    // Initialize free block header/footer
    block_t *block = payload_to_header(bp);
    write_block(block, size, false);

    // only write the prev alloc and prev block type if there are blocks in
    // the heap
    if (orig_heap_size >= min_block_size) {
        write_prev_alloc(block, extract_prev_alloc(old_epilogue));
        write_prev_miniblock_status(
            block, extract_prev_miniblock_status(old_epilogue));
    }

    // if there are no free blocks in the free list, set free_list_start to
    // this block
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
 * @brief Splits the block  at asize if the two blocks meet the minimum block
 * size requirement
 *
 * also sets the mini block status bit on the split_block if the first block is
 * a miniblock or the next block if the split block is a miniblock
 *
 * @param[in] block - the block to be split
 * @param[in] asize - the requested size of the block
 */
static void split_block(block_t *block, size_t asize) {
    dbg_requires(get_alloc(block));

    size_t block_size = get_size(block);

    // the block is only splitable if the two new blocks are larger than the
    // minmum block size
    if ((block_size - asize) >= min_block_size) {

        // if split_block is mini block set mini block bit on next block
        // header
        if (block_size - asize < min_full_free_block_size)
            write_prev_miniblock_status(find_next(block), true);
        else
            write_prev_miniblock_status(find_next(block), false);

        block_t *block_split;
        write_block(block, asize, true);

        block_split = find_next(block);
        write_block(block_split, block_size - asize, false);
        write_prev_alloc(block_split, true);

        // if first block is mini block set miniblock bit on split block
        // header
        if (asize < min_full_free_block_size)
            write_prev_miniblock_status(block_split, true);
        else
            write_prev_miniblock_status(block_split, false);
    }

    dbg_ensures(get_alloc(block));
}

/**
 * @brief Finds a free block that is at least the requested size
 *
 * Starts at the free list corresponding to the requested size and finds the
 * first block that is at least the size of the requested block and returns that
 * block. If there are no blocks in the free list that meet the size
 * requirement, it goes to the next free list and traverses that one looking for
 * the first block that fits and returns that one. This repeats until the are no
 * more free lists. Returns NULL if there are no blocks that fit
 *
 * @param[in] asize - the requested size
 * @return a block at least the size of asize or NULL if no block exists in the
 * free lists that are bigger than asize
 */
static block_t *find_fit(size_t asize) {
    dbg_printheap("");
    int free_list_index = get_free_list_index(asize);

    // traverse each free list starting at the one that the block should be in
    // if no blocks are found that fit the requested size then the next free
    // list is traversed.
    for (; free_list_index < max_free_lists; free_list_index++) {
        block_t *free_list_start = free_lists[free_list_index];
        if (free_list_start != NULL) {
            // traverse free list
            for (block_t *block = free_list_start; block != NULL;
                 block = get_next_free_block(block)) {
                if (!(get_alloc(block)) && (asize <= get_size(block))) {
                    // return the block since it fits
                    return block;
                }
            }
        }
    }
    return NULL;
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
 * prev block miniblock status bit is set correctly
 *
 * Free lists:
 * make sure free lists has no cycles
 * check to make sure there are no allocated blocks in the free list
 * check consistency of the current block's next pointer
 * ensure that the number of blocks in the free list is the same as the
 * number in the heap ensure all blocks are within the right bucket size
 * range.
 *
 * @param[in] line
 * @return bool true if the heap is correct, false if there are problems
 * with the heap.
 */
bool mm_checkheap(int line) {

    // ensure heap has an epilogue and a prologue
    if (!has_epilogue_prologue()) {
        char *error_msg = "No prologue or epilogue.";
        print_error(error_msg);
        return false;
    }

    // sentry variable to make sure coalesing does not fail on the first
    // block in the heap
    unsigned short prev_alloc = 1;

    // tally the number of free blocks in the heap to compare to number in
    // free lists
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

        // miniblock bit consitent with previous block
        if (get_size(curr_block) == min_block_size &&
            !get_prev_miniblock_status(find_next(curr_block))) {
            print_error("miniblock but header not set");
            return false;
        } else if (get_size(curr_block) != min_block_size &&
                   get_prev_miniblock_status(find_next(curr_block))) {
            print_error("no miniblock but header set");
            return false;
        }

        // check to make sure coalesing is correct
        // i.e. no free blocks next to each other
        if (get_alloc(curr_block) == 0 && prev_alloc == 0) {
            print_error("Coalesing incorrect. Two free consecutive blocks "
                        "in heap.");
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

            for (; block != NULL; block = get_next_free_block(block)) {

                if (get_size(block) == 0) {
                    num_free_list_blocks--;
                }
                // check to make sure there are no allocated blocks in the
                // free list
                if (get_alloc(block) == 1) {
                    print_error("Free list has allocated blocks");
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

                // check consistency of the current block's  previous
                // pointer
                block_t *prev_block = get_prev_free_block(block);
                if (get_prev_free_block(block) != NULL) {
                    if (get_next_free_block(prev_block) != block) {
                        print_error("Block prev pointer is not consitent with "
                                    "the previous block's next pointer");
                        return false;
                    }
                }

                // check that all free list pointers are between mem_heap_lo
                // and mem_heap_hi
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
                    print_error("Block in incorrect bucket");
                    return false;
                }

                prev_next_pointers = get_free_block_contents(block);
                num_free_list_blocks++; // count total blocks in the free
                                        // lists to compare with total free
                                        // blocks in the heap
            }
        }
    }

    // check the number of free blocks in the heap and in the free lists are
    // the same
    if (num_free_heap_blocks != num_free_list_blocks) {
        print_error("Number of block in free list incorrect");
        return false;
    }
    return true;
}

/**
 * @brief initialzes an empty heap
 *
 * clears out all of the free lists, writes a heap prologue and epilogue, and
 * extends the heap chunksize bytes
 *
 * @return true if initialization was successful false otherwise
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
 * @brief allocates a block of at least the specified size
 *
 * traverses the free lists to find a block that is at least as big as the
 * specified size if no blocks are found, the heap will be extended to the max
 * of asize and chunksize if the block that fits is too big it is split into two
 * blocks one the size of the requested size and the other the size of the
 * remaining space it then sets the prev_alloc and prev_miniblok status bits of
 * the next block's header
 *
 * @param[in] size - the requested block size
 * @return bp - a pointer to the payload of a block of at least the requested
 * size
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

    // Adjust block size to include overhead and to meet alignment
    // requirements
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

    if (block_size == get_size(block)) {
        // block not split

        // set the prev allocation bit for the next block
        block_t *next_block = find_next(block);
        write_prev_alloc(next_block, true);

        if (block_size < min_full_free_block_size)
            // set mini block status on next block
            write_prev_miniblock_status(next_block, true);
        else
            write_prev_miniblock_status(next_block, false);
    }

    // if block size is less than  the size of a header plus the 2 pointers,
    // the next block will be overwritten
    if (get_size(block) > header_and_pointer_size)
        write_next_pointer(block, NULL);
    write_prev_pointer(block, NULL);

    bp = header_to_payload(block);

    dbg_ensures(mm_checkheap(__LINE__));
    dbg_printheap("");
    return bp;
}

/**
 * @brief frees the specified block
 *
 * marks the  block as unallocated and sets the prev_alloc and previous block
 * miniblock status bit on the header of the next block Then the block is
 * coalesced if there are freed blocks next to it in the heap
 *
 * @param[in] bp - a pointer pointing to the payload of the block to be freed
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

    // if miniblock write header of next block
    if (size < min_full_free_block_size) {
        write_prev_miniblock_status(next_block, true);
    }

    // Try to coalesce the block with its neighbors
    block = coalesce_block(block);

    dbg_ensures(mm_checkheap(__LINE__));
}

/**
 * @brief returns a pointer to an allocated region of at least size bytes with
 * the following constraints:
 *
 * if ptr is null, the call is equivilent to malloc(size)
 *
 * if size is equal to 0, the call is equivalent to free(ptr)
 *
 * if ptr is not null, the call is equivalent to free(ptr) followed by
 * malloc(size) except the contents of the new block will be the same as those
 * fo teh old block up to the minimum of the old and new sizes
 *
 *
 *
 * @param[in] ptr - a pointer pointing to the block to be realloced
 * @param[in] size - the requested size
 * @return a pointer to a payload of a block of at least the requested size
 * unless the size is 0 in which case it returns NULL
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
 * @brief allocates memory for an array of elements and sets the memory to 0
 * before returning
 *
 * @param[in] elements - the number of elements to allocate
 * @param[in] size - the size of each element
 * @return a pointer to the payload of a block of at least the requested size
 * and the memory set to 0
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
 * Do not delete the following super-secret(tm) lines! *
 *                                                                           *
 * 53 6f 20 79 6f 75 27 72 65 20 74 72 79 69 6e 67 20 74 6f 20 *
 *                                                                           *
 * 66 69 67 75 72 65 20 6f 75 74 20 77 68 61 74 20 74 68 65 20 * 68 65 78 61
 *64 65 63 71 6d 41 6c 20 64 69 67 69 74 73 20 64               * 6f 2e 2e
 *2e 20 68 61 68 61 68 61 21 20 41 53 43 49 49 20 69               *
 *                                                                           *
 * 73 6e 30 84 19 45 68 65 20 72 69 67 68 74 20 65 6e 63 6f 64 * 69 6e 67 21
 *20 4e 69 45 27 40 64 81 1e 4d 20 74 68 6f 75 67               * 68 21 20
 *2d 44 72 2e 20 45 76 69 6c 0a c5 7c fc 80 6e 57 0a               *
 *                                                                           *
 *****************************************************************************
 */
