/*
 * @file mm.c
 * @brief A 64-bit struct-based segregated list memory allocator with a
 *minimum-sized block of 16 bytes. There is a prologue and epilogue block at the
 *start of the heap and the blocks are 8-byte aligned (payload aligned at
 *16-bytes). The blocks have an 8-byte header, footer and a next (and sometimes
 *prev) block pointers when unallocated and an 8-byte header and a request-sized
 *payload. The sizes of the blocks are 16-byte multiples.
 * *
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
 * @author Sanah Imani <simani@andrew.cmu.edu>
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
#define dbg_printf(...) ((void)printf(__VA_ARGS__))
#define dbg_requires(expr) assert(expr)
#define dbg_assert(expr) assert(expr)
#define dbg_ensures(expr) assert(expr)
#define dbg_printheap(...) print_heap(__VA_ARGS__)
#else
/* When DEBUG is not defined, no code gets generated for these */
/* The sizeof() hack is used to avoid "unused variable" warnings */
#define dbg_printf(...) ((void)sizeof(__VA_ARGS__))
#define dbg_requires(expr) ((void)sizeof(expr))
#define dbg_assert(expr) ((void)sizeof(expr))
#define dbg_ensures(expr) ((void)sizeof(expr))
#define dbg_printheap(...) ((void)sizeof(__VA_ARGS__))
#endif

#define SEGLISTN 13

/* Basic constants */

typedef uint64_t word_t;

/** @brief Word and header size (bytes) */
static const size_t wsize = sizeof(word_t);

/** @brief Double word size (bytes) */
static const size_t dsize = 2 * wsize;

/** @brief Minimum block size (bytes) */
static const size_t min_block_size = 2 * dsize;
static const size_t min_miniblock_size = 2 * wsize;

/**
 * @brief this is the initial heap size
 * (Must be divisible by dsize)
 */
static const size_t chunksize = (1 << 13);
/*@brief num of size classes for the seg list **/
static const size_t LIST_MAX = 13;
/**
 * Every block contains an allocation status (1 => allocated block; 0 =>
 * free block). Since the size and allocation status is stored as one word we
 * need to get the rightmost bit through a mask
 */
static const word_t alloc_mask = 0x1;
// a mask to extract the second rightmost bit of a header
static const word_t prev_alloc_mask = (word_t)(1 << 2);
// a mask to extract the third rightmost bit of a header
static const word_t mini_block_mask = (word_t)(1 << 3);

/**
 * Every block contains a size indicator in the header which we can
 * extract by anding with this mask.
 */
static const word_t size_mask = ~(word_t)0xF;

/** @brief Represents the header and payload/pointers of one block in the heap
 */

typedef struct block_t {
    word_t header;
    union {
        struct {
            struct block_t *next;
            struct block_t *prev;
        } freeP;
        char payload[0];
    };
} block_t;

/** @brief represents a block with a header and a payload that can only
 * accomodate 8 bytes of information.*/
typedef struct mini_block_t {
    word_t header;
    union {
        struct mini_block_t *next;
        char payload[0];
    };
} mini_block_t;

/* Global variables */

/** @brief Pointer to first block in the heap */
static block_t *heap_start = NULL;
/** @brief an array of 12 pointers for different size classes of free blocks.
 * The way we represent a segregated free list. */
static block_t *segList[SEGLISTN];
/** @brief a pointer to a mini block free list (singly-linked) */
static mini_block_t *mini_block_start = NULL;
/*
 *****************************************************************************
 * The functions below are short wrapper functions to perform                *
 * bit manipulation, pointer arithmetic, and other helper operations.        *
 *                                                                           *
 * We've given you the function header comments for the functions below      *
 * to help you understand how this baseline code works.                      *
 *                                                                           *
 * Note that these function header comments are short since the functions    *
 * they are describing are short as well; you will need to provide           *
 * adequate details for the functions that you write yourself!               *
 *****************************************************************************
 */

/*
 * ---------------------------------------------------------------------------
 *                        BEGIN SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

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
static word_t pack(size_t size, bool isMiniBlock, bool prev_alloc, bool alloc) {
    word_t word = size;
    if (alloc) {
        word |= alloc_mask;
    }
    if (prev_alloc) {
        word |= prev_alloc_mask;
    }
    if (isMiniBlock) {
        word |= mini_block_mask;
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
    dbg_requires(block != NULL);
    return extract_size(block->header);
}

/**
 * @brief Given a payload pointer, returns a pointer to the corresponding
 *        block.
 * @param[in] bp A pointer to a block's payload
 * @return The corresponding block
 */
static block_t *payload_to_header(void *bp) {
    return (block_t *)((char *)bp - offsetof(block_t, payload));
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
    return (void *)(block->payload);
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
    return (word_t *)(block->payload + get_size(block) - dsize);
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
    dbg_assert(size != 0 && "Called footer_to_header on the prologue block");
    return (block_t *)((char *)footer + wsize - size);
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
 * @brief Returns the allocation status of a block, based on its header.
 * @param[in] block
 * @return The allocation status of the block
 */
static bool get_alloc(block_t *block) {
    dbg_requires(block != NULL);
    return extract_alloc(block->header);
}

/**
 * @brief Returns the allocation status of the previous block given an allocated
 * block, based on its header.
 * @param[in] block
 * @return The allocation status of the block
 */
static bool get_prev_alloc(block_t *block) {
    word_t header = block->header;
    return (bool)((header & prev_alloc_mask) >> 1);
}

/**
 * @brief Returns a boolean representing wheather or not the previous block is a
 * miniblock
 * @param[in] block    a block_t pointer
 * @return The allocation status of the block
 */
static bool get_prev_miniflag(block_t *block) {
    dbg_requires(block != NULL);
    word_t header = block->header;
    return (bool)((header & mini_block_mask) >> 2);
}
/* @brief Writes an epilogue header at the given address.
 *
 * The epilogue header has size 0, and is marked as allocated.
 *
 * @param[out] block The location to write the epilogue header
 */
static void write_epilogue(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires((char *)block == (char *)mem_heap_hi() - 7);
    block->header = pack(0, false, false, true);
}

/**
 * @brief Writes a block starting at the given address.
 *
 * This function writes both a header and footer (only for unallocated, regular
 * blocks), where the location of the footer is computed in relation to the
 * header based on the block size. Different conditions for mini-block and
 * unallocated block.
 *
 * Preconditions: the block pointer should not be null
 *
 * @param[out] block The location to begin writing the block header
 * @param[in] size The size of the new block
 * @param[in] alloc The allocation status of the new block
 * @param[in] prev_mini_block the status of the previous block if its mini or
 * not (size 16 bytes).
 * @param[in]
 */
static void write_block(block_t *block, size_t size, bool prev_mini_block,
                        bool prev_alloc, bool alloc) {
    dbg_requires(block != NULL);
    // cast into mini block/regular block
    if (size == 16) {
        mini_block_t *nBlock = ((mini_block_t *)block);
        nBlock->header = pack(16, prev_mini_block, prev_alloc, alloc);
    } else {
        // only for free blocks
        block_t *nBlock = (block_t *)block;
        nBlock->header = pack(size, prev_mini_block, prev_alloc, alloc);
        if (!alloc) {
            word_t *footerp = header_to_footer(block);
            *footerp = pack(size, prev_mini_block, prev_alloc, alloc);
        }
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
    word_t *footerp = find_prev_footer(block);

    // Return NULL if called on first block in the heap
    if (extract_size(*footerp) == 0) {
        return NULL;
    }

    return footer_to_header(footerp);
}

/*
 * ---------------------------------------------------------------------------
 *                        END SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/******** The remaining content below are helper and debug routines ********/

/**
 * @brief Given a block size to look for, the function looks for the appropriate
 * size class or bucket index in the segregated list of free blocks.
 *
 * A modified powers of 2 idea is utilized.
 *
 * @param[in] size the size of the free block being requested
 * @return An index between 0 and 11
 */
static int seg_search(size_t size) {
    int tot_buckets = 12;
    if (size > 32768) {
        return tot_buckets;
    } else if (size > 16384) {
        return (tot_buckets - 1);
    } else if (size > 8192) {
        return (tot_buckets - 2);
    } else if (size > 6144) {
        return (tot_buckets - 3);
    } else if (size > 4096) {
        return (tot_buckets - 4);
    } else if (size > 2048) {
        return (tot_buckets - 5);
    } else if (size > 1024) {
        return (tot_buckets - 6);
    } else if (size > 512) {
        return (tot_buckets - 7);
    } else if (size > 256) {
        return (tot_buckets - 8);
    } else if (size > 128) {
        return (tot_buckets - 9);
    } else if (size > 96) {
        return (tot_buckets - 10);
    } else if (size > 64) {
        return (tot_buckets - 11);
    } else if (size >= min_block_size) {
        return (tot_buckets - 12);
    }
    return 0;
}

/**
 * @brief Given a block size and a block pointer, the function looks for the
 * appropriate size class or bucket index in the segregated list of free blocks
 * and inserts the free block.
 *
 * The LIFO policy was used.
 *
 * @param[in] block a block pointer to the free block being inserted in the list
 * @param[in] size the size of the free block being requested
 * @pre block should not be null and it should be unallocated.
 */
static void seg_insert(block_t *block, size_t size) {
    dbg_requires(block != NULL);
    dbg_requires(!get_alloc(block));
    // find the bucket the block will be inserted into
    int bucket = seg_search(size);
    // insert to the root of the list
    block->freeP.prev = NULL;
    block_t *temp = segList[bucket];
    // check if free list has any pointers yet
    if (temp == NULL) {
        block->freeP.next = NULL;
        block->freeP.prev = NULL;
        segList[bucket] = block;
    } else {
        block->freeP.next = temp;
        temp->freeP.prev = block;
        segList[bucket] = block;
    }
    // printf("finished seg_list insert at address %p\n", (void
    // *)segList[bucket]);
}

/**
 * @brief Splicing a block out of the segregated list
 *
 * Used when a free block is about to be allocated and before coalescing
 *
 * @param[in] block a block pointer to the block being taken out of the free
 * list
 * @pre block != NULL and block should be free
 */
static void splice_block(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires(!get_alloc(block));
    // find the size bucket based on block size
    int bucket = seg_search(get_size(block));
    // find the previous free block
    block_t *prevBlock = block->freeP.prev;
    // the next free block
    block_t *nextBlock = block->freeP.next;

    if (prevBlock != NULL) {
        // the previous free block's next pointer should point to the next free
        // block of the given block
        prevBlock->freeP.next = nextBlock;
    }
    if (nextBlock != NULL) {
        // the next free block's previous pointer should point to the previous
        // free block of the given block
        nextBlock->freeP.prev = prevBlock;
    }
    if (nextBlock == NULL && prevBlock == NULL) {
        // if there was no previous or next block set the seglist of that size
        // class to NULL
        segList[bucket] = NULL;
    }
    if (prevBlock == NULL) {
        // if there is only no previous block, the seg list of that size class
        // can start at the nextBlock.
        segList[bucket] = nextBlock;
    }

    block->freeP.prev = NULL;
    block->freeP.next = NULL;
}

/**
 * @brief The mini blocks of size 16 bytes have their own singly linked list
 * with the free mini blocks. The function removes the miniblock from this list
 *
 *
 * Similar to splice block, the block may need to be coalesced with another free
 * block or we are mallocing data into this block.
 *
 * @param[in] block a mini block pointer that represents the block being
 * removed.
 * @pre block != NULL, get_size(block) = 16, and it should be free.
 */
static void remove_mini_block(mini_block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires(!extract_alloc(block->header));
    dbg_requires(extract_size(block->header) == 16);

    // if the block is at the root, the root should now start at the next mini
    // block
    if (block == mini_block_start) {
        mini_block_start = block->next;
        block->next = NULL;
    } else {
        mini_block_t *prevBlock = NULL;
        mini_block_t *currBlock = mini_block_start;
        // traversing through the singly linked list till we find the block we
        // are looking for.
        while (currBlock != NULL) {
            if (currBlock == block) {
                if (prevBlock != NULL) {
                    prevBlock->next = block->next;
                }
                block->next = NULL;
                break;
            }
            prevBlock = currBlock;
            currBlock = currBlock->next;
        }
    }
}

/**
 * @brief Inserting a miniblock into the mini block free list
 *
 * Always insert at the root
 *
 * @param[in] block a mini block pointer that represents the block being
 * inserted.
 * @pre block != NULL, get_size(block) = 16, and it should be free.
 */
static void add_mini_list(mini_block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires(!extract_alloc(block->header));
    dbg_requires(extract_size(block->header) == min_miniblock_size);
    if (mini_block_start == NULL) {
        mini_block_start = block;
        block->next = NULL;
    } else {
        block->next = mini_block_start;
        mini_block_start = block;
    }
}

/**
 * @brief this function implements constant time coalescing which is a technique
 * to reduce external fragmentation.
 *
 *
 * @param[in] block a pointer to the block that is currently being freed
 * @return a block pointer which has been coalesced.
 *
 * @pre the current block should not be null
 * @post the return block should not be null
 */
static block_t *coalesce_block(block_t *block) {
    dbg_requires(block != NULL);
    // a flag is the block is a miniblock or not
    size_t size = get_size(block);
    // a pointer to the previous block
    block_t *prevBlock;
    // a pointer to the next block
    block_t *nextBlock = find_next(block);
    // useful local variables
    bool prev_alloc;
    bool next_alloc;
    bool prev_mini;

    // finding out if the next block is to be considered free or not
    if (nextBlock == NULL) {
        // any NULL pointer should be thought of as "allocated"
        next_alloc = true;
    } else {
        next_alloc = get_alloc(nextBlock);
    }

    // if the previous block is unallocated, we want to get a pointer to that
    // block. If the previous block is a minblock it does not have a footer but
    // we can subtract by its fixed size to retrieve it.
    prev_alloc = get_prev_alloc(block);
    prev_mini = get_prev_miniflag(block);
    if (!prev_alloc) {
        if (get_prev_miniflag(block)) {
            prevBlock = (block_t *)((char *)block - min_miniblock_size);
            if (prevBlock == NULL) {
                prev_alloc = true;
            }
        } else {
            prevBlock = find_prev(block);
            if (prevBlock == NULL) {
                prev_alloc = true;
            }
        }
    }
    // case #1: both the adjacent(previous and next) blocks are allocated
    if (prev_alloc && next_alloc) {
        write_block(block, size, prev_mini, true, false);
    }
    // case #2: the previous block is allocated but the next one is not
    else if (prev_alloc && !next_alloc) {
        size_t newSize = size + get_size(nextBlock);
        write_block(block, newSize, prev_mini, true, false);
    }
    // case #3: the previous block is free but the next one is allocated.
    else if (!prev_alloc && next_alloc) {
        size_t newSize = size + get_size(prevBlock);
        bool dPrevStatus = get_prev_alloc(prevBlock);
        bool dPrevMini = get_prev_miniflag(prevBlock);
        write_block(prevBlock, newSize, dPrevMini, dPrevStatus, false);
        block = prevBlock;
    }
    // case #2: both adjacent blocks are free
    else if (!prev_alloc && !next_alloc) {
        size_t newSize =
            get_size(block) + get_size(nextBlock) + get_size(prevBlock);
        bool dPrevStatus = get_prev_alloc(prevBlock);
        bool dPrevMini = get_prev_miniflag(prevBlock);
        write_block(prevBlock, newSize, dPrevMini, dPrevStatus, false);
        block = prevBlock;
    }

    // this is now considered a new block and all pointers stored need to be set
    // to NULL
    if (get_size(block) == min_miniblock_size) {
        block->freeP.next = NULL;
    } else {
        block->freeP.prev = NULL;
        block->freeP.next = NULL;
    }
    return block;
}

/**
 * @brief extend the heap to introduce more blocks.
 *
 * When are a correct block fit is not found, we extend the heap by chunsize
 * bytes at the end of the heap. params[in]  size   the number of bytes to
 * increase the heap by
 *
 * @return a block pointer to the new block produced after the extension.
 */
static block_t *extend_heap(size_t size) {
    // new payload pointer
    void *bp;
    // we need to get to the epilogue and save the previous blcok's allocation
    // status and if the previous block is a miniblock or not.
    block_t *epilogueB = (block_t *)((char *)mem_heap_hi() - wsize + 1);
    bool prev_alloc = get_prev_alloc(epilogueB);
    bool prev_mini = get_prev_miniflag(epilogueB);
    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk((intptr_t)size)) == (void *)-1) {
        return NULL;
    }

    // get to the header of the block
    block_t *block = payload_to_header(bp);
    // this is a new free block
    write_block(block, size, prev_mini, prev_alloc, false);
    dbg_assert(get_size(block) == size);
    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_epilogue(block_next);
    // splice adjacent free blocks by first retrieving pointers to the previous
    // and nextblock.
    block_t *prevBlock = NULL;
    if (get_prev_miniflag(block)) {
        prevBlock = (block_t *)((char *)block - 16);
    } else {
        if (!get_prev_alloc(block)) {
            prevBlock = find_prev(block);
        }
    }

    // removing from the free or miniblock list
    if (prevBlock != NULL && !get_alloc(prevBlock)) {
        if (get_size(prevBlock) == 16) {
            remove_mini_block((mini_block_t *)prevBlock);
        } else {
            splice_block(prevBlock);
        }
    }

    // Coalesce in case the previous block was free
    block = coalesce_block(block);
    // insert into the regular block seg list has the extended block is a large
    // one.
    if (get_size(block) != min_miniblock_size) {
        seg_insert(block, get_size(block));
    }
    return block;
}

/**
 * @brief if a block being allocated to has an apprioriate amount of free space,
 * we can split a large block into pieces instead.
 *
 * @param[out] block a block pointer to the block being allocated to
 * @param[in] asize the adjusted size of payload being allocated.
 *
 * @pre block != NULL, the size of the block should at least be the adjusted
 * size and the block should be allocated.
 * @post the original block pointer should still be allocated.
 */
static void split_block(block_t *block, size_t asize) {
    dbg_requires(block != NULL);
    dbg_requires(get_size(block) >= asize);
    dbg_requires(get_alloc(block));
    dbg_requires(asize > 0);

    size_t block_size = get_size(block);
    bool prev_mini = get_prev_miniflag(block);
    // allocating a mini block
    if (asize == min_miniblock_size) {
        write_block(block, asize, prev_mini, get_prev_alloc(block), true);
        // adjusting the previous miniblock status to true
        prev_mini = true;
    }
    // split the latter  into miniblock
    if ((block_size - asize) == min_miniblock_size) {
        // the first part of the block could be a regular block
        if (asize >= min_block_size) {
            write_block(block, asize, prev_mini, get_prev_alloc(block), true);
            // adjusting the previous miniblock status to false
            prev_mini = false;
        }
        block_t *block_next = find_next(block);
        write_block(block_next, min_miniblock_size, prev_mini, true, false);
        // insert into mini list
        add_mini_list((mini_block_t *)block_next);
        // need to indicate to the block after this that this block is a
        // miniblock
        block_t *block_next_next = find_next(block_next);
        if (block_next_next != NULL) {
            block_next_next->header = pack(get_size(block_next_next), true,
                                           get_prev_alloc(block_next_next),
                                           get_alloc(block_next_next));
        }
        return;
    }

    // if there is space for a regular block of minimum size 32
    if ((block_size - asize) >= min_block_size) {
        block_t *block_next;

        // regular block
        if (asize >= min_block_size) {
            write_block(block, asize, prev_mini, get_prev_alloc(block), true);
            prev_mini = false;
        }

        block_next = find_next(block);
        write_block(block_next, block_size - asize, prev_mini, true, false);
        seg_insert(block_next, block_size - asize);
        dbg_ensures(get_alloc(block));
        return;
    }

    // if splitting the block was not necessary, need to tell the next block
    // that the previous block is allocated.
    block_t *block_next = find_next(block);
    if (block_next != NULL) {
        write_block(block_next, get_size(block_next),
                    get_prev_miniflag(block_next), true, get_alloc(block_next));
    }

    dbg_ensures(get_alloc(block));
}

/**
 * @brief searching within one of the size class's of the seg list for an
 * appropriately-sized block based on the adjusted size required.
 *
 * @param[out] block a block pointer to start of a particular size class's free
 * list
 * @param[in] asize the adjusted size of payload being allocated.
 *
 * @pre block != NULL, the block should be free
 */
static block_t *search_seg_list(block_t *block, size_t asize) {
    dbg_requires(block != NULL);
    dbg_requires(!get_alloc(block));
    if (block != NULL) {
        block_t *nextB = block->freeP.next;
        while (nextB != NULL) {
            if (!get_alloc(nextB) && get_size(nextB) >= asize) {
                return nextB;
            }
            nextB = nextB->freeP.next;
        }
    }
    return NULL;
}

/**
 * @brief finding which block best fits for the size we need to allocate from a
 * malloc/calloc/realloc call.
 *
 * A first-fit algorithm
 *
 * @param[in] asize adjusted size of the block we need to allocate
 * @return a block that is that least asize from the segregated free list.
 *
 */
static block_t *find_fit(size_t asize) {
    // the index of the 'bucket' an appropriately sized free block could be.
    int bucket = seg_search(asize);
    block_t *block;
    // search through all buckets higher (as they have larger-sized block) and
    // stop when we find the first apprioriate fit.
    while ((size_t)bucket != LIST_MAX) {
        block = segList[bucket];
        if (block != NULL && get_size(block) >= asize) {
            return block;
        }
        if (block != NULL) {
            block = search_seg_list(block, asize);
            if (block != NULL) {
                return block;
            }
        }
        bucket++;
    }
    return NULL; // no fit found
}

/*
 * @brief the header and footer of a block must be consistent
 *
 *
 * params[in] header   a word_t param that represents the header of a block
 * params[in] footer   a word_t param that represents the footer of a block
 *
 * */
static bool header_footer_match(word_t header, word_t footer) {
    if (extract_size(header) != extract_size(footer)) {
        return false;
    }
    if (extract_alloc(header) != extract_alloc(footer)) {
        return false;
    }
    return true;
}

/*
 * @brief a block should lie between mem_heap_lo() and mem_heap_high()
 *
 *
 * params[in]   block   a block pointer on the heap
 *
 * @pre block != NULL
 * */

static bool checkWithinBounds(block_t *block) {
    dbg_assert(block != NULL);
    void *lo = mem_heap_lo();
    void *hi = mem_heap_hi();
    void *myAdd = (void *)block;
    if (lo > myAdd) {
        return false;
    }
    if (myAdd > hi) {
        return false;
    }
    return true;
}

/*
 * @brief a block's payload needs to be aligned to 16 bytes which means the
 * header needs to be aligned to 8 bytes.
 *
 * getting the address held by pointer and checking if it cleanly divides 8
 *
 * params[in]   block   a pointer to a block on the heap
 *
 * @pre block != NULL
 * */
static bool checkAligned(block_t *block) {
    dbg_requires(block != NULL);
    return (bool)((unsigned long)(block) % (unsigned long)8 == 0);
}

/*
 * @brief a block needs to be of size at least 32 bytes
 *
 *
 * params[in]   mSize     block size
 *
 * @pre 0 <= mSize
 * */

static bool checkMinimumSize(size_t mSize) {
    if (mSize < min_block_size) {
        if (mSize != 16) {
            return false;
        }
    }
    return true;
}

/*
 * @brief based on the bucket get the lowest size allowed in the bucket
 *
 *
 * params[in]   bucket   the size bucket is was found in
 *
 * @pre 0 <= bucket < LIST_MAX
 * */
static size_t get_bucket_lo(size_t bucket) {
    dbg_requires(bucket < LIST_MAX);
    if (bucket == 11) {
        return 32768;
    } else if (bucket == 10) {
        return 16384;
    } else if (bucket == 9) {
        return 8192;
    } else if (bucket == 8) {
        return 4096;
    } else if (bucket == 7) {
        return 2048;
    } else if (bucket == 6) {
        return 1024;
    } else if (bucket == 5) {
        return 512;
    } else if (bucket == 4) {
        return 256;
    } else if (bucket == 3) {
        return 128;
    } else if (bucket == 2) {
        return 96;
    } else if (bucket == 1) {
        return 64;
    }
    // being inclusive of min_block_size
    return (min_block_size - 1);
}

/*
 * @brief checking if a free block is in the correct size class in the seg list
 *
 * params[in]   block    a pointer to the block in the free lists
 * params[in]   bucket   the size bucket is was found in
 *
 * @pre 0 <= bucket < LIST_MAX
 * @pre block != NULL and !get_alloc(block)
 * */
static bool seg_correct_bucket(block_t *block, size_t bucket) {
    dbg_requires(block != NULL);
    dbg_requires(!get_alloc(block));
    dbg_requires(bucket < LIST_MAX);

    size_t currSize = get_size(block);
    // if last bucket
    if (bucket == LIST_MAX - 1) {
        if (currSize > get_bucket_lo(bucket)) {
            return true;
        }
    } else {
        if (currSize > get_bucket_lo(bucket) &&
            get_bucket_lo(bucket + 1) >= currSize) {
            return true;
        }
    }
    return false;
}

/**
 * @brief scans the entire heap and checks it for errors.
 *
 * useful for degugging the malloc implementation.
 *
 * @param[in] line allows you to print the line number where mm_checkheap was
called, if you detect a problem with the heap.
 * @return false if and only if an error is detected, else true.
 */
bool mm_checkheap(int line) {
    // heapsize is the number of bytes
    size_t heapsize = mem_heapsize();
    // first valid byte in the heap
    block_t *startPointer = (block_t *)mem_heap_lo();
    // flag to see if we are at a free block for not
    bool atFreeBlock = false;
    // rechecking the heap size
    size_t totalSize = 0;
    // number of free (normally-sized blocks)  blocks in the heap
    size_t numFreeB = 0;
    // the number of free mini blocks in the heap
    size_t fMiniBlockCountH = 0;
    // if the heap was been initialised
    if (startPointer != NULL) {
        /*checking the validity of the prologue and epilogue blocks - heap-level
check*/
        if (get_size(startPointer) != 0 || !get_alloc(startPointer)) {
            return false;
        }
        // epilogue
        block_t *epilogueB = (block_t *)((char *)mem_heap_hi() - wsize + 1);
        if (!get_alloc(epilogueB) && get_size(epilogueB) != 0) {
            return false;
        }
        // blocks start at the address pointed by heap_start
        block_t *currBlock = heap_start;
        block_t *prevBlock = NULL;
        block_t *nextBlock;
        // looping through blocks in the heap
        while (currBlock != NULL && currBlock != epilogueB) {
            size_t currSize = get_size(currBlock);
            totalSize += currSize;
            if (!checkWithinBounds(currBlock)) {
                return false;
            }
            if (!checkMinimumSize(currSize)) {
                return false;
            }
            if (!checkAligned(currBlock)) {
                return false;
            }

            /*checking if there are no two consecutive free blocks in the
    heap.*/
            if (!get_alloc(currBlock) && atFreeBlock) {
                return false;
            }
            if (get_alloc(currBlock)) {
                atFreeBlock = false;
            } else {
                atFreeBlock = true;
                if (get_size(currBlock) == 16) {
                    fMiniBlockCountH++;
                } else {
                    numFreeB++;
                }
            }

            /*if we are at a free block currently, we check for header and
footer consistency.*/
            if (!get_alloc(currBlock)) {
                word_t *footer = header_to_footer(currBlock);
                if (footer == NULL) {
                    return false;
                }
                header_footer_match(currBlock->header, *footer);
            }

            // check if the prev_alloc flag is set correctly
            if (prevBlock != NULL) {
                // printf("prev consistency check");
                bool true_alloc_prev = get_alloc(prevBlock);
                bool prev_alloc_flag = get_prev_alloc(currBlock);
                if (true_alloc_prev != prev_alloc_flag) {
                    return false;
                }
            }

            // checking if the previous block's miniblock status is correct
            if (prevBlock != NULL) {
                // printf("prev_miniflag check\n");
                bool true_prev_miniflag = (get_size(prevBlock) == 16);
                bool prev_miniflag = get_prev_miniflag(currBlock);
                if (true_prev_miniflag != prev_miniflag) {
                    return false;
                }
                // printf("passed miniflag check\n");
            }
            // in case we are stuck in an infinite loop
            if (totalSize > heapsize) {
                return false;
            }
            nextBlock = find_next(currBlock);

            prevBlock = currBlock;
            currBlock = nextBlock;
        }

        // adding the size of the prologue and epilogue
        totalSize += 2 * wsize;
        // need to ensure we ended at the epilogue block
        if (currBlock != epilogueB) {
            return false;
        }
        // rechecking if the heap size is correct
        if (totalSize != heapsize) {
            return false;
        }

        // checking the free list
        // looking at the consistency of free blocks
        size_t numFreeBL = 0;
        // iterating over every size class of the seg list
        for (size_t i = 0; i < LIST_MAX; i++) {
            if (segList[i] != NULL) {
                block_t *currFBlock = segList[i];
                block_t *start = segList[i];
                // iterating over the free blocks in the seg list
                while (currFBlock != NULL) {
                    // checking if the block is actually a free block
                    if (get_alloc(currFBlock)) {
                        return false;
                    }
                    // checking if block is in the correct bucket based on size
                    if (!seg_correct_bucket(currFBlock, i)) {
                        return false;
                    }
                    // checking if the list is well-defined in terms of pointer
                    // connectivity
                    block_t *currNext = currFBlock->freeP.next;
                    if (currNext != NULL) {
                        block_t *prev = currNext->freeP.prev;
                        if (prev != currFBlock) {
                            return false;
                        }
                    }

                    /*checking if free list pointers are between mem_heap_lo()
            and mem_heap_high()*/
                    bool safe = checkWithinBounds(currFBlock);
                    if (!safe) {
                        return false;
                    }
                    // increment the free block count
                    numFreeBL++;
                    // stop the loop is we already account for more blocks than
                    // we have
                    if (numFreeBL > numFreeB) {
                        return false;
                    }
                    currFBlock = currNext;
                    // circularity check
                    if (currFBlock == start) {
                        return false;
                    }
                }
            }
        }
        // free blocks accounted for by the heap should be the same number in
        // the free lists
        if (numFreeB != numFreeBL) {
            return false;
        }

        // checking the integrity of the mini block free list
        mini_block_t *startMini = mini_block_start;
        size_t fMiniBlockCount = 0;
        while (startMini != NULL) {
            if (get_size((block_t *)startMini) != min_miniblock_size ||
                get_alloc((block_t *)startMini)) {
                return false;
            }
            fMiniBlockCount++;
            startMini = startMini->next;
        }

        // checking if the free mini blocks found in the heap is equal to the
        // number in the list
        if (fMiniBlockCount != fMiniBlockCountH) {
            return false;
        }
    }
    return true;
}

/**
 * @brief initialising the seg list with the first free block created
 *
 * @params[in] block adding the block pointer to the appropriate size bucket.
 * @param[in] chunksize the size of the block we are adding to the seg list
 * during initialization
 *
 * @return a bool to confirm that initialization happened successfully
 */
static bool seg_init(block_t *block, size_t chunksize) {
    int bucket = seg_search(chunksize);
    for (size_t i = 0; i < LIST_MAX; i++) {
        if ((size_t)bucket == i) {
            segList[i] = block;
        } else {
            segList[i] = NULL;
        }
    }
    return true;
}

/**
 * @brief clearing the seg list when we initialize the heap
 */
static void clear_seg() {
    for (size_t i = 0; i < LIST_MAX; i++) {
        segList[i] = NULL;
    }
}
/**
 * @brief Performs any necessary initializations, such as allocating the initial
 * heap area. The return value should be false if there was a problem in
 * performing the initialization, true otherwise.
 *
 * @post a well-formed heap
 * */
bool mm_init(void) {
    // clearing the seg list (if it has blocks)
    clear_seg();
    // want to reset the miniblock list
    mini_block_start = NULL;
    // Create the initial empty heap
    word_t *start = (word_t *)(mem_sbrk(2 * wsize));
    if (start == (void *)-1) {
        return false;
    }
    start[0] = pack(0, false, false, true); // Heap prologue (block footer)
    start[1] = pack(0, false, true, true);  // Heap epilogue (block header)

    // Heap starts with first "block header", currently the epilogue
    heap_start = (block_t *)&(start[1]);

    // Extend the empty heap with a free block of chunksize bytes
    block_t *init_block = extend_heap(chunksize);
    // init_block->freeP.next = init_block;
    // init_block->freeP.prev = init_block;
    if (init_block == NULL) {
        return false;
    }
    if (!seg_init(init_block, chunksize)) {
        return false;
    }
    return true;
    dbg_assert(mm_checkheap(__LINE__));
}

/**
 * @brief used to allocate a block of memory on the heap
 *
 * @param[in] size the size of the payload being allocated for
 * @return a pointer to an allocated block payload of at least size bytes
 */
void *malloc(size_t size) {
    dbg_requires(mm_checkheap(__LINE__));
    size_t asize;      // Adjusted block size
    size_t extendsize; // Amount to extend heap if no fit is found
    block_t *block = NULL;
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

    asize = round_up(size + wsize, dsize);
    if (asize == min_miniblock_size) {
        block = (block_t *)mini_block_start;
        if (block != NULL) {
            remove_mini_block((mini_block_t *)block);
        }
    }

    // Adjust block size to include overhead and to meet alignment
    // requirements
    if (block == NULL) {
        // Search the regular free list for a fit
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
    }

    // The block should be marked as free
    dbg_assert(!get_alloc(block));

    // splice block
    if (get_size(block) > 16) {
        splice_block(block);
        block->freeP.prev = NULL;
        block->freeP.next = NULL;
    }
    // Mark block as allocated
    size_t block_size = get_size(block);
    write_block(block, block_size, get_prev_miniflag(block),
                get_prev_alloc(block), true);
    // Try to split the block if too large
    split_block(block, asize);

    bp = header_to_payload(block);

    dbg_ensures(mm_checkheap(__LINE__));
    return bp;
}

/**
 * @brief freeing a block and deactivated
 *
 * @param[in] bp a ptr to the beginning of a block payload returned by a
 * previous call to malloc, calloc, or realloc and not already freed.
 * @post a well-formed heap
 * */
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
    write_block(block, size, get_prev_miniflag(block), get_prev_alloc(block),
                false);

    // splice the free block out
    /* may have to do some casing */
    block_t *prevBlock = NULL;
    if (get_prev_miniflag(block)) {
        prevBlock = (block_t *)((char *)block - min_miniblock_size);
    } else {
        if (!get_prev_alloc(block)) {
            prevBlock = find_prev(block);
        }
    }
    block_t *nextBlock = find_next(block);
    if (prevBlock != NULL && !get_alloc(prevBlock)) {
        if (get_size(prevBlock) == 16) {
            remove_mini_block((mini_block_t *)prevBlock);
        } else {
            splice_block(prevBlock);
        }
    }

    if (nextBlock != NULL && !get_alloc(nextBlock)) {
        if (get_size(nextBlock) == 16) {
            remove_mini_block((mini_block_t *)nextBlock);
        } else {
            splice_block(nextBlock);
        }
    }
    // Try to coalesce the block with its neighbors
    block = coalesce_block(block);
    // changing the next block based on caolesce
    nextBlock = find_next(block);
    if (nextBlock != NULL) {
        write_block(nextBlock, get_size(nextBlock),
                    (bool)(get_size(block) == 16), false, get_alloc(nextBlock));
    }
    if (get_size(block) == min_miniblock_size) {
        // new free mini block into free mini list
        add_mini_list((mini_block_t *)block);
    } else {
        // insert to the root of appropriate freelist (LIFO policy)
        seg_insert(block, get_size(block));
    }
    dbg_ensures(mm_checkheap(__LINE__));
}

/**
 * @brief used to resize a block of memory that was previously allocated
 *
 * @param[in] ptr the original payload pointer
 * @param[in] size the minimum size of the new block
 * @return a pointer to the payload of the new block.
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
 * @brief Allocates memory for an array of a certain number of elements of
 * size bytes each, initializes the memory to all bytes zero
 *
 * @param[in] elements the number of elements
 * @param[in] size the size of each element
 * @return a pointer to the allocated memory
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
 * 68 65 78 61 64 65 63 69 6d 61 6c 20 64 69 67 69 74 73 20 64               *
 * 6f 2e 2e 2e 20 68 61 68 61 68 61 21 20 41 53 43 49 49 20 69               *
 *                                                                           *
 * 73 6e 27 74 20 74 68 65 20 72 69 67 68 74 20 65 6e 63 6f 64               *
 * 69 6e 67 21 20 4e 69 63 65 20 74 72 79 2c 20 74 68 6f 75 67               *
 * 68 21 20 2d 44 72 2e 20 45 76 69 6c 0a c5 7c fc 80 6e 57 0a               *
 *                                                                           *
 *****************************************************************************
 */
