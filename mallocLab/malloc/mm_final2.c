/*
 ******************************************************************************
 *                                     mm.c                                   *
 *                                Final Version                               *
 *                                                                            *
 *                                 Name: Xin Wang                             *
 *                                Andrew ID: xinw3                            *
 *                                                                            *
 *  ************************************************************************  *
 *                                                                            *
 *   ** STRUCTURE. **                                                         *
 *                                                                            *
 *                           Using segregated free list.                      *
 *  Every element of the segerated free list array is an explicit free list.  *
 *                                                                            *
 *  HEADER: Both allocated and free blocks share the same header structure,   *
 *          i.e. the least significant bit indicates the allocation status of *
 *          current block, while the second last bit indicates the allocation *
 *          status of the previous block.                                     *                                     *
 *                                                                            *
 *  FOOTER: Only free blocks whose size are larger than 16 bytes have footers.*
 *          Treating the blocks whose size is equal to 16 bytes as a singly   *
 *          linked list and the other blocks as doubly linked list as before. *
 *          Meaning, there is only one pointer in the 16-byte blocks and two  *
 *          pointers in the blocks that size is larger than 16 bytes.         *
 *                                                                            *
 *  Optimization:                                                             *
 *  1. Eliminate footers in allocated blocks but keep them in free blocks.    *
 *     Change all header's second least bit to indicate the allocation status *
 *     of the previous block.                                                 *
 *  2. Decrease the minimum block size to dsize(16 bytes),                    *
 *  3. Using Find-n-fit policy.                                               *
 *     Instead of usint first fit, find n fits at one search and select the   *
 *     best fit from these blocks. So that the internal fragmentation will be *
 *     decreased and the throughput is larger than best fit.                  *
 *                                                                            *
 *                                                                            *
 *  Visualization:                                                            *
 *  HEAP:                                                                     *
 *                                                                            *
 *  | PROLOGUE |    ...             BLOCK         ...           | EPILOGUE |  *
 *                                                                            *
 *  Block:                                                                    *
 *                                                                            *
 *  Allocated blocks:   |  HEADER  |  ... PAYLOAD ...  |                      *
 *                                                                            *
 *  Unallocated blocks:                                                       *
 *       |  HEADER  | prev | next | ... (empty) ... |  FOOTER  | (size > 16)  *
 *                                                                            *
 *       |  HEADER  | prev | (size == 16)                                     *
 *                                                                            *
 *                                                                            *
 *                                                                            *
 *                                                                            *
 *  ************************************************************************  *
 ******************************************************************************
 */

/* Do not change the following! */
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stddef.h>
#include <assert.h>
#include <stddef.h>

#include "mm.h"
#include "memlib.h"

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
 * If DEBUG is defined, enable printing on dbg_printf and contracts.
 * Debugging macros, with names beginning "dbg_" are allowed.
 * You may not define any other macros having arguments.
 */
//#define DEBUG // uncomment this line to enable debugging

#ifdef DEBUG
/* When debugging is enabled, these form aliases to useful functions */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_requires(...) assert(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#define dbg_ensures(...) assert(__VA_ARGS__)
#else
/* When debugging is disnabled, no code gets generated for these */
#define dbg_printf(...)
#define dbg_requires(...)
#define dbg_assert(...)
#define dbg_ensures(...)
#endif

/* Basic constants */
typedef uint64_t word_t;
/* The alignment is 16 bytes */
#define ALIGNMENT 16

static const size_t wsize = sizeof(word_t);     // word and header size (bytes)
static const size_t dsize = 2 * wsize;          // double word size (bytes)
static const size_t min_block_size = dsize;    // Minimum block size
static const size_t chunksize = (1 << 12);    // requires (chunksize % 16 == 0)

static const word_t alloc_mask = 1;           //00...0001
static const word_t free_alloc_mask = 2;      //00...0010
static const word_t free_size_mask = 4;       //00...0100  
static const word_t size_mask = ~(word_t)0xF;

typedef struct block
{
    /* 
     * Header contains size + prev_size + prev_alloc + curr_alloc flag 
     */
    word_t header;
    /*
     * We don't know how big the payload will be.  Declaring it as an
     * array of size 0 allows computing its starting address using
     * pointer notation.
     */
    char payload[0];
    /*
     * We can't declare the footer as part of the struct, since its starting
     * position is unknown
     */
} block_t;

/* Global variables */
/* Pointer to first block */
static block_t *heap_listp = NULL;
static block_t *seg_free_list[14];

/* Function prototypes for internal helper routines */
static block_t *extend_heap(size_t size);
static void place(block_t *block, size_t asize);
static block_t *find_fit(size_t asize);
static block_t *coalesce(block_t *block);

static size_t max(size_t x, size_t y);
static size_t round_up(size_t size, size_t n);
static word_t pack(size_t size, bool prev_size, bool prev, bool alloc);

static size_t extract_size(word_t header);
static size_t get_size(block_t *block);
static word_t get_payload_size(block_t *block);

static bool 
extract_alloc(word_t header, bool prev_size, bool prev, bool curr);
static bool 
get_alloc(block_t *block, bool prev_size, bool prev, bool curr);

static void 
write_header(block_t *block, size_t size, 
            bool prev_size, bool prev, bool alloc);
static void 
write_free_footer(block_t *block, size_t size, bool alloc);

static block_t *payload_to_header(void *bp);
static void *header_to_payload(block_t *block);

static block_t *find_next(block_t *block);
static word_t *find_prev_footer(block_t *block);
static block_t *find_prev(block_t *block);

bool mm_checkheap(int verbose);
static void remove_free_block(block_t *block);
static void insert(block_t *block);
static block_t *find_free_next(block_t *block);
static block_t *find_free_prev(block_t *block);
static bool check_block(block_t *block);
static word_t *find_footer(block_t *block);
static bool check_free_list(block_t *block);
static void set_prev(block_t *block, block_t *prev);
static void set_next(block_t *block, block_t *next);
static int find_index(size_t size);

/*
 * mm_init: initializes the heap; it is run once when heap_start == NULL.
 *          prior to any extend_heap operation, this is the heap:
 *              start            start+8           start+16
 *          INIT: | PROLOGUE_FOOTER | EPILOGUE_HEADER |
 * heap_listp ends up pointing to the epilogue header.
 */
bool mm_init(void) 
{

    // Create the initial empty heap 
    word_t *start = (word_t *)(mem_sbrk(2 * wsize));

    if (start == (void *)-1) 
    {
        return false;
    }
    // Initialize prologue and epilogue of the heap
    start[0] = pack(0, false, true, true); // Prologue footer
    start[1] = pack(0, false, true, true); // Epilogue header

    // Heap starts with first block header (epilogue)
    heap_listp = (block_t *) & (start[1]);

    // Initialize segregate free list.
    memset(seg_free_list, 0, 14 * sizeof(block_t *));

    // Extend the empty heap with a free block of chunksize bytes
    if (extend_heap(chunksize) == NULL)
    {
        return false;
    }
    //mm_checkheap(1); //Check the heap.
    return true;
}

/*
 * malloc: allocates a block with size at least (size + dsize), rounded up to
 *         the nearest 16 bytes, with a minimum of 2*dsize. Seeks a
 *         sufficiently-large unallocated block on the heap to be allocated.
 *         If no such block is found, extends heap by the maximum between
 *         chunksize and (size + dsize) rounded up to the nearest 16 bytes,
 *         and then attempts to allocate all, or a part of, that memory.
 *         Returns NULL on failure, otherwise returns a pointer to such block.
 *         The allocated block will not be used for further allocations until
 *         freed.
 */
void *malloc(size_t size) 
{
    dbg_requires(mm_checkheap);
    //printf("\nMalloc: %d\n", (int)size);
    size_t asize;      // Adjusted block size
    size_t extendsize; // Amount to extend heap if no fit is found
    block_t *block;
    void *bp = NULL;

    if (heap_listp == NULL) // Initialize heap if it isn't initialized
    {
        mm_init();
    }

    if (size == 0) // Ignore spurious request
    {
        dbg_ensures(mm_checkheap);
        return bp;
    }

    // Adjust block size to include overhead and to meet alignment requirements
    asize = round_up(size + wsize, dsize);


    // Search the free list for a fit
    block = find_fit(asize);

    // If no fit is found, request more memory, and then and place the block
    if (block == NULL)
    {  
        extendsize = max(asize, chunksize);
        block = extend_heap(extendsize);
        if (block == NULL) // extend_heap returns an error
        {
            return bp;
        }

    }

    place(block, asize);
    bp = header_to_payload(block);

    dbg_printf("Malloc size %zd on address %p.\n", size, bp);
    dbg_ensures(mm_checkheap);
    return bp;
} 

/*
 * free: Frees the block such that it is no longer allocated while still
 *       maintaining its size. Block will be available for use on malloc.
 */
void free(void *bp)
{
    if (bp == NULL)
    {
        return;
    }

    block_t *block = payload_to_header(bp);

    size_t size = get_size(block);

    bool prev_alloc_status = get_alloc(block, false, true, false);
    bool prev_size_status = get_alloc(block, true, false, false);

    write_header(block, size, prev_size_status, prev_alloc_status, false);
    write_free_footer(block, size, false);

    //printf("\nFree: %d\n", (int)size);
    coalesce(block);

}

/*
 * realloc: returns a pointer to an allocated region of at least size bytes:
 *          if ptr is NULL, then call malloc(size);
 *          if size == 0, then call free(ptr) and returns NULL;
 *          else allocates new region of memory, copies old data to new memory,
 *          and then free old block. Returns old block if realloc fails or
 *          returns new pointer on success.
 */
void *realloc(void *ptr, size_t size)
{
    block_t *block = payload_to_header(ptr);
    size_t copysize;
    void *newptr;

    // If size == 0, then free block and return NULL
    if (size == 0)
    {
        free(ptr);
        return NULL;
    }

    // If ptr is NULL, then equivalent to malloc
    if (ptr == NULL)
    {
        return malloc(size);
    }

    // Otherwise, proceed with reallocation
    newptr = malloc(size);
    // If malloc fails, the original block is left untouched
    if (!newptr)
    {
        return NULL;
    }

    // Copy the old data
    copysize = get_payload_size(block); // gets size of old payload
    if(size < copysize)
    {
        copysize = size;
    }
    memcpy(newptr, ptr, copysize);

    // Free the old block
    free(ptr);

    return newptr;
}
    

/*
 * calloc: Allocates a block with size at least (elements * size + dsize)
 *         through malloc, then initializes all bits in allocated memory to 0.
 *         Returns NULL on failure.
 * @param nmemb: number of element in the array.
 * @param size: the size of each element.
 */
void *calloc(size_t nmemb, size_t size)
{
    void *bp;
    size_t asize = nmemb * size;

    if (asize/nmemb != size)
    // Multiplication overflowed
    return NULL;
    
    bp = malloc(asize);
    if (bp == NULL)
    {
        return NULL;
    }
    // Initialize all bits to 0
    memset(bp, 0, asize);

    return bp;
}

/******** The remaining content below are helper and debug routines ********/

/*
 * extend_heap: Extends the heap with the requested number of bytes, and
 *              recreates epilogue header. Returns a pointer to the result of
 *              coalescing the newly-created block with previous free block, if
 *              applicable, or NULL in failure.
 */
static block_t *extend_heap(size_t size) 
{
    void *bp;

    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    //printf("Extend: %d\n", (int)size);
    if ((bp = mem_sbrk(size)) == (void *)-1)
    {
        return NULL;
    }
    
    // Initialize free block header/footer 
    block_t *block = payload_to_header(bp);
    // Find the allocation status of the previous block.
    bool prev_status = get_alloc(block, false, true, false);
    bool prev_size = get_alloc(block, true, false, false);
    write_header(block, size, prev_size, prev_status, false);
    write_free_footer(block, size, false);
    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_header(block_next, 0, false, false, true);

    // Coalesce in case the previous block was free
    return coalesce(block);
}

/* Coalescing with boundary tags.
 * Coalesces current block with previous and next blocks if either
 * or both are unallocated; otherwise the block is not modified.
 * Returns pointer to the coalesced block. After coalescing, the
 * immediate contiguous previous and next blocks must be allocated.
 */
static block_t *coalesce(block_t * block) 
{
    block_t *block_next = find_next(block);
    block_t *block_next_next = find_next(block_next);
    

    bool prev_alloc = get_alloc(block, false, true, false);
    bool next_alloc = get_alloc(block_next, false, false, true);

    bool prev_size_status = get_alloc(block, true, false, false);
    bool block_size_status = get_alloc(block_next, true, false, false);

    size_t size = get_size(block);
    size_t next_size = get_size(block_next);
    size_t next_next_size = get_size(block_next_next);
    //printf("Coalesce: %d\n", (int)size);
    // If both blocks are not free, no need coalescing.
    if (prev_alloc && next_alloc)              // Case 1
    {
        write_header(block, size, prev_size_status, true, false);
        write_header(block_next, next_size, block_size_status, false, true);
        insert(block);
        return block;
    }
    // If only the next block is free.
    else if (prev_alloc && !next_alloc)        // Case 2
    {
        size += next_size;
        remove_free_block(block_next);
        write_header(block, size, prev_size_status, true, false);
        write_header(block_next_next, next_next_size, false, false, true);
        write_free_footer(block, size, false);
        insert(block);
    }
    // If the previous block is free.
    else if (!prev_alloc && next_alloc)        // Case 3
    {
        block_t *block_prev = find_prev(block);
        bool prev_prev_size_status = get_alloc(block_prev, true, false, false);
        size_t prev_size = get_size(block_prev);
        size += prev_size;

        remove_free_block(block_prev);
        write_header(block_prev, size, prev_prev_size_status, true, false);
        write_header(block_next, next_size, false, false, true);
        write_free_footer(block_prev, size, false);
        block = block_prev;
        insert(block);
    }
    // If both previous and the next blocks are free.
    else                                        // Case 4
    {
        block_t *block_prev = find_prev(block);
        bool prev_prev_size_status = get_alloc(block_prev, true, false, false);
        size_t prev_size = get_size(block_prev);
        size += next_size + prev_size;

        remove_free_block(block_prev);
        remove_free_block(block_next);
        write_header(block_prev, size, prev_prev_size_status, true, false);
        write_header(block_next_next, next_next_size, false, false, true);
        write_free_footer(block_prev, size, false);
        block = block_prev;
        insert(block);
    }
    return block;
}

/*
 * place: Places block with size of asize at the start of bp. If the remaining
 *        size is at least the minimum block size, then split the block to the
 *        the allocated block and the remaining block as free, which is then
 *        inserted into the segregated list. Requires that the block is
 *        initially unallocated.
 */
static void place(block_t *block, size_t asize)
{
    size_t csize = get_size(block);
    bool prev_size_status = get_alloc(block, true, false, false);
    bool block_size_status = (asize == 16) ? true : false;
    //printf("Place: %d\n", (int)asize);
    if ((csize - asize) >= min_block_size) 
    {
        block_t *block_next;
        block_t *block_next_next;
        remove_free_block(block);
        write_header(block, asize, prev_size_status, true, true);

        block_next = find_next(block);
        write_header(block_next, csize-asize, block_size_status, true, false);

        bool next_status = (csize - asize == 16) ? true : false;
        if (!next_status)
        {
            write_free_footer(block_next, csize - asize, false);
        }

        block_next_next = find_next(block_next);
        write_header(block_next_next, get_size(block_next_next), 
                        next_status, false, true);

        insert(block_next);
        return;
    }
    
    else
    { 
        remove_free_block(block);
        write_header(block, csize, prev_size_status, true, true);
        block_t *block_next = find_next(block);
        write_header(block_next, get_size(block_next), 
                      block_size_status, true, true);
    }
}

/*
 * find_n_fit: Looks for a free block with at least asize bytes with
 *           find-n-fit policy. Returns NULL if none is found.
 */
static block_t *find_fit(size_t asize)
{
    block_t *block;
    block_t *min_block = NULL;
    int index = find_index(asize);
    int n = 9;              //find n fit.
    size_t min_size = ~(size_t)0;    //assign the maximum value of size_t.

    //printf("Find: %d\n", (int)asize);
    if (index == 0 && seg_free_list[0] != NULL)
    {
        return seg_free_list[0];
    }

    index = (index == 0) ? (index + 1) : index;
    for (int i = index; i < 14; i++)
    {
        for (block = seg_free_list[i]; block != NULL;
                                 block = find_free_next(block))
        {
            if(get_size(block) == asize)
            {
                return block;
            }
            if (get_size(block) > asize)
            {
                n--;                //find one fit
                if (get_size(block) < min_size)
                {
                    min_size = get_size(block);
                    min_block = block;
                }
                if (n == 0)
                {
                    return min_block;
                }
            }
        }
        if (min_block != NULL)
        {
            return min_block;
        }
    }
    return NULL;
}

/*
 * max: returns x if x > y, and y otherwise.
 */
static size_t max(size_t x, size_t y)
{
    return (x > y) ? x : y;
}


/*
 * round_up: Rounds size up to next multiple of n
 */
static size_t round_up(size_t size, size_t n)
{
    return (n * ((size + (n-1)) / n));
}

/*
 * pack: returns a header reflecting a specified size and its alloc status.
 *       If the block is allocated, the lowest bit is set to 1, and 0 otherwise.
 *       If the previous block is allocated, the second lowest bit is set to 1,
 *           otherwise 0.
 */
static word_t pack(size_t size, bool prev_size, bool prev, bool alloc)
{
    int new_prev = (int)prev << 1;
    int new_prev_size = (int) prev_size << 2;
    return size | new_prev_size | new_prev | alloc;
}


/*
 * extract_size: returns the size of a given header value based on the header
 *               specification above.
 */
static size_t extract_size(word_t word)
{
    return (word & size_mask);
}

/*
 * get_size: returns the size of a given block by clearing the lowest 4 bits
 *           (as the heap is 16-byte aligned).
 */
static size_t get_size(block_t *block)
{
    
    return extract_size(block->header);
    
}

/*
 * get_payload_size: returns the payload size of a given block, equal to
 *                   the entire block size minus the header and footer sizes.
 */
static word_t get_payload_size(block_t *block)
{
    size_t asize = get_size(block);
    return asize - wsize;
}

/*
 * extract_alloc: returns the allocation status of a given header value based
 *                on the header specification above.
 */
static bool extract_alloc(word_t word, 
                            bool prev_size, bool prev, bool curr)
{
    if (curr)
    {
        return (bool)(word & alloc_mask);
    }
    if (prev)
    {
        return (bool)(word & free_alloc_mask);
    }
    return (bool)(word & free_size_mask);
}

/*
 * get_alloc: get the status of the allocation status of current block,
 *            prev block, and the size status of the previous block.
 *            return true if the current and the previous block is allocated
 *            and if the previous block size is 16 bytes.
 */
static bool get_alloc(block_t *block, 
                        bool prev_size, bool prev, bool curr)
{
    return extract_alloc(block->header, prev_size, prev, curr);
}

/*
 * write_header: given a block and its size and allocation status,
 *               writes an appropriate value to the block header.
 *               prev indicates write the status of the previous block.
 *               prev_size indicates the size status of the previous block.
 */
static void 
write_header(block_t *block, size_t size, bool prev_size,
             bool prev, bool alloc)
{
    block->header = pack(size, prev_size, prev, alloc);
}


/*
 * write_footer: given a block and its size and allocation status,
 *               writes an appropriate value to the block footer by first
 *               computing the position of the footer.
 */
static void 
write_free_footer(block_t *block, size_t size, bool alloc)
{
    word_t *footerp = (word_t *)((block->payload) + get_size(block) - dsize);
    *footerp = pack(size, false, false, alloc);
}


/*
 * find_next: returns the next consecutive block on the heap by adding the
 *            size of the block.
 */
static block_t *find_next(block_t *block)
{
    dbg_requires(block != NULL);
    block_t *block_next = (block_t *)(((char *)block) + get_size(block));

    dbg_ensures(block_next != NULL);
    return block_next;
}

/*
 * find_prev_footer: returns the footer of the previous block.
 */
static word_t *find_prev_footer(block_t *block)
{
    // Compute previous footer position as one word before the header
    return (&(block->header)) - 1;
}

/*
 * find_prev: returns the previous block position by checking the previous
 *            block's footer and calculating the start of the previous block
 *            based on its size.
 */
static block_t *find_prev(block_t *block)
{
    bool is16 = get_alloc(block, true, false, false);

    // If the block size is not 16 bytes.
    if (!is16)
    {
        word_t *footerp = find_prev_footer(block);
        size_t size = extract_size(*footerp);
        return (block_t *)((char *)block - size);
    }
    // If the block size is 16 bytes, 
    return (block_t *)((char *)block - dsize);
}

/*
 * payload_to_header: given a payload pointer, returns a pointer to the
 *                    corresponding block.
 */
static block_t *payload_to_header(void *bp)
{
    return (block_t *)(((char *)bp) - offsetof(block_t, payload));
}

/*
 * header_to_payload: given a block pointer, returns a pointer to the
 *                    corresponding payload.
 */
static void *header_to_payload(block_t *block)
{
    return (void *)(block->payload);
}

/* Remove block from free list*/
static void remove_free_block(block_t *block)
{
    
    int index = find_index(get_size(block));
    //printf("Remove: %d\n", (int)get_size(block));
    /* If found block size is equal to 16 bytes.
     * Can only have one prev pointers. 
     * Header + prev
     * Imagine the list is from the bottom to top. 
     */
    if (index == 0)
    {
        block_t *prev_tmp = seg_free_list[0];
        block_t *block_prev = find_free_prev(block);
        if (prev_tmp == block)
        {
            seg_free_list[0] = block_prev;
            return;
        }

        while(find_free_prev(prev_tmp) != block)
        {
            prev_tmp = find_free_prev(prev_tmp);
        }
        set_prev(prev_tmp, block_prev);
        return;
    }
    // If the index is not 0, i.e. the block size is larger than 16 bytes.
    block_t *block_prev = find_free_prev(block);
    block_t *block_next = find_free_next(block);
    // If there is only one block
    if ((block_prev == NULL) && (block_next == NULL))
    {
        seg_free_list[index] = NULL;
        return;
    }
    if (block_prev == NULL)
    {
        set_prev(block_next, NULL);
        seg_free_list[index] = block_next;
        return;
    }
    if (block_next == NULL)
    {
        set_next(block_prev, NULL);
        return;
    }
    set_next(block_prev, block_next);
    set_prev(block_next, block_prev);
}
// Insert the block to the first of the free list.
static void insert(block_t *block)
{
    int index = find_index(get_size(block));
    //printf("Insert: %d\n", (int)get_size(block));
    if (index == 0)
    {
        set_prev(block, seg_free_list[0]);
        seg_free_list[0] = block;
        return;
    }
    if (seg_free_list[index] == NULL) 
    {
        seg_free_list[index] = block;
        //Set the predecessor pointer to NULL
        set_prev(block, NULL);
        //Set the successor pointer to NULL
        set_next(block, NULL);
        return;
    }
    set_prev(seg_free_list[index], block);
    set_next(block, seg_free_list[index]);
    set_prev(block, NULL);
    seg_free_list[index] = block;
    
}
// Find successor pointer.
static block_t *find_free_next(block_t *block)
{
    return (block_t *)(*((word_t *)block + 2));
}
// Find predecessor pointer.
static block_t *find_free_prev(block_t *block)
{
    return (block_t *)(*((word_t *)block + 1));
}
// Set the the block pointed by the predecessor pointer.
static void set_prev(block_t *block, block_t *prev)
{
    *((word_t *)block + 1) = (word_t)prev;
}
// Set the the block pointed by the successor pointer.
static void set_next(block_t *block, block_t *next)
{
    *((word_t *)block + 2) = (word_t)next;
}
/* Find the index of the segreated free list array 
 * The smallest block size is 2 * dsize = 32 bytes
 * So when the size is less than 64 bytes, return 0 and so on.
 */
static int find_index(size_t size) 
{
    if (size < 32)
    {
        return 0;
    }
    if (size < 64)
    {
        return 1;
    }
    if (size < 128)
    {
        return 2;
    }
    if (size < 256)
    {
        return 3;
    }
    if (size < 512)
    {
        return 4;
    }
    if (size < 1024)
    {
        return 5;
    }
    if (size < 2048)
    {
        return 6;
    }
    if (size < 4096)
    {
        return 7;
    }
    if (size < 8192)
    {
        return 8;
    }
    if (size < 16382)
    {
        return 9;
    }
    if (size < 32764)
    {
        return 10;
    }
    if (size < 65536)
    {
        return 11;
    }
    if (size < 131072)
    {
        return 12;
    }
    return 13;
}
/* mm_checkheap: checks the heap for correctness; returns true if
 *               the heap is correct, and false otherwise.
 *               can call this function using mm_checkheap(__LINE__);
 *               to identify the line number of the call site.
 */
bool mm_checkheap(int verbose)  
{ 
    block_t *bp;
    block_t *prologue = (block_t *)mem_heap_lo();
    block_t *epilogue = (block_t *)mem_heap_hi();
    /* Check prologue 
     * Check if the first block's header's size or allocation bit is wrong. 
     */
    if (get_size(prologue) != 0 
            || !get_alloc(prologue, false, false, true))
    {
        printf(" Error: Wrong prologue header.\n");
        return false;
    }
    // Chenck the status of allocated blocks.
    for (bp = heap_listp; ((bp->header) ^ 0x1) > 0; bp = find_next(bp))
    {
        check_block(bp);
        return false;
    }
    for (int i = 0; i < 14; i++)
    {
        for (bp = seg_free_list[i]; ((bp->header) ^ 0x1) > 0; 
                        bp = find_free_next(bp))
        {
            check_free_list(bp);
        }
        return false;
    }
    // Check epilogue.
    if (get_size(epilogue) != 0 || !get_alloc(epilogue, false, false, true))
    {
        printf(" Error: Wrong epilogue header.\n");
        return false;
    }
    return true; 
}

/* Check allocated blocks.
 * 1. Address alignment and matching.
 * 2. Within heap boundaries. 
 */
static bool check_block(block_t *block)
{
    if (((word_t)(block)) % dsize)
    {
        printf(" Error: block %p is not aligned correctly.\n", block);
        return false;
    }
    if ((void *)find_prev(block) < mem_heap_lo() 
        || (void *) find_prev(block) > mem_heap_hi())
    {
        printf(" Error: previous block pointer %p is out of boundary.", block);
        return false;
    }
    if ((void *)find_next(block) < mem_heap_lo() 
        || (void *) find_next(block) > mem_heap_hi())
    {
        printf(" Error: previous block pointer %p is out of boundary.", block);
        return false;
    }
    return true;
}
/* Check explicit free list 
 * 1. Header & footer matching.
 * 2. All free list pointers are between mem_heap_lo() and mem_heap_hi().
 * 3. Check coalescing.
 */
static bool check_free_list(block_t *block)
{
    if ((void *)find_free_prev(block) < mem_heap_lo() 
                    || (void *)find_free_prev(block) > mem_heap_hi())
    {
        printf(" Error: previous pointer %p is out of boundary.", block);
        return false;
    }
    if ((void *)find_free_next(block) < mem_heap_lo() 
                    || (void *)find_free_next(block) > mem_heap_hi())
    {
        printf(" Error: next pointer %p is out of boundary.", block);
        return false;
    }
    if (!get_alloc(block, false, false, true))
    {
        block_t *block_next = find_next(block);
        if (get_alloc(block_next, false, false, true))
        {
            printf(" Error: two consecutive free blocks %p & %p.", 
                            block, block_next);
            return false;
        }
    }
    return true;
}
static word_t *find_footer(block_t *block)
{
    word_t *footerp = (word_t *)((block->payload) + get_size(block) - dsize);
    return footerp;
}