/*
 ******************************************************************************
 *                                     mm.c                                   *
 *                                 Name: Xin Wang                             *
 *                                Andrew ID:xinw3                             *
 *                                                                            *
 *  ************************************************************************  *
 *                               DOCUMENTATION                                *
 *                                                                            *
 *  ** STRUCTURE. **                                                          *
 *                                                                            *
 *  Both allocated and free blocks share the same header structure.           *
 *  HEADER: 8-byte, aligned to 8th byte of an 16-byte aligned heap, where     *
 *          - The lowest order bit is 1 when the block is allocated, and      *
 *            0 otherwise.                                                    *
 *          - The whole 8-byte value with the least significant bit set to 0  *
 *            represents the size of the block as a size_t                    *
 *            The size of a block includes the header and footer.             *
 *  FOOTER: 8-byte, aligned to 0th byte of an 16-byte aligned heap. It        *
 *          contains the exact copy of the block's header.                    *
 *  The minimum blocksize is 32 bytes.                                        *
 *                                                                            *
 *  Allocated blocks contain the following:                                   *
 *  HEADER, as defined above.                                                 *
 *  PAYLOAD: Memory allocated for program to store information.               *
 *  FOOTER, as defined above.                                                 *
 *  The size of an allocated block is exactly PAYLOAD + HEADER + FOOTER.      *
 *                                                                            *
 *  Free blocks contain the following:                                        *
 *  HEADER, as defined above.                                                 *
 *  FOOTER, as defined above.                                                 *
 *  The size of an unallocated block is at least 32 bytes.                    *
 *                                                                            *
 *  Block Visualization.                                                      *
 *                    block     block+8          block+size-8   block+size    *
 *  Allocated blocks:   |  HEADER  |  ... PAYLOAD ...  |  FOOTER  |           *
 *                                                                            *
 *                    block     block+8          block+size-8   block+size    *
 *  Unallocated blocks: |  HEADER  |  ... (empty) ...  |  FOOTER  |           *
 *                                                                            *
 *  ************************************************************************  *
 *  ** INITIALIZATION. **                                                     *
 *                                                                            *
 *  The following visualization reflects the beginning of the heap.           *
 *      start            start+8           start+16                           *
 *  INIT: | PROLOGUE_FOOTER | EPILOGUE_HEADER |                               *
 *  PROLOGUE_FOOTER: 8-byte footer, as defined above, that simulates the      *
 *                    end of an allocated block. Also serves as padding.      *
 *  EPILOGUE_HEADER: 8-byte block indicating the end of the heap.             *
 *                   It simulates the beginning of an allocated block         *
 *                   The epilogue header is moved when the heap is extended.  *
 *                                                                            *
 *  ************************************************************************  *
 *  ** BLOCK ALLOCATION. **                                                   *
 *                                                                            *
 *  Upon memory request of size S, a block of size S + dsize, rounded up to   *
 *  16 bytes, is allocated on the heap, where dsize is 2*8 = 16.              *
 *  Selecting the block for allocation is performed by finding the first      *
 *  block that can fit the content based on a first-fit or next-fit search    *
 *  policy.                                                                   *
 *  The search starts from the beginning of the heap pointed by heap_listp.   *
 *  It sequentially goes through each block in the implicit free list,        *
 *  the end of the heap, until either                                         *
 *  - A sufficiently-large unallocated block is found, or                     *
 *  - The end of the implicit free list is reached, which occurs              *
 *    when no sufficiently-large unallocated block is available.              *
 *  In case that a sufficiently-large unallocated block is found, then        *
 *  that block will be used for allocation. Otherwise--that is, when no       *
 *  sufficiently-large unallocated block is found--then more unallocated      *
 *  memory of size chunksize or requested size, whichever is larger, is       *
 *  requested through mem_sbrk, and the search is redone.                     *
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

/* rounds up to the nearest multiple of ALIGNMENT */
static size_t align(size_t x) {
    return ALIGNMENT * ((x+ALIGNMENT-1)/ALIGNMENT);
}
static const size_t wsize = sizeof(word_t);   // word and header size (bytes)
static const size_t dsize = 2 * wsize;          // double word size (bytes)
static const size_t min_block_size = 2 * dsize; // Minimum block size
static const size_t chunksize = (1 << 12);    // requires (chunksize % 16 == 0)

static const word_t alloc_mask = 0x1;
static const word_t size_mask = ~(word_t)0xF;

typedef struct block
{
    /* Header contains size + allocation flag */
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
/* Pointer to the first free block */
static block_t *free_listp = NULL;

/* Function prototypes for internal helper routines */
static block_t *extend_heap(size_t size);
static void place(block_t *block, size_t asize);
static block_t *find_fit(size_t asize);
static block_t *coalesce(block_t *block);

static size_t max(size_t x, size_t y);
static size_t round_up(size_t size, size_t n);
static word_t pack(size_t size, bool alloc);

static size_t extract_size(word_t header);
static size_t get_size(block_t *block);
static word_t get_payload_size(block_t *block);

static bool extract_alloc(word_t header);
static bool get_alloc(block_t *block);

static void write_header(block_t *block, size_t size, bool alloc);
static void write_footer(block_t *block, size_t size, bool alloc);

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
    //Initialize prologue and epilogue of the heap
    start[0] = pack(0, true); // Prologue footer
    start[1] = pack(0, true); // Epilogue header

    // Heap starts with first block header (epilogue)
    heap_listp = (block_t *) &(start[1]);

    free_listp = NULL;

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
    if (size <= dsize) 
    {
        asize = 2 * dsize;
    } else {
        asize = round_up(size, dsize) + dsize;
    }

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

    write_header(block, size, false);
    write_footer(block, size, false);

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
    if ((bp = mem_sbrk(size)) == (void *)-1)
    {
        return NULL;
    }
    
    // Initialize free block header/footer 
    block_t *block = payload_to_header(bp);
    write_header(block, size, false);
    write_footer(block, size, false);
    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_header(block_next, 0, true);

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
    block_t *block_prev = find_prev(block);

    bool prev_alloc = extract_alloc(*(find_prev_footer(block)));
    bool next_alloc = get_alloc(block_next);
    size_t size = get_size(block);
    /* If both blocks are not free, not need coalescing */
    if (prev_alloc && next_alloc)              // Case 1
    {
        insert(block);
        return block;
    }
    /* If only the next block is free */
    else if (prev_alloc && !next_alloc)        // Case 2
    {
        size += get_size(block_next);
        remove_free_block(block_next);
        write_header(block, size, false);
        write_footer(block, size, false);
        insert(block);
    }
    /* If the previous block is free */
    else if (!prev_alloc && next_alloc)        // Case 3
    {
        size += get_size(block_prev);
        remove_free_block(block_prev);
        write_header(block_prev, size, false);
        write_footer(block_prev, size, false);
        block = block_prev;
        insert(block);
    }
    /* If both previous and the next blocks are free */
    else                                        // Case 4
    {
        size += get_size(block_next) + get_size(block_prev);
        remove_free_block(block_prev);
        remove_free_block(block_next);
        write_header(block_prev, size, false);
        write_footer(block_prev, size, false);
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

    if ((csize - asize) >= min_block_size)
    {
        block_t *block_next;
        write_header(block, asize, true);
        write_footer(block, asize, true);
        remove_free_block(block);
        block_next = find_next(block);
        write_header(block_next, csize-asize, false);
        write_footer(block_next, csize-asize, false);
        insert(block_next);
    }
    else
    { 
        write_header(block, csize, true);
        write_footer(block, csize, true);
        remove_free_block(block);
    }
}

/*
 * find_fit: Looks for a free block with at least asize bytes with
 *           first-fit policy. Returns NULL if none is found.
 */
static block_t *find_fit(size_t asize)
{
    block_t *block;

    for (block = free_listp; block != NULL;
                             block = find_free_next(block))
    {
        if (asize <= get_size(block))
        {
            return block;
        }
    }
    return NULL; // no fit found
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
 */
static word_t pack(size_t size, bool alloc)
{
    return alloc ? (size | 1) : size;
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
    return asize - dsize;
}

/*
 * extract_alloc: returns the allocation status of a given header value based
 *                on the header specification above.
 */
static bool extract_alloc(word_t word)
{
    return (bool)(word & alloc_mask);
}

/*
 * get_alloc: returns true when the block is allocated based on the
 *            block header's lowest bit, and false otherwise.
 */
static bool get_alloc(block_t *block)
{
    return extract_alloc(block->header);
}

/*
 * write_header: given a block and its size and allocation status,
 *               writes an appropriate value to the block header.
 */
static void write_header(block_t *block, size_t size, bool alloc)
{
    block->header = pack(size, alloc);
}


/*
 * write_footer: given a block and its size and allocation status,
 *               writes an appropriate value to the block footer by first
 *               computing the position of the footer.
 */
static void write_footer(block_t *block, size_t size, bool alloc)
{
    word_t *footerp = (word_t *)((block->payload) + get_size(block) - dsize);
    *footerp = pack(size, alloc);
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
    word_t *footerp = find_prev_footer(block);
    size_t size = extract_size(*footerp);
    return (block_t *)((char *)block - size);
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

/* mm_checkheap: checks the heap for correctness; returns true if
 *               the heap is correct, and false otherwise.
 *               can call this function using mm_checkheap(__LINE__);
 *               to identify the line number of the call site.
 */
bool mm_checkheap(int verbose)  
{ 
    block_t *bp = heap_listp;
    /* Check prologue */
    /* Check if the first block's header's size or allocation bit is wrong. */
    if (get_size(heap_listp) != wsize || !get_alloc(heap_listp))
    {
        printf(" Error: Wrong prologue header.\n");
        return false;
    }
    /* Chenck the alignment and header-footer matching of each block. */
    for (bp = heap_listp; ((heap_listp->header) ^ 0x1) > 0; bp = find_next(bp))
    {
        check_block(bp);
        return false;
    }
    /* Check epilogue */
    if (bp->header != 0 || !get_alloc(bp))
    {
        printf(" Error: Wrong epilogue header.\n");
        return false;
    }
    return check_free_list(free_listp);
    
}
/* Remove block from free list*/
static void remove_free_block(block_t *block)
{
    block_t *block_prev = find_free_prev(block);
    block_t *block_next = find_free_next(block);
    /* If there is only one block */
    if ((block_prev == NULL) && (block_next == NULL))
    {
        free_listp = NULL;
        return;
    }
    if (block_prev == NULL)
    {
        set_prev(block_next, NULL);
        free_listp = block_next;
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
/* Insert the block to the first of the free list */
static void insert(block_t *block)
{
    if (free_listp == NULL) 
    {
        free_listp = block;
        //Set the predecessor pointer to NULL
        set_prev(block, NULL);
        //Set the successor pointer to NULL
        set_next(block, NULL);
        return;
    }
    set_prev(free_listp, block);
    set_next(block, free_listp);
    set_prev(block, NULL);
    free_listp = block;
    
}
static int find_index(size_t size) 
{
    if (size < 64)
    {
        return 0;
    }
    if (size < 128)
    {
        return 1;
    }
    if (size < 256)
    {
        return 2;
    }
    if (size < 512)
    {
        return 3;
    }
    if (size < 1024)
    {
        return 4;
    }
    if (size < 2048)
    {
        return 5;
    }
    if (size < 4096)
    {
        return 6;
    }
    if (size < 8192)
    {
        return 7;
    }
    if (size < 16382)
    {
        return 8;
    }
    if (size < 32764)
    {
        return 9;
    }
    if (size < 65536)
    {
        return 10;
    }
    if (size < 131072)
    {
        return 11;
    }
    if (size < 262144)
    {
        return 12;
    }
    // if (size < 524288)
    // {
    //     return 13;
    // }
    return 13;
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
static void set_prev(block_t *block, block_t *prev)
{
    *((word_t *)block + 1) = (word_t)prev;
}
static void set_next(block_t *block, block_t *next)
{
    *((word_t *)block + 2) = (word_t)next;
}
/* Check the address alignment and matching of the footer and header. */
static bool check_block(block_t *block)
{
    if (((word_t)(block)) % dsize)
    {
        printf("Error: block %p is not aligned correctly.\n", block);
        return false;
    }
    if (block->header != *find_footer(block))
    {
        printf("Error: header of block %p doesn't mathch footer.\n", block);
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
/* Check explicit free list */
static bool check_free_list(block_t *block)
{
    if ((void *)find_free_prev(block) < mem_heap_lo() 
                    || (void *)find_free_prev(block) > mem_heap_hi())
    {
        printf(" Error: previous pointer %p is out of boundary.", block);
        return false;
    }
    if ((void *)find_free_next(block) < mem_heap_lo() 
                    || (void *)find_free_prev(block) > mem_heap_hi())
    {
        printf(" Error: next pointer %p is out of boundary.", block);
        return false;
    }
    return true;
}
static word_t *find_footer(block_t *block)
{
    word_t *footerp = (word_t *)((block->payload) + get_size(block) - dsize);
    return footerp;
}