#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

team_t team = {
    /* Team name */
    "10조",
    /* First member's full name */
    "강민규",
    /* First member's email address */
    "stkang9409@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

#define ALIGN(size) (((size) + 0x7) & ~0x7)

#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define MIN(x, y) ((x) < (y) ? (x) : (y))
#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE 1 << 12

#define GET(bp) (*(unsigned int *)(bp))
#define PUT(bp, val) (GET(bp) = (val))

#define PACK(size, alloc) ((size) | (alloc))
#define GET_SIZE(bp) (GET(bp) & ~0x7)
#define GET_ALLOC(bp) (GET(bp) & 0x1)

#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP((char *)(bp))) - DSIZE)

#define NEXT(bp) ((char *)(FTRP((char *)bp) + DSIZE))
#define PREV(bp) ((char *)((char *)(bp)-GET_SIZE((char *)(bp)-DSIZE)))

static char *heap_listp;
static char *last_free;

void *coalesce(void *bp)
{
    size_t next_a = GET_ALLOC(HDRP(NEXT(bp)));
    size_t prev_a = GET_ALLOC(HDRP(PREV(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (next_a && prev_a)
    {
        last_free = bp;
        return bp;
    }
    else if (!next_a && prev_a)
    {
        size += GET_SIZE(HDRP(NEXT(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (next_a && !prev_a)
    {
        size += GET_SIZE(HDRP(PREV(bp)));
        PUT(HDRP(PREV(bp)), PACK(size, 0));
        PUT(FTRP(PREV(bp)), PACK(size, 0));
        bp = PREV(bp);
    }
    else
    {
        size += GET_SIZE(HDRP(PREV(bp))) + GET_SIZE(HDRP(NEXT(bp)));
        PUT(HDRP(PREV(bp)), PACK(size, 0));
        PUT(FTRP(PREV(bp)), PACK(size, 0));
        bp = PREV(bp);
    }
    last_free = bp;
    return bp;
}

void *extend_heap(size_t size)
{
    void *bp;

    size_t asize = ALIGN(size * WSIZE);

    if ((bp = mem_sbrk(asize)) == NULL)
    {
        return NULL;
    }

    PUT(HDRP(bp), PACK(asize, 0));
    PUT(FTRP(bp), PACK(asize, 0));
    PUT(HDRP(NEXT(bp)), PACK(0, 1));

    return coalesce(bp);
}

void *find_fit(size_t size)
{
    void *bp = last_free;

    while (GET_SIZE(HDRP(bp)) != 0)
    {
        if (GET_SIZE(HDRP(bp)) >= size && !GET_ALLOC(HDRP(bp)))
        {
            return bp;
        }
        bp = NEXT(bp);
    }
    return NULL;
}

void place(void *bp, size_t asize)
{
    size_t remainder = GET_SIZE(HDRP(bp)) - asize;

    if (remainder >= 2 * DSIZE)
    {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        PUT(HDRP(NEXT(bp)), PACK(remainder, 0));
        PUT(FTRP(NEXT(bp)), PACK(remainder, 0));
        last_free = NEXT(bp);
    }
    else
    {
        PUT(HDRP(bp), PACK(GET_SIZE(HDRP(bp)), 1));
        PUT(FTRP(bp), PACK(GET_SIZE(HDRP(bp)), 1));
    }
}

int mm_init()
{
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == -1)
    {
        return -1;
    }

    PUT(heap_listp + 0 * WSIZE, 0);
    PUT(heap_listp + 1 * WSIZE, PACK(DSIZE, 1));
    PUT(heap_listp + 2 * WSIZE, PACK(DSIZE, 1));
    PUT(heap_listp + 3 * WSIZE, PACK(0, 1));

    heap_listp += 2 * WSIZE;

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
    {
        return -1;
    }

    return 0;
}

void *mm_malloc(size_t size)
{
    void *bp;
    size_t asize;
    size_t extend_size;

    if (size == 0)
        return NULL;

    if (size < DSIZE)
        asize = DSIZE * 2;
    else
        asize = ALIGN(size + DSIZE);

    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp;
    }

    extend_size = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extend_size / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);

    return bp;
}

void mm_free(void *bp)
{
    PUT(HDRP(bp), PACK(GET_SIZE(HDRP(bp)), 0));
    PUT(FTRP(bp), PACK(GET_SIZE(HDRP(bp)), 0));
    coalesce(bp);
}

void *mm_realloc(void *ptr, size_t size)
{
    void *new_ptr = ptr; /* Pointer to be returned */
    void *bp;
    size_t new_size = size; /* Size of new block */
    int remainder;          /* Adequacy of block sizes */
    int extendsize;         /* Size of heap extension */
    int block_buffer;       /* Size of block buffer */

    /* Ignore invalid block size */
    if (size == 0)
        return NULL;

    /* Adjust block size to include boundary tag and alignment requirements */
    if (new_size <= DSIZE)
    {
        new_size = 2 * DSIZE;
    }
    else
    {
        new_size = ALIGN(size + DSIZE);
    }

    /* Calculate block buffer */
    block_buffer = GET_SIZE(HDRP(ptr)) - new_size; //얼마나 더 큰가? 플러스면 작은거, 마이너스면 큰거

    /* Allocate more space if overhead falls below the minimum */
    if (block_buffer < 0) //늘리고싶다.
    {
        if (!GET_ALLOC(HDRP(NEXT(ptr))))
        {
            remainder = GET_SIZE(HDRP(ptr)) + GET_SIZE(HDRP(NEXT(ptr))) - new_size;
            if (remainder >= 0)
            {
                PUT(HDRP(ptr), PACK(new_size + remainder, 1));
                PUT(FTRP(ptr), PACK(new_size + remainder, 1));
            }
        }
        else if (!GET_SIZE(HDRP(NEXT(ptr))))
        {
            remainder = GET_SIZE(HDRP(ptr)) - new_size;

            extendsize = MAX(-remainder, CHUNKSIZE);

            if ((long)(bp = mem_sbrk(extendsize)) == -1)
            {
                return NULL;
            }
            PUT(HDRP(bp), PACK(extendsize, 0));
            PUT(FTRP(bp), PACK(extendsize, 0));
            PUT(HDRP(NEXT(bp)), PACK(0, 1));

            PUT(HDRP(ptr), PACK(GET_SIZE(HDRP(ptr)) + extendsize, 0));
            PUT(FTRP(ptr), PACK(GET_SIZE(HDRP(ptr)), 0));

            PUT(HDRP(ptr), PACK(GET_SIZE(HDRP(ptr)), 1));
            PUT(FTRP(ptr), PACK(GET_SIZE(HDRP(ptr)), 1));
        }
        else
        {
            new_ptr = mm_malloc(new_size - DSIZE);
            memcpy(new_ptr, ptr, MIN(size, new_size));
            mm_free(ptr);
        }
    }

    /* Tag the next block if block overhead drops below twice the overhead */
    // if (block_buffer < 4 * REALLOC_BUFFER)
    //     SET_RATAG(HDRP(NEXT_BLKP(new_ptr)));

    /* Return the reallocated block */
    return new_ptr;
}