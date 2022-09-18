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

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "lykteam",
    /* First member's full name */
    "liuyikai",
    /* First member's email address */
    "lykfrancis@163.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8
#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1<<12)
#define SIZE_TMAX 65535

/* rounds up to the nearest multiple of ALIGNMENT */

#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define PACK(size, alloc) ((size) | (alloc))

#define GET(p) (*(unsigned int*)(p))
#define PUT(p, val)(*(unsigned int*)(p) = (unsigned int)(val))

#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HDRP(bp) ((char*)(bp) - WSIZE)
#define FTRP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp) ((char*)(bp) - GET_SIZE((char*)(bp) - DSIZE))

#define MAX(x,y) ((x) > (y) ? (x):(y)) 
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

static void* extend_heap(size_t words);
static void place(void* bp, size_t asize);
static void* find_fit(size_t asize);
static void* best_fit(size_t asize);
static void* coalesce(void* bp);
static void printblock(void* bp);
static void checkblock(void* bp); 
static char* heap_listp;

static unsigned int list;
static int64_t t;
static void* head = &list;
static void* tail = &t;

int mm_init(void)
{
    if((heap_listp = mem_sbrk(4 * WSIZE)) == (void*)-1) { return -1; }
    PUT(heap_listp, 0);                            //填充块
    PUT(heap_listp + 1 * WSIZE, PACK(DSIZE, 1));   //序言块头部
    PUT(heap_listp + 2 * WSIZE, PACK(DSIZE, 1));   //序言块脚部
    PUT(heap_listp + 3 * WSIZE, PACK(0, 1));       //结尾块
    heap_listp += DSIZE; //heap_listp指针指向序言块脚部
    if(extend_heap(CHUNKSIZE/WSIZE) == NULL) { return -1; }
    return 0;
}

static void* extend_heap(size_t words) {
    char* bp;
    size_t size;
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if((bp = mem_sbrk(size)) == (void*)-1) { return NULL; }

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));
    return coalesce(bp);
}

static void* coalesce(void* bp) {
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(bp)));        
    size_t size       = GET_SIZE(HDRP(bp));

    if(next_alloc && prev_alloc) { return bp; }
    
    else if(next_alloc && !prev_alloc) {
        size = size + GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    
    else if(!next_alloc && prev_alloc) {
        size = size + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    
    else {
        size = size + GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */

void *mm_malloc(size_t size) {
    size_t asize;
    size_t extendsize;
    char* bp;
    if(size == 0) { return NULL; }
    else if(size <= DSIZE) { asize = 2 * DSIZE; }
    else { asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE); }

   /*
    if((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }
    */

    if((bp = best_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }
    extendsize = MAX(asize, CHUNKSIZE);
    if((bp = extend_heap(extendsize / WSIZE)) == NULL) { return NULL; }
    place(bp, asize);
    return bp;
}

static void* find_fit(size_t asize) {
    char* bp = heap_listp;
    for(; GET_SIZE(HDRP(bp)) != 0; bp = NEXT_BLKP(bp)) {
        if((GET_SIZE(HDRP(bp)) >= asize) && (GET_ALLOC(HDRP(bp)) == 0)) {
            return bp;
        }
    }
    return NULL;
}

static void place(void* bp, size_t asize) {
    size_t size = GET_SIZE(HDRP(bp));
    if((size - asize) >= 2 * DSIZE) { 
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(size - asize, 0));
        PUT(FTRP(bp), PACK(size - asize, 0));
    }
    else {
        PUT(HDRP(bp), PACK(size, 1));
        PUT(FTRP(bp), PACK(size, 1));
    }
}

static void* best_fit(size_t asize) {
    char* bp = heap_listp;
    char* best_p = NULL;
    size_t record = SIZE_TMAX;
    for(; GET_SIZE(HDRP(bp)) != 0; bp = NEXT_BLKP(bp)) {
        if((GET_SIZE(HDRP(bp)) >= asize) && (GET_ALLOC(HDRP(bp)) == 0) && (asize < record)) {
            record = asize;
            best_p = bp;
        }
    }
    if(best_p == NULL) { return NULL; }
    return best_p;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr) {
    size_t size = GET_SIZE(HDRP(ptr));
    if((GET_ALLOC(HDRP(ptr)) != 0) && (GET_SIZE(HDRP(ptr)) != 0)) {
        PUT(HDRP(ptr), PACK(size, 0));
        PUT(FTRP(ptr), PACK(size, 0));
        coalesce(ptr);
    }
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

