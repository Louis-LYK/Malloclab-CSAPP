#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "explicit_mm.h"
#include "memlib.h"

team_t team = {
    /* Team name */
    "lyk-explicit",
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
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define MAX(x, y) ((x) > (y)? (x) : (y))  
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
#define PACK(size, alloc)  ((size) | (alloc)) //line:vm:mm:pack

#define GET(p)       (*(unsigned int*)(p))            //line:vm:mm:get
#define PUT(p, val)  (*(unsigned int*)(p) = (unsigned int)(val))    //line:vm:mm:put

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)                   //line:vm:mm:getsize
#define GET_ALLOC(p) (GET(p) & 0x1)                    //line:vm:mm:getalloc

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)                      //line:vm:mm:hdrp
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) //line:vm:mm:ftrp

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) 
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) 

#define SUCC_INDEX(bp) ((char *)(bp) + WSIZE)
#define PRED_INDEX(bp) ((char *)(bp))

static char* heap_listp;
static void* extend_heap(size_t words);
static void* coalesce(void* bp);
static void place(void* bp, size_t asize);
static void* find_fit(size_t asize);
static void* best_fit(size_t asize);
static void* addlist(void* bp);


int mm_init(void) {
    if((heap_listp = mem_sbrk(6 * WSIZE)) == (void*)-1) { return -1; }
    PUT(heap_listp, 0);
    PUT(heap_listp + (1*WSIZE), PACK(2 * DSIZE, 1));
    PUT(heap_listp + (2*WSIZE), NULL);
    PUT(heap_listp + (3*WSIZE), NULL);
    PUT(heap_listp + (4*WSIZE), PACK(2 * DSIZE, 1));
    PUT(heap_listp + (5*WSIZE), PACK(0, 1));

    heap_listp += (2 * WSIZE);
    if(extend_heap(CHUNKSIZE / WSIZE) == NULL) { return -1; }
    return 0;
}

static void* extend_heap(size_t words) {
    char* bp;
    size_t asize;
    if(words == 0) { return NULL; }
    asize = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;  
    if(asize < 2 * DSIZE) { asize = 2 * DSIZE; }
    if((long)(bp = mem_sbrk(asize)) == (void*)-1) { return NULL; }
    
    PUT(HDRP(bp), PACK(asize, 0));
    PUT(FTRP(bp), PACK(asize, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));
    return coalesce(bp);
}

static void* addlist(void* bp) {
    PUT(PRED_INDEX(bp), heap_listp);
    PUT(SUCC_INDEX(bp), GET(SUCC_INDEX(heap_listp)));
    unsigned int succ_addr = GET(SUCC_INDEX(heap_listp));
    if(succ_addr != NULL) { 
        PUT(PRED_INDEX(succ_addr), bp);
    }
    PUT(SUCC_INDEX(heap_listp), bp);
    return bp;
}

static void* coalesce(void* bp) {
    size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(bp)));
    size_t succ_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    
    if(prev_alloc && succ_alloc) {
        PUT(SUCC_INDEX(bp), NULL);
        PUT(PRED_INDEX(bp), NULL);
    }
    else if(prev_alloc && !succ_alloc) {   //物理后继块是空闲的
        void* next_bp = NEXT_BLKP(bp);
        size += GET_SIZE(HDRP(next_bp));
        
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));

        PUT(SUCC_INDEX(GET(PRED_INDEX(next_bp))), GET(SUCC_INDEX(next_bp)));
        if(GET(SUCC_INDEX(next_bp)) != NULL) {
            PUT(PRED_INDEX(GET(SUCC_INDEX(next_bp))), GET(PRED_INDEX(next_bp)));
        }
        PUT(SUCC_INDEX(bp), NULL);
        PUT(PRED_INDEX(bp), NULL);
    }

    else if(!prev_alloc && succ_alloc) {    //物理前驱块是空闲的
        void* prev_bp = PREV_BLKP(bp);
        size += GET_SIZE(HDRP(prev_bp));
        
        PUT(HDRP(prev_bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        
        PUT(SUCC_INDEX(GET(PRED_INDEX(prev_bp))), GET(SUCC_INDEX(prev_bp)));
        if(GET(SUCC_INDEX(prev_bp)) != NULL) {
            PUT(PRED_INDEX(GET(SUCC_INDEX(prev_bp))), GET(PRED_INDEX(prev_bp)));
        }
        bp = prev_bp;
        PUT(PRED_INDEX(bp), NULL);
        PUT(SUCC_INDEX(bp), NULL);
    }

    else if(!prev_alloc && !succ_alloc) {    //两边块都空闲
        void* prev_bp = PREV_BLKP(bp);
        void* next_bp = NEXT_BLKP(bp);
        size += GET_SIZE(HDRP(prev_bp)) + GET_SIZE(HDRP(next_bp));
        PUT(HDRP(prev_bp), PACK(size, 0));
        PUT(FTRP(next_bp), PACK(size, 0));
        
        PUT(SUCC_INDEX(GET(PRED_INDEX(prev_bp))), GET(SUCC_INDEX(prev_bp)));
        if(GET(SUCC_INDEX(prev_bp)) != NULL) {
            PUT(PRED_INDEX(GET(SUCC_INDEX(prev_bp))), GET(PRED_INDEX(prev_bp)));
        }
        
        PUT(SUCC_INDEX(GET(PRED_INDEX(next_bp))), GET(SUCC_INDEX(next_bp)));
        if(GET(SUCC_INDEX(next_bp)) != NULL) {
            PUT(PRED_INDEX(GET(SUCC_INDEX(next_bp))), GET(PRED_INDEX(next_bp)));
        }
        bp = prev_bp;
        PUT(PRED_INDEX(bp), NULL);
        PUT(SUCC_INDEX(bp), NULL);
    }
    return addlist(bp);
    //return bp;
}

static void* find_fit(size_t asize) {
    void* bp;
    for(bp = heap_listp; bp; bp = GET(SUCC_INDEX(bp))) {
        if(!GET_ALLOC(HDRP(bp)) && (GET_SIZE(HDRP(bp)) >= asize)) { return bp; }
    }
    
    return NULL;
}

static void* best_fit(size_t asize) {
    void* bp;
    size_t size;
    void* best_bp = NULL;
    size_t min_size = SIZE_TMAX;
    for(bp = heap_listp; bp; bp = GET(SUCC_INDEX(bp))) {
        size = GET_SIZE(HDRP(bp));
        if((size >= asize) && (size < min_size)) { best_bp = bp; }
    }
    return best_bp; 
}

static void place(void* bp, size_t asize) {
    size_t size = GET_SIZE(HDRP(bp));
    if(size - asize >= 2 * DSIZE) {
        char* another_bp;
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        another_bp = NEXT_BLKP(bp);
        PUT(HDRP(another_bp), PACK(size - asize, 0));
        PUT(FTRP(another_bp), PACK(size - asize, 0));
        
        PUT(PRED_INDEX(another_bp), GET(PRED_INDEX(bp)));
        PUT(SUCC_INDEX(another_bp), GET(SUCC_INDEX(bp)));
        PUT(SUCC_INDEX(GET(PRED_INDEX(bp))), another_bp);
        if(GET(SUCC_INDEX(bp)) != NULL) {
            PUT(PRED_INDEX(GET(SUCC_INDEX(bp))), another_bp);
        }
    }
    else {
        if(GET(SUCC_INDEX(bp)) != NULL) {
            PUT(PRED_INDEX(GET(SUCC_INDEX(bp))), GET(PRED_INDEX(bp)));
        }
        PUT(SUCC_INDEX(GET(PRED_INDEX(bp))), GET(SUCC_INDEX(bp)));
        PUT(HDRP(bp), PACK(size, 1));
        PUT(FTRP(bp), PACK(size, 1));
    }
}

void* mm_malloc(size_t size) {
    char* bp;
    size_t extend_size;
    size_t asize;
    if(size == 0) { return NULL; }
    else if(size < DSIZE) { asize = 2 * DSIZE; }
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
    
    extend_size = MAX(asize, CHUNKSIZE);
    if((bp = extend_heap(extend_size / WSIZE)) == NULL) { return NULL; }
    place(bp, asize);
    return bp;
}

void mm_free(void* bp) {
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    
    coalesce(bp);
}

void *mm_realloc(void *ptr, size_t size) {
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

