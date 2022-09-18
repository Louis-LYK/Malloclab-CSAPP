#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>      
#include "explicit_mm.h"
#include "memlib.h"

team_t team = {
    /* Team name */
    "lyksegregated",
    /* First member's full name */
    "liuyikai",
    /* First member's email address */
    "lykfrancis@163.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};
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
#define SUCC_INDEX(bp) ((char *)(bp) + WSIZE)
#define PRED_INDEX(bp) ((char *)(bp))

static char* heap_listp;
static char* listp;
static void* coalesce(void*);
static void* add_list(void*);
static void* extend_heap(size_t);
static void  delete_blk_from_lst(void*);
static void* LIFO(void*, void*);
static int   get_index(size_t);
static void* find_fit(size_t);
static void* best_fit(size_t);
static void palce(void*, size_t);

int mm_init(void) {
    if((heap_listp = mem_sbrk(12 * WSIZE)) == (void*)-1) { return -1; }
    //这里划分出9条链表，用于保存9类不同大小的块:
    //1B     - 31B
    //32B   - 63B
    //64B   - 127B
    //128B  - 255B
    //256B  - 511B
    //512B  - 1023B
    //1024B - 2047B
    //2048B - 4095B
    //4096B - ...

    PUT(heap_listp + 0*WSIZE, NULL);
    PUT(heap_listp + 1*WSIZE, NULL);
    PUT(heap_listp + 2*WSIZE, NULL);
    PUT(heap_listp + 3*WSIZE, NULL);
    PUT(heap_listp + 4*WSIZE, NULL);
    PUT(heap_listp + 5*WSIZE, NULL);
    PUT(heap_listp + 6*WSIZE, NULL);
    PUT(heap_listp + 7*WSIZE, NULL);
    PUT(heap_listp + 8*WSIZE, NULL);
    
    PUT(heap_listp + 9*WSIZE, PACK(DSIZE, 1));
    PUT(heap_listp + 10*WSIZE, PACK(DSIZE, 1));
    PUT(heap_listp + 11*WSIZE, PACK(0, 1));
    listp = heap_listp;
    heap_listp += 9 * WSIZE;

    if(extend_heap(CHUNKSIZE/WSIZE) == NULL) { return -1; }
    return 0;
}

void* coalesce(void* bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    if(prev_alloc && next_alloc) { return bp; }
    else if(prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        delete_blk_from_lst(NEXT_BLKP(bp));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));                       
    }
    else if(!prev_alloc && next_alloc) {                         
        size += GET_SIZE(FTRP(PREV_BLKP(bp)));                          
        delete_blk_from_lst(PREV_BLKP(bp));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        bp = PREV_BLKP(bp);                          
    }
    else {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))) + GET_SIZE(FTRP(PREV_BLKP(bp)));                          
        delete_blk_from_lst(NEXT_BLKP(bp));
        delete_blk_from_lst(PREV_BLKP(bp));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}

static void delete_blk_from_lst(void* bp) {
    void* pred_bp = GET(PRED_INDEX(bp));
    void* succ_bp = GET(SUCC_INDEX(bp));
    
    size_t size  = GET_SIZE(HDRP(bp));
    int    index = get_index(size);
    void*  root  = listp + index * WSIZE;
    
    if(pred_bp == root) { PUT(root, succ_bp); }
    else { PUT(SUCC_INDEX(pred_bp), succ_bp); }

    if(succ_bp != NULL) {
        PUT(PRED_INDEX(succ_bp), pred_bp);
    }
}

static int get_index(size_t size) {
    int ind = 0;
    if(size >= CHUNKSIZE) { return 8; }

    size = size >> 5;
    while(size) {
        size = size >> 1;
        ind += 1;
    }
    return ind;
}

static void* add_list(void* bp) {
    size_t size = GET_SIZE(HDRP(bp));
    int   index = get_index(size);
    void*  root = listp + index * WSIZE;

    return LIFO(bp, root);
}

static void* LIFO(void* bp, void* root) {
    void* succ_root = GET(root);
    if(succ_root == NULL) { 
        PUT(root, bp); 
        PUT(PRED_INDEX(bp), root);
    }
    else {
        PUT(PRED_INDEX(GET(root)), bp);
        PUT(SUCC_INDEX(bp), GET(root));
        PUT(PRED_INDEX(bp), root);
        PUT(root, bp);
    }
    return bp;
}

static void* extend_heap(size_t words) {
    size_t size;
    void* bp;
    if(words == 0) { return NULL; }
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if((bp = mem_sbrk(size)) == (void*)-1) { return NULL; }
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));
    PUT(PRED_INDEX(bp), NULL);
    PUT(SUCC_INDEX(bp), NULL);
    
    bp = coalesce(bp);
    bp = add_list(bp);
    return bp;
}

static void* find_fit(size_t asize) {
    int ind = get_index(asize);
    void* bp;
    while(ind <= 8) {
        bp = GET(listp + ind * WSIZE);
        while(bp != NULL) {
            if(GET_SIZE(HDRP(bp)) >= asize) { return bp; }
            bp = GET(SUCC_INDEX(bp));
        }
        ind += 1;
    }
    return NULL;
}

static void* best_fit(size_t asize) {
    int ind = get_index(asize);
    void* bp;
    size_t min_size = SIZE_TMAX;
    void* best_p = NULL;

    while(ind <= 8) {
        bp = GET(listp + ind * WSIZE);
        while(bp != NULL) {
            size_t size = GET_SIZE(HDRP(bp));
            if((size >= asize) && (size - asize < min_size)) { 
                min_size = size - asize;
                best_p = bp;
                bp = GET(SUCC_INDEX(bp));
            }
            else { bp = GET(SUCC_INDEX(bp)); }
        }
        if(best_p == NULL) { ind += 1; }
        else { return best_p; }
    }
    return NULL;
}

static void place(void* bp, size_t asize) {
    size_t remain_size;
    remain_size = GET_SIZE(HDRP(bp)) - asize;
    delete_blk_from_lst(bp);
    if(remain_size >= DSIZE * 2) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        PUT(HDRP(NEXT_BLKP(bp)), PACK(remain_size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(remain_size, 0));
        add_list(NEXT_BLKP(bp));
    }
    else {
        PUT(HDRP(bp), PACK(GET_SIZE(HDRP(bp)), 1));
        PUT(FTRP(bp), PACK(GET_SIZE(HDRP(bp)), 1));
    }
}

void* mm_malloc(size_t size) {
    char* bp;
    size_t asize;
    size_t extendsize;
    if(size == 0) { return NULL; }
    else if(size <= 2 * DSIZE) { asize = 2 * DSIZE; }
    else { asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE); }
    if((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }
    else {
        extendsize = MAX(asize, CHUNKSIZE);
        if((bp = extend_heap(extendsize / WSIZE)) == NULL) { return NULL; }
        place(bp, asize);
        return bp;
    }
}

void mm_free(void* bp) {
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    bp = coalesce(bp);
    add_list(bp);
}

void *mm_realloc(void *ptr, size_t size) {
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize) { copySize = size; }
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}

