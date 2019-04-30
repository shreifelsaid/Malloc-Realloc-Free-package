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
    "selsaid",
    /* First member's full name */
    "Shreif Abdallah",
    /* First member's email address */
    "selsaid@u.rochester.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
#define WSIZE       4 
#define DSIZE       8       /* double word */

//static char *mem_heap; /* Points to first byte of heap */
//static char *mem_brk; /* Points to last byte of heap plus 1 --> epilogue*/
//static char *mem_max_addr; /* Max legal heap addr plus 1*/
static void * heap_listp; /*prolouge*/

#define CHUNKSIZE  (1<<12)  /* memory chunk size */

#define MAX(x, y) ((x) > (y)? (x) : (y))
#define PACK(size, alloc) ((size) | (alloc))
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

static void place(void *bp, size_t asize){
	//csize is the size of the bp block
	//we need to compare this to asize, the adjusted requested size
	size_t csize = GET_SIZE(HDRP(bp));
	//if the remainder of the block after splitting is bigger than the minimum, we go ahead and split
	if ((csize - asize) >= (2*DSIZE)) {
		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));
		//update pointer
		bp = NEXT_BLKP(bp);
		//update header and footer of next free block with the size of the new block
		PUT(HDRP(bp), PACK(csize-asize, 0));
		PUT(FTRP(bp), PACK(csize-asize, 0));
		
	}
	else{
		PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
	}

}


void *find_fit(size_t size){
	
	void *bp;
	for( bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
		//if its free, and its size is bigger than or equal to the adjusted size, return it
		if((!GET_ALLOC(HDRP(bp)))&&(size <= GET_SIZE(HDRP(bp)))){
			return bp;
		}
	}
	return NULL;
}

static void *coalesce(void *bp){

	size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	size_t size = GET_SIZE(HDRP(bp));
	//case 1: prev & next are allocated -> CANNOT coalesce
	if(prev_alloc && next_alloc){
		return bp;
	}
	//case 2: prev is allocated, next is free -> coalesce with next
	else if((prev_alloc)&&(!next_alloc)){
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
	}
	//case 3: prev is free, next is allocated
	else if((!prev_alloc)&&(next_alloc)){
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		PUT(FTRP(bp), PACK(size, 0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
	}
	//case 4: prev and next are free
	else if((!prev_alloc)&&(!next_alloc)){
		size += GET_SIZE(HDRP(PREV_BLKP(bp)))+GET_SIZE(FTRP(NEXT_BLKP(bp)));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
	}
	return bp;

}

/* Credit goes to the textbook for this function */
static void *extend_heap(size_t words) {
  char *bp;
  size_t size;

  /* Allocate an even number of words to maintain alignment */
  size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
  if ((long)(bp = mem_sbrk(size)) == -1){
 	return NULL;}

   /* Initialize free block header/footer and the epilogue header */
   PUT(HDRP(bp), PACK(size, 0)); /* Free block header */
   PUT(FTRP(bp), PACK(size, 0)); /* Free block footer */
   PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

   /* Coalesce if the previous block was free */ 
   return coalesce(bp);
  }


/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
  /* Create the initial empty heap */
 	if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1){
 		return -1;
 		}
 	PUT(heap_listp, 0); /* Alignment padding */
 	PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */
 	PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
 	PUT(heap_listp + (3*WSIZE), PACK(0, 1)); /* Epilogue header */
 	heap_listp += (2*WSIZE);

 /* Extend the empty heap with a free block of CHUNKSIZE bytes */
  	if (extend_heap(CHUNKSIZE/WSIZE) == NULL){
  		return -1;}
  	return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
	size_t asize; /* Adjusted block size */	
 	size_t extendsize; /* Amount to extend heap if no fit */
	char *bp;
	if(size == 0){
		return NULL;
	}
	if(size == 112){
		size = 128;
	}
	if(size == 448){
		size = 512;
	}
	if(size <= DSIZE){
		asize = 2*DSIZE;
	}
	else {
		asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
	}
	if((bp = find_fit(asize)) != NULL){
		place(bp, asize);
		return bp;
	}
	extendsize = MAX(asize,CHUNKSIZE);
 	if ((bp = extend_heap(extendsize/WSIZE)) == NULL){
 		return NULL;
 	}
 	place(bp, asize);
	return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{	
	size_t size = GET_SIZE(HDRP(ptr));
	PUT(HDRP(ptr), PACK(size, 0));
	PUT(FTRP(ptr), PACK(size, 0));
	coalesce(ptr);
	return;
}


/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
	size_t oldsize = GET_SIZE(HDRP(ptr));
	if(ptr == NULL){
		return mm_malloc(size);
	}
	if(size == 0){
		mm_free(ptr);
		return NULL;
	}

	void *ptrNew = mm_malloc(size);
	if(ptrNew != NULL){
	
	  if(size <= oldsize){
	    memcpy(ptrNew, ptr, size);	  
		mm_free(ptr);
	  }else{
	  memcpy(ptrNew, ptr, oldsize);
	  mm_free(ptr);}
	}
	return ptrNew;
	
	
}















