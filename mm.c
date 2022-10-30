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

// 가용 리스트 조작을 위한 기본 상수와 매크로
/* Basic constants and macros */
#define WSIZE 4             /* Word and header/footer size (bytes) */
#define DSIZE 8             /* Double word size (bytes) */
#define CHUNKSIZE (1 << 12) /* Extend heap by this amount (bytes)  초기 가용블록과 힙 확장을 위한 기본크기*/

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit into a word 가용리스트를 접근하고 방문하는 작은 매크로 */
#define PACK(size, alloc) ((size) | (alloc))    // pack 매크로 -> 크기와 할당비트를 통합해서 헤더와 풋터에 저장할 수 있는 값을 리턴
/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))   // get -> 파라미터 p가 참조하는 워드를 읽어 리턴
#define PUT(p, val) (*(unsigned int *)(p) = (val))  // put -> 파라미터 p가 가르키는 워드에 val 저장
/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7) // 주소 p에 있는 헤더 또는 풋터의 size와 할당 비트 리턴
#define GET_ALLOC(p) (GET(p) & 0x1)
/* Given block ptr bp, compute address of its header and footer */
// bp -> 블록 포인터
#define HDRP(bp) ((char *)(bp) - WSIZE) // header 가르킴
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // footer 가르킴
/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) // 다음 블록의 bp
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) // 이전 블록의 bp
/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
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


/*------------- 1. implicit -----------------------------------------------------*/

/*
 * coalesce -> 경계 태그 연결을 사용해서 상수 시간에 인접 가용 블록들과 통합
 * 완벽이해
*/
static void *coalesce(void *bp){
    // 1. PREV_BLKP(Bp)->이전 블록의 bp 리턴 -> 2. FTRP(bp) -> bp의 footer 가르킴 -> 3. GET_ALLOC(bp에있는 할당 비트(0, 1) 리턴)
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); 
    // 1. NEXT_BLKP(Bp)->다음 블록의 bp 리턴 -> 2. HDRP(bp) -> bp의 헤더 가르킴 -> 3. GET_ALLOC(bp에있는 할당 비트(0, 1) 리턴)
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));   // 헤더에 있는 size 불러옴 (블록 Size 가져옴)

    // case 1 
    // 현재 블록을 free했을때 이전과 다음 블록이 모두 할당되어있을때 -> 아무것도 안함
    if (prev_alloc && next_alloc){
        return bp;  // q1. 밑이랑 리팩토링 가능한 부분아닌가?
    }
    // case 2
    // 현재 블록을 free했을때 다음 블록이 가용상태라면 합쳐줌.
    else if (prev_alloc && !next_alloc){
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));  // 현재 블록의 사이즈 + 다음 블록의 사이즈
        // 현재 블록의 헤더와 푸터에 구해진 사이즈와 할당 비트 선언 
        PUT(HDRP(bp), PACK(size ,0));  
        PUT(FTRP(bp), PACK(size ,0));   // FTRP(bp) == FTRP(NEXT_BLKP(bp))
    }
    // case 3
    // 현재 블록을 free했을때 이전 블록이 가용상태라면 합쳐줌.
    else if (!prev_alloc && next_alloc){
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));  // 현재 블록의 사이즈 + 이전 블록의 사이즈
        // 이전 블록의 헤더와 현재 블록의 푸터에 구해진 사이즈와 할당 비트 선언
        PUT(FTRP(bp), PACK(size ,0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size ,0));
        bp = PREV_BLKP(bp); // 주소값 ->  이전 블록의 주소
    }
    
    // case 4
    // 현재 블록을 free했을때 이전, 다음 블록이 가용상태라면 합쳐줌.
    else {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))); // 현재 블록의 사이즈 + 이전 블록의 사이즈 + 다음 블록의 사이즈
        // 이전 블록의 헤더와 다음 블록의 푸터에 구해진 사이즈와 할당 비트 선언
        PUT(HDRP(PREV_BLKP(bp)), PACK(size ,0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size ,0));
        bp = PREV_BLKP(bp); // 주소값 ->  이전 블록의 주소
    }
    return bp;  
}

/* 
 * extend_heap - 새 가용 블록으로 힙 확장하기
   두가지 경우에 사용되는데
   1. 힙이 초기화 될때
   2. mm_malloc이 적당한 맞춤 fit을 찾기 못했을 때
*/
static void *extend_heap(size_t words){
    
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignmnet */
    /*   
    정렬을 유지하기 위해 요청한 크기를 인접 2워드의 배수(8byte)로 반올림하며, 
    그 후에 메모리 시스템으로 부터 추가적인 힙 공간을 요청한다.
   */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /* Initialize free block header/footer and the epilogue header*/
    // 힙은 더블워드 경계에서 시작하고, extend_heap으로 가는 모든 호출은 그 크기가 더블워드의 배수인 블록을 리턴
    PUT(HDRP(bp), PACK(size, 0));   // 가용 블록 헤더
    PUT(FTRP(bp), PACK(size, 0));   // 가용 블록 푸터
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));   // 새로운 에필로그 헤더

    /* Coalesce if the previous block was free*/
    // 이전 힙이 가용 블록으로 끝났다면, 두 개의 가용블록을 통합 -> 통합된 블록 포인터 리턴
    return coalesce(bp);

}

/* 
 * mm_init - initialize the malloc package.
 최소 가용 블록으로 힙 생성-> 할당기 초기화 완료하고, 할당과 반환 요청 받을 준비 완료
 */
int mm_init(void){
    /* Create the inital empty heap*/
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) // ???
        return -1;
    PUT(heap_listp, 0); // 초기 패딩
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); // 프롤로그 블록 헤더 (1, 할당했다.)
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); // 프롤로그 블록 푸터
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));  // 에필로그 블록 헤더
    heap_listp += (2 * WSIZE);   // 다음 주소값->프롤로그 푸터로 설정

    /* Extend the empty heap with a free block of CHUNKSIZE bytes*/
    // 힙을 CHUNKSIZE byte로 확장하고, 초기 가용 블록을 생성
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 * 가용 리스트에서 블록 할당하기.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendSize;
    char *bp;

    if (size == 0)
        return NULL;
    // 최소 16byte 크기의 블록을 구성-> 8byte는 정렬 요건을 만족 시키기 위해, 추가적인 8byte는 푸터,헤더
    // 할당려는 블록의 size가 8byte 이하일때 -> 최소 16byte (8(헤더,푸터)/ 8(size + 나머지(정렬요건 때문)))
    if (size <= DSIZE)
        asize = 2 * DSIZE;  // asize -> 16 byte
    // 할당려는 블록의 size가 8byte 초과 일때 -> 기본 요건인 8(헤더,푸터) + (size + 나머지)를 인접 8의 배수로 구성 
    // (ex-> size = 9, asize = 24)
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1) / DSIZE));
    
    // 할당기가 요청한 크기를 조정 후 적절한 가용 블록을 가용리스트에서 검색
    if ((bp = find_fit(asize)) != NULL){
        place(bp, asize);   // 옵션으로 초과부분 분할 
        return bp;  // 새롭게 할당한 블록 리턴
    }
    // 할당기가 맞는 블록을 찾지 못했을 때
    // 힙을 새로운 가용 블록으로 확장하고, 요청 블록을 새 가용블록에 배치
    extendSize = MAX(asize, CHUNKSIZE); // 최소 16byte 보장
    if ((bp = extend_heap(extendSize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);   // 옵션으로 초과부분 분할
    return bp;

}
/*
 * find_fit -> first fit
 */
static void *find_fit(size_t asize){
    /* First-fit search*/
    // malloc은 특정한 size의 크기로 메모리를 할당하고나서 우리들에게 알맞게 변환해서 써라 라는 의미로 void*를 내뱉게 됩니다.
    void *bp;
    // 힙의 처음 블록부터 끝까지 탐색
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))   {
        // 가용 블록이고, 할당하려는 Size가 현재 블록에 할당가능한 크기일 때
        if (!GET_ALLOC(HDRP(bp))) & (asize <= GET_SIZE(HDRP(bp)))   {
            return bp;
        }
    }
    return NULL;    //  no fit -> 넣을 수 있는 블록이 없음
}

/*
 * place -> 요청한 블록을 가용 블록의 시작 부분에 배치 하고, 나머지 부분의 크기가 최소 블록 크기와 같거나 큰 경우 분할
 */
static void place(void *bp, size_t asize){ /

    size_t csize = GET_SIZE(HDRP(bp));
    // 분할 후에 현재 블록의 나머지가 최소 블록 크기(16byte)와 같거나 크다면
    if ((csize - asize) >= (2 * DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * mm_free - Freeing a block does nothing.
 블록을 반환
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);

}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 * malloc으로 새로 할당 후 그 전에 있는 것은 프리해줌
 */
void *mm_realloc(void *bp, size_t size)
{
    void *oldptr = bp;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    // copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    copySize = GET_SIZE(HDRP(oldptr));  // ?
    if (size < copySize)
      copySize = size;
    // 메모리의 특정한 부분으로부터 얼마까지의 부분을 다른 메모리 영역으로 복사해주는 함수
    // oldptr로부터 copySize만큼의 문자를 newptr에 복사
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}














