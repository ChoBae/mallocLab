// mm_implicit_nextfit.c
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
    "team 3",
    /* First member's full name */
    "Chobae",
    /* First member's email address */
    "tmsprqo@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

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



// Declaration
// global variable
static void *heap_listp;
static void *last_bp;   // next fit을 위한 이전 bp 저장
// function
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *next_fit(size_t adjustedSize);
static void place(void *bp, size_t adjustedSize);

/* 
 * mm_init - initialize the malloc package.
 최소 가용 블록으로 힙 생성-> 할당기 초기화 완료하고, 할당과 반환 요청 받을 준비 완료
 */
int mm_init(void){
    /* Create the inital empty heap*/
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *) - 1) // ???
        return -1;
    PUT(heap_listp, 0); // 초기 패딩
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); // 프롤로그 블록 헤더 (1, 할당했다.)
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); // 프롤로그 블록 푸터
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));  // 에필로그 블록 헤더
    heap_listp += (2 * WSIZE);   // 다음 주소값->프롤로그 푸터로 설정

    /* Extend the empty heap with a free block of CHUNKSIZE bytes*/
    // 힙을 CHUNKSIZE byte로 확장하고, 초기 가용 블록을 생성
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    last_bp = (char *)heap_listp;   // heap_listp는 void였기 때문에 last_bp에 맞게 char형으로 변환 ok
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 * Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size) {
    size_t adjustedSize;       // adjusted block szie
    size_t extendSize;         // Amount to extend heap if no fit
    char *bp;

    // Ignore spurious requests
    if (size == 0) {
        return NULL;
    }

    // Adjust block size to include overhead and alignment reqs
    if (size <= DSIZE) {    // 2 words 이하의 사이즈는 4워드로 할당 요청 (header 1word, footer 1word)
        adjustedSize = 2 * DSIZE;
    }
    else {                  // 할당 요청의 용량이 2words 초과 시, 충분한 8byte의 배수의 용량 할당
        adjustedSize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
    }

    // Search the free list for a fit
    if ((bp = next_fit(adjustedSize)) != NULL) {   // 적당한 크기의 가용 블록 검색
        place(bp, adjustedSize);                   // 초과 부분을 분할하고 새롭게 할당한 블록의 포인터 반환
        last_bp = bp;
        return bp;
    }

    // NO fit found. Get more memory and place the block
    extendSize = MAX(adjustedSize, CHUNKSIZE);
    if ((bp = extend_heap(extendSize/WSIZE)) == NULL) {    // 칸의 개수
        return NULL;
    }
    place(bp, adjustedSize);
    last_bp = bp;
    return bp;
}

/* 
   적당한 크기의 가용블록 검색. 
   이 때, next_fit 방법을 이용(최근에 할당된 블록을 기준으로 다음 블록 검색)
   완벽 이해
*/
static void *next_fit(size_t adjustedSize) {
    char *bp = last_bp;

    for (bp = NEXT_BLKP(bp); GET_SIZE(HDRP(bp)) != 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= adjustedSize) {
            last_bp = bp;
            return bp;
        }
    }
    // 왜 또하지 -> 끝까지 갔을때 가용 블록이 없으면 다시 처음부터 last_bp전까지 탐색
    bp = heap_listp;
    while (bp < last_bp) {
        bp = NEXT_BLKP(bp);
        if (!GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= adjustedSize) {
            last_bp = bp;
            return bp;
        }
    }

    return NULL;
}

/*
 * mm_free - Freeing a block does nothing.
  블록을 반환
  완벽이해
 */
void mm_free(void *bp){
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);

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
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
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
        last_bp = bp;   // 이전 bp 업데이트
        return bp;  
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
    last_bp = bp;   // 이전 bp 업데이트
    return bp;  
}

/*
 * place -> 요청한 블록을 가용 블록의 시작 부분에 배치 하고, 나머지 부분의 크기가 최소 블록 크기와 같거나 큰 경우 분할
 * 완벽이해
 */
static void place(void *bp, size_t adjustedSize){ 

    size_t nowBlockSize = GET_SIZE(HDRP(bp));  // 배치하려고하는 블록 size
    // 분할 후에 현재 블록의 나머지가 최소 블록 크기(16byte)와 같거나 크다면
    if ((nowBlockSize - adjustedSize) >= (2 * DSIZE)) {
        PUT(HDRP(bp), PACK(adjustedSize, 1));
        PUT(FTRP(bp), PACK(adjustedSize, 1));
        bp = NEXT_BLKP(bp);
        // 남은 블록에 header, footer 배치(가용 블록 생성)
        PUT(HDRP(bp), PACK(nowBlockSize - adjustedSize, 0));
        PUT(FTRP(bp), PACK(nowBlockSize - adjustedSize, 0));
    }
    // nowBlockSize와 aszie 차이가 네 칸(16byte)보다 작다면 해당 블록 통째로 사용
    else {
        PUT(HDRP(bp), PACK(nowBlockSize, 1));
        PUT(FTRP(bp), PACK(nowBlockSize, 1));
    }
}
/*
   기존에 malloc으로 동적 할당된 메모리 크기를 변경시켜주는 함수
   현재 메모리에 bp가 가르키는 사이즈를 할당한 만큼 충분하지 않다면 메모리의 다른 공간의 기존 크기의 공간 할당 + 기존에 있던 데이터를 복사한 후 추가로 메모리 할당
*/
void *mm_realloc(void *bp, size_t size) {
    size_t old_size = GET_SIZE(HDRP(bp));
    size_t new_size = size + (2 * WSIZE);   // 2*WISE는 헤더와 풋터

    // new_size가 old_size보다 작거나 같으면 기존 bp 그대로 사용
    if (new_size <= old_size) {
        return bp;
    }
    // new_size가 old_size보다 크면 사이즈 변경
    else {
        size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
        size_t current_size = old_size + GET_SIZE(HDRP(NEXT_BLKP(bp)));

        // next block이 가용상태이고 old, next block의 사이즈 합이 new_size보다 크면 그냥 그거 바로 합쳐서 쓰기
        if (!next_alloc && current_size >= new_size) {
            PUT(HDRP(bp), PACK(current_size, 1));
            PUT(FTRP(bp), PACK(current_size, 1));
            return bp;
        }
        // 아니면 새로 block 만들어서 거기로 옮기기
        else {
            void *new_bp = mm_malloc(new_size);
            place(new_bp, new_size);
            memcpy(new_bp, bp, new_size);  // 메모리의 특정한 부분으로부터 얼마까지의 부분을 다른 메모리 영역으로 복사해주는 함수(old_bp로부터 new_size만큼의 문자를 new_bp로 복사해라!)
            mm_free(bp);
            return new_bp;
        }
    }
}