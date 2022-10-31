/* mm_explicit_LIFO.c

  가용 블록들을 연결리스트로 관리해서 모든 블록을 검사하지않고 가용 블록만 검사하는 방식
  Implicit의 next-fit방식과 성능이 유사함

*/    
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>
#include "mm.h"
#include "memlib.h"
// explicit add 
#include <sys/mman.h>
#include <errno.h>

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
/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8
/* rounds up to the nearest multiple of ALIGNMENT */
// ?
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
// 가용 리스트 조작을 위한 기본 상수와 매크로
/* Basic constants and macros */
#define WSIZE 4 // 워드 = 헤더 = 풋터 사이즈(bytes)
#define DSIZE 8 // 더블워드 사이즈(bytes)
#define CHUNKSIZE (1<<12) // heap을 이정도 늘린다(bytes) -> 최소 16바이트 ~ 최대 4G
#define MAX(x, y) ((x) > (y)? (x):(y))

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
// explicit add
#define PRED_FREEP(bp) (*(void**)(bp))  // 이전 가용 블록 주소
#define SUCC_FREEP(bp) (*(void**)(bp + WSIZE))  // 다음 가용 블록 주소

// global variable
static void *heap_listp = NULL; // heap 시작주소 pointer
static void *free_listp = NULL; // free list head - 가용리스트 시작부분

// function
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t adjustedSize);
static void place(void *bp, size_t adjustedSize);
static void removeBlock(void *bp);
static void putFreeBlock(void *bp);

/* 
 * mm_init - initialize the malloc package.
 최소 가용 블록으로 힙 생성-> 할당기 초기화 완료하고, 할당과 반환 요청 받을 준비 완료
 */
int mm_init(void){   // explicit add, implicit mem_sbrk(16)->emplicit mem_sbrk(24)
    heap_listp = mem_sbrk(24);// 24byte를 늘려주고, 함수의 시작부분을 가리키는 주소를 반환, mem_brk는 끝에 가있음
    if (heap_listp == (void *)- 1){
        return -1;
    }
    PUT(heap_listp, 0); //Unused padding
    PUT(heap_listp + WSIZE, PACK(16,1)); // 프롤로그 헤더 16/1
    PUT(heap_listp + 2 * WSIZE, NULL); // 프롤로그 PRED 포인터 NULL로 초기화
    PUT(heap_listp + 3 * WSIZE, NULL); // 프롤로그 SUCC 포인터 NULL로 초기화
    PUT(heap_listp + 4 * WSIZE, PACK(16,1)); // 프롤로그 풋터 16/1
    PUT(heap_listp + 5 * WSIZE, PACK(0,1)); // 에필로그 헤더 0/1

    free_listp = heap_listp + DSIZE; // free_listp를 PRED 포인터의 위치로 업데이트
    // Extend the empty heap with a free block of CHUNKSIZE bytes
    // 힙을 CHUNKSIZE byte로 확장하고, 초기 가용 블록을 생성
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) 
        return -1;
    return 0;
}
/*
 * coalesce -> 경계 태그 연결을 사용해서 인접 가용 블록들과 통합
 * 완벽이해
*/
static void *coalesce(void *bp){
    // 이전 블록의 할당 여부
    // 1. PREV_BLKP(Bp)->이전 블록의 bp 리턴 -> 2. FTRP(bp) -> bp의 footer 가르킴 -> 3. GET_ALLOC(bp에있는 할당 비트(0, 1) 리턴)
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); 
    // 다음 블록의 할당 여부
    // 1. NEXT_BLKP(Bp)->다음 블록의 bp 리턴 -> 2. HDRP(bp) -> bp의 헤더 가르킴 -> 3. GET_ALLOC(bp에있는 할당 비트(0, 1) 리턴)
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));   // bp의 블록 사이즈
    
    // explicit add
    // case 1
    // 현재 블록을 free했을때 이전과 다음 블록이 모두 할당되어있을때 -> 아무것도 안하고, freelist에 넣어줌
    if (prev_alloc && next_alloc){
        putFreeBlock(bp);
        return bp;
    }
    // case 2
    if(prev_alloc && !next_alloc){
        removeBlock(NEXT_BLKP(bp)); // @@@@ explicit에서 추가 @@@@
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size,0));
        PUT(FTRP(bp), PACK(size,0));//header가 바뀌었으니까 size도 바뀐다!
    }
    // case 3
    else if(!prev_alloc && next_alloc){
        removeBlock(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size,0));
        PUT(FTRP(bp), PACK(size,0));
        // PUT(FTRP(bp), PACK(size,0));  // @@@@ explicit에서 추가 @@@@ - 여기 다르긴함
        // PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
        // bp = PREV_BLKP(bp); //bp를 prev로 옮겨줌
    }
    // case 4
    else if(!prev_alloc && !next_alloc){
        removeBlock(PREV_BLKP(bp));
        removeBlock(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
                GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size,0));
        bp = PREV_BLKP(bp); //bp를 prev로 옮겨줌
    }
    putFreeBlock(bp); // 연결이 된 블록을 free list 에 추가
    return bp;
}

/*
 extend_heap은 두 가지 경우에 호출된다.
 1. heap이 초기화될 때 다음 블록을 CHUNKSIZE만큼 미리 할당해준다.
 2. mm_malloc이 적당한 맞춤(fit)을 찾지 못했을 때 CHUNKSIZE만큼 할당해준다.
                        - - -
 heap을 CHUNKSIZE byte로 확장하고 초기 가용 블록을 생성한다.
 여기까지 진행되면 할당기는 초기화를 완료하고, application으로부터
 할당과 반환 요청을 받을 준비를 완료하였다.
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
 * find_fit -> first fit
 * 완벽 이해
 */
static void *find_fit(size_t adjustedSize){
    void *bp;
    // explicit add
    // 가용리스트 내부의 유일한 할당블록인 프롤로그 블록을 만나면 종료
    for(bp = free_listp; GET_ALLOC(HDRP(bp)) != 1; bp = SUCC_FREEP(bp)){
        if(GET_SIZE(HDRP(bp)) >= adjustedSize){
            return bp;
        }
    }
    return NULL; // No fit -> 넣을 수 있는 블록이 없음
}

/*
 * place -> 요청한 블록을 가용 블록의 시작 부분에 배치 하고, 나머지 부분의 크기가 최소 블록 크기와 같거나 큰 경우 분할
 * 완벽이해
 */
static void place(void *bp, size_t adjustedSize){
    size_t nowBlockSize = GET_SIZE(HDRP(bp));  // 배치하려고하는 블록 size
    //할당 블록은 가용리스트에서 지운다
    removeBlock(bp);
    // 분할 후에 현재 블록의 나머지가 최소 블록 크기(16byte)와 같거나 크다면
    if ((nowBlockSize - adjustedSize) >= (2*DSIZE)){
        PUT(HDRP(bp), PACK(adjustedSize,1));//현재 크기를 헤더에 집어넣고
        PUT(FTRP(bp), PACK(adjustedSize,1));
        bp = NEXT_BLKP(bp);
        // 남은 블록에 header, footer 배치(가용 블록 생성)
        PUT(HDRP(bp), PACK(nowBlockSize - adjustedSize,0));
        PUT(FTRP(bp), PACK(nowBlockSize - adjustedSize,0));
        putFreeBlock(bp); // 가용리스트 첫번째에 분할된 블럭을 넣는다.
    }
    // nowBlockSize와 aszie 차이가 네 칸(16byte)보다 작다면 해당 블록 통째로 사용
    else{
        PUT(HDRP(bp), PACK(nowBlockSize, 1));
        PUT(FTRP(bp), PACK(nowBlockSize, 1));
    }
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 * 가용 리스트에서 블록 할당하기.
 * 완벽 이해
 */
void *mm_malloc(size_t size){
    size_t adjustedSize; //할당할 블록 사이즈
    size_t extendSize;
    void *bp; 

    // Ignore spurious requests - size가 0이면 할당x
    if(size <= 0) // == 대신 <=
        return NULL;
    
    // Adjust block size to include overhead and alignment reqs.
    // 최소 16byte 크기의 블록을 구성-> 8byte는 정렬 요건을 만족 시키기 위해, 추가적인 8byte는 푸터,헤더
    // 할당려는 블록의 size가 8byte 이하일때 -> 최소 16byte (8(헤더,푸터)/ 8(size + 나머지(정렬요건 때문)))
    // size가 8byte보다 작다면,
    if(size <= DSIZE) 
        adjustedSize = 2 * DSIZE; // 최소블록조건인 16byte로 맞춤
    // size가 8byte보다 크다면 인접한 8의 배수로
    // (ex-> size = 9, adjustedSize = 24)
    else              
        adjustedSize = DSIZE * ((size+(DSIZE)+(DSIZE-1)) / DSIZE);

    //Search the free list for a fit - 적절한 가용(free)블록을 가용리스트에서 검색
    if((bp = find_fit(adjustedSize))!=NULL){
        place(bp, adjustedSize); // 옵션으로 초과부분 분할 
        return bp;  // 새롭게 할당한 블록 포인터 리턴
    }

    //No fit found -> Get more memory and place the block
    // 할당기가 맞는 블록을 찾지 못했을 때
    // 힙을 새로운 가용 블록으로 확장하고, 요청 블록을 새 가용블록에 배치
    extendSize = MAX(adjustedSize,CHUNKSIZE);
    if((bp = extend_heap(extendSize/WSIZE)) == NULL)
        return NULL;
    place(bp,adjustedSize);
    return bp;
}

/*
  putFreeBlock -> LIFO 방식으로 새로 반환되거나 생성된 가용 블록을 가용리스트 맨 앞에 추가
  완벽이해
*/
void putFreeBlock(void *bp){
    SUCC_FREEP(bp) = free_listp;    // bp(새로 반환되거나 생성된 가용블록)의 다음 블록(successor)을 가용리스트의 첫번째로 선언
    PRED_FREEP(bp) = NULL;  // bp(새로 반환되거나 생성된 가용블록)의 이전 블록(predecessor)을 NULL 설정(첫번째이기 때문에)
    PRED_FREEP(free_listp) = bp;    //  free_listp(가용 리스트의 첫번째 블록)의 이전 블록(predecessor)을 bp(새로 반환되거나 생성된 가용블록)로 선언
    free_listp = bp;    // 가용 리스트의 첫번째 포인터 업데이트
}

/*
  removeBlock -> 가용 블록이 사용되었을때 가용 리스트를 연결
  완벽이해
*/
void removeBlock(void *bp){
    // 첫 번째 블록을 없앨 때
    // bp(삭제한 블록)의 다음 블록(successor)을 첫번째 블록으로 바꾸는 과정
    if(bp == free_listp){
        PRED_FREEP(SUCC_FREEP(bp)) = NULL;  
        free_listp = SUCC_FREEP(bp);
    // 두번째 이상 블록을 없앨 떄
    // bp(삭제한 블록)의 PRED 와 SUCC를 이어주는 과정
    }else{
        SUCC_FREEP(PRED_FREEP(bp)) = SUCC_FREEP(bp);
        PRED_FREEP(SUCC_FREEP(bp)) = PRED_FREEP(bp);
    }
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
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *bp, size_t size){
    if(size <= 0){ 
        mm_free(bp);
        return 0;
    }
    if(bp == NULL){
        return mm_malloc(size); 
    }
    void *newp = mm_malloc(size); 
    if(newp == NULL){
        return 0;
    }
    size_t oldsize = GET_SIZE(HDRP(bp));
    if(size < oldsize){
    	oldsize = size; 
	}
    // 메모리의 특정한 부분으로부터 얼마까지의 부분을 다른 메모리 영역으로
    // 복사해주는 함수(bp로부터 oldsize만큼의 문자를 newp로 복사해라)
    memcpy(newp, bp, oldsize); 
    mm_free(bp);
    return newp;
}
