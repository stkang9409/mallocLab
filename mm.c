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
    "team2",
    /* First member's full name */
    "Tongky",
    /* First member's email address */
    "chotjd329@gmail.com",
    /* Second member's full name (leave blank if none) */
    "Micky",
    /* Third member's full name (leave blank if none) */
    "Johny"};
/*------------------------------------------------------------------------------------------------------------------------------------------------------*/
#define WSIZE 4                                                       // [bytes] word, header, footer size
#define DSIZE 8                                                       // [bytes] double word size
#define CHUNKSIZE (1 << 12)                                           // [bytes] extend heap by this amount 하나의 페이지는 4[kb]
#define MAX(x, y) ((x) > (y) ? (x) : (y))                             // max 값 반환
#define PACK(size, alloc) ((size) | (alloc))                          // size 뒤의 000 공간에 allocation 여부를 저장한 비트를 반환
#define GET(p) (*(unsigned int *)(p))                                 // 주소값에서 값 읽어옴
#define PUT(p, val) (*(unsigned int *)(p) = (val))                    // 주소값에다 값 씀
#define GET_SIZE(p) (GET(p) & ~0x7)                                   // 블록 사이즈 읽어옴
#define GET_ALLOC(p) (GET(p) & 0x1)                                   // 할당 여부를 읽어옴 \
                                                                      //bp = block pointer
#define HDRP(bp) ((char *)(bp)-WSIZE)                                 // 헤더의 주소값을 반환
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)          // 푸터의 주소값을 반환, 헤더에서 사이즈를 안 다음 double word를 빼줌. \
                                                                      //blkp = block pointer
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE))) // 다음 블록의 주소값을 반환, 헤더에서 내 사이즈 더해주고 word를 빼줌.
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))   // 전 블록의 주소값을 반환, 헤더에서 double word를 빼고 전 블록의 사이즈를 알아낸다.
#define GET_P(p) ((char *)*(unsigned int *)(p))                       //
#define PUT_P(p, val) (*(unsigned int *)(p) = (int)(val))             //
#define NEXTRP(bp) ((char *)(bp) + WSIZE)                             // 다음 free를 담는 주소값
#define PREVRP(bp) ((char *)(bp))                                     // 이전 free를 담는 주소값
#define NEXT_FREE_BLKP(bp) (GET_P((char *)(bp) + WSIZE))              // 다음 FREE BLOCK POINTER
#define PREV_FREE_BLKP(bp) (GET_P((char *)(bp)))                      // 이전 FREE BLOCK POINTER
#define CHANGE_PREV(bp, val) (PUT_P(PREVRP(bp), val));
#define CHANGE_NEXT(bp, val) (PUT_P(NEXTRP(bp), val));

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void printlist(void);
static void cut_link(void *bp);
static void push_first(void *bp);
static char *heap_listp; // heap의 첫 번째 pointer-------------------------------------------------------
static char *seg_listp;  // heap의 첫 번째 pointer-------------------------------------------------------
static void seg_init(void);
static void seg_find(int size);
void seg_print(void);

void seg_print(void)
{
    if ((seg_listp = mem_sbrk(32 * WSIZE)) == (void *)-1)
        return;
    for (int i = 0; i < 32; i++)
    {
        printf("%d. %p\n", i, seg_listp + (i * WSIZE));
    }
}

void seg_init(void)
{
    if ((seg_listp = mem_sbrk(32 * WSIZE)) == (void *)-1)
        return;
    for (int i = 0; i < 32; i++)
    {
        PUT_P(seg_listp + (i * WSIZE), NULL);
    }
    seg_print();
}

void seg_find(int size)
{
    int i = 0;
    for (i = 32; i > 0; i--)
    {
        printf("%d  %d\n", i, (size & (1 << (i + 1))));
        if ((size & (1 << (i + 1))) > 0)
        {
            break;
        }
    }
    heap_listp = seg_listp + (i * WSIZE);
    printf("changed heap to %d: %p\n", i, heap_listp);
}

int mm_init(void) // 메모리 처음 만들기
{
    if ((heap_listp = mem_sbrk(6 * WSIZE)) == (void *)-1)
        return -1;                                     // mem_sbrk 호출해서 4W 메모리 request하는 데, 실패 하면 -1 리턴
    PUT(heap_listp, 0);                                // heap:0에  free 넣음 (Alignment padding)
    PUT(heap_listp + (1 * WSIZE), PACK(2 * DSIZE, 1)); // heap:1에  DSIZE와 allocated 넣음 (PROLOGUE HEADER)
    PUT_P(heap_listp + (2 * WSIZE), NULL);             // heap:2 previous free block pointer 는 null
    PUT_P(heap_listp + (3 * WSIZE), NULL);             // heap:3 next free block pointer 는 null
    PUT(heap_listp + (4 * WSIZE), PACK(2 * DSIZE, 1)); // heap:4에  DSIZE와 allocated 넣음 (PROLOGUE PUTTER)
    PUT(heap_listp + (5 * WSIZE), PACK(0, 1));         // heap:5에  allocated 넣음 (EPILOGUE HEADER)
    heap_listp += (2 * WSIZE);
    seg_init();
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL) // chunk size 확인(받을수 있는 사이즈인지)??
        return -1;
    return 0;
}

static void *extend_heap(size_t words)
{ // 힙을 넘어간다면 힙을 추가로 받아옴---------------------------------------------
    char *bp;
    size_t size;
    printf("-extend_heap\n");
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE; // 짝수로 만듬
    if ((long)(bp = mem_sbrk(size)) == -1)                    // 너무 커서 할당 못받으면 return -1
        return NULL;
    PUT(HDRP(bp), PACK(size, 0));         // block header free
    PUT(FTRP(bp), PACK(size, 0));         // block putter free
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 새로운 epiloge 헤더
    return coalesce(bp);                  // 만약 전 block이 프리였다면 합친다.
}

void *mm_malloc(size_t size) // 메모리할당-----------------------------------------------------------------------
{
    size_t asize;      // 생성할 size
    size_t extendsize; // 만약 chunksize를 넘긴 사이즈
    char *bp;
    printf("--------------------------------------find %d\n", size);
    printf("recent = %p\n", PREV_FREE_BLKP(heap_listp));
    printlist();
    if (size == 0) // 만약 입력받은 사이즈가 0 이면 무시
        return NULL;
    if (size <= DSIZE) // 만약 입력받은 사이즈가 dsize보다 작아도 최소 size로 생성
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE); // 8의 배수(Dsize)로 생성
    if ((bp = find_fit(asize)) != NULL)
    { // 들어갈 free 블록이 있다면 넣어준다.
        place(bp, asize);
        printlist();
        return bp;
    }
    extendsize = MAX(asize, CHUNKSIZE);                 // 만약 chunksize를 넘긴 사이즈라면
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL) // 넘긴 사이즈만큼의 힙을 할당받음
        return NULL;
    place(bp, asize);
    printlist();
    return bp;
}

static void *find_fit(size_t asize)
{ // 들어갈 자리를 찾는 함수------------------------------------------------------------
    void *bp;
    seg_find(asize);
    printf("find_fit %d\n", asize);
    for (bp = PREV_FREE_BLKP(heap_listp); bp != (char *)NULL; bp = PREV_FREE_BLKP(bp))
    { // bp 처음부터 블록단위로 for문 0(epilogue)
        if (asize <= GET_SIZE(HDRP(bp)))
        { // block이 주어진 사이즈보다 fit하면
            printf("-found!! %d = %p[%d]\n", asize, bp, GET_SIZE(HDRP(bp)));
            return bp;
        }
    }
    return NULL;
}

static void place(void *bp, size_t asize)
{                                      // free 블록에 넣어주는 함수 ---------------------------------------------------------
    size_t csize = GET_SIZE(HDRP(bp)); // 헤더의 사이즈를 읽어옴
    if ((csize - asize) >= (2 * DSIZE))
    { // 삽입하고 자리가 남으면 SPLIT 해준다.
        printf("-split\n");
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        cut_link(bp);
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
        push_first(bp);
    }
    else
    { // 딱 맞는다면 그냥 넣어준다.
        printf("-fit\n");
        cut_link(bp);
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

void mm_free(void *bp) //블록 free시키는 함수 ---------------------------------------------------------------
{
    size_t size = GET_SIZE(HDRP(bp)); // 헤더의 사이즈를 읽어옴
    printf("--------------------------------------free!  %p[%d]\n", bp, size);
    printlist();
    PUT(HDRP(bp), PACK(size, 0)); // 헤더에 free 입력
    PUT(FTRP(bp), PACK(size, 0)); // 푸터에 free 입력
    coalesce(bp);                 // coalesce 시켜줌
    printlist();
}

static void cut_link(void *bp)
{
    printf("-cut %p\n", bp);
    if (PREV_FREE_BLKP(bp) != (char *)NULL)
    {
        CHANGE_NEXT(PREV_FREE_BLKP(bp), NEXT_FREE_BLKP(bp)); // 전에 free의 next를 내 다음 free로
    }
    if (NEXT_FREE_BLKP(bp) != (char *)NULL)
    {
        CHANGE_PREV(NEXT_FREE_BLKP(bp), PREV_FREE_BLKP(bp)); // 다음 free의 prev를 내 전 free로
    }
}

static void push_first(void *bp)
{
    printf("-push %p\n", bp);
    seg_find(GET_SIZE(HDRP(bp))); //
    if (PREV_FREE_BLKP(heap_listp) != (char *)NULL)
    {
        CHANGE_NEXT(PREV_FREE_BLKP(heap_listp), bp); // 최신free를 나와 연결시킨다
    }
    PUT_P(PREVRP(bp), PREV_FREE_BLKP(heap_listp)); // 나의 이전은 최신 free
    PUT_P(NEXTRP(bp), heap_listp);                 //
    // to do 확인;;
    //CHANGE_PREV(heap_listp, bp);// 최신free를 나와 연결시킨다
    PUT_P(PREVRP(heap_listp), bp);
}

static void *coalesce(void *bp) // 연속된 free 처리--------------------------------------------------------------------
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 전에 블록이 alloc 인가
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음 블록이 alloc 인가
    size_t size = GET_SIZE(HDRP(bp));                   // 현재 노드의 사이즈
    printf("-coalesce %p\n", bp);
    if (prev_alloc && next_alloc)
    { // case 1 : 앞 뒤 다 alloc
        printf("--case1\n");
        push_first(bp);
        return bp; // 그냥 리턴
    }
    else if (prev_alloc && !next_alloc)
    { // case 2 : 다음도 free
        printf("--case2\n");
        cut_link(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // 다음 블록의 사이즈까지 합쳐서 free시킴
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        push_first(bp);
    }
    else if (!prev_alloc && next_alloc)
    { // case 3 : 전꺼도 free
        printf("--case3\n");
        cut_link(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))); // 전의 사이즈까지 합쳐서 free시킴
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        push_first(PREV_BLKP(bp));
        bp = PREV_BLKP(bp);
    }
    else
    { // case 4 : 앞 뒤 다 free
        printf("--case4\n");
        cut_link(NEXT_BLKP(bp));
        cut_link(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        push_first(PREV_BLKP(bp));
        bp = PREV_BLKP(bp);
    }
    return bp;
}

void *mm_realloc(void *bp, size_t size) // reallocation--------------------------------------------------------------------
{
    void *old_dp = bp;
    void *new_dp;
    size_t copySize;
    new_dp = mm_malloc(size); // 다른데다가 다시 할당 받기
    if (new_dp == NULL)       // 실패하면 NULL 리턴
        return NULL;
    copySize = GET_SIZE(HDRP(old_dp)); // 원래 블록의 사이즈
    if (size < copySize)               // 요청한 사이즈가 작다면 작은사이즈로 카피
        copySize = size;
    memcpy(new_dp, old_dp, copySize);
    mm_free(old_dp); // 기존 사이즈는 삭제
    return new_dp;
}

static void printlist(void)
{
    void *bp;
    int i = 0;
    printf("list\n");
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
    { // bp 처음부터 블록단위로 for문 0(epilogue)
        printf("%d. %p [%d]", i, bp, GET_SIZE(HDRP(bp)));
        if (GET_ALLOC(HDRP(bp)))
        {
            printf("[o]\n");
        }
        else
        {
            printf("\n");
        }
        i++;
    }
    i = 0;
    printf("freelist\n");
    for (bp = PREV_FREE_BLKP(heap_listp); bp != (char *)NULL; bp = PREV_FREE_BLKP(bp))
    {
        printf("%d. %p [%d] \n", i, bp, GET_SIZE(HDRP(bp)));
        i++;
    }
    printf("\n");
}