/*      Name: Xin Wang                     
 *     Andrew ID: xinw3   
 */

/* 
 * trans.c - Matrix transpose B = A^T
 *
 * Each transpose function must have a prototype of the form:
 * void trans(int M, int N, int A[N][M], int B[M][N]);
 *
 * A transpose function is evaluated by counting the number of misses
 * on a 1KB direct mapped cache with a block size of 32 bytes.
 *
 */ 

/*
 * s = 5, E = 1, b = 5
 */
#include <stdio.h>
#include "cachelab.h"
#include "contracts.h"

int is_transpose(int M, int N, int A[N][M], int B[M][N]);
void transpose_32by32(int M, int N, int A[N][M], int B[M][N], int bsize);
void transpose_64by64(int M, int N, int A[N][M], int B[M][N], int bsize);
void transpose_61by67(int M, int N, int A[N][M], int B[M][N], int bsize);

/* 
 * transpose_submit - This is the solution transpose function that you
 *     will be graded on for Part B of the assignment. Do not change
 *     the description string "Transpose submission", as the driver
 *     searches for that string to identify the transpose function to
 *     be graded. The REQUIRES and ENSURES from 15-122 are included
 *     for your convenience. They can be removed if you like.
 */
char transpose_submit_desc[] = "Transpose submission";
void transpose_submit(int M, int N, int A[N][M], int B[M][N])
{
    REQUIRES(M > 0);
    REQUIRES(N > 0);
    switch (M)
    {
        case 32:
            transpose_32by32(M, N, A[N][M], B[M][N], 8);
            break;
        case 64:
            transpose_64by64(M, N, A[N][M], B[M][N], 4);
            break;
        case 61:
            transpose_61by67(M, N, A[N][M], B[M][N], 18);
            break;  
    }


    ENSURES(is_transpose(M, N, A, B));
}

/* 
 * You can define additional transpose functions below. We've defined
 * a simple one below to help you get started. 
 */ 

/*
 * Given the Block size of the cache(B = 2^5), considering sizeof(int) = 4
 * every Block can contain 8 ints. 
 * Thus make the block size of matrix to be 8.
 * 
 */
char transpose_32by32_desc[] = "Transpose 32 by 32 matrix";
void transpose_32by32(int M, int N, int A[N][M], int B[M][N], int bsize)
{
    /*
     * i: the block row number.
     * j: the block column number.
     * ii: the row number in each block.
     * jj: the column number in each block.
     * temp: to put temporary value, make use of temporal locality. 
     */
    int i, j, ii, jj;
    int temp;
    for (i = 0; i < N; i += bsize)
    {
        for (j = 0; j < M; j += bsize)
        {
            for (ii = i; ii < i + bsize && ii < N; ii++)
            {
                for (jj = j; jj < j + bsize && jj < M; jj++)
                {
                        if (ii != jj) 
                        {
                            temp = A[ii][jj];
                            B[jj][ii] = temp;
                        } 
                }
                /**
                 * Diagonal elements evict each other.
                 */
                if (i == j) 
                {
                    temp = A[ii][ii];
                    B[ii][ii] = temp;
                }
            }
        }
    }
}

char transpose_64by64_desc[] = "Transpose 64 by 64 matrix";
void transpose_64by64(int M, int N, int A[N][M], int B[M][N], int bsize)
{
    
}

char transpose_61by67_desc[] = "Transpose 61 by 67 matrix";
void transpose_61by67(int M, int N, int A[N][M], int B[M][N], int bsize)
{
    
}
/* 
 * trans - A simple baseline transpose function, not optimized for the cache.
 */
char trans_desc[] = "Simple row-wise scan transpose";
void trans(int M, int N, int A[N][M], int B[M][N])
{
    int i, j, tmp;

    REQUIRES(M > 0);
    REQUIRES(N > 0);

    for (i = 0; i < N; i++) {
        for (j = 0; j < M; j++) {
            tmp = A[i][j];
            B[j][i] = tmp;
        }
    }    

    ENSURES(is_transpose(M, N, A, B));
}

/*
 * registerFunctions - This function registers your transpose
 *     functions with the driver.  At runtime, the driver will
 *     evaluate each of the registered functions and summarize their
 *     performance. This is a handy way to experiment with different
 *     transpose strategies.
 */
void registerFunctions()
{
    /* Register your solution function */
    registerTransFunction(transpose_submit, transpose_submit_desc); 

    /* Register any additional transpose functions */
    registerTransFunction(transpose_32by32, transpose_32by32_desc); 
    registerTransFunction(transpose_64by64, transpose_32by32_desc);
    registerTransFunction(transpose_61by67, transpose_32by32_desc);

}

/* 
 * is_transpose - This helper function checks if B is the transpose of
 *     A. You can check the correctness of your transpose by calling
 *     it before returning from the transpose function.
 */
int is_transpose(int M, int N, int A[N][M], int B[M][N])
{
    int i, j;

    for (i = 0; i < N; i++) {
        for (j = 0; j < M; ++j) {
            if (A[i][j] != B[j][i]) {
                return 0;
            }
        }
    }
    return 1;
}

