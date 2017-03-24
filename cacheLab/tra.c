/*      
 *  
 *                       Name:    Xin Wang                     
 *                     Andrew ID:     xinw3   
 *
 *               trans.c - Matrix transpose B = A^T
 *
 * Each transpose function must have a prototype of the form:
 * void trans(int M, int N, int A[N][M], int B[M][N]);
 *
 * A transpose function is evaluated by counting the number of misses
 * on a 1KB direct mapped cache with a block size of 32 bytes.
 *
 *
 *
 *                          s = 5, E = 1, b = 5
 *                   "Block" is the concept in cache. 
 *                      "block" is the matrix block. 
 * The number of sets is 32(S = 2^5).
 * Given the Block size of the cache(B = 2^5), considering sizeof(int) = 4
 * every Block can contain maximum 8 ints in order to eliminate conflict miss. 
 * 
 * Transpose 32 by 32:
 * When Thus make the block size of 32 by 32 matrix to be 8.
 * 
 * 
 */

#include <stdio.h>
#include "cachelab.h"
#include "contracts.h"

int is_transpose(int M, int N, int A[N][M], int B[M][N]);



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
    /*
     * i: the block row number.
     * j: the block column number.
     * ii: the row number in each block.
     * jj: the column number in each block.
     * r1-r8: to put temporary value, make use of temporal locality. 
     */
    int i, j, ii, jj;
    int r1, r2, r3, r4, r5, r6, r7, r8;
    int bsize;

    /**
     * Transpose 32 by 32 matrix.
     */
    if (M == 32 && N == 32) 
    {
        bsize = 8;
        for (i = 0; i < N; i += bsize)
        {
            for (j = 0; j < M; j += bsize)
            {
                for (ii = i; (ii < i + bsize) && ii < N; ii++)
                {
                    for (jj = j; (jj < j + bsize) && jj < M; jj++)
                    {
                            if (ii != jj) 
                            {
                                r1 = A[ii][jj];
                                B[jj][ii] = r1;
                            } 
                    }
                    /**
                     * Diagonal elements evict each other.
                     */
                    if (i == j) 
                    {
                        r1 = A[ii][ii];
                        B[ii][ii] = r1;
                    }
                }
            }
        }
    }
    /**
     * Transpose 64 by 64 matrix.
     * Seperate the matrix into 8*8 blocks and transpose 4 elements
     * each time. The order is like pipeline, 
     * i.e. from left top to left bottom and then right bottom to 
     * right right top.
     * To eliminate the conflict miss that may happen and utilize the 
     * 12 variables, put the last 4 elements into 4 registers.
     * 
     */
    if (M == 64 && N == 64) 
    {
        bsize = 8;
        for (i = 0; i < N; i += bsize)
        {
            for (j = 0; j < M; j += bsize)
            {
                /*
                 * Put the last 4 elements into 4 registers 
                 * to eliminate the eviction that may happen.
                 */
                r5 = A[i][j+4];
                r6 = A[i][j+5];
                r7 = A[i][j+6];
                r8 = A[i][j+7];

                for(ii = 0; ii < bsize; ii ++)
                {
                    
                    r1 = A[i+ii][j];
                    r2 = A[i+ii][j+1];
                    r3 = A[i+ii][j+2];
                    r4 = A[i+ii][j+3];

                    B[j][i+ii] = r1;
                    B[j+1][i+ii] = r2;
                    B[j+2][i+ii] = r3;
                    B[j+3][i+ii] = r4;

                }
                for(ii = 1; ii < bsize; ii++)
                {
                    r1 = A[i+bsize-ii][j+4];
                    r2 = A[i+bsize-ii][j+5];
                    r3 = A[i+bsize-ii][j+6];
                    r4 = A[i+bsize-ii][j+7];

                    B[j+4][i+bsize-ii] = r1;
                    B[j+5][i+bsize-ii] = r2;
                    B[j+6][i+bsize-ii] = r3;
                    B[j+7][i+bsize-ii] = r4;
                }
                

                B[j+4][i] = r5;
                B[j+5][i] = r6;
                B[j+6][i] = r7;
                B[j+7][i] = r8;                   
            }
        }
    }

    /**
     * Transpose 61 by 67 matrix.
     */

    if (M == 61 && N == 67) 
    {
        bsize = 18;
        for (i = 0; i < N; i += bsize)
        {
            for (j = 0; j < M; j += bsize)
            {
                for (ii = i; (ii < i + bsize) && (ii < N); ii++)
                {
                    for (jj = j; (jj < j + bsize) && (jj < M); jj++)
                    {
                        if (ii != jj) 
                            {
                                r1 = A[ii][jj];
                                B[jj][ii] = r1;
                            } 
                    }
                    /**
                     * Diagonal elements evict each other.
                     */
                    if (i == j) 
                    {
                        r1 = A[ii][ii];
                        B[ii][ii] = r1;
                    }
                }
            }
        }
    }
    ENSURES(is_transpose(M, N, A, B));
}

/* 
 * You can define additional transpose functions below. We've defined
 * a simple one below to help you get started. 
 */ 

    
// }
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
    //registerTransFunction(transpose_32by32, transpose_32by32_desc); 
    // registerTransFunction(transpose_64by64, transpose_32by32_desc);
    // registerTransFunction(transpose_61by67, transpose_32by32_desc);

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

