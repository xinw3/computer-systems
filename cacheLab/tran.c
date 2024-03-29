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
        bsize = 8
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
     */
    if (M == 64 && N == 64) {
        bsize = 4;
        for (i = 0; i < N; i += bsize){
            for (j = 0; j < M; j += bsize){
                /* load A[i][] A[i+1][] A[i+2][]*/
                r1 = A[i][j];
                r2 = A[i+1][j];
                r3 = A[i+2][j];
                r4 = A[i+2][j+1];
                r5 = A[i+2][j+2];



                /* Load A[][j+3]  to B[j+3][]. hit */
                B[j+3][i] = A[i][j+3];
                B[j+3][i+1] = A[i+1][j+3];
                B[j+3][i+2] = A[i+2][j+3];

                /* load B[j+2][], may evict A[i+2][] */
                B[j+2][i] = A[i][j+2];
                B[j+2][i+1] = A[i+1][j+2];
                B[j+2][i+2] = r5;

                r5 = A[i+1][j+1];

                /* load B[j+1][], may evict A[i+1][] */
                B[j+1][i] = A[i][j+1];
                B[j+1][i+1] = r5;
                B[j+1][i+2] = r4;

                /* load B[j][], may evict A[i][] */
                B[j][i] = r1;
                B[j][i+1] = r2;
                B[j][i+2] = r3;

                /* load A[i+3][], may evict B[j+3][] */
                B[j][i+3] = A[i+3][j];
                B[j+1][i+3] = A[i+3][j+1];
                B[j+2][i+3] = A[i+3][j+2];

                r1 = A[i+3][j+3];

                /* load B[j+3][], may evict A[i+3][] */
                B[j+3][i+3] = r1;
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

