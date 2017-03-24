/***************************************************
* This program is a cache simulator that takes a   *
* memory trace as input and simulates the hit/miss *
* behavior of a cache memory on this trace.        *
*             Author: Xin Wang                     *
*             Andrew ID: xinw3                     *
*                                                  *
***************************************************/
#include "cachelab.h"
#include <stdio.h>
#include <stdlib.h>
#include <getopt.h>
#include <unistd.h>
/**
 * Parameters declaration.
 * h: help; v: verbose; 
 * s: Number of set index bits; 
 * b: Number of block offset bits;
 * t: Number of tag bits, t = m - (s + b);
 * E: Number of lines per set;
 * m: Number of physical address bits;
 * S: Number of sets, S = 2^s;
 * B: Block size, B = 2^b;
 */

int hitNum = 0, missNum = 0, evictNum = 0;
int v = 0, h = 0;
int s, b, E, t;
const int m = 64;
char *trace;
/*
 * Declare each line, set, cache as a linked list
 * so that the cache can replace a block using LRU
 * policy in which choose the block that was last 
 * accessed the furthest in the past. 
 */

/*
 * Define a linked list of each line.
 */
struct Line {
    int valid ;
    unsigned tag ;
    struct Line *next;
};
/*
 * Define a linked list of each set.
 * Each set is a linked list of each line.
 */
struct Set {
    int E;
    struct Line *head_line;
    struct Set *next;
};
/*
 * Define a linked list of cache.
 * The cache is a linked list of sets.
 */
struct Cache {
    int S;
    struct Set *head_set;
};

/*
 * Return the number of lines in a set.
 * A set only stores valid lines or it is empty.
 */
int set_size(struct Set *set){
    struct Line *curr = set->head_line;
    int size = 0;
    while (curr != NULL){
        size++;
        curr = curr->next;
    }
    return size;
}


/* Line Replacement on misses
 * If the cache misses, then it needs to retrieve
 * the new block from the next level and replace the existing lines.
 */
void replace_line(struct Set *set){
    struct Line *curr = set->head_line;
    struct Line *prev = NULL;
    struct Line *prev2 = NULL;
    while (curr != NULL){
        prev2 = prev;
        prev = curr;
        curr = curr->next;
    }
    if (prev2 != NULL){
        prev2->next = NULL;
    } else {
        set->head_line = NULL;
    }
    if (prev != NULL) free(prev);
}

void fetch_in_cache(struct Cache *cache, unsigned long address){
    /*Get the tag by right shift (s+b) bits of address.*/
    int tag_bits = address >> (s+b);
    /*Get set index by left shift first to remove tag bits
      and right shift (t+b) bits */
    int set_bits = (address << t) >> (t+b);

    /* locate set */
    struct Set *target_set = cache->head_set;   
    int i;
    for (i = 0; i < set_bits; ++i){
        target_set = target_set->next;
    } 

    struct Line *ln = target_set->head_line;
    struct Line *prev = NULL;
    while (ln != NULL){
        /* Check if any line in set has matching tag
           and the valid_bit == 1 */
        if (ln->valid && (ln->tag == tag_bits)){
            hitNum++;
            if (v) printf("hit ");
            if (prev != NULL)
            {
                prev->next = ln->next;
                ln->next = target_set->head_line;
                target_set->head_line = ln;
            }
            return ;
        }
        prev = ln;
        ln = ln->next;  
    }

    /*
     * If miss happens, go to level k+1 to fetch the block 
     * that containing an object.
     * If the level k is already full, then evicting happens.
     */
    missNum++;
    if (v) printf("miss ");
    struct Line *newln = (struct Line *)malloc(sizeof(struct Line));
    /* set the valid bit of the new line and replace the tag bits with that
     * of the target.
     */
    newln->valid = 1;
    newln->tag = tag_bits;

    /*fetch new line and add to head*/
    if (set_size(target_set) == target_set->E){
        replace_line(target_set);
        evictNum++;
        if (v) printf("eviction ");
    }
    newln->next = target_set->head_line;
    target_set->head_line = newln;
}

/* free cache, every set of cache, and every line in set */

int main(int argc, char** argv){    
    int opt;
    char identifier;
    unsigned long address;
    int size;

    /* read arguments from command line */
    while((opt = getopt(argc, argv, "vhs:E:b:t:")) != -1 ) {
        switch(opt) {
            case 'v':
                v = 1;
                break;
            case 'h':
                h = 1;
                break;
            case 's':
                s = atoi(optarg);
                break;
            case 'E':
                E = atoi(optarg);
                break;
            case 'b':
                b = atoi(optarg);
                break;
            case 't':
                trace = optarg;
                break;
            default:
                break;
        }
    }

    t = m - s - b;
    struct Cache *cache = (struct Cache *)malloc(sizeof(struct Cache));
 /*
 * Initialize the cache with 2^s sets and 
 * allocate address to each set and each
 # line using malloc.
 */
    cache->S = (1 << s);
    struct Set *thisset = (struct Set*)malloc(sizeof(struct Set));
    
    /*Initialize set*/

    thisset->E = E;
    thisset->head_line = NULL;
    thisset->next = NULL;

    /*Initialize cache*/
    cache->head_set= thisset; 
    int i;
    for (i = 1; i < cache->S; ++i){
        struct Set *nextset = (struct Set*)malloc(sizeof(struct Set));
        nextset->E = E;
        nextset->head_line = NULL;
        nextset->next = NULL;
        thisset->next = nextset; 
        thisset = nextset;
    }

    /* read trace file and access cache */
    FILE *traceFile;
    traceFile = fopen(trace, "r");

    while(fscanf(traceFile, "%c %lx, %d", &identifier, &address, &size) > 0) {
        if (v) printf("%c %lx, %d ", identifier, address, size);
        switch(identifier){
            case 'L':
                fetch_in_cache(cache, address);
                break;
            case 'S':
                fetch_in_cache(cache, address);
                break;
            default:
                break;
        }
    }
    fclose(traceFile); 

    /* free cache, every set of cache, and every line in set */
    struct Set *free_set = cache->head_set;
    while (!free_set){
        struct Line *free_line = free_set->head_line;
        while (!free_line){
            struct Line *temp_ln = free_line->next;
            free(free_line);
            free_line = temp_ln;
        }
        struct Set *temp_set = free_set->next;
        free(free_set);
        free_set = temp_set;
    }
    free(cache);

    /*print results*/
    printSummary(hitNum, missNum, evictNum);

    return 0; 
}