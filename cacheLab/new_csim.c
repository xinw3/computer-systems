/****************************************************
 * This program is a cache simulator that takes a   *
 * memory trace as input and simulates the hit/miss *
 * behavior of a cache memory on this trace.        *
 *             Author: Xin Wang                     *
 *             Andrew ID: xinw3                     *
 *                                                  *
 ****************************************************/
#include "cachelab.h"
#include <getopt.h>
#include <stdlib.h>
#include <unistd.h>
#include <stdio.h>
#include <string.h>

const int m = 64; 
int hitNum = 0, missNum = 0, evictNum = 0;
int v_flag = 0, h_flag = 0;
int s, b, E, t;
char *trace;
/**
 * Define a structure to group cache's parameters 
 * and arguments entered from command line together.
 * h: help; v: verbose; 
 * s: Number of set index bits; 
 * b: Number of block offset bits;
 * m: Number of physical address bits;
 * t: Number of tag bits, t = m - (s + b);
 * E: Number of lines per set;
 * S: Number of sets, S = 2^s;
 * B: Block size, B = 2^b;
 * 
 * 
 * 
 */
struct Params
{
    int h, v, s, b, m, t, E, S, B;
    char *trace;
};

/*
 *
 * Cache data structure implimentation
 *
 *  Each Cache is a linked list of 2^s Sets, stores a pointer to head Set.
 *  Each Set is a linked list of Lines, and has a capacity of E.
 *  A Set stores VALID LINES ONLY, otherwise is empty (points to NULL).
 *
 *  The linked list of lines is in the order from mru to lru.
 *  If a search can't find a match in target set, add a new line at head.
 *  When the length of the Set exceeds the capacity E, delete the last line.
 *  If a search hits a match, move the matching line to the head of the set.
 *
 */

struct Line 
{
    int valid ;
    int tag ;
    struct Line *next;
};

struct Set {
    int E;
    struct Line *head_line;
    struct Set *next;
};

struct Cache {
    int S;
    struct Set *head_set;
};
/*
 * Define a method that prints usage info.
 */
int usage_info()
{
    printf("Usage:  ./csim [-hv] -s <s> -E <E> -b <b> -t <tracefile>\n");
    printf("-h: Optional help flag.\n");
    printf("-v: Optional verbose flag.\n");
    printf("-s <s>: Number of set index bits (S = 2^s is the number of sets).\n");
    printf("-E <E>: Associativity (number of lines per set).\n");
    printf("-b <b>: Number of block bits (B = 2^b is the block size).\n");
    printf("-t <tracefile>: Name of the memory trace to replay.");
    return -1;
}
/*
 * Define a method to get the command line arguments.
 */
int get_params(struct Params* params, int argc, char** argv)
{
    char c;
    while ((c = getopt(argc, argv, "hvs:E:b:t:")) != -1)
    {
        switch(c)
        {
            case 'h': 
                usage_info();
                break;
            case 'v': 
                params->v = 1;
                break;
            case 's':
                params->s = atoi(optarg);
                break;
            case 'E':
                params->E = atoi(optarg);
                break;
            case 'b':
                params->b = atoi(optarg);
                break;
            case 't':
                strncpy(params->trace, optarg, sizeof(params->trace) - 1);
                break;
            default:
                return usage_info();

        }
    }
    return 0;
}

/* return the number of valid lines in a set*/
int set_size(struct Set *set){
    struct Line *currentLine = set->head_line;
    int size = 0;
    while (currentLine != NULL){
        size++;
        currentLine = currentLine->next;
    }
    return size;
}

/* initialize set with capacity E and no valid lines */
void set_init(struct Set *set, int E){
    set->E = E;
    set->head_line = NULL;
    set->next = NULL;
}

//Create cache memory given parameters.
void create_cache(struct Cache *cache, int s, int E) {
    cache->S = (1 << s);
    struct Set *thisset = (struct Set*)malloc(sizeof(struct Set));
    set_init(thisset, E);
    cache->head_set= thisset; 
    int i;
    for (i = 1; i < cache->S; ++i){
        struct Set *nextset = (struct Set*)malloc(sizeof(struct Set));
        set_init(nextset, E);
        thisset->next = nextset; 
        thisset = nextset;
    }
}

/* delete the last line of a set */
void delete_last_line(struct Set *set) {
    struct Line *currentLine = set->head_line;
    struct Line *prev = NULL;
    struct Line *prev2 = NULL;
    while (currentLine != NULL){
        prev2 = prev;
        prev = currentLine;
        currentLine = currentLine->next;
    }
    if (prev2 != NULL){
        prev2->next = NULL;
    } else {
        set->head_line = NULL;
    }
    if (prev != NULL) free(prev);
}

/* add a (valid) line to the head of a set, evict when exceeds capacity */
void add_line_to_head(struct Set *set, struct Line *line){
    if (set_size(set) == set->E){
        delete_last_line(set);
        evictNum++;
    }
    line->next = set->head_line;
    set->head_line = line;
}

/* move the matched line to head of the set */
void move_line_to_head(struct Set *set, struct Line *line, struct Line *prev){
    if (prev != NULL){
        prev->next = line->next;
        line->next = set->head_line;
        set->head_line = line;
    }
}

/* the procedure of fetching an address in the cache */
void access_cache(struct Cache *cache, unsigned long address) 
{
    /*Get the tag by right shift (s+b) bits of address.*/
    int tag_bits = address >> (s+b);
    /*Get set index by left shift first to remove tag bits
      and right shift (t+b) bits */
    int set_index = (address << t) >> (t+b);

    /* locate set */
    struct Set *select_set = cache->head_set;   
    int i;
    for (i = 0; i < set_index; i++)
    {
        select_set = select_set->next;
    } 

    struct Line *ln = select_set->head_line;
    struct Line *prev = NULL;
    while (ln != NULL){
        /* Check if any line in set has matching tag
           and the valid_bit == 1 */
        if (ln->valid && (ln->tag == tag_bits))
        {
            hitNum++;
            move_line_to_head(select_set, ln, prev);
            return ;
        }
        prev = ln;
        ln = ln->next;  
    }

    /* miss if no match, add a new line */
    /* possible eviction happens in add_line_to_head */
    missNum++;
    struct Line *newln = (struct Line *)malloc(sizeof(struct Line));
    newln->valid = 1;
    newln->tag = tag_bits;
    add_line_to_head(select_set,newln);
}

/* free cache, every set of cache, and every line in set */
void free_cache(struct Cache *cache){
    struct Set *free_set= cache->head_set;
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
}

int main(int argc, char** argv){    
    // int opt;
    char opt;
    unsigned long addr;
    int size;
    struct Params* params = {0};
    if (get_params(params, argc, argv)<0)
        exit(-1);
 
    params->t = params->m - params->s - params->b;
    struct Cache *mycache = (struct Cache *)malloc(sizeof(struct Cache));
    create_cache(mycache, params->s, params->E);

    //Read from tracefile.
    FILE *tracefile;
    tracefile = fopen(params->trace, "r");
    
    while(fscanf(tracefile, "%c %lx, %d", &opt, &addr, &size) > 0) {
        switch(opt){
            case 'L':
                access_cache(mycache, addr);
                break;
            case 'S':
                access_cache(mycache, addr);
                break;
            default:
                break;
        }
    }
    fclose(tracefile); 

    free_cache(mycache);
    printSummary(hitNum, missNum, evictNum);

    return 0; 
}
