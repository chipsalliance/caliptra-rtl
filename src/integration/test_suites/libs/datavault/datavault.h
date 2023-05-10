// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//


#ifndef _DATAVAULT_H
#define _DATAVAULT_H

// #define DV_SMALLSET    // Use this for debug; may not work from smoke test file due to compilation order 


#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include "caliptra_defines.h"
#include "printf.h"

#define DV_ONES 0xffffffff


#ifdef DV_SMALLSET    // Smaller test set for DEBUG

#define DV_PFX_COUNT    10 
#define DV_MAXWIDTH     3 

#else               // Default larger set 

#define DV_PFX_COUNT    27  
#define DV_MAXWIDTH     12

#endif // DV_SMALLSET


enum ctrl_type {STICKY_2D, NONSTICKY_2D, STICKY_1D, NONSTICKY_1D};


typedef struct {
    char * pfx; 
    volatile uint32_t * addr;
    int width; 
    uint32_t sticky_mask;   
    uint32_t rstval; 
} widereg_t;


typedef struct  {
    int index;                  // dv_reg
    enum ctrl_type influence;
    int entries;                // entries per set
    int set [10];               // set of dv_reg indices
} ctrl_reg_t;


// -------------------------------------------
// -- Global variables --
// -------------------------------------------

extern widereg_t dv_regs [DV_PFX_COUNT];
extern ctrl_reg_t dv_ctrl_regids []; 
extern int lock_status_bitmap [DV_PFX_COUNT]; 


// -------------------------------------------
// -- DV register specific functions -- 
// -------------------------------------------

// True if prefix string contains "CTRL" 
int is_ctrl_reg(widereg_t *dv_reg);

// given an address find the dv reg wide register struct 
widereg_t *find_dv_reg(volatile uint32_t *reg_addr);

// lookup the dv reg structure given a prefix 
widereg_t *find_dv_reg_by_pfx(char * c);

// find number of datasets locked by ctrl register 
int get_datset_len(ctrl_reg_t *dv_ctrl_ptr);

// update bitmap of locked register status
void update_bitmap( int ix, int j );

// print whole locked register bitmap status 
void print_bitmap();


// -------------------------------------------
// -- Standard lib util functions --
// -------------------------------------------

// shorthand for if str "a" in "b"
int str_contains(char *b, char *a);

// simple in-place shuffle of an array of integers 
void shuffle(int *ptr, int N);


#endif // _DATAVAULT_H


