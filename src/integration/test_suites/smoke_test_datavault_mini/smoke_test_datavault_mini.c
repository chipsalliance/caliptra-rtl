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

// This test is based on "smoke_test_datavault_lock"; it runs on a smaller 
// dataset for nightly regression purposes. It covers register locking capability on 
// the same number of groups, and runs on "all" the groups (unlike the bigger version
// which randomly inititates locking on one set).   
//
// NOTE. Warm reset is currently not covered as part of this.  


// -- Begin Boilerplate --
#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "riscv-csr.h"
#include <string.h>
#include <stdint.h>
#include <stdlib.h>
#include "printf.h"
#include "datavault.h"

volatile char*    stdout           = (char *)STDOUT;
volatile uint32_t intr_count = 0;
volatile uint32_t rst_count __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t err_count __attribute__((section(".dccm.persistent"))) = 0;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {
    .doe_error        = 0,
    .doe_notif        = 0,
    .ecc_error        = 0,
    .ecc_notif        = 0,
    .hmac_error       = 0,
    .hmac_notif       = 0,
    .kv_error         = 0,
    .kv_notif         = 0,
    .sha512_error     = 0,
    .sha512_notif     = 0,
    .sha256_error     = 0,
    .sha256_notif     = 0,
    .qspi_error       = 0,
    .qspi_notif       = 0,
    .uart_error       = 0,
    .uart_notif       = 0,
    .i3c_error        = 0,
    .i3c_notif        = 0,
    .soc_ifc_error    = 0,
    .soc_ifc_notif    = 0,
    .sha512_acc_error = 0,
    .sha512_acc_notif = 0,
};


#ifndef MY_RANDOM_SEED
#define MY_RANDOM_SEED 17
#endif // MY_RANDOM_SEED
// -- End Boilerplate --

const long seed = MY_RANDOM_SEED; 

const int EXPECT_LOCKED = 1;
const int EXPECT_UNLOCKED = 0;

#define SM_DV_PFX_COUNT 10 

// ===============================================================================================
// Smaller datavault set -- using ifdef is problematic when order of compilation is not known 
// Copy of data set with "sm_" prefixed
// ===============================================================================================

widereg_t sm_dv_regs [SM_DV_PFX_COUNT] = {
    { "STICKYDATAVAULTCTRL",                 (uint32_t *) CLP_DV_REG_STICKYDATAVAULTCTRL_0,             2,  0x1,     0x0 }, //  0. (0x1001c000) 
    { "STICKY_DATA_VAULT_ENTRY_0",           (uint32_t *) CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_0_0,       3,  DV_ONES, 0x0 }, //  1. (0x1001c028) 
    { "STICKY_DATA_VAULT_ENTRY_1",           (uint32_t *) CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_1_0,       3,  DV_ONES, 0x0 }, //  2. (0x1001c058) 
    { "DATAVAULTCTRL",                       (uint32_t *) CLP_DV_REG_DATAVAULTCTRL_0,                   2,  0x0,     0x0 }, //  3. (0x1001c208) 
    { "DATA_VAULT_ENTRY_0",                  (uint32_t *) CLP_DV_REG_DATA_VAULT_ENTRY_0_0,              3,  DV_ONES, 0x0 }, //  4. (0x1001c230) 
    { "DATA_VAULT_ENTRY_1",                  (uint32_t *) CLP_DV_REG_DATA_VAULT_ENTRY_1_0,              3,  DV_ONES, 0x0 }, //  5. (0x1001c260) 
    { "LOCKABLE_SCRATCHREG_CTRL",            (uint32_t *) CLP_DV_REG_LOCKABLESCRATCHREGCTRL_0,          2,  0x0,     0x0 }, //  6. (0x1001c410)
    { "LOCKABLE_SCRATCHREG",                 (uint32_t *) CLP_DV_REG_LOCKABLESCRATCHREG_0,              2,  DV_ONES, 0x0 }, //  7. (0x1001c438) 
    { "STICKY_LOCKABLE_SCRATCHREGCTRL",      (uint32_t *) CLP_DV_REG_STICKYLOCKABLESCRATCHREGCTRL_0,    2,  0x1,     0x0 }, //  8. (0x1001c480) 
    { "STICKY_LOCKABLE_SCRATCHREG",          (uint32_t *) CLP_DV_REG_STICKYLOCKABLESCRATCHREG_0,        2,  DV_ONES, 0x0 }  //  9. (0x1001c4a0) 
};

enum sm_ctrl_index {SM_CTRL1 = 0, SM_CTRL2 = 3, SM_CTRL3 = 6, SM_CTRL4 = 8, IXNA=-1}; 

ctrl_reg_t sm_dv_ctrl_regids [] = {
    {SM_CTRL1, STICKY_2D,      3, {SM_CTRL1+1, SM_CTRL1+2, IXNA, IXNA, IXNA, IXNA, IXNA, IXNA, IXNA, IXNA}},      // 2 sets x 3 slots
    {SM_CTRL2, NONSTICKY_2D,   3, {SM_CTRL2+1, SM_CTRL2+2, IXNA, IXNA, IXNA, IXNA, IXNA, IXNA, IXNA, IXNA}},      // 2 sets x 3 slots
    {SM_CTRL3, NONSTICKY_1D,   1, {SM_CTRL3+1, SM_CTRL3+1, IXNA, IXNA, IXNA, IXNA, IXNA, IXNA, IXNA, IXNA}},      // 2 x 1 set x 1 slot 
    {SM_CTRL4, STICKY_1D,      1, {SM_CTRL4+1, SM_CTRL4+1, IXNA, IXNA, IXNA, IXNA, IXNA, IXNA, IXNA, IXNA}}       // 2 x 1 set x 1 slot 
};

int sm_lock_status_bitmap [SM_DV_PFX_COUNT] = { 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 };  // each entry corresponds to a row in sm_dv_regs

// ===============================================================================================



//NOTE. Functions below that do not have the "sm_" prefix are IDENTICAL to the counterparts in 
//      smoke_test_datavault_lock.c. Can move them to datavault.h/c on next update of the functions 


// Write to all registers for a given row in the sm_dv_regs table
// If unlocked: Write followed by Read and expected data is set thru rmask. 
// If locked: Read, Write, then Read again. Two reads should match. 
int wr_regs_per_pfx(widereg_t *dv_reg, uint32_t rmask, int locked) { 

    volatile uint32_t *tmpreg;
    volatile uint32_t rdata, wdata, expdata;

    int errs = 0;

    for (int j = 0; j < dv_reg->width; j++) {
        tmpreg = dv_reg->addr + j; 

        if (locked)
            expdata = *tmpreg; 

        wdata = (uint32_t) rand(); 
        *tmpreg = wdata;

        rdata = *tmpreg;
        if (!locked)
            expdata = wdata & rmask; 

        if (j == 0) {
            VPRINTF(LOW,"INFO. (Group Write) For addr 0x%x (%s[%d]), attempting to write 0x%08x, read back 0x%08x\n",  
                tmpreg, dv_reg->pfx, j, wdata, rdata);
        } else {
            VPRINTF(LOW,".");
        }

        if (rdata != expdata) {
            errs++;
            VPRINTF(ERROR,"\nERROR. Mismatch at addr 0x%x (%s[%d]), read data 0x%08x != expected data 0x%08x --\n",  
                tmpreg, dv_reg->pfx, j, rdata, expdata); 
        } 
    }
    VPRINTF (LOW, "\n");
    return errs;
}



// Writes to the k-th register for a given row in the sm_dv_regs table
// Unlike wr_regs_per_pfx(...), explicit values for writing & checking are provided
int wr_single_reg_explicit(widereg_t *dv_reg, uint32_t wdata, uint32_t expdata, int j) {

    volatile uint32_t *tmpreg;
    volatile uint32_t rdata; 

    int errs = 0;

    tmpreg = dv_reg->addr + j; 

    *tmpreg = wdata;
    rdata = *tmpreg;

    VPRINTF(LOW,"INFO. (Single Write) For addr 0x%x (%s[%d]), attempting to write 0x%08x, read back 0x%08x\n",  
        tmpreg, dv_reg->pfx, j, wdata, rdata);

    if (rdata != expdata) {
        errs++;
        VPRINTF(ERROR,"\nERROR. Mismatch at addr 0x%x (%s[%d]), read data 0x%08x != expected data 0x%08x --\n",  
            tmpreg, dv_reg->pfx, j, rdata, expdata); 
    } 

    return errs;
}


// Walk through the sm_dv_regs list, skipping over the ctrl regs or fully locked regs. 
// Else, randomly select an index (position) to write to.  
int sm_exercise_unlocked() {

    int pos, curr;
    int errs = 0;
    int found_unlocked = 0; 

    widereg_t *dv_ptr = sm_dv_regs;
    int *bmp_ptr = lock_status_bitmap;
    
    VPRINTF (LOW, "checking all dv_reg indices for unlocked registers\n");
    // print_bitmap();  

    for (int i = 0; i < SM_DV_PFX_COUNT; i++) {
        found_unlocked = 0;
        curr = *bmp_ptr;

        if (str_contains(dv_ptr->pfx, "CTRL") || 
            (curr == ((1 << dv_ptr->width) - 1))) {  // all 1's 
            ;
        } else if (curr == 0) { 
            // VPRINTF (LOW, "found fully unlocked registers at sm_dv_regs[%d]...(curr status is 0x%-3x):\n", i, curr);
            found_unlocked = 1;
            pos = rand() % dv_ptr->width; 
        } else {
            // VPRINTF (LOW, "found partially unlocked registers at sm_dv_regs[%d]...(curr status is 0x%-3x):\n", i, curr);
            for (int j = 0; j < dv_ptr->width; j++) {
                pos = rand() % dv_ptr-> width;
                if ( (curr & (1 << pos)) == 0 ) { 
                    found_unlocked = 1;
                    break;
                }
            } 
        }

        if (found_unlocked) {
            uint32_t rand_data = rand();
            errs += wr_single_reg_explicit( dv_ptr, rand_data, rand_data, pos );  // unlocked registers
        }

        dv_ptr++;
        bmp_ptr++;
    }

    return errs;
}



int sm_handle_2d_locking(ctrl_reg_t *dv_ctrl_ptr) { 

    widereg_t * ctrlgrp_ptr; 
    widereg_t * datagrp_ptr; 

    int errs = 0;

    // This part before loop is common to both 2d and 1d handling 
    int ctrl_entry_count = dv_ctrl_ptr->entries;
    int *dataset_ptr = dv_ctrl_ptr->set;
    int dataset_len = get_datset_len(dv_ctrl_ptr); 

    ctrlgrp_ptr = & (sm_dv_regs[dv_ctrl_ptr->index]);
    VPRINTF (LOW, "INFO. handle_2d_locking(). Number of items in datset = %d\n", dataset_len); 

    widereg_t * datagrp_head = sm_dv_regs;

    // Unique to 2D control groups
    for (int j = 0; j < dataset_len; j++, dataset_ptr++) {
        // lock ctrlgrp[j] -> only datagrp_j[0..k-1] affected
        VPRINTF (LOW, "\n--next set--\n");
        datagrp_ptr = &sm_dv_regs[*dataset_ptr];

        VPRINTF(LOW, "%s[%d] -LOCKS-> %s[0..%d]\n", ctrlgrp_ptr->pfx, j, datagrp_ptr->pfx, ctrl_entry_count-1);
        errs += wr_regs_per_pfx( datagrp_ptr, DV_ONES, EXPECT_UNLOCKED );                // write random 
        errs += wr_single_reg_explicit( ctrlgrp_ptr, 0x1, 0x1, j );                      // lock registers
        errs += wr_regs_per_pfx( datagrp_ptr, DV_ONES, EXPECT_LOCKED );                  // attempt write random 
        lock_status_bitmap[datagrp_ptr - datagrp_head] = (1 << datagrp_ptr->width) - 1;  // mark lock bitmap -- all 1's
        errs += sm_exercise_unlocked();                                                     // attempt write random to unlocked blocks
        errs += wr_single_reg_explicit( ctrlgrp_ptr, 0x0, 0x1, j );                      // attempt unlock registers 
    }
    return errs;
}


int sm_handle_1d_locking(ctrl_reg_t *dv_ctrl_ptr) { 

    widereg_t * ctrlgrp_ptr; 
    widereg_t * datagrp_ptr; 

    int errs = 0;

    // This part before loop is common to both 2d and 1d handling 
    int ctrl_entry_count = dv_ctrl_ptr->entries;
    int *dataset_ptr = dv_ctrl_ptr->set;
    int dataset_len = get_datset_len(dv_ctrl_ptr); 

    ctrlgrp_ptr = & (sm_dv_regs[dv_ctrl_ptr->index]);
    VPRINTF (LOW, "INFO. handle_1d_locking(). Number of items in datset = %d\n", dataset_len); 

    widereg_t * datagrp_head = sm_dv_regs;

    // Unique to 1D control groups
    for (int j = 0; j < dataset_len; j++, dataset_ptr++) {
        // lock ctrlgrp[j] -> only datagrp[j] affected
        VPRINTF (LOW, "\n--next set--\n");
        datagrp_ptr = &sm_dv_regs[*dataset_ptr];

        VPRINTF(LOW, "%s[%d] -LOCKS-> %s[%d]\n", ctrlgrp_ptr->pfx, j, datagrp_ptr->pfx, j);

        uint32_t locked_data = rand();
        errs += wr_single_reg_explicit( datagrp_ptr, locked_data, locked_data, j );     // write random
        errs += wr_single_reg_explicit( ctrlgrp_ptr, 0x1, 0x1, j );                     // lock register 
        errs += wr_single_reg_explicit( datagrp_ptr, rand(), locked_data, j );          // attempt write random
        update_bitmap(datagrp_ptr - datagrp_head, j);                                   // mark lock bitmap
        errs += sm_exercise_unlocked();                                                    // attempt write random to unlocked blocks
        errs += wr_single_reg_explicit( ctrlgrp_ptr, 0x0, 0x1, j );                     // attempt unlock register 
    }

    return errs;
}



void main() {

    VPRINTF(LOW,"-------------------------------------------------------------------\n");
    VPRINTF(LOW," Datavault (Mini) Smoke Test for checking Lock & Basic Controls\n");
    VPRINTF(LOW,"-------------------------------------------------------------------\n");

    VPRINTF(LOW,"\nINFO. Using random seed = %d\n", seed);
    srand(seed);

    // We have up to 4 array of pairings of Control and Data registers that are lockable 
    ctrl_reg_t *dv_ctrl_ptr;

    int ctrl_data_indices [4] = {0, 1, 2, 3};

    shuffle(ctrl_data_indices, 4);  

    if (rst_count == 0) {

        // CYCLE THROUGH 4 CTRL GROUP 
        for (int i = 0; i < 4; i++) {

            dv_ctrl_ptr = & sm_dv_ctrl_regids[ctrl_data_indices[i]]; 
            VPRINTF (LOW, "\n\n** Working on new Control Group Prefix %s to Start Locking Data Registers **\n\n", sm_dv_regs[dv_ctrl_ptr->index].pfx);

            if ((dv_ctrl_ptr->influence == STICKY_2D) || (dv_ctrl_ptr->influence == NONSTICKY_2D))  
                err_count += sm_handle_2d_locking(dv_ctrl_ptr);
            else
                err_count += sm_handle_1d_locking(dv_ctrl_ptr);
        }

        VPRINTF(LOW,"\n\n-- Done w/test; %d errors found -- \n", err_count);
        if (err_count != 0)  {
            SEND_STDOUT_CTRL(0x1);
        }

        SEND_STDOUT_CTRL(0xff);


    } else {
        // Unexecuted branch. Placeholder for any future reset based tests 
        VPRINTF(LOW,"** Moving on to phase 2 of test **\n");

        VPRINTF(LOW,"\n\n-- Done w/test; %d errors found -- \n", err_count);
        if (err_count != 0)  {
            SEND_STDOUT_CTRL(0x1);
        }

        SEND_STDOUT_CTRL(0xff);
    }

}
