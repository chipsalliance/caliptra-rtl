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

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "riscv-csr.h"
#include <string.h>
#include <stdint.h>
#include <stdlib.h>
#include "printf.h"

volatile char*    stdout           = (char *)STDOUT;
volatile uint32_t intr_count = 0;
volatile uint32_t rst_count __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t err_count __attribute__((section(".dccm.persistent"))) = 0;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif
// -- End Boilerplate --

// #define _DV_DEBUG
#include "smoke_test_dv_common.h"

const long seed = 17; 

const int EXPECT_LOCKED = 1;
const int EXPECT_UNLOCKED = 0;


// Write to all registers for a given row in the dv_regs table
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

        // VPRINTF(LOW,"INFO. For addr 0x%x (%s[%d]), attempting to write 0x%08x, read back 0x%08x\n",  
        //     tmpreg, dv_reg->pfx, j, wdata, rdata);
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



// Writes to the k-th register for a given row in the dv_regs table
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


// find number of datasets locked by ctrl register 
int get_datset_len(ctrl_reg_t *dv_ctrl_ptr) {

    int *ptr = dv_ctrl_ptr->set; 

    for (int i = 0; i < 10; i++, ptr++) {
        if (*ptr < 0) 
            return i;
    }
    return 10;
}


int handle_2d_locking(ctrl_reg_t *dv_ctrl_ptr) { 

    widereg_t * ctrlgrp_ptr; 
    widereg_t * datagrp_ptr; 

    int errs = 0;

    // This part before loop is common to both 2d and 1d handling 
    int ctrl_entry_count = dv_ctrl_ptr->entries;
    int *dataset_ptr = dv_ctrl_ptr->set;
    int dataset_len = get_datset_len(dv_ctrl_ptr); 

    ctrlgrp_ptr = & (dv_regs[dv_ctrl_ptr->index]);
    VPRINTF (LOW, "INFO. handle_2d_locking(). Number of items in datset = %d\n", dataset_len); 

    // Unique to 2D control groups
    for (int j = 0; j < dataset_len; j++, dataset_ptr++) {

        // lock ctrlgrp[j] -> only datagrp_j[0..k-1] affected
        VPRINTF (LOW, "\n--next set--\n");
        datagrp_ptr = &dv_regs[*dataset_ptr];

        // VPRINTF(LOW, "INFO. Control register %s[%d] -LOCKING-> %s[0] - [%d]\n", 
        //     ctrlgrp_ptr->pfx, j, datagrp_ptr->pfx, ctrl_entry_count-1);
        VPRINTF(LOW, "%s[%d] -LOCKS-> %s[0..%d]\n", ctrlgrp_ptr->pfx, j, datagrp_ptr->pfx, ctrl_entry_count-1);
        errs += wr_regs_per_pfx( datagrp_ptr, DV_ONES, EXPECT_UNLOCKED );           // write random 
        errs += wr_single_reg_explicit( ctrlgrp_ptr, 0x1, 0x1, j );              // lock registers
        errs += wr_regs_per_pfx( datagrp_ptr, DV_ONES, EXPECT_LOCKED );          // attempt write random 
        // errs += exercise_unlocked( ??, DV_ONES, EXPECT_LOCKED );                 // attempt write random to other blocks
        errs += wr_single_reg_explicit( ctrlgrp_ptr, 0x0, 0x1, j );              // attempt unlock registers 
    }
    return errs;
}


int handle_1d_locking(ctrl_reg_t *dv_ctrl_ptr) { 

    widereg_t * ctrlgrp_ptr; 
    widereg_t * datagrp_ptr; 

    int errs = 0;

    // This part before loop is common to both 2d and 1d handling 
    int ctrl_entry_count = dv_ctrl_ptr->entries;
    int *dataset_ptr = dv_ctrl_ptr->set;
    int dataset_len = get_datset_len(dv_ctrl_ptr); 

    ctrlgrp_ptr = & (dv_regs[dv_ctrl_ptr->index]);

    VPRINTF (LOW, "INFO. handle_1d_locking(). Number of items in datset = %d\n", dataset_len); 

    // Unique to 1D control groups
    for (int j = 0; j < dataset_len; j++, dataset_ptr++) {

        // lock ctrlgrp[j] -> only datagrp[j] affected
        VPRINTF (LOW, "\n--next set--\n");
        datagrp_ptr = &dv_regs[*dataset_ptr];

        VPRINTF(LOW, "%s[%d] -LOCKS-> %s[%d]\n", ctrlgrp_ptr->pfx, j, datagrp_ptr->pfx, j);

        uint32_t locked_data = rand();
        err_count += wr_single_reg_explicit( datagrp_ptr, locked_data, locked_data, j );     // write random
        err_count += wr_single_reg_explicit( ctrlgrp_ptr, 0x1, 0x1, j );                     // lock register 
        err_count += wr_single_reg_explicit( datagrp_ptr, rand(), locked_data, j );          // attempt write random
        // err_count += wr_regs_per_pfx( datagrp_ptr, DV_ONES, EXPECT_LOCKED);               // attempt write random to other blocks
        err_count += wr_single_reg_explicit( ctrlgrp_ptr, 0x0, 0x1, j );                     // attempt unlock register 
    }

    return errs;
}



void main() {

    // We have up to 4 array of pairings of Control and Data registers that are lockable 
    ctrl_reg_t *dv_ctrl_ptr;

    int ctrl_data_indices [4] = {0, 1, 2, 3};

    shuffle(ctrl_data_indices, 4);  

    srand(seed);

    VPRINTF(LOW,"-----------------------------------------\n");
    VPRINTF(LOW," DV Smoke Test for checking Lock Controls\n");
    VPRINTF(LOW,"-----------------------------------------\n");

    VPRINTF(LOW,"INFO. Using random playbook seed = %d\n\n", getenv("PLAYBOOK_RANDOM_SEED")); 

    if (rst_count == 0) {

        // CYCLE THROUGH 4 CTRL GROUP 
        for (int i = 0; i < 4; i++) {

            dv_ctrl_ptr = & dv_ctrl_regids[ctrl_data_indices[i]]; 
            VPRINTF (LOW, "\n\n** Working on new Control Group Prefix %s to Start Locking Data Registers **\n\n", dv_regs[dv_ctrl_ptr->index].pfx);

            if ((dv_ctrl_ptr->influence == STICKY_2D) || (dv_ctrl_ptr->influence == NONSTICKY_2D))  
                err_count += handle_2d_locking(dv_ctrl_ptr);
            else
                err_count += handle_1d_locking(dv_ctrl_ptr);
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
