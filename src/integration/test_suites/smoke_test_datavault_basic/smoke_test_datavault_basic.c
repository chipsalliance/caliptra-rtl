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


#ifndef MY_RANDOM_SEED
#define MY_RANDOM_SEED 17
#endif // MY_RANDOM_SEED
// -- End Boilerplate --

const long seed = MY_RANDOM_SEED; 


int wr_regs_per_pfx(widereg_t *dv_reg, uint32_t rmask) {

    volatile uint32_t *baseaddr;
    volatile uint32_t *tmpreg;
    volatile uint32_t rdata, wdata, expdata;

    int errs = 0;

    baseaddr = dv_reg->addr; 

    VPRINTF(LOW,"INFO. Writing to addr group starting w/ 0x%x (%s[0..%d]), reporting only for index 0\n", 
        baseaddr, dv_reg->pfx, dv_reg->width-1);

    for (int j = 0; j < dv_reg->width; j++) {
        tmpreg = baseaddr + j; 

        wdata = (uint32_t) rand(); 
        *tmpreg = wdata;

        rdata = *tmpreg;
        expdata = wdata & rmask; 

        if (j == 0) {
            VPRINTF(LOW,"INFO. For addr 0x%x, attempting to write 0x%08x, read back 0x%08x\n", tmpreg, wdata, rdata);
        } else {
            VPRINTF(LOW,".");
        }

        if (rdata != expdata) {
            errs++;
            VPRINTF(ERROR,"\nMismatch at addr 0x%x (%s[%d]), read data 0x%08x != expected data 0x%08x --\n",  
                tmpreg, dv_reg->pfx, j, rdata, expdata); 
        } 
    }
    VPRINTF(LOW,"\n");

    return errs;
}


void main() {


    VPRINTF(LOW,"--------------------------------------\n");
    VPRINTF(LOW," DV Smoke Test With Basic Read/Write!!\n");
    VPRINTF(LOW,"--------------------------------------\n");


    VPRINTF(LOW,"\nINFO. Using random seed = %d\n", seed);
    srand(seed);

    VPRINTF(LOW,"\n** Phase 1. Basic random writes and reads **\n"); 

    widereg_t *dvreg_ptr;

    if (rst_count == 0) {

        // Write data entry registers only - skipping control 
        VPRINTF(LOW,"\n-- Performing WR followed by RD to data (non-control) registers only; printing once per prefix --\n\n"); 

        dvreg_ptr = dv_regs; 
        for (int i = 0; i < DV_PFX_COUNT; i++, dvreg_ptr++) {
            if (!str_contains(dvreg_ptr->pfx, "CTRL"))
                err_count += wr_regs_per_pfx(dvreg_ptr, DV_ONES);
        }

        // Write only control registers 
        VPRINTF(LOW,"\n\n-- Performing WR followed by RD to control (non-data) registers only; printing once per prefix --\n\n"); 

        dvreg_ptr = dv_regs; 
        for (int i = 0; i < DV_PFX_COUNT; i++, dvreg_ptr++) {
            if (str_contains(dvreg_ptr->pfx, "CTRL"))
                err_count += wr_regs_per_pfx(dvreg_ptr, 0x1);
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
