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


int wr_regs_per_pfx(widereg_t *dv_reg, uint32_t rmask) {

    volatile uint32_t *tmpreg;
    volatile uint32_t rdata, wdata, expdata;

    int errs = 0;

    for (int j = 0; j < dv_reg->width; j++) {
        tmpreg = dv_reg->addr + j; 

        wdata = (uint32_t) rand(); 
        *tmpreg = wdata;

        rdata = *tmpreg;
        expdata = wdata & rmask; 

        VPRINTF(LOW,"\nINFO. For addr 0x%x (%s[%d]), attempting to write 0x%08x, read back 0x%08x\n",  
            tmpreg, dv_reg->pfx, j, wdata, rdata);
        if (j == 0) {
            VPRINTF(LOW,".");
        } else {
            VPRINTF(LOW,".");
        }

        if (rdata != expdata) {
            errs++;
            VPRINTF(ERROR,"\nMismatch at addr 0x%x (%s[%d]), read data 0x%08x != expected data 0x%08x --\n",  
                tmpreg, dv_reg->pfx, j, rdata, expdata); 
        } 
    }

    return errs;
}


void main() {

    srand(seed);
    // long seed = atoi(getenv("PLAYBOOK_RANDOM_SEED")); // FIXME. Currently always 0

    VPRINTF(LOW,"--------------------------------------\n");
    VPRINTF(LOW," DV Smoke Test With Basic Read/Write!!\n");
    VPRINTF(LOW,"--------------------------------------\n");

    VPRINTF(LOW,"INFO. Using random seed = %d\n\n", seed);

    VPRINTF(LOW,"\n** Phase 1. Basic random writes and reads **\n"); 

    if (rst_count == 0) {

        // Write data entry registers only - skipping control 
        VPRINTF(LOW,"\n-- Performing WR followed by RD to data (non-control) registers only; printing once per prefix --\n\n"); 

        for (int i = 0; i < DV_PFX_COUNT; i++) {
            if (str_contains(dv_regs[i].pfx, "CTRL"))
                continue; 
            err_count += wr_regs_per_pfx(&dv_regs[i], DV_ONES);
        }

        // Write only control registers 
        VPRINTF(LOW,"\n\n-- Performing WR followed by RD to control (non-data) registers only; printing once per prefix --\n\n"); 

        for (int i = 0; i < DV_PFX_COUNT; i++) {
            if (!str_contains(dv_regs[i].pfx, "CTRL"))
                continue; 
            err_count += wr_regs_per_pfx(&dv_regs[i], 0x1);
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
