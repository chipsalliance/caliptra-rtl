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

const int DV_WARM_RESET   = 0;
const int DV_COLD_RESET   = 1;

uint32_t wdata_values [DV_PFX_COUNT] [DV_MAXWIDTH]; 
uint32_t survived_values [DV_PFX_COUNT] [DV_MAXWIDTH]; 


void populate_wr_exp_values(uint32_t init_val) { 

    uint32_t curr = init_val; 

    VPRINTF(LOW, "\n-- Populating write data and expected values into arrays starting w/0x%x--\n", init_val);

    for (int i = 0; i < DV_PFX_COUNT; i++) {
        for (int j = 0; j < dv_regs[i].width; j++) {
            wdata_values[i][j] = curr;  
            survived_values[i][j] = wdata_values[i][j] & dv_regs[i].sticky_mask; 
            curr += 0x10;
        }
    }
    VPRINTF(LOW, "\n-- Done with populating data --\n");
}    


void write_dv_regs() {

    volatile uint32_t * tmpreg;
    int pfx_count = sizeof(dv_regs)/sizeof(widereg_t);

    VPRINTF(LOW,"\n** Performing a WRITE to all registers (reporting once per prefix)**\n\n");

    // First write to non-control registers 
    for (int i = 0; i < pfx_count; i++) {
        if (is_ctrl_reg( &dv_regs[i] )) 
            continue;

        for (int j = 0; j < dv_regs[i].width; j++) {
            tmpreg = dv_regs[i].addr + j; 
            *tmpreg = wdata_values[i][j];

            if (j == 0) {
                VPRINTF(LOW,"\nINFO. For addr 0x%x (%s), attempting to write 0x%08x, expected survived value 0x%08x", 
                    tmpreg, dv_regs[i].pfx, wdata_values[i][j], survived_values[i][j]); 
            } else {
                VPRINTF(LOW,"."); 
            }
        }
    }

    // Then write only to control registers 
    for (int i = 0; i < pfx_count; i++) {
        if ( !is_ctrl_reg( &dv_regs[i] ) ) 
            continue;
        for (int j = 0; j < dv_regs[i].width; j++) {
            tmpreg = dv_regs[i].addr + j; 
            *tmpreg = wdata_values[i][j];

            if (j == 0) {
                VPRINTF(LOW,"\nINFO. For addr 0x%x (%s), attempting to write 0x%08x, expected survived value 0x%08x", 
                    tmpreg, dv_regs[i].pfx, wdata_values[i][j], survived_values[i][j]); 
            } else {
                VPRINTF(LOW,"."); 
            }
        }
    }

    VPRINTF(LOW, "\n-- Done writing dat to registers --\n");
}


int check_reset_values(int rst_type) {

    volatile uint32_t * tmpreg;
    int pfx_count = sizeof(dv_regs)/sizeof(widereg_t);

    for (int i = 0; i < pfx_count; i++) {                   
        for (int j = 0; j < dv_regs[i].width; j++) {      
            tmpreg = dv_regs[i].addr + j; 

            if (rst_type == DV_COLD_RESET) {
                if(*tmpreg != 0) { 
                    err_count++; 
                    VPRINTF(ERROR,"\nERROR. incorrect power-on value for addr 0x%x (%s)= 0x%08x (expected 0x%08x)\n", 
                        tmpreg, dv_regs[i].pfx, *tmpreg, dv_regs[i].rstval); 
                } else {
                    VPRINTF(LOW,".");
                }
            } else if (rst_type == DV_WARM_RESET) {
                if (*tmpreg != survived_values[i][j]) { 
                    err_count++; 
                    VPRINTF(ERROR,"\nERROR. incorrect warm-reset value for addr 0x%x (%s)= 0x%08x (expected 0x%08x)\n", 
                        tmpreg, dv_regs[i].pfx, *tmpreg, survived_values[i][j]);
                } else {
                    VPRINTF(LOW,".");
                }
            } else {
                VPRINTF(ERROR,"TEST ERROR. Unsupported reset type '%d'", (int) rst_type);
            } 
        }
    }
    VPRINTF(LOW,"\n");

    return err_count;
}


void main() {

    // long seed = atoi(getenv("PLAYBOOK_RANDOM_SEED")); // FIXME. Currently always 0

    if (rst_count == 0) {

        srand(seed);

        VPRINTF(LOW,"------------------------------------\n");
        VPRINTF(LOW," DV Smoke Test for Cold/Warm Reset !!\n");
        VPRINTF(LOW,"------------------------------------\n");

        VPRINTF(LOW,"\nINFO. Using random seed = %d\n\n", seed);

        populate_wr_exp_values(0x10000001);
        write_dv_regs();

        VPRINTF(LOW,"\n-- Issue warm reset --\n"); 
        rst_count++;
        SEND_STDOUT_CTRL(0xf6);

    } else if (rst_count == 1) {

        VPRINTF(LOW,"** Checking warm reset survived values **\n"); 

        populate_wr_exp_values(0x10000001);
        err_count = check_reset_values(DV_WARM_RESET);

        if (err_count == 0) {
            VPRINTF(LOW,"\n-- All good so far; moving onto next phase-- \n");
        } else {
            VPRINTF(LOW,"-- %d errors found in warm-reset test phase; proceeding to next phase -- \n", err_count);
        }

        populate_wr_exp_values(0x20000001);
        write_dv_regs();

        VPRINTF(LOW,"\n** Performing a WRITE to all registers again (reporting once per prefix)**\n\n");

        VPRINTF(LOW,"\n-- Issue cold reset --\n"); 
        rst_count++;
        SEND_STDOUT_CTRL(0xf5);

    } else {

        VPRINTF(LOW,"\n** Checking cold reset values **\n\n"); 

        err_count = check_reset_values(DV_COLD_RESET);

        if (err_count != 0) {
            VPRINTF(LOW,"** ERROR. Done w/test; %d errors found ** \n", err_count);
            SEND_STDOUT_CTRL(0x1);
        } 

        VPRINTF(LOW,"** Done w/test; no errors found ** \n");
        SEND_STDOUT_CTRL(0xff);
    }

}
