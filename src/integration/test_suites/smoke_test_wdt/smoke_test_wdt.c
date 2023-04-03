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
#include "printf.h"

volatile char*    stdout           = (char *)STDOUT;
volatile uint32_t intr_count = 0;
volatile uint32_t rst_count __attribute__((section(".dccm.persistent"))) = 0;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile uint32_t * wdt_timer1_en       = (uint32_t *) CLP_SOC_IFC_REG_CPTRA_WDT_TIMER1_EN;
volatile uint32_t * wdt_timer1_ctrl     = (uint32_t *) CLP_SOC_IFC_REG_CPTRA_WDT_TIMER1_CTRL;
volatile uint32_t * wdt_timer1_period_0 = (uint32_t *) CLP_SOC_IFC_REG_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD_0;
volatile uint32_t * wdt_timer1_period_1 = (uint32_t *) CLP_SOC_IFC_REG_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD_1;
volatile uint32_t * soc_intr_en         = (uint32_t *) CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R;

volatile uint32_t * wdt_timer2_en       = (uint32_t *) CLP_SOC_IFC_REG_CPTRA_WDT_TIMER2_EN;
volatile uint32_t * wdt_timer2_ctrl     = (uint32_t *) CLP_SOC_IFC_REG_CPTRA_WDT_TIMER2_CTRL;
volatile uint32_t * wdt_timer2_period_0 = (uint32_t *) CLP_SOC_IFC_REG_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD_0;
volatile uint32_t * wdt_timer2_period_1 = (uint32_t *) CLP_SOC_IFC_REG_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD_1;

volatile uint32_t * hw_error_fatal      = (uint32_t *) CLP_SOC_IFC_REG_CPTRA_HW_ERROR_FATAL;

void main() {
    VPRINTF(LOW, "---------------------------\n");
    VPRINTF(LOW, " WDT Smoke Test !!\n");
    VPRINTF(LOW, "---------------------------\n");

    //Enable SOC notif interrupt
    *soc_intr_en = SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_WDT_TIMER1_TIMEOUT_EN_MASK | SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_WDT_TIMER2_TIMEOUT_EN_MASK;
    
    //Call interrupt init
    init_interrupts();
    
    if(rst_count == 0) {
        VPRINTF(LOW, "Cascaded mode\n");
        //Enable WDT timer1
        *wdt_timer1_en = SOC_IFC_REG_CPTRA_WDT_TIMER1_EN_TIMER1_EN_MASK;
        *wdt_timer1_period_0 = 0x00000040;
        *wdt_timer1_period_1 = 0x00000000;
        VPRINTF(LOW, "Stall until timer1 times out\n");
        *wdt_timer1_ctrl = SOC_IFC_REG_CPTRA_WDT_TIMER1_CTRL_TIMER1_RESTART_MASK;

        //Set timer1 period to something else to avoid immediate time out
        *wdt_timer1_period_0 = 0x0000FFFF;
        *wdt_timer1_period_1 = 0x00000000;
        
    
        VPRINTF(LOW, "Independent mode\n");
        //Enable WDT timer1
        *wdt_timer2_en = SOC_IFC_REG_CPTRA_WDT_TIMER2_EN_TIMER2_EN_MASK;
        *wdt_timer2_period_0 = 0x00000040;
        *wdt_timer2_period_1 = 0x00000000;
        
        VPRINTF(LOW, "Stall until timer2 times out\n");
        //Release forced timer periods from tb so test can set them
        SEND_STDOUT_CTRL(0xf1);

        VPRINTF(LOW, "Cascaded mode with timer2 timeout\n");
        *wdt_timer2_en = 0x0;
        *wdt_timer1_ctrl = 0x1; //restart counter so timer1 can start counting
        
        rst_count++; //Increment count so when NMI is processed we advance in the test
        *wdt_timer1_period_0 = 0x00000040;
        *wdt_timer1_period_1 = 0x00000000;
        

        VPRINTF(LOW, "Stall until timer1 times out");
        VPRINTF(LOW, "Stall until timer2 times out");

        
    }
    else if(rst_count == 1) {
        //Issue warm reset after NMI as per spec
        rst_count++;
        SEND_STDOUT_CTRL(0xf6);
    }
    else {
        //Write 1 to clear HW fatal error register
        *hw_error_fatal = 0x00000001;
    }
}
