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
#include "riscv_hw_if.h"
#include "wdt.h"

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
volatile uint32_t * soc_intr_en         = (uint32_t *) CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R;

volatile uint32_t * wdt_timer2_en       = (uint32_t *) CLP_SOC_IFC_REG_CPTRA_WDT_TIMER2_EN;
volatile uint32_t * wdt_timer2_ctrl     = (uint32_t *) CLP_SOC_IFC_REG_CPTRA_WDT_TIMER2_CTRL;
volatile uint32_t * wdt_timer2_period_0 = (uint32_t *) CLP_SOC_IFC_REG_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD_0;
volatile uint32_t * wdt_timer2_period_1 = (uint32_t *) CLP_SOC_IFC_REG_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD_1;

volatile uint32_t * hw_error_fatal      = (uint32_t *) CLP_SOC_IFC_REG_CPTRA_HW_ERROR_FATAL;

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

void main() {
    VPRINTF(LOW, "---------------------------\n");
    VPRINTF(LOW, " WDT Smoke Test !!\n");
    VPRINTF(LOW, "---------------------------\n");

    //Enable SOC notif interrupt
    *soc_intr_en = SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_WDT_TIMER1_TIMEOUT_EN_MASK | SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_WDT_TIMER2_TIMEOUT_EN_MASK;
    
    //Call interrupt init
    init_interrupts();
    
    if(rst_count == 0) {
        VPRINTF(LOW, "Cascaded mode\n");
        //Enable WDT timer1
        *wdt_timer1_en = SOC_IFC_REG_CPTRA_WDT_TIMER1_EN_TIMER1_EN_MASK;
        set_t1_period(0x00000040, 0x00000000);
        
        VPRINTF(LOW, "Stall until timer1 times out\n");
        while (!(lsu_read_32(SOC_IFC_REG_CPTRA_WDT_STATUS_T1_TIMEOUT_MASK)));
        VPRINTF(LOW, "WDT T1 timed out as expected\n");
        *wdt_timer1_ctrl = SOC_IFC_REG_CPTRA_WDT_TIMER1_CTRL_TIMER1_RESTART_MASK;

        //Set timer1 period to default to avoid immediate time out
        set_default_t1_period();
        
    
        VPRINTF(LOW, "Independent mode - both timers enabled\n");
        //Enable WDT timer1
        *wdt_timer2_en = SOC_IFC_REG_CPTRA_WDT_TIMER2_EN_TIMER2_EN_MASK;
        set_t2_period(0x00000040, 0x00000000);
        
        VPRINTF(LOW, "Stall until timer2 times out\n");
        //Release forced timer periods from tb so test can set them
        SEND_STDOUT_CTRL(0xf1);

        VPRINTF(LOW, "Cascaded mode with timer2 timeout\n");
        *wdt_timer2_en = 0x0;
        *wdt_timer1_ctrl = 0x1; //restart counter so timer1 can start counting
        
        rst_count++; //Increment count so when NMI is processed we advance in the test
        set_t1_period(0x00000040, 0x00000000);
        

        VPRINTF(LOW, "Stall until timer1 times out\n");
        VPRINTF(LOW, "Stall until timer2 times out\n");

        
    }
    else if(rst_count == 1) {
        //Issue warm reset after NMI as per spec
        VPRINTF(LOW, "Issuing reset in response to NMI (t2 timeout)\n");
        rst_count++;
        SEND_STDOUT_CTRL(0xf6);
    }
    else {
        VPRINTF(LOW, "Independent mode - timer2 enabled, timer1 disabled\n");
        *wdt_timer2_en = SOC_IFC_REG_CPTRA_WDT_TIMER2_EN_TIMER2_EN_MASK;
        set_t2_period(0x00000040, 0x00000000);
        
        VPRINTF(LOW, "Stall until timer2 times out\n");
        while (!(lsu_read_32(SOC_IFC_REG_CPTRA_WDT_STATUS_T2_TIMEOUT_MASK)));
        VPRINTF(LOW, "WDT T2 timed out as expected\n")
        //Release forced timer periods from tb so test can set them
        // SEND_STDOUT_CTRL(0xf1);

        //Write 1 to clear HW fatal error register
        if ((*hw_error_fatal && SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_NMI_PIN_MASK) == 1) {
            *hw_error_fatal = SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_NMI_PIN_MASK;
        }
        else {
            VPRINTF(ERROR, "Did not see expected hw fatal error!");
        }
    }
}
