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
volatile uint32_t * soc_global_intr_en  = (uint32_t *) CLP_SOC_IFC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R;

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

void nmi_handler       (void);

void nmi_handler (void) {
    VPRINTF(LOW, "**** Entering NMI Handler ****\n");
    if (lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_ERROR_FATAL) & SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_NMI_PIN_MASK) {
        SEND_STDOUT_CTRL(0xf5);
    }
    else {
        VPRINTF(ERROR, "Unexpected entry into NMI handler function!\n");
    }

}

void main() {
    VPRINTF(LOW, "---------------------------\n");
    VPRINTF(LOW, " WDT Smoke Test with reset !!\n");
    VPRINTF(LOW, "---------------------------\n");

    //Enable SOC error interrupt
    *soc_global_intr_en = SOC_IFC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_MASK;
    *soc_intr_en = SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_WDT_TIMER1_TIMEOUT_EN_MASK | SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_WDT_TIMER2_TIMEOUT_EN_MASK;
    
    //Call interrupt init
    // init_interrupts();

    rst_count++;

    // Setup the NMI Handler
    lsu_write_32((uintptr_t) (CLP_SOC_IFC_REG_INTERNAL_NMI_VECTOR), (uint32_t) (nmi_handler));
    
    if(rst_count == 1) {
        VPRINTF(LOW, "Cascaded mode\n");
        configure_wdt_cascade(0x200, 0x00, 0xffffffff, 0xffffffff);
        
        VPRINTF(LOW, "Stall until timer1 times out\n");
        service_t1_intr();
        
        SEND_STDOUT_CTRL(0xf6);
    }
    else if (rst_count == 2) {
        //Release forced timer periods from tb so test can set them
        SEND_STDOUT_CTRL(0xf1);
        configure_wdt_cascade(0x200, 0x00, 0xffffffff, 0xffffffff);

        *wdt_timer1_ctrl = SOC_IFC_REG_CPTRA_WDT_TIMER1_CTRL_TIMER1_RESTART_MASK;

        service_t1_intr();
        SEND_STDOUT_CTRL(0xf5);
    }
    else if (rst_count == 3) {
        //Release forced timer periods from tb so test can set them
        SEND_STDOUT_CTRL(0xf1);
        // configure_wdt_cascade(0x200, 0x00, 0xffffffff, 0xffffffff);
        // set_t2_period(0x00000200, 0x00000000);
        configure_wdt_independent(BOTH_TIMERS_EN, 0x200, 0x00000000, 0x200, 0x00000000);
        //Enable WDT timer2
        // *wdt_timer2_en = SOC_IFC_REG_CPTRA_WDT_TIMER2_EN_TIMER2_EN_MASK;
    
        VPRINTF(LOW, "Independent mode - both timers enabled - warm rst\n");
        
        VPRINTF(LOW, "Stall until timer1 times out\n");
        service_t1_intr();
        //reset t1
        *wdt_timer1_en = 0;
        
        service_t2_intr();
        //reset t2
        *wdt_timer2_en = 0;
        
        SEND_STDOUT_CTRL(0xf6);
    }
    else if (rst_count == 4) {
        //Release forced timer periods from tb so test can set them
        SEND_STDOUT_CTRL(0xf1);
        // configure_wdt_cascade(0x200, 0x00, 0xffffffff, 0xffffffff);
        configure_wdt_independent(BOTH_TIMERS_EN, 0x200, 0x00000000, 0x200, 0x00000000);
    
        VPRINTF(LOW, "Independent mode - both timers enabled - cold rst\n");
        //Enable WDT timer1
        // *wdt_timer2_en = SOC_IFC_REG_CPTRA_WDT_TIMER2_EN_TIMER2_EN_MASK;
        // set_t2_period(0x00000200, 0x00000000);
        
        VPRINTF(LOW, "Stall until timer1 times out\n");
        service_t1_intr();
        *wdt_timer1_en = 0;

        VPRINTF(LOW, "Stall until timer2 times out\n");
        service_t2_intr();
        *wdt_timer2_en = 0;
        
        SEND_STDOUT_CTRL(0xf5);
    }
    else if (rst_count == 5) {
        //Release forced timer periods from tb so test can set them
        SEND_STDOUT_CTRL(0xf1);
        configure_wdt_cascade(0x200, 0x00, 0xffffffff, 0xffffffff);
        VPRINTF(LOW, "Cascaded mode with timer2 timeout - NMI - cold rst\n");
        *wdt_timer2_en = 0x0;
        *wdt_timer1_ctrl = 0x1; //restart counter so timer1 can start counting
        
        set_t2_period(0x00000200, 0x00000000);
        
        VPRINTF(LOW, "Stall until timer1 times out\n");
        VPRINTF(LOW, "Stall until timer2 times out\n");
        // while (!(lsu_read_32(SOC_IFC_REG_CPTRA_WDT_STATUS) & SOC_IFC_REG_CPTRA_WDT_STATUS_T2_TIMEOUT_MASK));
        // service_t2_intr();
        while(!(lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_ERROR_FATAL) & SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_NMI_PIN_MASK));

        //Not executed since handler issues reset
        //Issue warm reset after NMI as per spec
        // VPRINTF(LOW, "Issuing reset in response to NMI (t2 timeout)\n");
        // SEND_STDOUT_CTRL(0xf5);
    }
    else if (rst_count == 6) {
        //Release forced timer periods from tb so test can set them
        SEND_STDOUT_CTRL(0xf1);
        //Write 1 to clear HW fatal error register
        if ((*hw_error_fatal && SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_NMI_PIN_MASK) == 1) {
            VPRINTF(ERROR, "Cold rst should have reset hw_fatal_error nmi_pin!\n");
            SEND_STDOUT_CTRL(0x1);
        }

        VPRINTF(LOW, "Independent mode - timer2 enabled, timer1 disabled - warm rst\n");
        *wdt_timer2_en = SOC_IFC_REG_CPTRA_WDT_TIMER2_EN_TIMER2_EN_MASK;
        set_t2_period(0x00000200, 0x00000000);
        
        VPRINTF(LOW, "Stall until timer2 times out\n");
        service_t2_intr();
        *wdt_timer2_en = 0;
        
        SEND_STDOUT_CTRL(0xf6);

    }
    else if (rst_count == 7) {
        //Release forced timer periods from tb so test can set them
        SEND_STDOUT_CTRL(0xf1);
        VPRINTF(LOW, "Independent mode - timer2 enabled, timer1 disabled - cold rst\n");
        // *wdt_timer2_en = SOC_IFC_REG_CPTRA_WDT_TIMER2_EN_TIMER2_EN_MASK;
        // set_t2_period(0x00000200, 0x00000000);
        configure_wdt_independent(T1_DIS_T2_EN, 0x200, 0x00000000, 0x200, 0x00000000);
        
        VPRINTF(LOW, "Stall until timer2 times out\n");
        service_t2_intr();
        *wdt_timer2_en = 0;
        
        SEND_STDOUT_CTRL(0xf5);
    }
    else if (rst_count == 8) {
        //Issue warm reset during WDT operation
        //WDT cascade mode
        configure_wdt_cascade(0x37, 0x00, 0xffffffff, 0xffffffff);
        SEND_STDOUT_CTRL(0xf6);
    }
    else if (rst_count == 9) {
        //Issue cold reset during WDT operation
        configure_wdt_cascade(0x37, 0x00, 0xffffffff, 0xffffffff);
        SEND_STDOUT_CTRL(0xf5);
    }
    else if (rst_count == 10) {
        //Issue warm reset during WDT operation
        //WDT cascade mode
        configure_wdt_independent(BOTH_TIMERS_EN, 0x200, 0x00000000, 0x34, 0x00000000);
        SEND_STDOUT_CTRL(0xf6);
    }
    else if (rst_count == 11) {
        //Issue warm reset during WDT operation
        //WDT cascade mode
        configure_wdt_independent(BOTH_TIMERS_EN, 0x200, 0x00000000, 0x34, 0x00000000);
        SEND_STDOUT_CTRL(0xf5);
    }
    else if (rst_count == 12) {
        //Issue warm reset during WDT operation
        //WDT cascade mode
        configure_wdt_independent(T1_DIS_T2_EN, 0x200, 0x00000000, 0x200, 0x00000000);
        SEND_STDOUT_CTRL(0xf6);
    }
    else if (rst_count == 13) {
        //Issue warm reset during WDT operation
        //WDT cascade mode
        configure_wdt_independent(T1_DIS_T2_EN, 0x200, 0x00000000, 0x200, 0x00000000);
        SEND_STDOUT_CTRL(0xf5);
    }
    else {
        VPRINTF(LOW, "End of test\n");
    }
}
