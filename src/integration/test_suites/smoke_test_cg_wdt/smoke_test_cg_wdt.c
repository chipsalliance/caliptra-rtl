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
#include "clk_gate.h"

volatile char*    stdout           = (char *)STDOUT;
volatile uint32_t intr_count       = 0;
volatile uint32_t hmac_intr_status;
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

volatile uint32_t * soc_ifc_error_status = (uint32_t *) CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R;
volatile uint32_t soc_error_status_int;

volatile uint32_t * clear_secrets = (uint32_t *) CLP_KV_REG_CLEAR_SECRETS;

void main() {
    
    volatile uint32_t * soc_ifc_flow_status = (uint32_t *) CLP_SOC_IFC_REG_CPTRA_FLOW_STATUS;
    volatile uint32_t * soc_ifc_clk_gating_en = (uint32_t *) CLP_SOC_IFC_REG_CPTRA_CLK_GATING_EN;
    uint32_t mitb0 = 0x00000500;
    uint32_t mie_timer0_ext_int_en = 0x20000800;
    //uint32_t mie_machinetimer_en = 0x00000080;
    //uint32_t mie_external_int_en = 0x00000800;

    printf("----------------------------------\n");
    printf(" CLK GATING + WDT smoke test !!\n"   );
    printf("----------------------------------\n");

    // Call interrupt init
    init_interrupts();

    //----------------------------------------------------
    //Clks shut off, core asleep, WDT running
    //1. soc_ifc_error_intr triggered. Core wakes up after internal timer0 expires and services intr
    //2. Fatal error is injected - check that clks are enabled again
    //3. Core asleep, scan mode enabled - check that KV regs are flushed
    //----------------------------------------------------
    
    //Enable clk gating
    VPRINTF(LOW, "Enabling clk gating\n====================\n");
    SEND_STDOUT_CTRL(0xf2); 

    if (rst_count == 0) {

        //Enable SOC notif interrupt
        *soc_intr_en = SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_WDT_TIMER1_TIMEOUT_EN_MASK | SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_WDT_TIMER2_TIMEOUT_EN_MASK;

        //Enable WDT timer1
        *wdt_timer1_en = SOC_IFC_REG_CPTRA_WDT_TIMER1_EN_TIMER1_EN_MASK;
        *wdt_timer1_period_0 = 0x00000100;
        *wdt_timer1_period_1 = 0x00000000;
        // *wdt_timer2_period_0 = 0x0000FFFF;
        // *wdt_timer2_period_1 = 0x00000000;

        //============= Case 1 ================
        VPRINTF(LOW, "WDT t1 intr\n");
        set_mit0_and_halt_core(mitb0, mie_timer0_ext_int_en);

        //Core wakes up and services timer1 intr
        VPRINTF(LOW, "Core is awake\n====================\n");

        //while ((*soc_ifc_error_status & SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_WDT_TIMER1_TIMEOUT_STS_MASK) == 1);
        soc_error_status_int = *soc_ifc_error_status;
        while (soc_error_status_int == SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_WDT_TIMER1_TIMEOUT_STS_MASK) {
            soc_error_status_int = *soc_ifc_error_status;
        }

        //============= Case 2 ================
        //Inject fatal error (after some delay)
        VPRINTF(LOW, "Cptra_f_err injection\n====================\n");
        SEND_STDOUT_CTRL(0xeb);

        set_mit0_and_halt_core(mitb0, mie_timer0_ext_int_en);

        //Check that clks wake up and core wakes up later due to internal timer0

        //============= Case 3 ================
        //Enable scan mode (after some delay)
        VPRINTF(LOW, "Scan mode enabled\n====================\n");
        SEND_STDOUT_CTRL(0xef);

        set_mit0_and_halt_core(mitb0, mie_timer0_ext_int_en);
        
        // //KV regs should be flushed

        //Disable scan mode
        VPRINTF(LOW, "Scan mode disabled\n====================\n");
        SEND_STDOUT_CTRL(0xf0);

        //============= Case 4 ================
        //Set debug mode value to 1
        *clear_secrets = 0x00000002;

        //Enable ss tran after some delay
        VPRINTF(LOW, "Debug mode unlocked\n====================\n");
        SEND_STDOUT_CTRL(0xfa);

        set_mit0_and_halt_core(mitb0, mie_timer0_ext_int_en);

        //Disable ss tran
        VPRINTF(LOW, "Debug mode locked\n====================\n");
        SEND_STDOUT_CTRL(0xf9); 

        //============= Case 5 ================  
        //cg enabled, issue warm reset
        VPRINTF(LOW, "Issue warm reset\n====================\n");
        rst_count++;
        SEND_STDOUT_CTRL(0xf6);
    }
    else if(rst_count == 1) {
        //Enable internal timer0
        __asm__ volatile ("csrwi    %0, %1" \
                        : /* output: none */        \
                        : "i" (0x7d2), "i" (0x00)  /* input : immediate  */ \
                        : /* clobbers: none */);

        //Set internal timer0 upper bound
        __asm__ volatile ("csrw    %0, %1" \
                        : /* output: none */        \
                        : "i" (0x7d3), "r" (mitb0)   /* input : immediate  */ \
                        : /* clobbers: none */);

        //Set internal timer0 control (halt_en = 1, enable = 1)
        __asm__ volatile ("csrwi    %0, %1" \
                        : /* output: none */        \
                        : "i" (0x7d4), "i" (0x03)  /* input : immediate  */ \
                        : /* clobbers: none */);
            
        //Set machine intr enable reg (mie) - enable internal timer0 intr
        __asm__ volatile ("csrw    %0, %1" \
                        : /* output: none */        \
                        : "i" (0x304), "r" (mie_timer0_ext_int_en)  /* input : immediate  */ \
                        : /* clobbers: none */);

        //Set mstatus reg - enable mie
        __asm__ volatile ("csrwi    %0, %1" \
                        : /* output: none */        \
                        : "i" (0x300), "i" (0x08)  /* input : immediate  */ \
                        : /* clobbers: none */);

        VPRINTF(LOW, "Issue random warm reset while core is asleep\n====================\n");
        rst_count++;
        SEND_STDOUT_CTRL(0xee);

        //Halt the core
        __asm__ volatile ("csrwi    %0, %1" \
                    : /* output: none */        \
                    : "i" (0x7c6), "i" (0x03)  /* input : immediate  */ \
                    : /* clobbers: none */);

    

    }
    else {
        //WDT independent mode:
        //Enable WDT timer1
        *wdt_timer1_en = SOC_IFC_REG_CPTRA_WDT_TIMER1_EN_TIMER1_EN_MASK;
        *wdt_timer1_period_0 = 0x00000100;
        *wdt_timer1_period_1 = 0x00000000;
        //Enable WDT timer2
        *wdt_timer2_en = SOC_IFC_REG_CPTRA_WDT_TIMER2_EN_TIMER2_EN_MASK;
        *wdt_timer2_period_0 = 0x00000100;
        *wdt_timer2_period_1 = 0x00000000;

        //============= Case 6 ================
        VPRINTF(LOW, "WDT independent mode and core is halted\n====================\n");
        set_mit0_and_halt_core(mitb0, mie_timer0_ext_int_en);
    }
}