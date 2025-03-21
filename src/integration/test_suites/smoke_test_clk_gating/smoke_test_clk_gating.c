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

volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count       = 0;
volatile uint32_t  hmac_intr_status = 0;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

void main() {
    
    volatile uint32_t * soc_ifc_flow_status = (uint32_t *) CLP_SOC_IFC_REG_CPTRA_FLOW_STATUS;
    volatile uint32_t * soc_ifc_clk_gating_en = (uint32_t *) CLP_SOC_IFC_REG_CPTRA_CLK_GATING_EN;
    uint32_t mitb0 = 0x00000020;
    uint32_t mitb0_1 = 0x00000500;
    uint32_t mie_timer0_en = 0x20000000;
    uint32_t mie_machinetimer_en = 0x00000080;
    uint32_t mie_external_int_en = 0x00000800;
    uint32_t mie_timer0_ext_int_en = 0x20000800;

    printf("----------------------------------\n");
    printf(" CLK GATING smoke test !!\n"         );
    printf("----------------------------------\n");

    // Call interrupt init
    init_interrupts();

    //----------------------------------------------------
    //Wake up using internal timer0
    //----------------------------------------------------
        SEND_STDOUT_CTRL(0xf2); 
        //Set internal timer0 counter to 0
        printf("Wake up core using internal timer0\n");
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
                      : "i" (0x304), "r" (mie_timer0_en)  /* input : immediate  */ \
                      : /* clobbers: none */);

        //Set mstatus reg - enable mie
        __asm__ volatile ("csrwi    %0, %1" \
                      : /* output: none */        \
                      : "i" (0x300), "i" (0x08)  /* input : immediate  */ \
                      : /* clobbers: none */);

        //Halt the core
        __asm__ volatile ("csrwi    %0, %1" \
                      : /* output: none */        \
                      : "i" (0x7c6), "i" (0x03)  /* input : immediate  */ \
                      : /* clobbers: none */);

    //------------------------------------------------------
    //Set STDOUT to F8 until all cases below finish running.
    //This is to assert interrupts to the core for testing
    //------------------------------------------------------
        SEND_STDOUT_CTRL(0xf8); 

    //------------------------------------------------------
    //Wake up using software int
    //------------------------------------------------------
        printf("Wake up core using software interrupt\n");
        //Set machine intr enable reg (mie) - enable soft intr
        __asm__ volatile ("csrwi    %0, %1" \
                      : /* output: none */        \
                      : "i" (0x304), "i" (0x08)  /* input : immediate  */ \
                      : /* clobbers: none */);

        //Halt the core
        __asm__ volatile ("csrwi    %0, %1" \
                      : /* output: none */        \
                      : "i" (0x7c6), "i" (0x03)  /* input : immediate  */ \
                      : /* clobbers: none */);

    //------------------------------------------------------
    //Wake SOC up for AXI tx and core using timer int later
    //------------------------------------------------------
        printf("Wake up SOC clk on AXI txns and later wake up core using timer interrupt\n");
        //Machine intr enable reg (mie) - enable timer int 
        __asm__ volatile ("csrw    %0, %1" \
                      : /* output: none */        \
                      : "i" (0x304), "r" (mie_machinetimer_en)  /* input : immediate  */ \
                      : /* clobbers: none */);

        *soc_ifc_flow_status = SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_MB_PROCESSING_MASK;

        //Halt the core
        __asm__ volatile ("csrwi    %0, %1" \
                      : /* output: none */        \
                      : "i" (0x7c6), "i" (0x03)  /* input : immediate  */ \
                      : /* clobbers: none */);

    //------------------------------------------------------
    //Wake up using generic input wires and then soft intr
    //------------------------------------------------------
        printf("Wake up clks on change in generic_input_wires and later wake up core using software interrupt\n");
        //Set machine intr enable reg (mie) - enable soft intr
        __asm__ volatile ("csrwi    %0, %1" \
                      : /* output: none */        \
                      : "i" (0x304), "i" (0x08)  /* input : immediate  */ \
                      : /* clobbers: none */);

        //Halt the core
        __asm__ volatile ("csrwi    %0, %1" \
                      : /* output: none */        \
                      : "i" (0x7c6), "i" (0x03)  /* input : immediate  */ \
                      : /* clobbers: none */);

    //------------------------------------------------------
    //Wake up using JTAG accesses and then mit0 timer intr
    //------------------------------------------------------
        printf("Wake up clks on JTAG accesses and later wake up core on t0 timer intr\n");
        set_mit0(mitb0_1, mie_timer0_en);
        SEND_STDOUT_CTRL(0xe9); //Force dmi_reg_en input to clk_gate after a delay
        halt_core();

}

