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

#include "wdt.h"
#include "riscv_hw_if.h"
#include "caliptra_defines.h"
#include "printf.h"

void set_t1_period(uint32_t t1_period_0, uint32_t t1_period_1) {
    //Set timer1 period
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD_0, t1_period_0);
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD_1, t1_period_1);
}

void set_t2_period(uint32_t t2_period_0, uint32_t t2_period_1) {
    //Set timer2 period
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD_0, t2_period_0);
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD_1, t2_period_1);
}

void set_default_t1_period() {
    //Set default timer1 period
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD_0, 0xffffffff);
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD_1, 0xffffffff);
}

void set_default_t2_period() {
    //Set default timer2 period
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD_0, 0xffffffff);
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD_1, 0xffffffff);
}

void service_t1_intr() {
    while (!(lsu_read_32(CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R) & SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_WDT_TIMER1_TIMEOUT_STS_MASK));
    //Clear timer1 intr
    lsu_write_32(CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R, SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_WDT_TIMER1_TIMEOUT_STS_MASK);
}

void service_t2_intr() {
    while (!(lsu_read_32(CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R) & SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_WDT_TIMER2_TIMEOUT_STS_MASK));
    //Clear timer2 intr
    lsu_write_32(CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R, SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_WDT_TIMER2_TIMEOUT_STS_MASK);
}

void configure_wdt_cascade(uint32_t t1_period_0, uint32_t t1_period_1, uint32_t t2_period_0, uint32_t t2_period_1) {

    set_t1_period(t1_period_0, t1_period_1);
    set_t2_period(t2_period_0, t2_period_1);

    //Enable timer1 to start cascade mode
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_WDT_TIMER1_EN, 1);

    //Restart timer1
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_WDT_TIMER1_CTRL, SOC_IFC_REG_CPTRA_WDT_TIMER1_CTRL_TIMER1_RESTART_MASK);
}

void configure_wdt_independent(enum wdt_independent_mode_e mode, uint32_t t1_period_0, uint32_t t1_period_1, uint32_t t2_period_0, uint32_t t2_period_1) {
    if (mode == BOTH_TIMERS_DIS) {
        VPRINTF(LOW, "Disabling both timers in independent mode\n");
        lsu_write_32(CLP_SOC_IFC_REG_CPTRA_WDT_TIMER1_EN, 0);
        lsu_write_32(CLP_SOC_IFC_REG_CPTRA_WDT_TIMER2_EN, 0);
    }
    else if (mode == T1_DIS_T2_EN) {
        VPRINTF(LOW, "Enabling only timer2 in independent mode\n");
        set_t2_period(t2_period_0, t2_period_1);
        lsu_write_32(CLP_SOC_IFC_REG_CPTRA_WDT_TIMER2_EN, 1);
        lsu_write_32(CLP_SOC_IFC_REG_CPTRA_WDT_TIMER2_CTRL, 1);

    }
    else if (mode == BOTH_TIMERS_EN) {
        VPRINTF(LOW, "Enabling both timers in independent mode\n");
        set_t1_period(t1_period_0, t1_period_1);
        set_t2_period(t2_period_0, t2_period_1);

        //Enable timer1 and timer2
        lsu_write_32(CLP_SOC_IFC_REG_CPTRA_WDT_TIMER1_EN, 1);
        lsu_write_32(CLP_SOC_IFC_REG_CPTRA_WDT_TIMER2_EN, 1);

        //Restart timer1 and timer2
        lsu_write_32(CLP_SOC_IFC_REG_CPTRA_WDT_TIMER1_CTRL, 1);
        lsu_write_32(CLP_SOC_IFC_REG_CPTRA_WDT_TIMER2_CTRL, 1);
    }

}