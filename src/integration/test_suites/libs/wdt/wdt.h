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

#ifndef WDT_H
    #define WDT_H_H

#include "caliptra_defines.h"
#include "caliptra_reg.h"
#include "riscv_hw_if.h"

/* --------------- symbols/typedefs --------------- */
enum wdt_independent_mode_e {
    BOTH_TIMERS_DIS = 0x0,
    T1_DIS_T2_EN    = 0x1,
    BOTH_TIMERS_EN  = 0x2
};

/* --------------- Function Prototypes --------------- */

void set_t1_period(uint32_t t1_period_0, uint32_t t1_period_1);
void set_t2_period(uint32_t t2_period_0, uint32_t t2_period_1);
void set_default_t1_period();
void set_default_t2_period();

void service_t1_intr();
void service_t2_intr();

void wdt_independent_both_timers_en(uint32_t t1_period_0, uint32_t t1_period_1, uint32_t t2_period_0, uint32_t t2_period_1);
void wdt_independent_only_t1_en();
void wdt_independent_only_t2_en();
void configure_wdt_independent(enum wdt_independent_mode_e mode, uint32_t t1_period_0, uint32_t t1_period_1, uint32_t t2_period_0, uint32_t t2_period_1);
void configure_wdt_cascade(uint32_t t1_period_0, uint32_t t1_period_1, uint32_t t2_period_0, uint32_t t2_period_1);

#endif