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

#include "clk_gate.h"
#include "riscv_hw_if.h"
#include "caliptra_defines.h"
#include "printf.h"

void set_mit0_and_halt_core(uint32_t mitb0, uint32_t mie_en) {
    VPRINTF(LOW, "Enabling internal timer0 and halting core\n");
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
                        : "i" (0x304), "r" (mie_en)  /* input : immediate  */ \
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
}