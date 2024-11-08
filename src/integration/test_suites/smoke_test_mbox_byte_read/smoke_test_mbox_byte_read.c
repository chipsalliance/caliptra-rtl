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
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include <stdint.h>
//#include <stdlib.h>
#include "printf.h"
#include "caliptra_isr.h"

volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count       = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity             verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity             verbosity_g = MEDIUM;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

//#ifndef MY_RANDOM_SEED
//#define MY_RANDOM_SEED 17
//#endif // MY_RANDOM_SEED
//
//const long seed = MY_RANDOM_SEED; 

void main () {

    uint32_t data;
    uint8_t* read_addr;

    // Message
    VPRINTF(LOW, "----------------------------------\n");
    VPRINTF(LOW, " Caliptra Mbox SRAM DIR Smoke Test!!\n"    );
    VPRINTF(LOW, "----------------------------------\n");

//    VPRINTF(LOW,"\nINFO. Using random seed = %d\n", seed);
//    srand(seed);
//    VPRINTF(MEDIUM, "srand done\n")

    // Acquire Lock
    if (soc_ifc_mbox_acquire_lock(1)) {
        VPRINTF(ERROR, "ERROR: Failed to acquire mbox lock\n");
        SEND_STDOUT_CTRL( 0x1);
        while(1);
    }

    // Write data to fill mailbox
    for (data = CLP_MBOX_SRAM_BASE_ADDR; data < CLP_MBOX_SRAM_END_ADDR; data+=4) {
        // Data written is the address being written to
        lsu_write_32((uintptr_t) data, data);
        if ((data & 0xfff) == 0) {
            VPRINTF(MEDIUM, "Writing [0x%x] to addr [0x%x]\n", data, data)
        }
    }

    // Read back one byte at a time and check values
    read_addr = (uint8_t*) CLP_MBOX_SRAM_BASE_ADDR;
    while(read_addr <= (uint8_t*) CLP_MBOX_SRAM_END_ADDR) {
        if (((uintptr_t)read_addr & 0xfff) == 0) {
            VPRINTF(MEDIUM, "Reading from addr [0x%x]\n", read_addr)
        }
        // Data should match the address being read from
        if (*read_addr != (uint8_t)(((uintptr_t) read_addr)      )) {
            VPRINTF(ERROR, "ERROR: Data mismatch at addr [0x%x]. Exp [0x%x] got [0x%x]\n", (uintptr_t) read_addr, (uint8_t)(((uintptr_t) read_addr) >> 0 ), *read_addr);
            SEND_STDOUT_CTRL( 0x1);
            while(1);
        }
        read_addr++;
        if (*read_addr != (uint8_t)(((uintptr_t) read_addr) >>  8)) {
            VPRINTF(ERROR, "ERROR: Data mismatch at addr [0x%x]. Exp [0x%x] got [0x%x]\n", (uintptr_t) read_addr, (uint8_t)(((uintptr_t) read_addr) >> 8 ), *read_addr);
            SEND_STDOUT_CTRL( 0x1);
            while(1);
        }
        read_addr++;
        if (*read_addr != (uint8_t)(((uintptr_t) read_addr) >> 16)) {
            VPRINTF(ERROR, "ERROR: Data mismatch at addr [0x%x]. Exp [0x%x] got [0x%x]\n", (uintptr_t) read_addr, (uint8_t)(((uintptr_t) read_addr) >> 16), *read_addr);
            SEND_STDOUT_CTRL( 0x1);
            while(1);
        }
        read_addr++;
        if (*read_addr != (uint8_t)(((uintptr_t) read_addr) >> 24)) {
            VPRINTF(ERROR, "ERROR: Data mismatch at addr [0x%x]. Exp [0x%x] got [0x%x]\n", (uintptr_t) read_addr, (uint8_t)(((uintptr_t) read_addr) >> 24), *read_addr);
            SEND_STDOUT_CTRL( 0x1);
            while(1);
        }
        read_addr++;
    }

    // Force unlock
    lsu_write_32(CLP_MBOX_CSR_MBOX_UNLOCK, MBOX_CSR_MBOX_UNLOCK_UNLOCK_MASK);

}
