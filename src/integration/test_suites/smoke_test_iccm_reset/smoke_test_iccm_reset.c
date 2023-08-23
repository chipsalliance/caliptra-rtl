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
volatile uint32_t iter __attribute__((section(".dccm.persistent"))) = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

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

extern uintptr_t iccm_code0_start, iccm_code0_end;
volatile uint32_t * soc_ifc_fw_update_reset = (uint32_t *) (CLP_SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET);
void exec_iccm (void) __attribute__ ((aligned(4),section (".data_iccm0")));

void main() {
    uint32_t * ICCM = (uint32_t *) RV_ICCM_SADR;
    uint32_t * code_word = 0;
    uint32_t * iccm_dest = ICCM;
    void (* iccm_fn) (void) = (void*) ICCM;
    VPRINTF(LOW,"---------------------------\n");
    VPRINTF(LOW," Smoke test ICCM/DCCM + reset !!\n");
    VPRINTF(LOW,"---------------------------\n");

    rst_count++;

    //Call interrupt init
    init_interrupts();
    if(rst_count == 1) {

        code_word = (uint32_t *) &iccm_code0_start;
        VPRINTF(LOW, "Copying code from %x [through %x] to %x\n", (uintptr_t) code_word, &iccm_code0_end, (uintptr_t) iccm_dest);
        while (code_word < (uint32_t *) &iccm_code0_end) {
            VPRINTF(ALL, "at %x: %x\n", (uintptr_t) code_word, *code_word);
            *iccm_dest++ = *code_word++;
        }

        VPRINTF(LOW, "Execute function from ICCM\n");
        iccm_fn();
        
        //Issue warm reset
        VPRINTF(LOW, "Issue warm reset\n");
        SEND_STDOUT_CTRL(0xf6);
    }
    else if(rst_count == 2) {
        VPRINTF(LOW, "Execute function from ICCM after warm reset\n");
        iccm_fn();

        //Issue cold reset
        VPRINTF(LOW, "Issue cold reset\n");
         SEND_STDOUT_CTRL(0xf5);

    }
    else if(rst_count == 3) {
        VPRINTF(LOW, "Execute function from ICCM after cold reset\n");
        iccm_fn();

        //Issue fw update reset
        VPRINTF(LOW, "Issue core only reset\n");
        *soc_ifc_fw_update_reset = SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET_CORE_RST_MASK;
    }
    else if (rst_count == 4) {
        VPRINTF(LOW, "Execute function from ICCM after core reset\n");
        iccm_fn();
    }

    return;
}

void exec_iccm (void) {
    VPRINTF (LOW, "In exec_iccm function, before incrementing = %d\n", iter);
    iter++;
    VPRINTF (LOW, "In exec_iccm function, after incrementing = %d\n", iter);
}
