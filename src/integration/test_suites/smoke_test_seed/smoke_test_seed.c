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
#include "veer-csr.h"
#include "riscv_hw_if.h"
#include <string.h>
#include <stdint.h>
#include "printf.h"


//int whisperPrintf(const char* format, ...);
//#define ee_printf whisperPrintf


volatile char* stdout = (char *)STDOUT;
volatile uint32_t intr_count;
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

extern uintptr_t stack_start;
extern uintptr_t STACK;

void main(void) {
        int argc=0;
        char *argv[1];

        uint32_t * DCCM = (uint32_t *) RV_DCCM_SADR;

        uint32_t * data_word = 0;
        uint32_t * dccm_dest = DCCM;

        VPRINTF(LOW, "---\nCaliptra Seed Smoke Test!!\n---\n");

        // Setup the interrupt CSR configuration
        init_interrupts();

        // Initialize the globals
        intr_count = 0;

        // Check ICCM_LOCK is not currently set
        if (lsu_read_32(CLP_SOC_IFC_REG_INTERNAL_ICCM_LOCK) & SOC_IFC_REG_INTERNAL_ICCM_LOCK_LOCK_MASK == SOC_IFC_REG_INTERNAL_ICCM_LOCK_LOCK_MASK) {
            VPRINTF(ERROR, "ERROR: ICCM_LOCK set unexpectedly!\n");
            SEND_STDOUT_CTRL( 0x1);
            while(1);
        }

        // Copy code section from Mailbox to DCCM
        while(!(lsu_read_32(CLP_MBOX_CSR_MBOX_LOCK) & MBOX_CSR_MBOX_LOCK_LOCK_MASK));
        data_word = (uint32_t *) MBOX_DIR_BASE_ADDR;
        VPRINTF(LOW, "Copying code from %x [through %x] to %x\n", (uintptr_t) data_word, MBOX_DIR_BASE_ADDR + 0x80, (uintptr_t) dccm_dest);
        while (data_word < (uint32_t *) (MBOX_DIR_BASE_ADDR + 0x80)) {
            VPRINTF(ALL, "at %x: %x\n", (uintptr_t) data_word, *data_word);
            *dccm_dest++ = *data_word++;
        }

        // Check interrupt count (die if !0)
        if (intr_count) {
            VPRINTF(ERROR, "ERROR: Detected interrupt while copying code to DCCM!\n");
            SEND_STDOUT_CTRL( 0x1);
        }

        // Check that DCCM can still be written/read
        if ((uint32_t)(&STACK) + 4 <= RV_DCCM_EADR) {
            uint32_t dccm_test_val = lsu_read_32((uintptr_t)(&STACK)+4);
            VPRINTF(LOW, "Test DCCM at addr: 0x%x\n", (uintptr_t)(&STACK)+4);
            dccm_test_val ^= 0xAAAAAAAA;
            lsu_write_32((uintptr_t)(&STACK)+4, dccm_test_val);
            if (lsu_read_32((uintptr_t)(&STACK)+4) != dccm_test_val) {
                VPRINTF(ERROR, "ERROR: Rd data (0x%x) after wr to DCCM does not match exp (0x%x)!\n", lsu_read_32((uintptr_t)(&STACK)+4), dccm_test_val);
                SEND_STDOUT_CTRL(0x1);
            } else {
                VPRINTF(LOW, "Rd data (0x%x) after DCCM wr matches exp (0x%x)!\n", lsu_read_32((uintptr_t)(&STACK)+4), dccm_test_val);
            }
        } else {
            VPRINTF(FATAL, "FATAL: Unable to test DCCM access because there is no unused space in DCCM (above STACK)!\n");
            SEND_STDOUT_CTRL(0x1);
        }

        return;
}
