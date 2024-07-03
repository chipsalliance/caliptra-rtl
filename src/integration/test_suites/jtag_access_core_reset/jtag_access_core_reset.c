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
#include "caliptra_isr.h"
#include "riscv-csr.h"
#include "soc_ifc.h"
#include <stdint.h>
#include "printf.h"

volatile char*    stdout           = (char *)STDOUT;
volatile uint32_t intr_count = 0;
volatile uint32_t rst_count __attribute__((section(".dccm.persistent"))) = 0;
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

volatile uint32_t *soc_ifc_fw_update_reset = (uint32_t *) (CLP_SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET);
volatile uint32_t *soc_ifc_bootfsm_go = (uint32_t *) (CLP_SOC_IFC_REG_CPTRA_BOOTFSM_GO);

void main() {
    uint32_t * code_word = 0;
    VPRINTF(LOW,"--------------------------------------\n");
    VPRINTF(LOW," Test JTAG access during core reset !!\n");
    VPRINTF(LOW,"--------------------------------------\n");

    rst_count++;

    init_interrupts();

    if (rst_count == 1) {
        //Issue fw update reset
        VPRINTF(LOW, "Wait for disabling FSM GO\n");
        while(*soc_ifc_bootfsm_go) {}
        VPRINTF(LOW, "FSM GO disabled\n\n");

        VPRINTF(LOW, "Issue core only reset\n");
        *soc_ifc_fw_update_reset = SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET_CORE_RST_MASK;
    }
    else if (rst_count == 2) {
        VPRINTF(LOW, "Reset successful\n");

        VPRINTF(LOW, "Write to mbox to indicate test finish\n");
        lsu_write_32(CLP_MBOX_CSR_MBOX_UNLOCK, MBOX_CSR_MBOX_UNLOCK_UNLOCK_MASK);
        while((lsu_read_32(CLP_MBOX_CSR_MBOX_LOCK) & MBOX_CSR_MBOX_LOCK_LOCK_MASK) == 1);
        lsu_write_32(CLP_MBOX_CSR_MBOX_CMD,0x12345678);
        lsu_write_32(CLP_MBOX_CSR_MBOX_DLEN, 1);
        lsu_write_32(CLP_MBOX_CSR_MBOX_DATAIN, 1);
        lsu_write_32(CLP_MBOX_CSR_MBOX_EXECUTE, MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK);

        VPRINTF(LOW, "Hand over flow control\n");
        while(1) {}
    }

    return;
}
