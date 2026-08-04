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
// Directed test targeting the EXECUTE_UC -> EXECUTE_SOC mailbox transition:
// an extra out-of-order mbox_datain write is issued alongside the uC's
// mbox_status write to attempt overlapping mbox_protocol_sram_we/_rd in the
// same cycle. Reachability is judged by MboxProtocolWriteReadOverlap_C
// (cover) and MboxSramWriteNoEccCheck_A (assert) in caliptra_top_sva.sv,
// not by this test's PASS/FAIL. Build with -DRACE_DELAY_CYCLES=N to scan
// the alignment window across runs.
#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "riscv-csr.h"
#include "veer-csr.h"
#include "riscv_hw_if.h"
#include <stdint.h>
#include "printf.h"
#include "soc_ifc.h"

volatile char* stdout = (char *)STDOUT;
volatile uint32_t intr_count = 0;
volatile caliptra_intr_received_s cptra_intr_rcv = {0};
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

#define MBOX_DLEN_VAL 8

// Extra nops between the uC's mbox_status write and the out-of-order
// mbox_datain write, to scan the race window across runs
// (-DRACE_DELAY_CYCLES=N).
#ifndef RACE_DELAY_CYCLES
#define RACE_DELAY_CYCLES 0
#endif

void nmi_handler() {
    VPRINTF(FATAL, "NMI");
}

void main(void) {
    mbox_op_s op;
    uint32_t ii;
    enum mbox_fsm_e state;
    uint32_t mbox_data[2] = { 0xaaaaaaaa, 0xbbbbbbbb };

    VPRINTF(LOW, "----------------------------------\nSmoke Test Mailbox Protocol-Path ECC Race !!\n----------------------------------\n");

    lsu_write_32((uintptr_t) (CLP_SOC_IFC_REG_INTERNAL_NMI_VECTOR), (uint32_t) (nmi_handler));

    // Let the TB's SoC BFM push a mailbox command (as in smoke_test_mbox.c),
    // putting the mailbox into MBOX_EXECUTE_UC with uC as the receiver.
    soc_ifc_set_flow_status_field(SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_MB_PROCESSING_MASK);

    VPRINTF(LOW, "FW: Wait for SoC-issued command\n");
    while ((lsu_read_32(CLP_MBOX_CSR_MBOX_EXECUTE) & MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK) != MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK);

    op = soc_ifc_read_mbox_cmd();

    // Drain the incoming command payload.
    VPRINTF(LOW, "FW: Reading %u bytes from mailbox\n", op.dlen);
    while (op.dlen) {
        (void) soc_ifc_mbox_read_dataout_single();
        op.dlen = (op.dlen < 4) ? 0 : (op.dlen - 4);
    }

    // Write response payload.
    for (ii = 0; ii < MBOX_DLEN_VAL / 4; ii++) {
        lsu_write_32(CLP_MBOX_CSR_MBOX_DATAIN, mbox_data[ii]);
    }

    // Arms arc_MBOX_EXECUTE_UC_MBOX_EXECUTE_SOC, asserting rst_mbox_rdptr.
    soc_ifc_set_mbox_status_field(DATA_READY);

    for (volatile int d = 0; d < RACE_DELAY_CYCLES; d++) {
        __asm__ volatile ("nop");
    }

    // Out-of-order DATAIN write attempting to land in the transition cycle
    // so inc_wrptr and rst_mbox_rdptr both assert; benign no-op otherwise.
    lsu_write_32(CLP_MBOX_CSR_MBOX_DATAIN, 0x33333333);

    for (volatile int s = 0; s < 20; s++) {
        __asm__ volatile ("nop");
    }

    state = (lsu_read_32(CLP_MBOX_CSR_MBOX_STATUS) & MBOX_CSR_MBOX_STATUS_MBOX_FSM_PS_MASK) >> MBOX_CSR_MBOX_STATUS_MBOX_FSM_PS_LOW;
    VPRINTF(LOW, "FW: FSM state after race attempt: 0x%x\n", state);

    VPRINTF(LOW, "Completed protocol-path write/read-enable race attempt.\n");
    VPRINTF(LOW, "Reachability/failure must be judged from MboxProtocolWriteReadOverlap_C (cover) and MboxSramWriteNoEccCheck_A (assert) in caliptra_top_sva.sv, not from this test's PASS/FAIL alone.\n");

    SEND_STDOUT_CTRL(0xff);
    while (1) {
    }
}
