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
// ---------------------------------------------------------------------
// Directed test attempting to reproduce a hypothesized hazard in the
// mailbox protocol/pointer path, structurally analogous to issue #1183
// (spurious mailbox SRAM ECC read-check on a write cycle), but triggered
// via the pointer-increment/reset path (mbox_protocol_sram_we/_rd) instead
// of the DMA path that #1183 originally exercised and that was fixed by
// commit 4b3636d8.
//
// Hazard hypothesis (from static RTL review of mbox.sv):
//   In MBOX_EXECUTE_UC, `inc_wrptr` (driven by a uC datain write, i.e. a
//   uC response being written back to the SoC) and the state-transition
//   arc that sets `rst_mbox_rdptr` (arc_MBOX_EXECUTE_UC_MBOX_EXECUTE_SOC,
//   driven by the uC's own mbox_status write reaching a non-CMD_BUSY
//   value) are computed in the same combinational block with no mutual
//   exclusion. If an out-of-order/extra `mbox_datain` write lands in the
//   exact same cycle the mbox_status write causes the transition arc to
//   fire, `mbox_protocol_sram_we` and `mbox_protocol_sram_rd` could both
//   assert in that cycle -- the same write/read-enable overlap signature
//   as #1183, via a different trigger.
//
// Test design note (IMPORTANT, found during test bring-up): an earlier
// version of this test used a uC-self-lock pattern (uC acquires the lock
// as its own "sender" and drives RDY_FOR_DATA -> EXECUTE_SOC itself, with
// no real SoC agent ever involved) to keep the test self-contained and to
// allow sweeping many attempts in a loop. That pattern was found, via a
// set of control experiments that progressively removed pieces of the
// sequence, to trigger a SEPARATE, unrelated, pre-existing X-propagation
// failure (mbox_csr.sv ERR_HWIF_IN) merely by reaching MBOX_EXECUTE_SOC
// that way -- independent of the race being tested and independent of
// unlock timing. That is a distinct bug outside the scope of this test
// and is NOT fixed here; it should be investigated separately (likely
// requires waveform-level root-causing of why the mailbox SRAM pre-load
// read on rst_mbox_rdptr can return X in that specific flow).
//
// To avoid that unrelated issue, this test instead uses the TB-driven SoC
// mailbox push flow (the same flow used by the first half of
// smoke_test_mbox.c, an established/passing test), so uC only ever acts
// as the intended RECEIVER of a SoC-issued command and reaches
// MBOX_EXECUTE_UC the normal way. The race is then attempted on the
// EXECUTE_UC -> EXECUTE_SOC transition (arc_MBOX_EXECUTE_UC_MBOX_EXECUTE_SOC,
// driven by the uC's own mbox_status write), matching this same
// established, working flow.
//
// Decisiveness note: the TB's SoC BFM issues a single command push per
// simulation run, so this test gets a single attempt at the race (unlike
// the DMA-path test, which could sweep many attempts against a
// self-contained flow). Exact single-cycle alignment from a RISC-V core
// issuing back-to-back stores is not guaranteed. Decisiveness is carried
// by the SVA cover property `MboxProtocolWriteReadOverlap_C` and assertion
// `MboxSramWriteNoEccCheck_A` in caliptra_top_sva.sv, NOT by any data
// check in this C code -- if the race is not hit on this single attempt,
// this test will still report PASS (a negative/inconclusive result), and
// reachability must be judged from the cover/assertion outcome.
// ---------------------------------------------------------------------
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

    // Let the TB's SoC BFM push a mailbox command (the same mechanism used
    // by smoke_test_mbox.c). This puts the mailbox into MBOX_EXECUTE_UC
    // with uC as the intended receiver -- avoiding the unrelated
    // uC-self-lock issue noted above.
    soc_ifc_set_flow_status_field(SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_MB_PROCESSING_MASK);

    VPRINTF(LOW, "FW: Wait for SoC-issued command\n");
    while ((lsu_read_32(CLP_MBOX_CSR_MBOX_EXECUTE) & MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK) != MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK);

    op = soc_ifc_read_mbox_cmd();

    // Drain the incoming command payload, matching smoke_test_mbox.c.
    VPRINTF(LOW, "FW: Reading %u bytes from mailbox\n", op.dlen);
    while (op.dlen) {
        (void) soc_ifc_mbox_read_dataout_single();
        op.dlen = (op.dlen < 4) ? 0 : (op.dlen - 4);
    }

    // Write response payload (as the uC receiver normally would).
    for (ii = 0; ii < MBOX_DLEN_VAL / 4; ii++) {
        lsu_write_32(CLP_MBOX_CSR_MBOX_DATAIN, mbox_data[ii]);
    }

    // Set data-ready status. Expected to cause
    // arc_MBOX_EXECUTE_UC_MBOX_EXECUTE_SOC to fire (soc_has_lock,
    // ~tap_mode, status != CMD_BUSY), asserting rst_mbox_rdptr on the next
    // evaluation while mbox_fsm_ps is still MBOX_EXECUTE_UC.
    soc_ifc_set_mbox_status_field(DATA_READY);

    // Extra, protocol-out-of-order DATAIN write, issued immediately
    // (back-to-back store, no artificial delay) to attempt to land in the
    // same cycle as the transition arc above. If it does, inc_wrptr and
    // rst_mbox_rdptr may both assert -- the hazard under test. If the FSM
    // has already transitioned to MBOX_EXECUTE_SOC by the time this write
    // lands, it is a benign no-op (inc_wrptr is only computed in
    // MBOX_RDY_FOR_DATA/MBOX_EXECUTE_UC).
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
