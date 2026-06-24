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
// directed_test_iccm_replay_block.c
// Verifies that after the autonomous ICCM hash completes, additional ICCM
// writes in the same boot cannot replay the measurement: PCR4 and PCR5
// must stay byte-for-byte equal to the snapshot taken right after the
// legitimate hash.

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "iccm_hash.h"
#include "printf.h"

volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count       = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

static void check_pcr_unchanged(uint32_t pcr_base, const uint32_t *snapshot,
                                uint32_t pcr_idx, uint8_t fail_cmd) {
    for (int i = 0; i < ICCM_HASH_PCR_DWORDS; i++) {
        volatile uint32_t *p = (volatile uint32_t *)pcr_base;
        if (p[i] != snapshot[i]) {
            VPRINTF(ERROR, "FAIL: PCR%u[%d] perturbed after post-done ICCM "
                           "write! got 0x%x expected 0x%x\n",
                    pcr_idx, i, p[i], snapshot[i]);
            SEND_STDOUT_CTRL(fail_cmd);
            while (1);
        }
    }
}

void main(void) {

    uint8_t fail_cmd = 0x1;

    VPRINTF(LOW, "-------------------------------------------------\n");
    VPRINTF(LOW, " ICCM Hash anti-replay (no re-arm after done)\n");
    VPRINTF(LOW, "-------------------------------------------------\n");

    init_interrupts();

    // Run the autonomous ICCM hash, wait for PCR4 to be written.
    VPRINTF(LOW, "Running default ICCM hash to populate PCR4/PCR5...\n");
    if (!run_default_iccm_hash()) {
        VPRINTF(ERROR, "FAIL: timed out waiting for PCR4 after ICCM hash\n");
        SEND_STDOUT_CTRL(fail_cmd);
        while (1);
    }

    // Snapshot both PCRs while measurement is fresh.
    uint32_t pcr4_snapshot[ICCM_HASH_PCR_DWORDS];
    uint32_t pcr5_snapshot[ICCM_HASH_PCR_DWORDS];
    snapshot_pcr(CLP_PV_REG_PCR_ENTRY_4_0, pcr4_snapshot);
    snapshot_pcr(CLP_PV_REG_PCR_ENTRY_5_0, pcr5_snapshot);

    if (!check_pcr_nonzero(CLP_PV_REG_PCR_ENTRY_4_0, 4) ||
        !check_pcr_nonzero(CLP_PV_REG_PCR_ENTRY_5_0, 5)) {
        SEND_STDOUT_CTRL(fail_cmd);
        while (1);
    }
    VPRINTF(LOW, "PASS: PCR4 and PCR5 populated, snapshots taken\n");

    // Post-done ICCM writes -- must not re-arm measurement.
    VPRINTF(LOW, "Writing post-done pattern to ICCM (must be ignored)...\n");
    volatile uint32_t *iccm = (volatile uint32_t *)RV_ICCM_SADR;
    for (uint32_t i = 0; i < 32; i++) {
        iccm[i] = 0xA5A50000 + i;
    }

    // Re-write the ICCM lock (no-op, woset already 1) and give any
    // spurious re-trigger paths time to settle before re-checking PCRs.
    VPRINTF(LOW, "Re-writing INTERNAL_ICCM_LOCK (no-op)...\n");
    lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_ICCM_LOCK,
                 SOC_IFC_REG_INTERNAL_ICCM_LOCK_LOCK_MASK);
    for (volatile uint32_t i = 0; i < 200; i++);

    VPRINTF(LOW, "Verifying PCR4 unchanged...\n");
    check_pcr_unchanged(CLP_PV_REG_PCR_ENTRY_4_0, pcr4_snapshot, 4, fail_cmd);
    VPRINTF(LOW, "PASS: PCR4 unchanged after post-done ICCM activity\n");

    VPRINTF(LOW, "Verifying PCR5 unchanged...\n");
    check_pcr_unchanged(CLP_PV_REG_PCR_ENTRY_5_0, pcr5_snapshot, 5, fail_cmd);
    VPRINTF(LOW, "PASS: PCR5 unchanged after post-done ICCM activity\n");

    VPRINTF(LOW, "=== ICCM hash replay-block verified ===\n");
    SEND_STDOUT_CTRL(0xff);
    while (1);
}
