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
// directed_test_iccm_sha_acc_reuse.c
// Verifies that after an ICCM hash completes, FW can use the SHA-512
// accelerator normally (streaming-mode SHA-384). The HW must release the
// LOCK so a fresh acquire+hash flow works.
//
// Step 1: Run an ICCM hash to completion.
// Step 2: Acquire the lock again (proves it was released by HW).
// Step 3: Streaming SHA-384 of 4 known words -- digest must match expected.

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

// Streaming SHA-384 of {0x01, 0x02, 0x03, 0x04} as 16 LE bytes.
// Same digest as the inner ICCM digest in smoke_test_iccm_hash for the
// same 4-word input.
static const uint32_t expected_stream_digest[ICCM_HASH_PCR_DWORDS] = {
    0x1639dafc, 0xda504134, 0x9489cdac, 0xe63691bc,
    0x887ff539, 0xb61e635b, 0x0f5849e5, 0x85344d5b,
    0xb13af6fa, 0x55f6041a, 0x12fc1ef6, 0xc09cf6cf
};

// Wait for SHA acc STATUS.VALID
static uint8_t wait_sha_acc_valid(void) {
    uint32_t timeout = 20000;
    while (timeout--) {
        uint32_t reg = lsu_read_32(CLP_SHA512_ACC_CSR_STATUS);
        if (reg & SHA512_ACC_CSR_STATUS_VALID_MASK) return 1;
    }
    return 0;
}

void main(void) {

    uint8_t fail_cmd = 0x1;

    VPRINTF(LOW, "------------------------------------------\n");
    VPRINTF(LOW, " ICCM SHA Acc Reuse Test\n");
    VPRINTF(LOW, "------------------------------------------\n");

    init_interrupts();

    // Step 1: run ICCM hash to completion
    VPRINTF(LOW, "Running ICCM hash...\n");
    if (!run_default_iccm_hash()) {
        VPRINTF(ERROR, "FAIL: Timed out waiting for PCR4 after ICCM hash\n");
        SEND_STDOUT_CTRL(fail_cmd); while(1);
    }
    VPRINTF(LOW, "PASS: ICCM hash done\n");

    // Step 2: acquire lock again. If HW released it after ICCM hash, the
    // standard acquire flow succeeds.
    VPRINTF(LOW, "Re-acquiring SHA acc lock...\n");
    if (!acquire_sha_lock()) {
        VPRINTF(ERROR, "FAIL: Could not re-acquire SHA acc lock\n");
        SEND_STDOUT_CTRL(fail_cmd); while(1);
    }
    VPRINTF(LOW, "PASS: SHA acc lock re-acquired\n");

    // Step 3: streaming SHA-384 of {0x01..0x04}, verify digest
    VPRINTF(LOW, "Streaming SHA-384 to verify accelerator still works...\n");
    // SHA-384, no endian toggle, streaming (MODE.MODE=0, ENDIAN_TOGGLE=0)
    lsu_write_32(CLP_SHA512_ACC_CSR_MODE, 0);
    lsu_write_32(CLP_SHA512_ACC_CSR_DLEN, 16);
    lsu_write_32(CLP_SHA512_ACC_CSR_DATAIN, 0x00000001);
    lsu_write_32(CLP_SHA512_ACC_CSR_DATAIN, 0x00000002);
    lsu_write_32(CLP_SHA512_ACC_CSR_DATAIN, 0x00000003);
    lsu_write_32(CLP_SHA512_ACC_CSR_DATAIN, 0x00000004);
    lsu_write_32(CLP_SHA512_ACC_CSR_EXECUTE, SHA512_ACC_CSR_EXECUTE_EXECUTE_MASK);

    if (!wait_sha_acc_valid()) {
        VPRINTF(ERROR, "FAIL: streaming SHA-384 did not complete\n");
        SEND_STDOUT_CTRL(fail_cmd); while(1);
    }

    volatile uint32_t *digest = (volatile uint32_t *)CLP_SHA512_ACC_CSR_DIGEST_0;
    uint8_t pass = 1;
    for (int i = 0; i < ICCM_HASH_PCR_DWORDS; i++) {
        if (digest[i] != expected_stream_digest[i]) {
            VPRINTF(ERROR, "ERROR: DIGEST[%d] mismatch! Got 0x%x, expected 0x%x\n",
                    i, digest[i], expected_stream_digest[i]);
            pass = 0;
        }
    }
    if (!pass) {
        VPRINTF(ERROR, "FAIL: streaming SHA-384 digest mismatch\n");
        SEND_STDOUT_CTRL(fail_cmd); while(1);
    }
    VPRINTF(LOW, "PASS: streaming SHA-384 digest matches expected\n");

    VPRINTF(LOW, "=== SHA acc reuse verified ===\n");
    SEND_STDOUT_CTRL(0xff);
}
