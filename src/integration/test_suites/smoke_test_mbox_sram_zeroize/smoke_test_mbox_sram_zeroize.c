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
// smoke_test_mbox_sram_zeroize
//
// Verifies that the mailbox SRAM is zeroed after each graceful lock release.
//
// The zeroization feature (mbox.sv) writes zeros to the entire mailbox SRAM
// immediately after the lock is released via any graceful arc. The lock is held
// (lock.value=1) throughout zeroization so that polling masters naturally wait.
// Only when zeroization completes does the lock become acquirable again.
//
// This test covers two flows from the uC perspective:
//
// Test 1 — SoC sends command via DMA, uC processes and responds
//   The UVM testbench must:
//     - Acquire mbox lock
//     - Program DMA: rd_route=AXI, wr_route=MBOX, src=known non-zero data,
//       byte_count=MBOX_DLEN_BYTES (64 bytes)
//     - Assert DMA go
//     - Write MBOX_CMD=MBOX_CMD_RESP_BASIC, MBOX_DLEN=MBOX_DLEN_BYTES
//     - Assert MBOX_EXECUTE
//     - Wait for DATA_READY status
//     - Read MBOX_DATAOUT (uC response)
//     - Clear MBOX_EXECUTE (triggers lock release and zeroization)
//   The uC (this firmware):
//     - Reads DMA-written data from MBOX_DATAOUT and verifies it is non-zero
//     - Sets DATA_READY status to signal response is ready
//     - Waits for SoC to release lock
//     - Re-acquires lock (polls MBOX_LOCK; naturally blocked during zeroization)
//     - Reads mailbox SRAM directly and verifies all words are zero
//
// Test 2 — uC initiates a command to SoC (uC→SoC direction)
//   The UVM testbench must:
//     - Wait for READY_FOR_RUNTIME signal
//     - Read MBOX_DATAOUT words (the uC response data)
//     - Clear MBOX_EXECUTE (triggers lock release and zeroization)
//   The uC (this firmware):
//     - Acquires mbox lock
//     - Writes known non-zero data to MBOX_DATAIN
//     - Sets MBOX_CMD and MBOX_DLEN
//     - Asserts MBOX_EXECUTE (FSM -> MBOX_EXECUTE_SOC)
//     - Waits for SoC to clear execute (lock releases, zeroization runs)
//     - Re-acquires lock (polls; waits through zeroization)
//     - Verifies SRAM is zero via direct access

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include <stdint.h>
#include "printf.h"

volatile uint32_t* stdout    = (uint32_t *)STDOUT;
volatile uint32_t  intr_count = 0;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

// Number of data words used in each test
#define MBOX_TEST_DWORDS      16
#define MBOX_DLEN_BYTES       (MBOX_TEST_DWORDS * 4)

// Number of SRAM words to verify after zeroization
// Checks the region that was written during the test plus a few extra
#define MBOX_VERIFY_DWORDS    32

// Response payload written by uC in Test 1
static const uint32_t uc_response[MBOX_TEST_DWORDS] = {
    0xDEADBEEF, 0xCAFEBABE, 0xA5A5A5A5, 0x12345678,
    0x11111111, 0x22222222, 0x33333333, 0x44444444,
    0x55555555, 0x66666666, 0x77777777, 0x88888888,
    0x99999999, 0xAAAAAAAA, 0xBBBBBBBB, 0xCCCCCCCC
};

// Data written by uC in Test 2
static const uint32_t uc_payload[MBOX_TEST_DWORDS] = {
    0xFEEDFACE, 0xBAADF00D, 0xDEADC0DE, 0xC0FFEE00,
    0x01234567, 0x89ABCDEF, 0xFEDCBA98, 0x76543210,
    0xAAAA5555, 0x5555AAAA, 0xF0F0F0F0, 0x0F0F0F0F,
    0xFF00FF00, 0x00FF00FF, 0xABCDABCD, 0xEFEFEFEF
};

// Verify the first MBOX_VERIFY_DWORDS words of mbox SRAM are zero
// Uses direct SRAM access (uC must hold the lock)
static uint8_t verify_sram_zeroed(void) {
    uint32_t data;
    uint32_t fail = 0;
    for (uint32_t ii = 0; ii < MBOX_VERIFY_DWORDS; ii++) {
        data = lsu_read_32(CLP_MBOX_SRAM_BASE_ADDR + (ii * 4));
        if (data != 0) {
            VPRINTF(ERROR, "ERROR: SRAM[%d] = 0x%x, expected 0 after zeroization\n", ii, data);
            fail = 1;
        }
    }
    return fail;
}

void main() {
    mbox_op_s op;
    uint32_t data;
    uint32_t ii;
    uint32_t fail = 0;

    VPRINTF(LOW, "----------------------------------\n");
    VPRINTF(LOW, " Mbox SRAM Zeroization Smoke Test\n");
    VPRINTF(LOW, "----------------------------------\n");

    init_interrupts();

    // =========================================================================
    // Test 1: SoC DMA writes data to mbox, uC reads, responds, verifies zero
    // =========================================================================
    VPRINTF(LOW, "Test 1: SoC DMA -> uC -> verify zeroization\n");

    // Signal ready so UVM testbench sends the DMA-written mailbox command
    soc_ifc_set_flow_status_field(SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_MB_PROCESSING_MASK);

    // Wait for SoC to acquire lock, write data via DMA, and assert execute
    VPRINTF(LOW, "FW: Waiting for execute...\n");
    while (!(lsu_read_32(CLP_MBOX_CSR_MBOX_EXECUTE) & MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK));

    op = soc_ifc_read_mbox_cmd();
    VPRINTF(LOW, "FW: cmd=0x%x dlen=0x%x\n", op.cmd, op.dlen);

    // Read data written by SoC DMA and verify it is non-zero
    VPRINTF(LOW, "FW: Reading DMA-written data from mbox\n");
    for (ii = 0; ii < op.dlen / 4; ii++) {
        data = soc_ifc_mbox_read_dataout_single();
        VPRINTF(HIGH, "FW: dataout[%d] = 0x%x\n", ii, data);
        if (data == 0) {
            VPRINTF(ERROR, "ERROR: Test 1: dataout[%d] is 0 — expected non-zero DMA data\n", ii);
            fail = 1;
        }
    }

    // Write response data back to mbox (uC response for SoC to read)
    VPRINTF(LOW, "FW: Writing uC response to mbox\n");
    for (ii = 0; ii < MBOX_TEST_DWORDS; ii++) {
        lsu_write_32(CLP_MBOX_CSR_MBOX_DATAIN, uc_response[ii]);
    }

    // Signal data is ready — FSM transitions to MBOX_EXECUTE_SOC
    lsu_write_32(CLP_MBOX_CSR_MBOX_STATUS, DATA_READY);
    VPRINTF(LOW, "FW: Set DATA_READY, waiting for SoC to clear execute...\n");

    // Wait for SoC to clear execute (lock releases, zeroization begins)
    while (lsu_read_32(CLP_MBOX_CSR_MBOX_EXECUTE) & MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK);
    VPRINTF(LOW, "FW: Execute cleared — zeroization running\n");

    // Re-acquire lock — lock.value stays 1 throughout zeroization so this
    // poll naturally waits until zeroization completes
    VPRINTF(LOW, "FW: Polling for lock (blocks through zeroization)...\n");
    while ((lsu_read_32(CLP_MBOX_CSR_MBOX_LOCK) & MBOX_CSR_MBOX_LOCK_LOCK_MASK) == 1);
    VPRINTF(LOW, "FW: Lock acquired — zeroization complete\n");

    // Verify SRAM is zero via direct access (uC holds lock, FSM in RDY_FOR_CMD)
    VPRINTF(LOW, "FW: Verifying SRAM zeroed...\n");
    if (verify_sram_zeroed()) {
        VPRINTF(ERROR, "ERROR: Test 1: SRAM not zeroed after lock release\n");
        fail = 1;
    } else {
        VPRINTF(LOW, "FW: PASS Test 1 — SRAM verified zero\n");
    }

    // Release lock before Test 2
    lsu_write_32(CLP_MBOX_CSR_MBOX_UNLOCK, MBOX_CSR_MBOX_UNLOCK_UNLOCK_MASK);

    // =========================================================================
    // Test 2: uC writes data and sends to SoC, then verifies zeroization
    // =========================================================================
    VPRINTF(LOW, "Test 2: uC -> SoC -> verify zeroization\n");

    // Acquire mbox lock
    VPRINTF(LOW, "FW: Acquiring lock...\n");
    while ((lsu_read_32(CLP_MBOX_CSR_MBOX_LOCK) & MBOX_CSR_MBOX_LOCK_LOCK_MASK) == 1);
    VPRINTF(LOW, "FW: Lock acquired\n");

    // Write command and data length
    lsu_write_32(CLP_MBOX_CSR_MBOX_CMD,  MBOX_CMD_RESP_BASIC);
    lsu_write_32(CLP_MBOX_CSR_MBOX_DLEN, MBOX_DLEN_BYTES);

    // Write payload into mbox via DATAIN register
    VPRINTF(LOW, "FW: Writing payload to mbox\n");
    for (ii = 0; ii < MBOX_TEST_DWORDS; ii++) {
        lsu_write_32(CLP_MBOX_CSR_MBOX_DATAIN, uc_payload[ii]);
    }

    // Signal SoC that data is ready — FSM -> MBOX_EXECUTE_SOC (uC holds lock)
    // Signal to UVM to start reading after READY_FOR_RUNTIME
    soc_ifc_set_flow_status_field(SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_RUNTIME_MASK);
    lsu_write_32(CLP_MBOX_CSR_MBOX_EXECUTE, MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK);
    VPRINTF(LOW, "FW: Execute asserted — waiting for SoC to consume and clear execute...\n");

    // Wait for SoC to read data and clear execute (lock releases, zeroization begins)
    while (lsu_read_32(CLP_MBOX_CSR_MBOX_EXECUTE) & MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK);
    VPRINTF(LOW, "FW: Execute cleared — zeroization running\n");

    // Re-acquire lock — waits through zeroization (lock.value=1 throughout)
    VPRINTF(LOW, "FW: Polling for lock (blocks through zeroization)...\n");
    while ((lsu_read_32(CLP_MBOX_CSR_MBOX_LOCK) & MBOX_CSR_MBOX_LOCK_LOCK_MASK) == 1);
    VPRINTF(LOW, "FW: Lock acquired — zeroization complete\n");

    // Verify SRAM is zero
    VPRINTF(LOW, "FW: Verifying SRAM zeroed...\n");
    if (verify_sram_zeroed()) {
        VPRINTF(ERROR, "ERROR: Test 2: SRAM not zeroed after lock release\n");
        fail = 1;
    } else {
        VPRINTF(LOW, "FW: PASS Test 2 — SRAM verified zero\n");
    }

    // Release lock
    lsu_write_32(CLP_MBOX_CSR_MBOX_UNLOCK, MBOX_CSR_MBOX_UNLOCK_UNLOCK_MASK);

    // =========================================================================
    // Result
    // =========================================================================
    if (fail) {
        VPRINTF(FATAL, "smoke_test_mbox_sram_zeroize FAILED\n");
        SEND_STDOUT_CTRL(0x1);
        while (1);
    } else {
        VPRINTF(LOW, "smoke_test_mbox_sram_zeroize PASSED\n");
        SEND_STDOUT_CTRL(0xff);
    }
}
