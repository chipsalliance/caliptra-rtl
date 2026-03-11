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
// Description:
//   Validates that ABR (adams-bridge) detects all-zero KV seed/msg
//   and raises an error interrupt, similar to HMAC key_zero_error.
//
//   Test iterations (via warm reset):
//     0 - MLDSA seed zero error: Inject all-zero seed via KV, trigger KEYGEN
//     1 - MLKEM seed zero error: Inject all-zero seed via KV, trigger KEYGEN
//     2 - MLKEM msg zero error:  Inject all-zero msg via KV, trigger ENCAPS

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "riscv_hw_if.h"
#include "riscv-csr.h"
#include "printf.h"
#include "mldsa.h"
#include "mlkem.h"

volatile char*    stdout           = (char *)STDOUT;
volatile uint32_t intr_count = 0;
volatile uint32_t rst_count __attribute__((section(".dccm.persistent"))) = 0;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

void main() {
    uint8_t fail_cmd = 0x1;
    uint8_t kv_slot;

    VPRINTF(LOW, "----------------------------------\n");
    VPRINTF(LOW, " ABR KV Zero Error Test - rst_count = %d\n", rst_count);
    VPRINTF(LOW, "----------------------------------\n");

    // Setup the interrupt CSR configuration
    init_interrupts();

    if (rst_count == 0) {
        //--------------------------------------------------------------
        // Test 0: MLDSA seed zero error
        //--------------------------------------------------------------
        VPRINTF(LOW, "\n=== TEST 0: MLDSA seed zero error ===\n");

        // Wait for MLDSA to be ready
        while((lsu_read_32(CLP_ABR_REG_MLDSA_STATUS) & ABR_REG_MLDSA_STATUS_READY_MASK) == 0);

        // Inject all-zero MLDSA seed into KV slot 8 (KV_ENTRY_FOR_MLDSA_SIGNING)
        // TB command 0xa1: zero MLDSA seed injection
        VPRINTF(LOW, "Injecting zero MLDSA seed into KV\n");
        SEND_STDOUT_CTRL(0xa1);

        // Program KV read for MLDSA seed from slot 8
        lsu_write_32(CLP_ABR_REG_KV_MLDSA_SEED_RD_CTRL,
                     ABR_REG_KV_MLDSA_SEED_RD_CTRL_READ_EN_MASK |
                     ((8 << ABR_REG_KV_MLDSA_SEED_RD_CTRL_READ_ENTRY_LOW) &
                      ABR_REG_KV_MLDSA_SEED_RD_CTRL_READ_ENTRY_MASK));

        // Wait for KV read to complete
        while((lsu_read_32(CLP_ABR_REG_KV_MLDSA_SEED_RD_STATUS) &
               (ABR_REG_KV_MLDSA_SEED_RD_STATUS_VALID_MASK |
                ABR_REG_KV_MLDSA_SEED_RD_STATUS_ERROR_MASK)) == 0);

        if ((lsu_read_32(CLP_ABR_REG_KV_MLDSA_SEED_RD_STATUS) &
             ABR_REG_KV_MLDSA_SEED_RD_STATUS_ERROR_MASK) != 0) {
            VPRINTF(ERROR, "Unexpected KV read error for MLDSA seed\n");
            SEND_STDOUT_CTRL(fail_cmd);
            while(1);
        }

        // Write dummy entropy
        for (int i = 0; i < 16; i++) {
            lsu_write_32(CLP_ABR_REG_ABR_ENTROPY_0 + i*4, 0xdeadbeef);
        }

        // Trigger MLDSA KEYGEN - should detect zero seed and raise error
        VPRINTF(LOW, "Triggering MLDSA KEYGEN with zero seed\n");
        lsu_write_32(CLP_ABR_REG_MLDSA_CTRL, MLDSA_CMD_KEYGEN);

        // Wait for interrupt (error or notification)
        wait_for_mldsa_intr();

        // Check that error interrupt was received
        if (cptra_intr_rcv.abr_error == 0) {
            VPRINTF(ERROR, "\nMLDSA seed_zero_error is NOT detected.\n");
            SEND_STDOUT_CTRL(fail_cmd);
            while(1);
        }
        VPRINTF(LOW, "MLDSA seed_zero_error detected successfully!\n");

        // Check STATUS.ERROR is set
        if ((lsu_read_32(CLP_ABR_REG_MLDSA_STATUS) & ABR_REG_MLDSA_STATUS_ERROR_MASK) == 0) {
            VPRINTF(ERROR, "MLDSA STATUS.ERROR not set after seed_zero_error\n");
            SEND_STDOUT_CTRL(fail_cmd);
            while(1);
        }

        mldsa_zeroize();
        rst_count++;
        SEND_STDOUT_CTRL(0xf6); // warm reset
    }
    else if (rst_count == 1) {
        //--------------------------------------------------------------
        // Test 1: MLKEM seed zero error
        //--------------------------------------------------------------
        VPRINTF(LOW, "\n=== TEST 1: MLKEM seed zero error ===\n");

        // Wait for MLKEM to be ready
        while((lsu_read_32(CLP_ABR_REG_MLKEM_STATUS) & ABR_REG_MLKEM_STATUS_READY_MASK) == 0);

        // Inject all-zero MLKEM seed into KV via 0xa8 (reuses HMAC zero key cmd, both 16 dwords)
        kv_slot = 0;
        VPRINTF(LOW, "Injecting zero MLKEM seed into KV slot %d\n", kv_slot);
        SEND_STDOUT_CTRL(0xa8);

        // Program KV read for MLKEM seed
        lsu_write_32(CLP_ABR_REG_KV_MLKEM_SEED_RD_CTRL,
                     ABR_REG_KV_MLKEM_SEED_RD_CTRL_READ_EN_MASK |
                     ((kv_slot << ABR_REG_KV_MLKEM_SEED_RD_CTRL_READ_ENTRY_LOW) &
                      ABR_REG_KV_MLKEM_SEED_RD_CTRL_READ_ENTRY_MASK));

        // Wait for KV read to complete
        while((lsu_read_32(CLP_ABR_REG_KV_MLKEM_SEED_RD_STATUS) &
               (ABR_REG_KV_MLKEM_SEED_RD_STATUS_VALID_MASK |
                ABR_REG_KV_MLKEM_SEED_RD_STATUS_ERROR_MASK)) == 0);

        if ((lsu_read_32(CLP_ABR_REG_KV_MLKEM_SEED_RD_STATUS) &
             ABR_REG_KV_MLKEM_SEED_RD_STATUS_ERROR_MASK) != 0) {
            VPRINTF(ERROR, "Unexpected KV read error for MLKEM seed\n");
            SEND_STDOUT_CTRL(fail_cmd);
            while(1);
        }

        // Write dummy entropy
        for (int i = 0; i < 16; i++) {
            lsu_write_32(CLP_ABR_REG_ABR_ENTROPY_0 + i*4, 0xdeadbeef);
        }

        // Trigger MLKEM KEYGEN - should detect zero seed and raise error
        VPRINTF(LOW, "Triggering MLKEM KEYGEN with zero seed\n");
        lsu_write_32(CLP_ABR_REG_MLKEM_CTRL, MLKEM_CMD_KEYGEN);

        // Wait for interrupt
        wait_for_mlkem_intr();

        // Check that error interrupt was received
        if (cptra_intr_rcv.abr_error == 0) {
            VPRINTF(ERROR, "\nMLKEM seed_zero_error is NOT detected.\n");
            SEND_STDOUT_CTRL(fail_cmd);
            while(1);
        }
        VPRINTF(LOW, "MLKEM seed_zero_error detected successfully!\n");

        // Check STATUS.ERROR is set
        if ((lsu_read_32(CLP_ABR_REG_MLKEM_STATUS) & ABR_REG_MLKEM_STATUS_ERROR_MASK) == 0) {
            VPRINTF(ERROR, "MLKEM STATUS.ERROR not set after seed_zero_error\n");
            SEND_STDOUT_CTRL(fail_cmd);
            while(1);
        }

        mlkem_zeroize();
        rst_count++;
        SEND_STDOUT_CTRL(0xf6); // warm reset
    }
    else if (rst_count == 2) {
        //--------------------------------------------------------------
        // Test 2: MLKEM msg zero error
        // Write MLKEM seed via SW registers (not KV), then inject
        // all-zero msg via KV. Only msg zero error should fire.
        //--------------------------------------------------------------
        VPRINTF(LOW, "\n=== TEST 2: MLKEM msg zero error ===\n");

        // Wait for MLKEM to be ready
        while((lsu_read_32(CLP_ABR_REG_MLKEM_STATUS) & ABR_REG_MLKEM_STATUS_READY_MASK) == 0);

        // Write non-zero MLKEM seed_d and seed_z via SW registers
        for (int i = 0; i < 8; i++) {
            lsu_write_32(CLP_ABR_REG_MLKEM_SEED_D_0 + i*4, 0xA5A5A500 + i);
            lsu_write_32(CLP_ABR_REG_MLKEM_SEED_Z_0 + i*4, 0x5A5A5A00 + i);
        }

        // Inject all-zero MLKEM msg into KV via 0xa1 (reuses MLDSA zero seed cmd, both 8 dwords)
        // 0xa1 writes to slot 8 (KV_ENTRY_FOR_MLDSA_SIGNING) with MLDSA_SEED+MLKEM_MSG dest_valid
        kv_slot = 8;
        VPRINTF(LOW, "Injecting zero MLKEM msg into KV slot %d\n", kv_slot);
        SEND_STDOUT_CTRL(0xa1);

        // Program KV read for MLKEM msg
        lsu_write_32(CLP_ABR_REG_KV_MLKEM_MSG_RD_CTRL,
                     ABR_REG_KV_MLKEM_MSG_RD_CTRL_READ_EN_MASK |
                     ((kv_slot << ABR_REG_KV_MLKEM_MSG_RD_CTRL_READ_ENTRY_LOW) &
                      ABR_REG_KV_MLKEM_MSG_RD_CTRL_READ_ENTRY_MASK));

        // Wait for KV msg read to complete
        while((lsu_read_32(CLP_ABR_REG_KV_MLKEM_MSG_RD_STATUS) &
               (ABR_REG_KV_MLKEM_MSG_RD_STATUS_VALID_MASK |
                ABR_REG_KV_MLKEM_MSG_RD_STATUS_ERROR_MASK)) == 0);

        if ((lsu_read_32(CLP_ABR_REG_KV_MLKEM_MSG_RD_STATUS) &
             ABR_REG_KV_MLKEM_MSG_RD_STATUS_ERROR_MASK) != 0) {
            VPRINTF(ERROR, "Unexpected KV read error for MLKEM msg\n");
            SEND_STDOUT_CTRL(fail_cmd);
            while(1);
        }

        // Write dummy entropy
        for (int i = 0; i < 16; i++) {
            lsu_write_32(CLP_ABR_REG_ABR_ENTROPY_0 + i*4, 0xdeadbeef);
        }

        // Write dummy encaps key (needed for ENCAPS command)
        for (int i = 0; i < MLKEM_EK_SIZE; i++) {
            lsu_write_32(CLP_ABR_REG_MLKEM_ENCAPS_KEY_BASE_ADDR + i*4, 0xcafebabe);
        }

        // Trigger MLKEM ENCAPS - should detect zero msg and raise error
        VPRINTF(LOW, "Triggering MLKEM ENCAPS with zero msg\n");
        lsu_write_32(CLP_ABR_REG_MLKEM_CTRL, MLKEM_CMD_ENCAPS);

        // Wait for interrupt
        wait_for_mlkem_intr();

        // Check that error interrupt was received
        if (cptra_intr_rcv.abr_error == 0) {
            VPRINTF(ERROR, "\nMLKEM msg_zero_error is NOT detected.\n");
            SEND_STDOUT_CTRL(fail_cmd);
            while(1);
        }
        VPRINTF(LOW, "MLKEM msg_zero_error detected successfully!\n");

        // Check STATUS.ERROR is set
        if ((lsu_read_32(CLP_ABR_REG_MLKEM_STATUS) & ABR_REG_MLKEM_STATUS_ERROR_MASK) == 0) {
            VPRINTF(ERROR, "MLKEM STATUS.ERROR not set after msg_zero_error\n");
            SEND_STDOUT_CTRL(fail_cmd);
            while(1);
        }

        mlkem_zeroize();
    }

    VPRINTF(LOW, "\n----------------------------------\n");
    VPRINTF(LOW, " ABR KV Zero Error Test PASSED\n");
    VPRINTF(LOW, "----------------------------------\n");
    SEND_STDOUT_CTRL(0xff);
}
