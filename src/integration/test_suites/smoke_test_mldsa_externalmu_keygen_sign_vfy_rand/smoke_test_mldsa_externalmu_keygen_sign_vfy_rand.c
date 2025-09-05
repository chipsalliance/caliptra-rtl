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
#include "riscv_hw_if.h"
#include "riscv-csr.h"
#include "printf.h"
#include "mldsa.h"
#include "sha3.h"

volatile char*    stdout     = (char *)STDOUT;
volatile uint32_t intr_count = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

volatile int indexer = 0;

// Processed message to calculate external mu must be prepended by one zero byte, the length of the context and then the context.
// In our case the context is empty so this message header is two zero bytes.
#define EXTERNAL_MU_HEADER_LEN (2)

void main() {
    VPRINTF(LOW, "-----------------------------------------\n");
    VPRINTF(LOW, " Running MLDSA Random External Mu Test !!\n");
    VPRINTF(LOW, "-----------------------------------------\n");

    //--------------------------------------------------------------
    // Calculate external mu.

    // Calculate the hash of the public key.
    dif_kmac_operation_state_t operation_state;
    uint32_t public_key_hash[MLDSA87_PUBKEY_HASH_SIZE];
    dif_kmac_mode_shake_start(CLP_KMAC_BASE_ADDR, &operation_state, kDifKmacModeShakeLen256, kDifKmacMsgEndiannessLittle);
    SEND_STDOUT_CTRL(0xd0); // Inject public key into SHA3 to calculate tr.
    for (indexer = 0; indexer < MLDSA87_PUBKEY_SIZE; ++indexer) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }
    dif_kmac_squeeze(CLP_KMAC_BASE_ADDR, &operation_state, public_key_hash, MLDSA87_PUBKEY_HASH_SIZE, /*processed=*/NULL, /*capacity=*/NULL);
    SEND_STDOUT_CTRL(0xd8); // Clear mldsa and sha3 forces.
    dif_kmac_end(CLP_KMAC_BASE_ADDR, &operation_state);
    dif_kmac_poll_status(CLP_KMAC_BASE_ADDR, KMAC_STATUS_SHA3_IDLE_LOW);

    // Calculate External mu which is a 64-bit SHAKE hash of the formatted message `tr ^ M'`.
    // `M' = 0 ^ 0 ^ M` where ^ is concatenation is M is the message.
    uint32_t mu[MLDSA87_EXTERNAL_MU_SIZE];
    const char message_header[EXTERNAL_MU_HEADER_LEN] = "\x00\x00";
    dif_kmac_mode_shake_start(CLP_KMAC_BASE_ADDR, &operation_state, kDifKmacModeShakeLen256, kDifKmacMsgEndiannessLittle);
    // Absorb the public key hash digest.
    dif_kmac_absorb(CLP_KMAC_BASE_ADDR, &operation_state, public_key_hash, MLDSA87_PUBKEY_HASH_SIZE*4, NULL);
    // Absorb the formatted message.
    dif_kmac_absorb(CLP_KMAC_BASE_ADDR, &operation_state, message_header, EXTERNAL_MU_HEADER_LEN, NULL);
    SEND_STDOUT_CTRL(0xd1);
    for (indexer = 0; indexer < MLDSA87_EXTERNAL_MU_SIZE; ++indexer) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }
    dif_kmac_squeeze(CLP_KMAC_BASE_ADDR, &operation_state, mu, MLDSA87_EXTERNAL_MU_SIZE, /*processed=*/NULL, /*capacity=*/NULL);
    SEND_STDOUT_CTRL(0xd8); // Clear mldsa and sha3 forces.
    dif_kmac_end(CLP_KMAC_BASE_ADDR, &operation_state);
    dif_kmac_poll_status(CLP_KMAC_BASE_ADDR, KMAC_STATUS_SHA3_IDLE_LOW);

    //--------------------------------------------------------------
    // Signing process.

    // Initialise interrupts including those for Adam's bridge.
    init_interrupts();

    // Wait for MLDSA to be ready.
    VPRINTF(LOW, "Waiting for mldsa status ready in keygen+sign\n");
    while((lsu_read_32(CLP_ABR_REG_MLDSA_STATUS) & ABR_REG_MLDSA_STATUS_READY_MASK) == 0);

    // Program MLDSA EXTERNAL_MU
    write_mldsa_reg((uint32_t *) CLP_ABR_REG_MLDSA_EXTERNAL_MU_0, mu, MLDSA87_EXTERNAL_MU_SIZE);

    SEND_STDOUT_CTRL(0xd2); // Inject secret key for signing.

    VPRINTF(LOW, "\nMLDSA KEYGEN_SIGN\n");
    // Enable MLDSA keygen sign
    lsu_write_32(CLP_ABR_REG_MLDSA_CTRL, MLDSA_CMD_KEYGEN_SIGN |
                                         ABR_REG_MLDSA_CTRL_EXTERNAL_MU_MASK);

    // Wait for MLDSA SIGNING process to be done.
    wait_for_mldsa_intr();
    SEND_STDOUT_CTRL(0xd8); // Clear mldsa and sha3 forces.
    mldsa_zeroize();
    cptra_intr_rcv.abr_notif = 0;

    //--------------------------------------------------------------
    // Verification process.

    // Wait for MLDSA to be ready.
    VPRINTF(LOW, "Waiting for mldsa status ready in verify\n");
    while((lsu_read_32(CLP_ABR_REG_MLDSA_STATUS) & ABR_REG_MLDSA_STATUS_READY_MASK) == 0);

    write_mldsa_reg((uint32_t *) CLP_ABR_REG_MLDSA_EXTERNAL_MU_0, mu, MLDSA87_EXTERNAL_MU_SIZE);
    SEND_STDOUT_CTRL(0xd3); // Inject signature and public key for verifying.

    VPRINTF(LOW, "\nMLDSA VERIFY\n");
    // Enable MLDSA Verify
    lsu_write_32(CLP_ABR_REG_MLDSA_CTRL, MLDSA_CMD_VERIFYING |
                                         ABR_REG_MLDSA_CTRL_EXTERNAL_MU_MASK);

    // Wait for MLDSA SIGNING process to be done.
    wait_for_mldsa_intr();
    SEND_STDOUT_CTRL(0xd8); // Clear mldsa and sha3 forces.
    mldsa_zeroize();
    cptra_intr_rcv.abr_notif = 0;

    SEND_STDOUT_CTRL(0xff); // End the test in success. Failures will cause assertion errors.
}


