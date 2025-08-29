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
#include "ACVP_External_Mu_Tests.h"

volatile char*    stdout           = (char *)STDOUT;
volatile uint32_t intr_count = 0;
volatile uint32_t  rst_count __attribute__((section(".dccm.persistent"))) = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

// Processed message to calculate external mu must be prepended by one zero byte, the length of the context and then the context.
// In our case the context is empty so this message header is two zero bytes.
#define EXTERNAL_MU_HEADER_LEN (2)

// This function calculates external mu based on the message and public key and compares it against the expected external mu value.
void check_external_mu(uintptr_t kmac, const char *message, const size_t message_len, const uint32_t *public_key, const uint32_t *expected_external_mu) {
    uint32_t mu[MLDSA87_EXTERNAL_MU_SIZE];
    uint32_t public_key_hash[MLDSA87_PUBKEY_HASH_SIZE];
    dif_kmac_operation_state_t operation_state;
    const char message_header[EXTERNAL_MU_HEADER_LEN] = "\x00\x00";

    // Calculate `tr` which is the 64-bit SHAKE hash of the public key.
    dif_kmac_mode_shake_start(kmac, &operation_state, kDifKmacModeShakeLen256, kDifKmacMsgEndiannessLittle);
    dif_kmac_absorb(kmac, &operation_state, public_key, MLDSA87_PUBKEY_SIZE*4, NULL);
    dif_kmac_squeeze(kmac, &operation_state, public_key_hash, MLDSA87_PUBKEY_HASH_SIZE, /*processed=*/NULL, /*capacity=*/NULL);
    dif_kmac_end(kmac, &operation_state);
    dif_kmac_poll_status(kmac, KMAC_STATUS_SHA3_IDLE_LOW);

    // Calculate External mu which is a 64-bit SHAKE hash of the formatted message `tr ^ M'`.
    // `M' = 0 ^ 0 ^ M` where ^ is concatenation is M is the message.
    dif_kmac_mode_shake_start(kmac, &operation_state, kDifKmacModeShakeLen256, kDifKmacMsgEndiannessLittle);
    // Absorb the public key hash digest.
    dif_kmac_absorb(kmac, &operation_state, public_key_hash, MLDSA87_PUBKEY_HASH_SIZE*4, NULL);
    // Absorb the formatted message.
    dif_kmac_absorb(kmac, &operation_state, message_header, EXTERNAL_MU_HEADER_LEN, NULL);
    dif_kmac_absorb(kmac, &operation_state, message, message_len, NULL);
    dif_kmac_squeeze(kmac, &operation_state, mu, MLDSA87_EXTERNAL_MU_SIZE, /*processed=*/NULL, /*capacity=*/NULL);
    dif_kmac_end(kmac, &operation_state);
    dif_kmac_poll_status(kmac, KMAC_STATUS_SHA3_IDLE_LOW);

    // Check that the calculated mu is as expected and otherwise fail the test.
    for (int i = 0; i < MLDSA87_EXTERNAL_MU_SIZE; ++i) {
        if (mu[i] != expected_external_mu[i]) {
            printf("External mu: mismatch at %d got=0x%x want=0x%x", i, mu[i], expected_external_mu[i]);
            SEND_STDOUT_CTRL(0x1); // Terminate test with failure.
            while (1);
            return;
        }
    }
    printf("External mu: Check pre-computed value with SHA3 engine successfull!\n");
}

void main() {
    VPRINTF(LOW, "-----------------------------------\n");
    VPRINTF(LOW, " Running SHA3 in ExternalMu test !!\n");
    VPRINTF(LOW, "-----------------------------------\n");

    //Call interrupt init
    init_interrupts();

    for (int i = 0; i < sizeof(external_mu_tests) / sizeof(external_mu_test_t); ++i) {
        external_mu_test_t test = external_mu_tests[i];
        VPRINTF(LOW, "Processing external mu test from ACVP with index %d\n", test.identifier);
        check_external_mu(CLP_KMAC_BASE_ADDR, test.message, test.message_len, test.public_key, test.external_mu);
    }

    SEND_STDOUT_CTRL(0xff); //End the test

}


