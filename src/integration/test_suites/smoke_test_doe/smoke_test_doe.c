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
// Deterministic DOE smoke test for the promote/L0 pipeline.
//
// This test intentionally contains NO randomness: fixed IVs, fixed KV
// destinations, and OCP lock disabled (+CLP_OCP_LOCK_DIS) so its behavior is
// identical on every run. It exercises the basic UDS and Field-Entropy
// deobfuscation flows and confirms each lands in the key vault. The randomized
// counterpart (random UDS/FE values, randomized OCP-lock state, random KV
// slots, and the OCP-lock rejection path) lives in rand_test_doe and runs in
// the nightly random regression.
//

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "riscv_hw_if.h"
#include "riscv-csr.h"
#include "printf.h"
#include "doe.h"
#include <stdint.h>

volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count = 0;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

// Fixed IVs and KV destinations - deterministic across runs.
uint32_t iv_data_uds[4] = {0x2eb94297, 0x77285196, 0x3dd39a1e, 0xb95d438f};
uint32_t iv_data_fe[4]  = {0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f};
uint32_t iv_data_hek[4] = {0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f};

#define DOE_UDS_KV_DEST 0
#define DOE_FE_KV_DEST  6
#define DOE_HEK_KV_DEST DOE_HEK_DES // 22

void main() {
    VPRINTF(LOW,"----------------------------------\n");
    VPRINTF(LOW," DOE Smoke Test (deterministic)   \n");
    VPRINTF(LOW,"----------------------------------\n");

    // Run the standard UDS + Field-Entropy (+ HEK when OCP lock mode is on)
    // deobfuscation flows to fixed KV slots and poll each for completion.
    doe_init(iv_data_uds, iv_data_fe, iv_data_hek,
             DOE_UDS_KV_DEST, DOE_FE_KV_DEST, DOE_HEK_KV_DEST);

    // Clear obfuscation secrets to leave DOE in a clean state.
    doe_clear_secrets();

    VPRINTF(LOW,"DOE smoke test completed\n");
    SEND_STDOUT_CTRL(0xff); // End the test
}
