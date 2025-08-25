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
#include "mlkem.h"

volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

uint32_t abr_entropy[ABR_ENTROPY_SIZE] = {0x3401CEFA,0xE20A7376,0x49073AC1,0xA351E329,0x26DB9ED0,0xDB6B1CFF,0xAB0493DA,0xAFB93DDD,
                                          0xD83EDEA2,0x8A803D0D,0x003B2633,0xB9D0F1BF,0x3401CEFA,0xE20A7376,0x49073AC1,0xA351E329};

void main() {

    mlkem_seed seed;
    mlkem_msg msg;
    mlkem_shared_key shared_key;
    uint32_t actual_ek[MLKEM_EK_SIZE];
    uint32_t actual_dk[MLKEM_DK_SIZE];
    uint32_t actual_ciphertext[MLKEM_CIPHERTEXT_SIZE];
    uint32_t actual_sharedkey[MLKEM_SHAREDKEY_SIZE];

    VPRINTF(LOW, "----------------------------\n");
    VPRINTF(LOW, " Running MLKEM Smoke Test !!\n");
    VPRINTF(LOW, "----------------------------\n");

    //Call interrupt init
    init_interrupts();

    seed.kv_intf = TRUE;
    seed.kv_id = 0;
    msg.kv_intf = TRUE;
    msg.kv_id = 1;
    shared_key.kv_intf = TRUE;
    shared_key.kv_id = 2;
    for (int i = 0; i < MLKEM_SHAREDKEY_SIZE; i++) {
        shared_key.data[i] = 0;
    }

    lsu_write_32(STDOUT, (seed.kv_id << 8) | 0xb1); //Inject MLKEM SEED vectors into KV 0
    lsu_write_32(STDOUT, (msg.kv_id << 8) | 0xb2); //Inject MLKEM MSG vectors into KV 1

    //Generate vectors
    mlkem_keygen_flow(seed, abr_entropy, actual_ek, actual_dk);
    mlkem_zeroize();
    cptra_intr_rcv.abr_notif = 0;

    mlkem_encaps_flow(actual_ek, msg, abr_entropy, actual_ciphertext, shared_key, actual_sharedkey);
    mlkem_zeroize();
    cptra_intr_rcv.abr_notif = 0;

    mlkem_keygen_decaps_check(seed, actual_ciphertext, abr_entropy, shared_key);
    mlkem_zeroize();
    cptra_intr_rcv.abr_notif = 0;

    SEND_STDOUT_CTRL(0xff); //End the test
    
}
