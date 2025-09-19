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
#include <stdlib.h>
#include "caliptra_rtl_lib.h"

volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

#ifdef MY_RANDOM_SEED
    unsigned time = (unsigned) MY_RANDOM_SEED;
#else
    unsigned time = 0;
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
    uint8_t ocp_progress_bit;

    VPRINTF(LOW, "----------------------------\n");
    VPRINTF(LOW, " Running MLKEM Smoke Test !!\n");
    VPRINTF(LOW, "----------------------------\n");

    srand(time);

    //Call interrupt init
    init_interrupts();

    uint32_t ocp_lock_mode = (lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_CONFIG) & SOC_IFC_REG_CPTRA_HW_CONFIG_OCP_LOCK_MODE_EN_MASK);
    VPRINTF(LOW, "OCP_LOCK_MODE_EN: 0x%x\n", ocp_lock_mode);

    //Generate the EK to be used later - no 23 to avoid bad EK
    seed.kv_intf = TRUE;
    seed.kv_id = (xorshift32() % KV_OCP_LOCK_SLOT_HI);
    seed.exp_kv_err = FALSE;

    lsu_write_32(STDOUT, (seed.kv_id << 8) | 0xb1); //Inject MLKEM SEED vectors into KV

    mlkem_keygen_flow(seed, abr_entropy, actual_ek, actual_dk);
    mlkem_zeroize();
    cptra_intr_rcv.abr_notif = 0;

    if (ocp_lock_mode) {
        ocp_progress_bit = xorshift32() % 2;
        //pick any kv slots that don't overlap
        seed.kv_intf = TRUE;
        seed.kv_id = (xorshift32() % 24);
        seed.exp_kv_err = FALSE;
        VPRINTF(LOW, "Running mlkem with seed kv_id = 0x%x\n", seed.kv_id);
        msg.kv_intf = TRUE;
        msg.kv_id = (xorshift32() % 24);
        msg.exp_kv_err = FALSE;
        while (msg.kv_id == seed.kv_id) {
            msg.kv_id = (xorshift32() % 24);
        }
        VPRINTF(LOW, "Running mlkem with msg kv_id = 0x%x\n", msg.kv_id);
        shared_key.kv_intf = TRUE;
        shared_key.kv_id = (xorshift32() % 24);
        shared_key.exp_kv_err = FALSE;
        while ((shared_key.kv_id == seed.kv_id) || (shared_key.kv_id == msg.kv_id)) {
            shared_key.kv_id = (xorshift32() % 24);
        }
        VPRINTF(LOW, "Running mlkem with shared_key kv_id = 0x%x\n", shared_key.kv_id);
        for (int i = 0; i < MLKEM_SHAREDKEY_SIZE; i++) {
            shared_key.data[i] = 0;
        }

        lsu_write_32(STDOUT, (msg.kv_id << 8) | 0xb2); //Inject MLKEM MSG vectors into KV

        //determine if kv access should fail
        if (ocp_progress_bit) {
            VPRINTF(LOW,"OCP lock in progress\n");
            lsu_write_32(CLP_SOC_IFC_REG_SS_OCP_LOCK_CTRL, 1);
            if (seed.kv_id == KV_OCP_LOCK_KEY_RELEASE_KV_SLOT){ 
                seed.exp_kv_err = TRUE;
            }
            if (msg.kv_id == KV_OCP_LOCK_KEY_RELEASE_KV_SLOT){ 
                msg.exp_kv_err = TRUE;
            }
            if ((shared_key.kv_id == KV_OCP_LOCK_KEY_RELEASE_KV_SLOT) ||                   //can't write to 23
                (msg.kv_id < KV_OCP_LOCK_SLOT_LOW && shared_key.kv_id >= KV_OCP_LOCK_SLOT_LOW) || //can't write from lower to upper
                (msg.kv_id >= KV_OCP_LOCK_SLOT_LOW && shared_key.kv_id < KV_OCP_LOCK_SLOT_LOW)) { //can't write from upper to lower 
                shared_key.exp_kv_err = TRUE;
            }
        }

        //run encaps flow to get ciphertext
        mlkem_encaps_flow(actual_ek, msg, abr_entropy, actual_ciphertext, shared_key, actual_sharedkey);
        mlkem_zeroize();
        cptra_intr_rcv.abr_notif = 0;

        //If msg KV error was expected, run again without error to get the ciphertext for the next step
        if (msg.exp_kv_err = TRUE) {
            msg.kv_intf = TRUE;
            msg.kv_id = (xorshift32() % KV_OCP_LOCK_SLOT_HI);
            while (msg.kv_id == seed.kv_id) {
                msg.kv_id = (xorshift32() % KV_OCP_LOCK_SLOT_HI);
            }
            msg.exp_kv_err = FALSE;
            shared_key.exp_kv_err = FALSE;
            //determine again if shared key should fail
            if (ocp_progress_bit && 
                ((shared_key.kv_id == KV_OCP_LOCK_KEY_RELEASE_KV_SLOT) ||                   //can't write to 23
                (msg.kv_id < KV_OCP_LOCK_SLOT_LOW && shared_key.kv_id >= KV_OCP_LOCK_SLOT_LOW) || //can't write from lower to upper
                (msg.kv_id >= KV_OCP_LOCK_SLOT_LOW && shared_key.kv_id < KV_OCP_LOCK_SLOT_LOW))) { //can't write from upper to lower 
                shared_key.exp_kv_err = TRUE;
            }
            lsu_write_32(STDOUT, (msg.kv_id << 8) | 0xb2); //Inject MLKEM MSG vectors into KV
            mlkem_encaps_flow(actual_ek, msg, abr_entropy, actual_ciphertext, shared_key, actual_sharedkey);
            mlkem_zeroize();
            cptra_intr_rcv.abr_notif = 0;
        }

        shared_key.exp_kv_err = FALSE;
        if (ocp_progress_bit) {
            if ((shared_key.kv_id == KV_OCP_LOCK_KEY_RELEASE_KV_SLOT) ||                    //can't write to 23
                (seed.kv_id < KV_OCP_LOCK_SLOT_LOW && shared_key.kv_id >= KV_OCP_LOCK_SLOT_LOW) || //can't write from lower to upper
                (seed.kv_id >= KV_OCP_LOCK_SLOT_LOW && shared_key.kv_id < KV_OCP_LOCK_SLOT_LOW)) { //can't write from upper to lower 
                shared_key.exp_kv_err = TRUE;
            }
        }

        lsu_write_32(STDOUT, (seed.kv_id << 8) | 0xb1); //Inject MLKEM SEED vectors into KV

        mlkem_keygen_decaps_check(seed, actual_ciphertext, abr_entropy, shared_key);
        mlkem_zeroize();
        cptra_intr_rcv.abr_notif = 0;
    }
    else {
        VPRINTF(ERROR, "This test is supported only in SS_MODE\n");
    }

    SEND_STDOUT_CTRL(0xff); //End the test
    
}
