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

uint32_t seed_z[MLKEM_SEED_SIZE] = {0xD3CAA87E, 0xBB015D46, 0xD3C927B2, 0x79DCE0F1, 0x8FCC5142, 0x516F5FE6, 0xE032B821, 0x324B5F78};
uint32_t seed_d[MLKEM_SEED_SIZE] = {0xD5714E87, 0x24ACBDDE, 0xDB9DD868, 0x271B0C4B, 0xD9946A76, 0x8E1D5905, 0x15578F60, 0x3C3FC5EE};

uint32_t abr_entropy[ABR_ENTROPY_SIZE] = {0x3401CEFA,0xE20A7376,0x49073AC1,0xA351E329,0x26DB9ED0,0xDB6B1CFF,0xAB0493DA,0xAFB93DDD,
                                          0xD83EDEA2,0x8A803D0D,0x003B2633,0xB9D0F1BF,0x3401CEFA,0xE20A7376,0x49073AC1,0xA351E329};

uint32_t msg_array[MLKEM_SEED_SIZE] = {0xa82925d4, 0x97bd0fbc, 0xb11eed56, 0x168b86d7, 0xdcc65c98, 0x9ec375e0,0x72815ca8, 0x9bf2de88};

uint32_t shared_key_array[MLKEM_SHAREDKEY_SIZE] = {0x9B8FAFFD, 0x4376FDA4, 0x6E3018D7, 0x7B79F7DD, 0x89825DBE, 0xBF48C026, 0xC627BFE0, 0x686D5222};

void main() {
    mlkem_seed seed;
    mlkem_msg msg;
    mlkem_shared_key shared_key;
    uint32_t actual_ek[MLKEM_EK_SIZE];
    uint32_t actual_dk[MLKEM_DK_SIZE];
    uint32_t actual_ciphertext[MLKEM_CIPHERTEXT_SIZE];
    uint32_t actual_sharedkey[MLKEM_SHAREDKEY_SIZE];
    uint8_t ocp_progress_bit;
    BOOL read_from_kv;
    uint8_t kv_slot_type;

    VPRINTF(LOW, "----------------------------\n");
    VPRINTF(LOW, " Running MLKEM Smoke Test !!\n");
    VPRINTF(LOW, "----------------------------\n");

    srand(time);

    //Call interrupt init
    init_interrupts();

    uint32_t ocp_lock_mode = (lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_CONFIG) & SOC_IFC_REG_CPTRA_HW_CONFIG_OCP_LOCK_MODE_EN_MASK);
    VPRINTF(LOW, "OCP_LOCK_MODE_EN: 0x%x\n", ocp_lock_mode);

    //1 in 4 tests will get data from FW
    read_from_kv = ((xorshift32() % 4) == 0) ? TRUE : FALSE;
    //1 in 2 tests will set ocp lock in progress
    ocp_progress_bit = xorshift32() % 2;

    //Generate the EK to be used later - no 23 to avoid bad EK
    //Generate the actual EK for the random vectors in TB services
    seed.kv_intf = read_from_kv;
    seed.kv_id = (xorshift32() % KV_OCP_LOCK_SLOT_HI);
    seed.exp_kv_err = FALSE;
    for (int i = 0; i < MLKEM_SEED_SIZE; i++) {
        seed.data[0][i] = seed_d[i];
        seed.data[1][i] = seed_z[i];
    }
    lsu_write_32(STDOUT, (seed.kv_id << 8) | 0xb1); //Inject MLKEM SEED vectors into KV

    mlkem_keygen_flow(seed, abr_entropy, actual_ek, actual_dk);
    mlkem_zeroize();
    cptra_intr_rcv.abr_notif = 0;

    if (ocp_lock_mode) {
        //pick a kv read slot for seed
        kv_slot_type = (xorshift32() % 3);
        seed.kv_intf = read_from_kv;
        seed.exp_kv_err = FALSE;    
        for (int i = 0; i < MLKEM_SEED_SIZE; i++) {
            seed.data[0][i] = seed_d[i];
            seed.data[1][i] = seed_z[i];
        }
        switch (kv_slot_type) {
            case 0:
                seed.kv_id = xorshift32() % KV_OCP_LOCK_SLOT_LOW;
                break;
            case 1:
                seed.kv_id = (xorshift32() % (KV_OCP_LOCK_SLOT_HI - KV_OCP_LOCK_SLOT_LOW)) + KV_OCP_LOCK_SLOT_LOW;
                break;
            case 2:
                seed.kv_id = KV_OCP_LOCK_KEY_RELEASE_KV_SLOT;
                break;
        }
        VPRINTF(LOW, "Running mlkem with seed kv_id = 0x%x\n", seed.kv_id);

        //pick a kv read slot for msg
        kv_slot_type = (xorshift32() % 3);
        msg.kv_intf = read_from_kv;
        msg.exp_kv_err = FALSE;
        for (int i = 0; i < MLKEM_MSG_SIZE; i++) {
            msg.data[i] = msg_array[i];
        }
        switch (kv_slot_type) {
            case 0:
                msg.kv_id = xorshift32() % KV_OCP_LOCK_SLOT_LOW;
                break;
            case 1:
                msg.kv_id = (xorshift32() % (KV_OCP_LOCK_SLOT_HI - KV_OCP_LOCK_SLOT_LOW)) + KV_OCP_LOCK_SLOT_LOW;
                break;
            case 2:
                msg.kv_id = KV_OCP_LOCK_KEY_RELEASE_KV_SLOT;
                break;
        }
        VPRINTF(LOW, "Running mlkem with msg kv_id = 0x%x\n", msg.kv_id);

        //Choose any kv write slot
        kv_slot_type = (xorshift32() % 4);
        shared_key.kv_intf = kv_slot_type == 0 ? FALSE : TRUE;
        shared_key.exp_kv_err = FALSE;
        for (int i = 0; i < MLKEM_SHAREDKEY_SIZE; i++) {
            shared_key.data[i] = shared_key_array[i];
        } 
        switch (kv_slot_type) {
            case 0:
                shared_key.kv_id = 0;
                break;
            case 1:
                shared_key.kv_id = xorshift32() % KV_OCP_LOCK_SLOT_LOW;
                break;
            case 2:
                shared_key.kv_id = (xorshift32() % (KV_OCP_LOCK_SLOT_HI - KV_OCP_LOCK_SLOT_LOW)) + KV_OCP_LOCK_SLOT_LOW;
                break;
            case 3:
                shared_key.kv_id = KV_OCP_LOCK_KEY_RELEASE_KV_SLOT;
                break;
        }
        VPRINTF(LOW, "Running mlkem with shared_key kv_id = 0x%x\n", shared_key.kv_id);

        //determine if kv access should fail
        if (ocp_progress_bit) {
            VPRINTF(LOW,"OCP lock in progress\n");
            lsu_write_32(CLP_SOC_IFC_REG_SS_OCP_LOCK_CTRL, 1);
            if (seed.kv_intf == TRUE && seed.kv_id == KV_OCP_LOCK_KEY_RELEASE_KV_SLOT){ 
                seed.exp_kv_err = TRUE;
            }
            if (msg.kv_intf == TRUE && msg.kv_id == KV_OCP_LOCK_KEY_RELEASE_KV_SLOT){ 
                msg.exp_kv_err = TRUE;
            }
            if ((shared_key.kv_intf == TRUE && shared_key.kv_id == KV_OCP_LOCK_KEY_RELEASE_KV_SLOT) ||                   //can't write to 23
                (msg.kv_intf == TRUE && msg.kv_id < KV_OCP_LOCK_SLOT_LOW && shared_key.kv_id >= KV_OCP_LOCK_SLOT_LOW) || //can't write from lower to upper
                (msg.kv_intf == TRUE && msg.kv_id >= KV_OCP_LOCK_SLOT_LOW && shared_key.kv_id < KV_OCP_LOCK_SLOT_LOW)) { //can't write from upper to lower 
                shared_key.exp_kv_err = TRUE;
            }
        }

        lsu_write_32(STDOUT, (msg.kv_id << 8) | 0xb2); //Inject MLKEM MSG vectors into KV
        //run encaps flow to get ciphertext
        mlkem_encaps_flow(actual_ek, msg, abr_entropy, actual_ciphertext, shared_key, actual_sharedkey);
        mlkem_zeroize();
        cptra_intr_rcv.abr_notif = 0;

        //If msg KV error was expected, run again without error to get the ciphertext for the next step
        if (msg.kv_intf == TRUE && msg.exp_kv_err == TRUE) {
            msg.kv_id = (xorshift32() % KV_OCP_LOCK_SLOT_HI);
            while (msg.kv_id == seed.kv_id) {
                msg.kv_id = (xorshift32() % KV_OCP_LOCK_SLOT_HI);
            }
            msg.exp_kv_err = FALSE;
            shared_key.exp_kv_err = FALSE;
            //determine again if shared key should fail
            if (ocp_progress_bit && 
                ((shared_key.kv_intf == TRUE && shared_key.kv_id == KV_OCP_LOCK_KEY_RELEASE_KV_SLOT) ||                   //can't write to 23
                (msg.kv_intf == TRUE && msg.kv_id < KV_OCP_LOCK_SLOT_LOW && shared_key.kv_id >= KV_OCP_LOCK_SLOT_LOW) ||  //can't write from lower to upper
                (msg.kv_intf == TRUE && msg.kv_id >= KV_OCP_LOCK_SLOT_LOW && shared_key.kv_id < KV_OCP_LOCK_SLOT_LOW))) { //can't write from upper to lower 
                shared_key.exp_kv_err = TRUE;
            }
            lsu_write_32(STDOUT, (msg.kv_id << 8) | 0xb2); //Inject MLKEM MSG vectors into KV
            mlkem_encaps_flow(actual_ek, msg, abr_entropy, actual_ciphertext, shared_key, actual_sharedkey);
            mlkem_zeroize();
            cptra_intr_rcv.abr_notif = 0;
        }

        shared_key.exp_kv_err = FALSE;
        if (ocp_progress_bit) {
            if ((shared_key.kv_intf == TRUE && shared_key.kv_id == KV_OCP_LOCK_KEY_RELEASE_KV_SLOT) ||                     //can't write to 23
                (seed.kv_intf == TRUE && seed.kv_id < KV_OCP_LOCK_SLOT_LOW && shared_key.kv_id >= KV_OCP_LOCK_SLOT_LOW) || //can't write from lower to upper
                (seed.kv_intf == TRUE && seed.kv_id >= KV_OCP_LOCK_SLOT_LOW && shared_key.kv_id < KV_OCP_LOCK_SLOT_LOW)) { //can't write from upper to lower 
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
