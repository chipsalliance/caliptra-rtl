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

volatile char*    stdout           = (char *)STDOUT;
volatile uint32_t intr_count = 0;
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

uint8_t ocp_progress_bit;
volatile caliptra_intr_received_s cptra_intr_rcv = {
    .doe_error        = 0,
    .doe_notif        = 0,
    .ecc_error        = 0,
    .ecc_notif        = 0,
    .hmac_error       = 0,
    .hmac_notif       = 0,
    .kv_error         = 0,
    .kv_notif         = 0,
    .sha512_error     = 0,
    .sha512_notif     = 0,
    .sha256_error     = 0,
    .sha256_notif     = 0,
    .qspi_error       = 0,
    .qspi_notif       = 0,
    .uart_error       = 0,
    .uart_notif       = 0,
    .i3c_error        = 0,
    .i3c_notif        = 0,
    .soc_ifc_error    = 0,
    .soc_ifc_notif    = 0,
    .sha512_acc_error = 0,
    .sha512_acc_notif = 0,
    .abr_error      = 0,
    .abr_notif      = 0,
    .axi_dma_notif    = 0,
    .axi_dma_error    = 0,
};

void mldsa_seed_read_flow(mldsa_io seed) {
    // wait for MLDSA to be ready
    VPRINTF(LOW, "Waiting for mldsa status ready in keygen\n");
    while((lsu_read_32(CLP_ABR_REG_MLDSA_STATUS) & ABR_REG_MLDSA_STATUS_READY_MASK) == 0);

    //Program mldsa seed
    if(seed.kv_intf){
        // Program MLDSA_SEED Read with 12 dwords from seed_kv_id
        lsu_write_32(CLP_ABR_REG_KV_MLDSA_SEED_RD_CTRL, (ABR_REG_KV_MLDSA_SEED_RD_CTRL_READ_EN_MASK |
                                                          ((seed.kv_id << ABR_REG_KV_MLDSA_SEED_RD_CTRL_READ_ENTRY_LOW) & ABR_REG_KV_MLDSA_SEED_RD_CTRL_READ_ENTRY_MASK)));

        // Check that MLDSA SEED is loaded
        while((lsu_read_32(CLP_ABR_REG_KV_MLDSA_SEED_RD_STATUS) & ABR_REG_KV_MLDSA_SEED_RD_STATUS_VALID_MASK) == 0);

        //Check for error status
        if (ocp_progress_bit & (seed.kv_id == 23)) {
            while ((lsu_read_32(CLP_ABR_REG_KV_MLDSA_SEED_RD_STATUS) & ABR_REG_KV_MLDSA_SEED_RD_STATUS_ERROR_MASK) == 0);
            VPRINTF(LOW, "Received expected err for MLDSA seed read while OCP lock in progress\n");
        }
    }
    else {
        VPRINTF(LOW, "This test is supported only in SS_MODE for MLDSA seed KV read flow\n");
    }
}

void main() {
    VPRINTF(LOW, "---------------------------------\n");
    VPRINTF(LOW, " KV Smoke Test With MLDSA flow !!\n");
    VPRINTF(LOW, "---------------------------------\n");


    srand(time);
    //Call interrupt init
    init_interrupts();
    mldsa_io seed;

    uint32_t ocp_lock_mode = (lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_CONFIG) & SOC_IFC_REG_CPTRA_HW_CONFIG_OCP_LOCK_MODE_EN_MASK);
    VPRINTF(LOW, "OCP_LOCK_MODE_EN: 0x%x\n", ocp_lock_mode);

    if (ocp_lock_mode) {

        seed.kv_intf = TRUE;
        seed.kv_id = (rand() % 2) + 22;
        VPRINTF(LOW, "Running mldsa with seed kv_id = 0x%x\n", seed.kv_id);

        //inject mldsa seed to kv key reg (in RTL)
        uint8_t key_inject_cmd = 0xab;
        SEND_STDOUT_CTRL(key_inject_cmd);

        ocp_progress_bit = rand() % 2;
        if (ocp_progress_bit) {
            // Enable OCP LOCK mode
            VPRINTF(LOW,"OCP lock in progress\n");
            lsu_write_32(CLP_SOC_IFC_REG_SS_OCP_LOCK_CTRL, 1);
        } else {
            VPRINTF(LOW,"OCP lock not in progress\n");
        }
        
        mldsa_seed_read_flow(seed);
        mldsa_zeroize();
        cptra_intr_rcv.abr_notif = 0;
    }
    else {
        VPRINTF(ERROR, "This test is supported only in SS_MODE\n");
    }

    SEND_STDOUT_CTRL(0xff); //End the test

}


