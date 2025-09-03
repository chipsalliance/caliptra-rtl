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

volatile caliptra_intr_received_s cptra_intr_rcv = {0};


void main() {
    VPRINTF(LOW, "----------------------------------\n");
    VPRINTF(LOW, " Running MLDSA Random Smoke Test !!\n");
    VPRINTF(LOW, "----------------------------------\n");

    //Call interrupt init
    init_interrupts();

    //--------------------------------------------------------------
    SEND_STDOUT_CTRL(0xd9); //inject keygen seed

    // wait for MLDSA to be ready
    VPRINTF(LOW, "Waiting for mldsa status ready in keygen\n");
    while((lsu_read_32(CLP_ABR_REG_MLDSA_STATUS) & ABR_REG_MLDSA_STATUS_READY_MASK) == 0);

    VPRINTF(LOW, "\nMLDSA KEYGEN\n");
    // Enable MLDSA KEYGEN
    lsu_write_32(CLP_ABR_REG_MLDSA_CTRL, MLDSA_CMD_KEYGEN);

    // // wait for MLDSA KEYGEN process to be done
    wait_for_mldsa_intr();

    SEND_STDOUT_CTRL(0xd8); //clear mldsa checking

    mldsa_zeroize();
    cptra_intr_rcv.abr_notif = 0;

    //--------------------------------------------------------------
    SEND_STDOUT_CTRL(0xda); //inject msg, sk for signing

    // wait for MLDSA to be ready
    VPRINTF(LOW, "Waiting for mldsa status ready in signing\n");
    while((lsu_read_32(CLP_ABR_REG_MLDSA_STATUS) & ABR_REG_MLDSA_STATUS_READY_MASK) == 0);

    VPRINTF(LOW, "\nMLDSA SIGNING\n");
    // Enable MLDSA SIGNING
    lsu_write_32(CLP_ABR_REG_MLDSA_CTRL, MLDSA_CMD_SIGNING);

    // // wait for MLDSA SIGNING process to be done
    wait_for_mldsa_intr();

    SEND_STDOUT_CTRL(0xd8); //clear mldsa checking

    mldsa_zeroize();
    cptra_intr_rcv.abr_notif = 0;

    //--------------------------------------------------------------
    SEND_STDOUT_CTRL(0xdb); //inject msg, sig, pk for verifying

    // wait for MLDSA to be ready
    VPRINTF(LOW, "Waiting for mldsa status ready in verify\n");
    while((lsu_read_32(CLP_ABR_REG_MLDSA_STATUS) & ABR_REG_MLDSA_STATUS_READY_MASK) == 0);

    VPRINTF(LOW, "\nMLDSA VERIFY\n");
    // Enable MLDSA Verify
    lsu_write_32(CLP_ABR_REG_MLDSA_CTRL, MLDSA_CMD_VERIFYING);

    // // wait for MLDSA SIGNING process to be done
    wait_for_mldsa_intr();

    SEND_STDOUT_CTRL(0xd8); //clear mldsa checking

    mldsa_zeroize();
    cptra_intr_rcv.abr_notif = 0;

    SEND_STDOUT_CTRL(0xff); //End the test

}


