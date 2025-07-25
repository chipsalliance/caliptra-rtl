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
    printf("-------------------------------------\n");
    printf(" PCR MLDSA Injection !!\n");
    printf("-------------------------------------\n");

    //Call interrupt init
    init_interrupts();

    //Inject mldsa failure
    printf("Inject random failure into mldsa\n");
    printf("%c", 0xd7);
    
    //inject seed to kv key reg (in RTL)
    printf("Inject randomized SEED into KV slot and MSG into SHA512 digest\n");
    printf("%c", 0x93);

    // wait for MLDSA to be ready
    printf("Waiting for mldsa status ready\n");
    while((lsu_read_32(CLP_ABR_REG_MLDSA_STATUS) & ABR_REG_MLDSA_STATUS_READY_MASK) == 0);

    // Enable MLDSA keygen sign
    printf("\nMLDSA PCR SIGNING\n");
    lsu_write_32(CLP_ABR_REG_MLDSA_CTRL, MLDSA_CMD_KEYGEN_SIGN | 
                                          ((1 << ABR_REG_MLDSA_CTRL_PCR_SIGN_LOW) & ABR_REG_MLDSA_CTRL_PCR_SIGN_MASK));

    // wait for MLDSA SIGNING process to be done
    wait_for_mldsa_intr();

    cptra_intr_rcv.abr_notif = 0;
    mldsa_zeroize();

    printf("%c",0xff); //End the test

}


