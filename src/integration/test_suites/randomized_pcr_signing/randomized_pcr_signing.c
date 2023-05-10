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
#include "ecc.h"

volatile char*    stdout           = (char *)STDOUT;
volatile uint32_t intr_count = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

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
};


void main(){
    volatile uint32_t * reg_ptr;

    printf("----------------------------------\n");
    printf(" Randomized PCR Signing flow !!\n");
    printf("----------------------------------\n");

    //Call interrupt init
    init_interrupts();

    //inject seed to kv key reg (in RTL)
    printf("Inject randomized PRIVKEY into KV slot and MSG into SHA512 digest\n");
    printf("%c", 0x91);
    
    while((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);

    // Enable ECC PCR SIGNING core
    printf("\nECC PCR SIGNING\n");
    lsu_write_32(CLP_ECC_REG_ECC_CTRL, ECC_CMD_SIGNING | 
                ((1 << ECC_REG_ECC_CTRL_PCR_SIGN_LOW) & ECC_REG_ECC_CTRL_PCR_SIGN_MASK));
    
    // wait for ECC SIGNING process to be done
    printf("ECC flow in progress...\n");
    while((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_VALID_MASK) == 0);
    
    // Read the data back from ECC register
    printf("Load SIGN_R data from ECC\n");
    reg_ptr = (uint32_t *) CLP_ECC_REG_ECC_SIGN_R_0;
    while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_SIGN_R_11) {
        printf("%x", *reg_ptr);
        reg_ptr++;
    }
    printf("\n");

    printf("Load SIGN_S data from ECC\n");
    reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_SIGN_S_0;
    while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_SIGN_S_11) {
        printf("%x", *reg_ptr); 
        reg_ptr++;
    }
    printf("\n");
    
    //inject seed to kv key reg (in RTL)
    printf("Check the signing results\n");
    printf("%c", 0x92);

    cptra_intr_rcv.ecc_notif = 0;

    ecc_zeroize();

    printf("%c",0xff); //End the test
}
