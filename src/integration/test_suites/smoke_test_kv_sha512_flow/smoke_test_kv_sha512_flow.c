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
#include <string.h>
#include <stdint.h>
#include <stdlib.h>
#include "printf.h"
#include "sha512.h"

volatile char*    stdout           = (char *)STDOUT;
volatile uint32_t intr_count = 0;
volatile uint32_t rst_count = 0;
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


/* SHA384 test vector:
    block = b1eeef324b499f19eba322215fe3ce19c9f000b698d2b2dab7145015046cc86d049ee15ad59dcd1564f30112e06444cb
    digest = 38742d18bfa6e918b888d68d1034e61f65dec0759172c2dbf08cf1e132b217eaf4ec29e15db7f4b07e08a70cc5662012
*/

void main() {
    printf("----------------------------------\n");
    printf(" KV Smoke Test With SHA384 flow !!\n");
    printf("----------------------------------\n");

    //Call interrupt init
    init_interrupts();

    uint32_t expected_digest[] =   {0x38742d18,
                                    0xbfa6e918,
                                    0xb888d68d,
                                    0x1034e61f,
                                    0x65dec075,
                                    0x9172c2db,
                                    0xf08cf1e1,
                                    0x32b217ea,
                                    0xf4ec29e1,
                                    0x5db7f4b0,
                                    0x7e08a70c,
                                    0xc5662012};

    uint8_t shablock_kv_id = 0x0;
    uint8_t store_to_kv = 0x1;
    uint8_t digest_kv_id = 0x0;
    sha384_kvflow(shablock_kv_id, store_to_kv, digest_kv_id, expected_digest);

    sha512_zeroize();
    
    printf("%c",0xff); //End the test
    
}
