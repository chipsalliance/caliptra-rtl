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
#include <string.h>
#include <stdint.h>
#include "printf.h"
#include "sha256.h"

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif
volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count       = 0;

volatile caliptra_intr_received_s cptra_intr_rcv = {0};


void main() {

    // Entry message
    VPRINTF(LOW, "----------------------------------\n");
    VPRINTF(LOW, " SHA256 wntz rand smoke test !!\n"   );
    VPRINTF(LOW, "----------------------------------\n");

    // Call interrupt init
    init_interrupts();

    // sha256_io sha256_block;
    // sha256_io sha256_digest;

    SEND_STDOUT_CTRL(0xdd); //Forces random block, w and n
    sha256_flow_wntz_rand(SHA256_MODE_SHA_256);
    sha256_zeroize();

    // Write 0xff to STDOUT for TB to terminate test.
    SEND_STDOUT_CTRL( 0xff);
    while(1);

}
