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

// HMAC-256 error trigger smoke test.
//
// Exercises the two illegal CTRL encodings the HMAC-256 block flags via
// error0_sts: LAST alone (no INIT/NEXT/RESTORE) and RESTORE alone
// (no NEXT/LAST). Each subtest checks that the error interrupt fires
// and that STATUS.READY comes back after ZEROIZE.

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "riscv_hw_if.h"
#include "riscv-csr.h"
#include <string.h>
#include <stdint.h>
#include "printf.h"
#include "hmac256.h"
#include "caliptra_rtl_lib.h"

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif
volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count       = 0;

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

void main() {

    init_interrupts();

    VPRINTF(LOW, "----------------------------------\n");
    VPRINTF(LOW, " HMAC256 error_trigger smoke test !!\n");
    VPRINTF(LOW, "----------------------------------\n");

    VPRINTF(LOW, " ***** HMAC256 last_alone_error !!\n");

    while ((lsu_read_32(CLP_HMAC256_REG_HMAC256_STATUS) &
            HMAC256_REG_HMAC256_STATUS_READY_MASK) == 0);

    lsu_write_32(CLP_HMAC256_REG_HMAC256_CTRL,
                 HMAC256_REG_HMAC256_CTRL_LAST_MASK);

    wait_for_hmac256_intr();
    if (cptra_intr_rcv.hmac256_error == 0) {
        VPRINTF(ERROR, "\nHMAC256 last_alone_error is not detected.\n");
        SEND_STDOUT_CTRL(0x1);
        while (1);
    }
    cptra_intr_rcv.hmac256_error = 0;
    hmac256_zeroize();

    while ((lsu_read_32(CLP_HMAC256_REG_HMAC256_STATUS) &
            HMAC256_REG_HMAC256_STATUS_READY_MASK) == 0);

    VPRINTF(LOW, " ***** HMAC256 restore_alone_error !!\n");

    lsu_write_32(CLP_HMAC256_REG_HMAC256_CTRL,
                 HMAC256_REG_HMAC256_CTRL_RESTORE_MASK);

    wait_for_hmac256_intr();
    if (cptra_intr_rcv.hmac256_error == 0) {
        VPRINTF(ERROR, "\nHMAC256 restore_alone_error is not detected.\n");
        SEND_STDOUT_CTRL(0x1);
        while (1);
    }
    cptra_intr_rcv.hmac256_error = 0;
    hmac256_zeroize();

    VPRINTF(LOW, "* TESTCASE PASSED\n");
    SEND_STDOUT_CTRL(0xff);
    while (1);
}
