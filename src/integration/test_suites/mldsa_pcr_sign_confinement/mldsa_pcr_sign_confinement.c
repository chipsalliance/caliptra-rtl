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
// Checks that the ML-DSA PCR signing seed can only be used by an atomic
// PCR_SIGN + KEYGEN_SIGN command over the hardware PCR digest. Each phase runs
// after a warm reset:
//   0: valid PCR signing (checked by the TB); a follow-on command before
//      zeroize must not start
//   1: PCR_SIGN with EXTERNAL_MU -> ERROR; a follow-on command must not start
//   2: PCR_SIGN with STREAM_MSG  -> ERROR, no signature
//   3: PCR_SIGN without a command (staged seed) -> ERROR; a follow-on
//      KEYGEN_SIGN with EXTERNAL_MU must not start
//   4: PCR_SIGN with SIGN -> ERROR, no signature

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "riscv_hw_if.h"
#include "riscv-csr.h"
#include "printf.h"
#include "mldsa.h"

volatile char*    stdout           = (char *)STDOUT;
volatile uint32_t intr_count = 0;
volatile uint32_t  rst_count __attribute__((section(".dccm.persistent"))) = 0;
// Status polls measured for one PCR signing operation in phase 0
volatile uint32_t  sign_polls __attribute__((section(".dccm.persistent"))) = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

#define MLDSA_CTRL_PCR_SIGN    ((1 << ABR_REG_MLDSA_CTRL_PCR_SIGN_LOW)    & ABR_REG_MLDSA_CTRL_PCR_SIGN_MASK)
#define MLDSA_CTRL_EXTERNAL_MU ((1 << ABR_REG_MLDSA_CTRL_EXTERNAL_MU_LOW) & ABR_REG_MLDSA_CTRL_EXTERNAL_MU_MASK)
#define MLDSA_CTRL_STREAM_MSG  ((1 << ABR_REG_MLDSA_CTRL_STREAM_MSG_LOW)  & ABR_REG_MLDSA_CTRL_STREAM_MSG_MASK)

// The error is flagged a few cycles after the command
#define ERROR_POLL_LIMIT 200
// Observation window when phase 0 did not run (per-phase debug builds)
#define DEFAULT_SIGN_POLLS 20000

void fail(const char *msg) {
    VPRINTF(ERROR, "%s", msg);
    SEND_STDOUT_CTRL(0x1);
    while(1);
}

uint32_t mldsa_status() {
    return lsu_read_32(CLP_ABR_REG_MLDSA_STATUS);
}

void wait_mldsa_ready() {
    while((mldsa_status() & ABR_REG_MLDSA_STATUS_READY_MASK) == 0);
}

void expect_mldsa_error(const char *what) {
    uint32_t status = 0;
    for (uint32_t i = 0; i < ERROR_POLL_LIMIT; i++) {
        status = mldsa_status();
        if (status & ABR_REG_MLDSA_STATUS_ERROR_MASK) break;
    }
    if ((status & ABR_REG_MLDSA_STATUS_ERROR_MASK) == 0) {
        VPRINTF(ERROR, "%s: MLDSA_STATUS = 0x%x\n", what, status);
        fail("MLDSA error was not reported\n");
    }
    for (uint32_t i = 0; (i < ERROR_POLL_LIMIT) && (cptra_intr_rcv.abr_error == 0); i++)
        mldsa_status();
    if (cptra_intr_rcv.abr_error == 0) fail("MLDSA error interrupt was not raised\n");
    VPRINTF(LOW, "%s: rejected as expected\n", what);
}

// Observe for twice the measured signing time: no operation may start or complete
void expect_no_operation(uint32_t status_mask, const char *what) {
    uint32_t window = 2 * (sign_polls ? sign_polls : DEFAULT_SIGN_POLLS);
    cptra_intr_rcv.abr_notif = 0;
    for (uint32_t i = 0; i < window; i++) {
        uint32_t status = mldsa_status();
        if ((status & status_mask) != 0) {
            VPRINTF(ERROR, "%s: MLDSA_STATUS = 0x%x\n", what, status);
            fail("MLDSA started or completed an operation\n");
        }
        if (cptra_intr_rcv.abr_notif != 0) {
            VPRINTF(ERROR, "%s: MLDSA_STATUS = 0x%x\n", what, status);
            fail("MLDSA completion interrupt observed\n");
        }
    }
    VPRINTF(LOW, "%s: no operation as expected\n", what);
}

void start_phase(const char *name) {
    wait_mldsa_ready();
    VPRINTF(LOW, "\n %s\n", name);
    SEND_STDOUT_CTRL(0x93);
    wait_mldsa_ready();
}

void next_phase() {
    mldsa_zeroize();
    rst_count++;
    SEND_STDOUT_CTRL(0xf6);
}

void main() {
    VPRINTF(LOW, "---------------------------------------\n");
    VPRINTF(LOW, " MLDSA PCR signing confinement test !!\n");
    VPRINTF(LOW, "---------------------------------------\n");

    init_interrupts();
    // DCCM is not reloaded on warm reset; drop interrupt flags left by the previous phase
    cptra_intr_rcv.abr_error = 0;
    cptra_intr_rcv.abr_notif = 0;

    if (rst_count == 0) {
        start_phase("TEST VALID PCR SIGNING");
        lsu_write_32(CLP_ABR_REG_MLDSA_CTRL, MLDSA_CMD_KEYGEN_SIGN | MLDSA_CTRL_PCR_SIGN);
        sign_polls = 0;
        while ((cptra_intr_rcv.abr_notif == 0) && (cptra_intr_rcv.abr_error == 0)) {
            mldsa_status();
            sign_polls++;
        }
        if (cptra_intr_rcv.abr_error != 0) fail("Valid PCR signing reported an error\n");
        VPRINTF(LOW, "PCR signing took %d status polls\n", sign_polls);
        SEND_STDOUT_CTRL(0x94);

        lsu_write_32(CLP_ABR_REG_MLDSA_CTRL, MLDSA_CMD_KEYGEN_SIGN | MLDSA_CTRL_EXTERNAL_MU);
        expect_no_operation(ABR_REG_MLDSA_STATUS_READY_MASK, "KEYGEN_SIGN + EXTERNAL_MU after PCR signing");
        next_phase();
    }
    else if (rst_count == 1) {
        start_phase("TEST PCR_SIGN WITH EXTERNAL_MU");
        lsu_write_32(CLP_ABR_REG_MLDSA_CTRL, MLDSA_CMD_KEYGEN_SIGN | MLDSA_CTRL_PCR_SIGN | MLDSA_CTRL_EXTERNAL_MU);
        expect_mldsa_error("PCR_SIGN + EXTERNAL_MU");
        lsu_write_32(CLP_ABR_REG_MLDSA_CTRL, MLDSA_CMD_KEYGEN_SIGN | MLDSA_CTRL_EXTERNAL_MU);
        expect_no_operation(ABR_REG_MLDSA_STATUS_READY_MASK | ABR_REG_MLDSA_STATUS_VALID_MASK, "Command after PCR_SIGN + EXTERNAL_MU");
        next_phase();
    }
    else if (rst_count == 2) {
        start_phase("TEST PCR_SIGN WITH STREAM_MSG");
        lsu_write_32(CLP_ABR_REG_MLDSA_CTRL, MLDSA_CMD_KEYGEN_SIGN | MLDSA_CTRL_PCR_SIGN | MLDSA_CTRL_STREAM_MSG);
        expect_mldsa_error("PCR_SIGN + STREAM_MSG");
        expect_no_operation(ABR_REG_MLDSA_STATUS_READY_MASK | ABR_REG_MLDSA_STATUS_VALID_MASK, "PCR_SIGN + STREAM_MSG");
        next_phase();
    }
    else if (rst_count == 3) {
        start_phase("TEST PCR_SIGN WITHOUT A COMMAND");
        lsu_write_32(CLP_ABR_REG_MLDSA_CTRL, MLDSA_CTRL_PCR_SIGN);
        expect_mldsa_error("PCR_SIGN without a command");
        lsu_write_32(CLP_ABR_REG_MLDSA_CTRL, MLDSA_CMD_KEYGEN_SIGN | MLDSA_CTRL_EXTERNAL_MU);
        expect_no_operation(ABR_REG_MLDSA_STATUS_READY_MASK | ABR_REG_MLDSA_STATUS_VALID_MASK, "KEYGEN_SIGN + EXTERNAL_MU with staged PCR seed");
        next_phase();
    }
    else {
        start_phase("TEST PCR_SIGN WITH SIGN");
        lsu_write_32(CLP_ABR_REG_MLDSA_CTRL, MLDSA_CMD_SIGNING | MLDSA_CTRL_PCR_SIGN);
        expect_mldsa_error("PCR_SIGN + SIGN");
        expect_no_operation(ABR_REG_MLDSA_STATUS_READY_MASK | ABR_REG_MLDSA_STATUS_VALID_MASK, "PCR_SIGN + SIGN");
        mldsa_zeroize();
        SEND_STDOUT_CTRL(0xff);
    }
}
