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
// Verify the mandatory-zeroize contract enforced by hmac_core's
// CTRL_WAIT_ZEROIZE state. After any completed HMAC operation, the
// engine parks with STATUS.READY=0 until firmware writes
// HMAC512_CTRL.ZEROIZE. CTRL writes during the parked window are
// dropped via swwe=ready_reg, so a stray INIT/RESTORE cannot bypass
// the zeroize step. After ZEROIZE, STATUS.READY recovers and a new
// operation runs normally.
//
#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "riscv_hw_if.h"
#include "riscv-csr.h"
#include <string.h>
#include <stdint.h>
#include <stdlib.h>
#include "printf.h"
#include "hmac.h"
#include "caliptra_rtl_lib.h"

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif
volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count       = 0;

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

// HMAC-512 reference vector (RFC 4231 style single-block) reused
// across both operations in the test.
static const uint32_t sw_key[16] = {
    0x0b0b0b0b,0x0b0b0b0b,0x0b0b0b0b,0x0b0b0b0b,
    0x0b0b0b0b,0x0b0b0b0b,0x0b0b0b0b,0x0b0b0b0b,
    0x0b0b0b0b,0x0b0b0b0b,0x0b0b0b0b,0x0b0b0b0b,
    0x0b0b0b0b,0x0b0b0b0b,0x0b0b0b0b,0x0b0b0b0b};

static const uint32_t block_data[32] = {
    0x48692054,0x68657265,0x80000000,0x00000000,
    0x00000000,0x00000000,0x00000000,0x00000000,
    0x00000000,0x00000000,0x00000000,0x00000000,
    0x00000000,0x00000000,0x00000000,0x00000000,
    0x00000000,0x00000000,0x00000000,0x00000000,
    0x00000000,0x00000000,0x00000000,0x00000000,
    0x00000000,0x00000000,0x00000000,0x00000000,
    0x00000000,0x00000000,0x00000000,0x00000440};

static const uint32_t expected_tag_512[16] = {
    0x637edc6e,0x01dce7e6,0x742a9945,0x1aae82df,
    0x23da3e92,0x439e590e,0x43e761b3,0x3e910fb8,
    0xac2878eb,0xd5803f6f,0x0b61dbce,0x5e251ff8,
    0x789a4722,0xc1be65ae,0xa45fd464,0xe89f8f5b};

static const uint32_t lfsr_seed_dwords[6] = {
    0xfeedface,0xdeadbeef,0xcafef00d,0x12345678,0x9abcdef0,0x0badc0de};

static uint32_t status_read(void) {
    return lsu_read_32(CLP_HMAC_REG_HMAC512_STATUS);
}

static void run_single_block_op(void) {
    write_hmac_reg((volatile uint32_t *)CLP_HMAC_REG_HMAC512_KEY_0, (uint32_t *)sw_key, 16);
    write_hmac_reg((volatile uint32_t *)CLP_HMAC_REG_HMAC512_BLOCK_0, (uint32_t *)block_data, 32);
    write_hmac_reg((volatile uint32_t *)CLP_HMAC_REG_HMAC512_LFSR_SEED_0,
                   (uint32_t *)lfsr_seed_dwords, 6);
    hmac512_ctrl_write(HMAC_REG_HMAC512_CTRL_INIT_MASK |
                       HMAC_REG_HMAC512_CTRL_LAST_MASK, FALSE);
    hmac_wait_valid();
}

static void check_tag_matches(const uint32_t *expected) {
    volatile uint32_t *tag = (uint32_t *)CLP_HMAC_REG_HMAC512_TAG_0;
    for (int i = 0; i < 16; i++) {
        if (tag[i] != expected[i]) {
            VPRINTF(LOW, "FAIL: TAG[%0d]=0x%08x expected 0x%08x\n",
                    i, tag[i], expected[i]);
            SEND_STDOUT_CTRL(0x1);
            while (1);
        }
    }
}

void main(void) {
    VPRINTF(LOW, "HMAC mandatory-zeroize test\n");
    hmac_wait_ready();

    run_single_block_op();
    check_tag_matches(expected_tag_512);

    // CTRL_WAIT_ZEROIZE must keep STATUS.READY at 0 without an explicit ZEROIZE.
    for (volatile int i = 0; i < 64; i++) { __asm__ volatile ("nop"); }
    if (status_read() & HMAC_REG_HMAC512_STATUS_READY_MASK) {
        VPRINTF(LOW, "FAIL: engine left CTRL_WAIT_ZEROIZE without ZEROIZE\n");
        SEND_STDOUT_CTRL(0x1);
        while (1);
    }

    // CTRL writes must be dropped while parked (swwe=ready_reg).
    cptra_intr_rcv.hmac_notif = 0;
    cptra_intr_rcv.hmac_error = 0;
    hmac512_ctrl_write(HMAC_REG_HMAC512_CTRL_INIT_MASK |
                       HMAC_REG_HMAC512_CTRL_LAST_MASK, FALSE);
    for (volatile int i = 0; i < 256; i++) { __asm__ volatile ("nop"); }
    if (cptra_intr_rcv.hmac_notif != 0) {
        VPRINTF(LOW, "FAIL: engine accepted INIT without ZEROIZE\n");
        SEND_STDOUT_CTRL(0x1);
        while (1);
    }
    if (status_read() & HMAC_REG_HMAC512_STATUS_READY_MASK) {
        VPRINTF(LOW, "FAIL: STATUS.READY went high without ZEROIZE\n");
        SEND_STDOUT_CTRL(0x1);
        while (1);
    }

    hmac_zeroize();
    hmac_wait_ready();
    run_single_block_op();
    check_tag_matches(expected_tag_512);
    hmac_zeroize();

    SEND_STDOUT_CTRL(0xff);
    while (1);
}
