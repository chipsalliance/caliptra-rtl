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
// Directed test for ECC mandatory zeroize with PCR signing: after the PCR
// signing key is loaded from KV slot 7, no further ECC operation is accepted.
// ECC must stay not-ready (inputs, commands and KV read controls locked) after
// an operation completes or after ECC_CTRL.PCR_SIGN is written, until
// ECC_CTRL.ZEROIZE is issued. A bare PCR_SIGN (no SIGN command) must be reported
// as an error, and HW clears KV-sourced key material when an operation ends.

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "riscv_hw_if.h"
#include "riscv-csr.h"
#include "printf.h"
#include "ecc.h"

volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

/* ECC test vector (PRIVKEY is injected into KV slot 7, MSG into the PCR digest):
    MSG      = C8F518D4F3AA1BD46ED56C1C3C9E16FB800AF504DB98843548C5F623EE115F73D4C62ABC06D303B5D90D9A175087290D
    PRIVKEY  = F274F69D163B0C9F1FC3EBF4292AD1C4EB3CEC1C5A7DDE6F80C14292934C2055E087748D0A169C772483ADEE5EE70E17
    Sign_R   = 871E6EA4DDC5432CDDAA60FD7F055472D3C4DD41A5BFB26709E88C311A97093599A7C8F55B3974C19E4F5A7BFC1DD2AC
    SIGN_S   = 3E5552DE6403350EE70AD74E4B854D2DC4126BBF9C153A5D7A07BD4B85D06E45F850920E898FB7D34F80796DAE29365C
    IV       = 3401CEFAE20A737649073AC1A351E32926DB9ED0DB6B1CFFAB0493DAAFB93DDDD83EDEA28A803D0D003B2633B9D0F1BF
*/
static const uint32_t ecc_msg[12]         = {0xC8F518D4, 0xF3AA1BD4, 0x6ED56C1C, 0x3C9E16FB,
                                             0x800AF504, 0xDB988435, 0x48C5F623, 0xEE115F73,
                                             0xD4C62ABC, 0x06D303B5, 0xD90D9A17, 0x5087290D};

static const uint32_t ecc_privkey[12]     = {0xF274F69D, 0x163B0C9F, 0x1FC3EBF4, 0x292AD1C4,
                                             0xEB3CEC1C, 0x5A7DDE6F, 0x80C14292, 0x934C2055,
                                             0xE087748D, 0x0A169C77, 0x2483ADEE, 0x5EE70E17};

static const uint32_t expected_sign_r[12] = {0x871E6EA4, 0xDDC5432C, 0xDDAA60FD, 0x7F055472,
                                             0xD3C4DD41, 0xA5BFB267, 0x09E88C31, 0x1A970935,
                                             0x99A7C8F5, 0x5B3974C1, 0x9E4F5A7B, 0xFC1DD2AC};

static const uint32_t expected_sign_s[12] = {0x3E5552DE, 0x6403350E, 0xE70AD74E, 0x4B854D2D,
                                             0xC4126BBF, 0x9C153A5D, 0x7A07BD4B, 0x85D06E45,
                                             0xF850920E, 0x898FB7D3, 0x4F80796D, 0xAE29365C};

static const uint32_t ecc_iv[12]          = {0x3401CEFA, 0xE20A7376, 0x49073AC1, 0xA351E329,
                                             0x26DB9ED0, 0xDB6B1CFF, 0xAB0493DA, 0xAFB93DDD,
                                             0xD83EDEA2, 0x8A803D0D, 0x003B2633, 0xB9D0F1BF};

#define TEST_MSG_DWORD     0xA5A5A5A5
#define TEST_PRIVKEY_DWORD 0x00000001
#define TEST_SIGN_R_DWORD  0x5A5A5A5A
#define TEST_KV_RD_ENTRY   3

static void test_fail(const char *msg) {
    VPRINTF(ERROR, "ERROR: %s\n", msg);
    SEND_STDOUT_CTRL(0x1);
    while(1);
}

static uint32_t ecc_status(void) {
    return lsu_read_32(CLP_ECC_REG_ECC_STATUS);
}

static void ecc_fill_block(uint32_t addr, uint32_t value) {
    volatile uint32_t *reg_ptr = (uint32_t *) addr;
    for (int i = 0; i < 12; i++)
        *reg_ptr++ = value;
}

static void ecc_check_block(uint32_t addr, const uint32_t *expected, const char *name) {
    volatile uint32_t *reg_ptr = (uint32_t *) addr;
    for (int i = 0; i < 12; i++) {
        uint32_t actual = *reg_ptr++;
        if (actual != expected[i]) {
            VPRINTF(ERROR, "%s[%d] = 0x%x, expected 0x%x\n", name, i, actual, expected[i]);
            test_fail("ECC result register mismatch");
        }
    }
}

// Attempt to start another operation before zeroize: overwrite the inputs, redirect
// the KV private key read and start a firmware controlled signing.
static void try_op_before_zeroize(void) {
    ecc_fill_block(CLP_ECC_REG_ECC_MSG_0, TEST_MSG_DWORD);
    ecc_fill_block(CLP_ECC_REG_ECC_PRIVKEY_IN_0, TEST_PRIVKEY_DWORD);
    ecc_fill_block(CLP_ECC_REG_ECC_SIGN_R_0, TEST_SIGN_R_DWORD);
    lsu_write_32(CLP_ECC_REG_ECC_KV_RD_PKEY_CTRL, ECC_REG_ECC_KV_RD_PKEY_CTRL_READ_EN_MASK |
                 ((TEST_KV_RD_ENTRY << ECC_REG_ECC_KV_RD_PKEY_CTRL_READ_ENTRY_LOW) & ECC_REG_ECC_KV_RD_PKEY_CTRL_READ_ENTRY_MASK));
    lsu_write_32(CLP_ECC_REG_ECC_CTRL, ECC_CMD_SIGNING);
    lsu_write_32(CLP_ECC_REG_ECC_CTRL, ECC_CMD_SIGNING |
                 ((1 << ECC_REG_ECC_CTRL_PCR_SIGN_LOW) & ECC_REG_ECC_CTRL_PCR_SIGN_MASK));
}

static void check_kv_rd_ctrl_locked(uint32_t kv_rd_ctrl_before) {
    if (lsu_read_32(CLP_ECC_REG_ECC_KV_RD_PKEY_CTRL) != kv_rd_ctrl_before)
        test_fail("ECC_KV_RD_PKEY_CTRL was writable before zeroize");
}

void main() {
    volatile uint32_t *reg_ptr;
    uint32_t poll_cnt;
    uint32_t kv_rd_ctrl_before;
    ecc_io privkey, msg, iv, sign_r, sign_s;

    VPRINTF(LOW, "------------------------------------------------\n");
    VPRINTF(LOW, " ECC PCR signing mandatory zeroize\n");
    VPRINTF(LOW, "------------------------------------------------\n");

    init_interrupts();

    // (a) Load the PCR signing key into KV slot 7 and the PCR hash into the SHA512 digest
    VPRINTF(LOW, "Inject PRIVKEY into KV slot 7\n");
    SEND_STDOUT_CTRL(0x88 + 0x7);
    VPRINTF(LOW, "Inject MSG into SHA512 digest\n");
    SEND_STDOUT_CTRL(0x90);

    // (b) PCR signing
    while ((ecc_status() & ECC_REG_ECC_STATUS_READY_MASK) == 0);
    reg_ptr = (uint32_t *) CLP_ECC_REG_ECC_IV_0;
    for (int i = 0; i < 12; i++)
        *reg_ptr++ = ecc_iv[i];

    VPRINTF(LOW, "ECC PCR SIGNING\n");
    lsu_write_32(CLP_ECC_REG_ECC_CTRL, ECC_CMD_SIGNING |
                 ((1 << ECC_REG_ECC_CTRL_PCR_SIGN_LOW) & ECC_REG_ECC_CTRL_PCR_SIGN_MASK));

    // Count status polls during a full signing to calibrate the observation window in (d)
    poll_cnt = 0;
    while ((ecc_status() & ECC_REG_ECC_STATUS_VALID_MASK) == 0)
        poll_cnt++;
    VPRINTF(LOW, "PCR signing done after %d status polls\n", poll_cnt);

    if (cptra_intr_rcv.ecc_error != 0)
        test_fail("unexpected ECC error during PCR signing");
    ecc_check_block(CLP_ECC_REG_ECC_SIGN_R_0, expected_sign_r, "SIGN_R");
    ecc_check_block(CLP_ECC_REG_ECC_SIGN_S_0, expected_sign_s, "SIGN_S");
    while (cptra_intr_rcv.ecc_notif == 0);
    cptra_intr_rcv.ecc_notif = 0;

    // (c) Without zeroize, the engine must be locked
    VPRINTF(LOW, "Attempting ECC operation without zeroize\n");
    if ((ecc_status() & ECC_REG_ECC_STATUS_READY_MASK) != 0)
        test_fail("ECC reports READY after PCR signing without zeroize");

    kv_rd_ctrl_before = lsu_read_32(CLP_ECC_REG_ECC_KV_RD_PKEY_CTRL);
    try_op_before_zeroize();
    for (int i = 0; i < 100; i++)
        __asm__ volatile ("nop");

    // Starting any operation would clear VALID immediately
    if ((ecc_status() & (ECC_REG_ECC_STATUS_READY_MASK | ECC_REG_ECC_STATUS_VALID_MASK)) != ECC_REG_ECC_STATUS_VALID_MASK)
        test_fail("ECC status changed: a new operation was accepted after PCR signing");
    if ((cptra_intr_rcv.ecc_notif != 0) || (cptra_intr_rcv.ecc_error != 0))
        test_fail("ECC interrupt observed: a new operation ran after PCR signing");
    check_kv_rd_ctrl_locked(kv_rd_ctrl_before);
    ecc_check_block(CLP_ECC_REG_ECC_SIGN_R_0, expected_sign_r, "SIGN_R");
    ecc_check_block(CLP_ECC_REG_ECC_SIGN_S_0, expected_sign_s, "SIGN_S");
    VPRINTF(LOW, "ECC operation after PCR signing correctly blocked\n");

    // (d) Writing PCR_SIGN alone (without SIGN) is an error: HW clears the loaded key
    //     and the engine stays locked until zeroize
    ecc_zeroize();
    while ((ecc_status() & ECC_REG_ECC_STATUS_READY_MASK) == 0);

    VPRINTF(LOW, "Writing PCR_SIGN without a command\n");
    cptra_intr_rcv.ecc_error = 0;
    lsu_write_32(CLP_ECC_REG_ECC_CTRL, ((1 << ECC_REG_ECC_CTRL_PCR_SIGN_LOW) & ECC_REG_ECC_CTRL_PCR_SIGN_MASK));
    if ((ecc_status() & ECC_REG_ECC_STATUS_READY_MASK) != 0)
        test_fail("ECC reports READY after PCR key load without zeroize");
    // Bound the wait by the measured signing time; the error is raised within a few cycles
    for (uint32_t i = 0; (i < poll_cnt + 100) && (cptra_intr_rcv.ecc_error == 0); i++)
        __asm__ volatile ("nop");
    if (cptra_intr_rcv.ecc_error == 0)
        test_fail("bare PCR_SIGN did not raise an ECC error");
    cptra_intr_rcv.ecc_error = 0;

    kv_rd_ctrl_before = lsu_read_32(CLP_ECC_REG_ECC_KV_RD_PKEY_CTRL);
    try_op_before_zeroize();

    // Observe for twice the measured signing time: no operation may start or complete
    for (uint32_t i = 0; i < 2 * poll_cnt + 100; i++) {
        if ((ecc_status() & (ECC_REG_ECC_STATUS_READY_MASK | ECC_REG_ECC_STATUS_VALID_MASK)) != 0)
            test_fail("ECC status changed: an operation ran with the loaded PCR key");
        if ((cptra_intr_rcv.ecc_notif != 0) || (cptra_intr_rcv.ecc_error != 0))
            test_fail("ECC interrupt observed: an operation ran with the loaded PCR key");
    }
    check_kv_rd_ctrl_locked(kv_rd_ctrl_before);
    reg_ptr = (uint32_t *) CLP_ECC_REG_ECC_SIGN_R_0;
    for (int i = 0; i < 12; i++) {
        if (*reg_ptr++ != 0)
            test_fail("SIGN_R was writable after PCR key load without zeroize");
    }
    VPRINTF(LOW, "ECC operation after PCR_SIGN load correctly blocked\n");

    // (e) After zeroize a normal signing must still work
    ecc_zeroize();
    while ((ecc_status() & ECC_REG_ECC_STATUS_READY_MASK) == 0);

    privkey.kv_intf = FALSE;
    msg.kv_intf = FALSE;
    iv.kv_intf = FALSE;
    sign_r.kv_intf = FALSE;
    sign_s.kv_intf = FALSE;
    for (int i = 0; i < 12; i++) {
        privkey.data[i] = ecc_privkey[i];
        msg.data[i]     = ecc_msg[i];
        iv.data[i]      = ecc_iv[i];
        sign_r.data[i]  = expected_sign_r[i];
        sign_s.data[i]  = expected_sign_s[i];
    }

    cptra_intr_rcv.ecc_notif = 0;
    ecc_signing_flow(privkey, msg, iv, sign_r, sign_s, TRUE);
    if (cptra_intr_rcv.ecc_error != 0)
        test_fail("unexpected ECC error during the signing after zeroize");
    cptra_intr_rcv.ecc_notif = 0;

    ecc_zeroize();

    SEND_STDOUT_CTRL(0xff); //End the test
}
