// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// ECC debug-unlock and scan-mode transition zeroize smoke.
//
// Both transitions feed debug_lock_or_scan_mode_switch (caliptra_top.sv:823)
// which drives ECC's zeroize_reg via debugUnlock_or_scan_mode_switch
// (ecc_dsa_ctrl.sv:397). This test exercises both paths in sequence using
// persistent rst_count to survive the warm reset that debug-unlock requires.
//
// Phase 0 (rst_count==1): KEYGEN P-384 -> issue debug-unlock (0xfa) +
//   warm reset (0xf6). cptra_security_state_Latched_d/_f update at reset
//   deassert and pulse debug_lock_switch through the boot.
// Phase 1 (rst_count==2): on re-entry, verify ECC PRIVKEY_OUT and PUBKEY
//   register blocks are cleared. Then KEYGEN P-384 again -> scan-mode-on
//   via TB cmd 0xef (clean variant; 0xb9 also forces DOE_CTRL.CMD) ->
//   scan-mode-off (0xf0). Verify ECC registers are cleared a second time.

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "riscv_hw_if.h"
#include "riscv-csr.h"
#include "printf.h"
#include "ecc.h"

volatile uint32_t* stdout         = (uint32_t *)STDOUT;
volatile uint32_t  intr_count     = 0;
volatile uint32_t  rst_count __attribute__((section(".dccm.persistent"))) = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

// P-384 KAT (smoke_test_ecc_keygen vectors).
static const uint32_t p384_seed[]    = {0x8FA8541C,0x82A392CA,0x74F23ED1,0xDBFD7354,
                                        0x1C596639,0x1B97EA73,0xD744B0E3,0x4B9DF59E,
                                        0xD0158063,0xE39C09A5,0xA055371E,0xDF7A5441};
static const uint32_t p384_nonce[]   = {0x1B7EC5E5,0x48E8AAA9,0x2EC77097,0xCA9551C9,
                                        0x783CE682,0xCA18FB1E,0xDBD9F1E5,0x0BC382DB,
                                        0x8AB39496,0xC8EE423F,0x8CA105CB,0xBA7B6588};
static const uint32_t p384_iv[]      = {0x3401CEFA,0xE20A7376,0x49073AC1,0xA351E329,
                                        0x26DB9ED0,0xDB6B1CFF,0xAB0493DA,0xAFB93DDD,
                                        0xD83EDEA2,0x8A803D0D,0x003B2633,0xB9D0F1BF};
static const uint32_t p384_privkey[] = {0xF274F69D,0x163B0C9F,0x1FC3EBF4,0x292AD1C4,
                                        0xEB3CEC1C,0x5A7DDE6F,0x80C14292,0x934C2055,
                                        0xE087748D,0x0A169C77,0x2483ADEE,0x5EE70E17};
static const uint32_t p384_pubkey_x[] = {0xD79C6D97,0x2B34A1DF,0xC916A7B6,0xE0A99B6B,
                                         0x5387B34D,0xA2187607,0xC1AD0A4D,0x1A8C2E41,
                                         0x72AB5FA5,0xD9AB58FE,0x45E43F56,0xBBB66BA4};
static const uint32_t p384_pubkey_y[] = {0x5A736393,0x2B06B4F2,0x23BEF0B6,0x0A639026,
                                         0x5112DBBD,0x0AAE67FE,0xF26B465B,0xE935B48E,
                                         0x451E68D1,0x6F1118F2,0xB32B4C28,0x608749ED};

static void make_io(ecc_io *io, const uint32_t *data) {
    io->kv_intf = FALSE;
    for (int i = 0; i < ECC_INPUT_SIZE; i++) io->data[i] = data[i];
}

// Confirm a 12-dword output register block reads as zero after the transition.
static void check_cleared(uintptr_t base_addr, const char *label) {
    volatile uint32_t *reg_ptr = (volatile uint32_t *)base_addr;
    for (uint8_t i = 0; i < 12; i++) {
        if (reg_ptr[i] != 0) {
            VPRINTF(ERROR, "%s dword[%0d] not cleared: 0x%x\n",
                    label, i, reg_ptr[i]);
            SEND_STDOUT_CTRL(0x1); while(1);
        }
    }
    VPRINTF(LOW, "%s cleared cleanly.\n", label);
}

// Run a P-384 KEYGEN to populate PRIVKEY_OUT/PUBKEY for the next zeroize check.
static void run_p384_keygen(void) {
    ecc_io seed, nonce, iv, privkey, pubkey_x, pubkey_y;
    make_io(&seed,     p384_seed);
    make_io(&nonce,    p384_nonce);
    make_io(&iv,       p384_iv);
    make_io(&privkey,  p384_privkey);
    make_io(&pubkey_x, p384_pubkey_x);
    make_io(&pubkey_y, p384_pubkey_y);
    ecc_keygen_flow(seed, nonce, iv, privkey, pubkey_x, pubkey_y, TRUE, 0);
    cptra_intr_rcv.ecc_notif = 0;
}

void main() {
    VPRINTF(LOW, "----------------------------------------\n");
    VPRINTF(LOW, " ECC debug-unlock + scan-mode zeroize smoke\n");
    VPRINTF(LOW, "----------------------------------------\n");

    init_interrupts();
    rst_count++;

    switch (rst_count) {
        case 1: {
            // First entry: populate ECC, then debug-unlock + warm-reset.
            VPRINTF(LOW, "\n[1A] P-384 KEYGEN -> PRIVKEY_OUT populated\n");
            run_p384_keygen();
            VPRINTF(LOW, "\n[1B] Issue debug-unlock (0xfa) + warm reset (0xf6)\n");
            SEND_STDOUT_CTRL(0xfa);
            // TB applies security_state change after 100 cycles.
            for (volatile uint32_t i = 0; i < 500; i++) { __asm__ volatile ("nop"); }
            SEND_STDOUT_CTRL(0xf6);
            while (1);  // wait for warm reset
        }
        case 2: {
            // Re-entry after debug-unlock + warm reset.
            // cptra_security_state_Latched_d captured the new debug_locked=0
            // at reset deassert, pulsing debug_lock_switch -> ECC zeroize.
            while ((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);
            VPRINTF(LOW, "\n[2A] Verify ECC cleared after debug-unlock transition\n");
            check_cleared(CLP_ECC_REG_ECC_PRIVKEY_OUT_0, "PRIVKEY_OUT");
            check_cleared(CLP_ECC_REG_ECC_PUBKEY_X_0,    "PUBKEY_X");
            check_cleared(CLP_ECC_REG_ECC_PUBKEY_Y_0,    "PUBKEY_Y");

            // Now exercise the scan-mode path in the same boot. 0xef is the
            // clean "enable scan_mode after 100 cycles" backdoor; 0xb9 also
            // forces DOE_CTRL.CMD which would skew the test (see TB services
            // line 1622+ and smoke_test_doe_scan rst_count==2).
            VPRINTF(LOW, "\n[2B] P-384 KEYGEN -> PRIVKEY_OUT re-populated\n");
            run_p384_keygen();

            VPRINTF(LOW, "\n[2C] Enter scan mode (0xef), exit (0xf0)\n");
            SEND_STDOUT_CTRL(0xef);
            // 0xef enables scan_mode after a 100-cycle TB delay; let it propagate
            // through the double-flop and fire scan_mode_switch -> ECC zeroize.
            for (volatile uint32_t i = 0; i < 500; i++) { __asm__ volatile ("nop"); }
            SEND_STDOUT_CTRL(0xf0);
            // Let scan_mode_Latched double-flop deassert before reading registers.
            for (volatile uint32_t i = 0; i < 1000; i++) { __asm__ volatile ("nop"); }

            VPRINTF(LOW, "\n[2D] Verify ECC cleared after scan-mode transition\n");
            check_cleared(CLP_ECC_REG_ECC_PRIVKEY_OUT_0, "PRIVKEY_OUT");
            check_cleared(CLP_ECC_REG_ECC_PUBKEY_X_0,    "PUBKEY_X");
            check_cleared(CLP_ECC_REG_ECC_PUBKEY_Y_0,    "PUBKEY_Y");

            VPRINTF(LOW, "\nDebug-unlock + scan-mode zeroize smoke passed.\n");
            break;
        }
        default:
            break;
    }

    SEND_STDOUT_CTRL(0xff);
}
