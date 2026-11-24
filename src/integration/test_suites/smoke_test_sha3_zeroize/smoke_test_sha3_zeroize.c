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

// SHA3 zeroize test:
//   1. Run a SHA3-512 operation and check the digest.
//      Zeroize while the digest is still exposed in the STATE window.
//      Check that zeroize worked.
//   2. Run a full SHA3-512 operation right after the zeroize and check the digest.
//   3. Start another SHA3-512 operation and zeroize while it is absorbing.
//      Check that zeroize worked.
//   4. Run the first operation again and check the digest.
//   5. Zeroize at random points: a random number of times, start an operation,
//      stop it at a random point (idle, started, after absorbing a random number
//      of bytes, while processing, squeezing, after a manual RUN or DONE, after
//      a cSHAKE start) and zeroize after a random delay.
//      Check that zeroize worked and that a following operation is correct.
//      The random points depend on MY_RANDOM_SEED.

#include "caliptra_isr.h"
#include "caliptra_rtl_lib.h"
#include "printf.h"
#include "sha3.h"
#include <string.h>

#ifdef CPT_VERBOSITY
  enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
  enum printf_verbosity verbosity_g = LOW;
#endif
volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count       = 0;

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

// SHA3_CTRL register (not yet in the generated caliptra_reg.h)
#ifndef CLP_SHA3_SHA3_CTRL
#define CLP_SHA3_SHA3_CTRL               (CLP_SHA3_BASE_ADDR + 0x10)
#endif
#ifndef SHA3_SHA3_CTRL_ZEROIZE_MASK
#define SHA3_SHA3_CTRL_ZEROIZE_MASK      (0x1)
#endif

// Number of message bytes absorbed before zeroizing the running operation.
// Larger than the SHA3-512 rate (72 bytes) so that a Keccak permutation has
// run and the remaining partial block is held in the Keccak state.
#define PARTIAL_MSG_LEN (100)

// Randomized zeroize (step 5)
#define NUM_RAND_ZEROIZE (16)
// Short enough to zeroize while the Keccak permutation is still running
#define MAX_RAND_DELAY   (16)

enum {
  kZeroizeIdle,       // engine idle
  kZeroizeStarted,    // operation started, nothing absorbed
  kZeroizeAbsorbing,  // a random number of message bytes absorbed
  kZeroizeProcessing, // whole message absorbed, PROCESS issued
  kZeroizeSqueezing,  // digest computed, still exposed in the STATE window
  kZeroizeManualRun,  // digest computed, RUN issued (manual Keccak run)
  kZeroizeDone,       // digest computed, DONE issued (state flush)
  kZeroizeCshake,     // cSHAKE operation started (prefix absorbed)
  kNumZeroizePoints
};

const char *const kZeroizePointNames[kNumZeroizePoints] = {
  "idle", "started", "absorbing", "processing", "squeezing", "manual run", "done", "cshake"};

// Example taken from NIST FIPS-202 Algorithm Test Vectors:
// https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/sha3/sha-3bytetestvectors.zip
const dif_kmac_mode_sha3_t kMode = kDifKmacModeSha3Len512;
const char kMsg[] =
    "\x66\x4e\xf2\xe3\xa7\x05\x9d\xaf\x1c\x58\xca\xf5\x20\x08\xc5\x22"
    "\x7e\x85\xcd\xcb\x83\xb4\xc5\x94\x57\xf0\x2c\x50\x8d\x4f\x4f\x69"
    "\xf8\x26\xbd\x82\xc0\xcf\xfc\x5c\xb6\xa9\x7a\xf6\xe5\x61\xc6\xf9"
    "\x69\x70\x00\x52\x85\xe5\x8f\x21\xef\x65\x11\xd2\x6e\x70\x98\x89"
    "\xa7\xe5\x13\xc4\x34\xc9\x0a\x3c\xf7\x44\x8f\x0c\xae\xec\x71\x14"
    "\xc7\x47\xb2\xa0\x75\x8a\x3b\x45\x03\xa7\xcf\x0c\x69\x87\x3e\xd3"
    "\x1d\x94\xdb\xef\x2b\x7b\x2f\x16\x88\x30\xef\x7d\xa3\x32\x2c\x3d"
    "\x3e\x10\xca\xfb\x7c\x2c\x33\xc8\x3b\xbf\x4c\x46\xa3\x1d\xa9\x0c"
    "\xff\x3b\xfd\x4c\xcc\x6e\xd4\xb3\x10\x75\x84\x91\xee\xba\x60\x3a"
    "\x76";
const size_t kMsgLen = 1160 / 8;
const uint32_t kExpectedDigest[DIGEST_LEN_SHA3_512] = {
    0xf15f82e5, 0xd570c0a3, 0xe7bb2fa5, 0x444a8511, 0x5f295405,
    0x69797afb, 0xd10879a1, 0xbebf6301, 0xa6521d8f, 0x13a0e876,
    0x1ca1567b, 0xb4fb0fdf, 0x9f89bc56, 0x4bd127c7, 0x322288d8,
    0x4e919d54};

void fail() {
  SEND_STDOUT_CTRL(0x1); // Terminate test with failure.
  while (1);
}

void sha3_zeroize() {
  lsu_write_32(CLP_SHA3_SHA3_CTRL, SHA3_SHA3_CTRL_ZEROIZE_MASK);
}

/**
 * Run a complete SHA3-512 operation over kMsg up to the squeeze phase.
 * The engine is left in the squeeze state (DONE is not issued) so that the
 * digest is still exposed in the STATE window.
 */
void run_sha3_until_squeeze(uintptr_t kmac, dif_kmac_operation_state_t *operation_state,
                            uint32_t *digest) {
  dif_kmac_mode_sha3_start(kmac, operation_state, kMode, kDifKmacMsgEndiannessLittle);
  dif_kmac_absorb(kmac, operation_state, kMsg, kMsgLen, NULL);
  dif_kmac_squeeze(kmac, operation_state, digest, DIGEST_LEN_SHA3_512,
                   /*processed=*/NULL, /*capacity=*/NULL);
}

void check_digest(const char *ctx, const uint32_t *got, const uint32_t *want) {
  for (int i = 0; i < DIGEST_LEN_SHA3_512; ++i) {
    if (got[i] != want[i]) {
      VPRINTF(ERROR, "%s: digest mismatch at %d got=0x%x want=0x%x\n", ctx, i, got[i], want[i]);
      fail();
    }
  }
}

/**
 * Check that the SHA3 engine has been zeroized:
 *  - engine idle, not absorbing or squeezing, config unlocked
 *  - message FIFO empty
 *  - whole STATE window reads zero
 *  - no error or fatal alert raised by the zeroize
 */
void check_zeroized(uintptr_t kmac, const char *ctx) {
  uint32_t status = lsu_read_32(kmac + KMAC_STATUS);
  VPRINTF(LOW, "%s: STATUS after zeroize = 0x%x\n", ctx, status);

  if (!(status & KMAC_STATUS_SHA3_IDLE_MASK)) {
    VPRINTF(ERROR, "%s: engine not idle after zeroize\n", ctx);
    fail();
  }
  if (status & (KMAC_STATUS_SHA3_ABSORB_MASK | KMAC_STATUS_SHA3_SQUEEZE_MASK)) {
    VPRINTF(ERROR, "%s: engine still absorbing/squeezing after zeroize\n", ctx);
    fail();
  }
  if (!(status & KMAC_STATUS_FIFO_EMPTY_MASK) || (status & KMAC_STATUS_FIFO_DEPTH_MASK)) {
    VPRINTF(ERROR, "%s: message FIFO not empty after zeroize\n", ctx);
    fail();
  }
  if (status & KMAC_STATUS_ALERT_FATAL_FAULT_MASK) {
    VPRINTF(ERROR, "%s: fatal fault after zeroize\n", ctx);
    fail();
  }
  if (!(lsu_read_32(kmac + KMAC_CFG_REGWEN) & KMAC_CFG_REGWEN_EN_MASK)) {
    VPRINTF(ERROR, "%s: config still locked after zeroize\n", ctx);
    fail();
  }

  for (uint32_t addr = CLP_KMAC_STATE_BASE_ADDR; addr <= CLP_KMAC_STATE_END_ADDR;
       addr += sizeof(uint32_t)) {
    uint32_t word = lsu_read_32(addr);
    if (word != 0) {
      VPRINTF(ERROR, "%s: STATE at 0x%x = 0x%x not zero after zeroize\n", ctx, addr, word);
      fail();
    }
  }

  uint32_t err_code = lsu_read_32(kmac + KMAC_ERR_CODE);
  if (err_code != 0) {
    VPRINTF(ERROR, "%s: ERR_CODE = 0x%x after zeroize\n", ctx, err_code);
    fail();
  }
  if ((lsu_read_32(CLP_KMAC_INTR_STATE) & KMAC_INTR_STATE_KMAC_ERR_MASK) ||
      cptra_intr_rcv.sha3_error) {
    VPRINTF(ERROR, "%s: SHA3 error interrupt after zeroize\n", ctx);
    fail();
  }
}

/**
 * Zeroize at random points: NUM_RAND_ZEROIZE times, stop an operation at a
 * random point (see kZeroizePointNames) and zeroize after a short random delay.
 * Check that zeroize worked and that a following operation is correct.
 */
void run_random_zeroize_test(uintptr_t kmac) {
  dif_kmac_operation_state_t operation_state;
  uint32_t digest[DIGEST_LEN_SHA3_512];
  dif_kmac_function_name_t n;

  dif_kmac_function_name_init("ZERO", 4, &n);

  VPRINTF(LOW, "Step 5: zeroize at random points (seed 0x%x)\n", MY_RANDOM_SEED);
  for (int i = 0; i < NUM_RAND_ZEROIZE; i++) {
    uint32_t point = xorshift32() % kNumZeroizePoints;
    uint32_t len   = 0;
    uint32_t delay = xorshift32() % MAX_RAND_DELAY;

    if (point == kZeroizeCshake) {
      dif_kmac_mode_cshake_start(kmac, &operation_state, kDifKmacModeCshakeLen128, &n, NULL,
                                 kDifKmacMsgEndiannessLittle);
    } else if (point >= kZeroizeStarted) {
      dif_kmac_mode_sha3_start(kmac, &operation_state, kMode, kDifKmacMsgEndiannessLittle);
    }
    if (point == kZeroizeAbsorbing) {
      len = 1 + xorshift32() % kMsgLen;
      dif_kmac_absorb(kmac, &operation_state, kMsg, len, NULL);
    } else if (point == kZeroizeProcessing) {
      dif_kmac_absorb(kmac, &operation_state, kMsg, kMsgLen, NULL);
      // Issue PROCESS without reading the digest
      dif_kmac_squeeze(kmac, &operation_state, NULL, 0, NULL, NULL);
    } else if (point >= kZeroizeSqueezing && point <= kZeroizeDone) {
      dif_kmac_absorb(kmac, &operation_state, kMsg, kMsgLen, NULL);
      dif_kmac_squeeze(kmac, &operation_state, digest, DIGEST_LEN_SHA3_512, NULL, NULL);
      if (point == kZeroizeManualRun) {
        // Zeroize directly after RUN, while the manual Keccak run (~24 cycles)
        // is still ongoing
        lsu_write_32(kmac + KMAC_CMD, KMAC_CMD_CMD_VALUE_RUN << KMAC_CMD_CMD_LOW);
        lsu_write_32(CLP_SHA3_SHA3_CTRL, SHA3_SHA3_CTRL_ZEROIZE_MASK);
      } else if (point == kZeroizeDone) {
        lsu_write_32(kmac + KMAC_CMD, KMAC_CMD_CMD_VALUE_DONE << KMAC_CMD_CMD_LOW);
      }
    }

    if (point != kZeroizeManualRun) {
      // A short random delay, e.g. to hit a running Keccak permutation
      for (volatile uint32_t d = delay; d > 0; d--);
      sha3_zeroize();
    }
    VPRINTF(LOW, "Step 5.%d: zeroized %s (%d bytes absorbed, delay %d)\n",
            i, kZeroizePointNames[point], len, delay);
    check_zeroized(kmac, "random zeroize");

    run_sha3_until_squeeze(kmac, &operation_state, digest);
    dif_kmac_end(kmac, &operation_state);
    dif_kmac_poll_status(kmac, KMAC_STATUS_SHA3_IDLE_LOW);
    check_digest("run after random zeroize", digest, kExpectedDigest);
  }
}

void main() {
  uintptr_t kmac = CLP_KMAC_BASE_ADDR;
  dif_kmac_operation_state_t operation_state;
  uint32_t digest[DIGEST_LEN_SHA3_512];
  uint32_t status;

  VPRINTF(LOW, "----------------------------------\n");
  VPRINTF(LOW, " SHA3 zeroize test!\n"               );
  VPRINTF(LOW, "----------------------------------\n");

  init_interrupts();

  // ---------------------------------------------------------------------
  // 1. First SHA3 operation, then zeroize after completion
  // ---------------------------------------------------------------------
  VPRINTF(LOW, "Step 1: first SHA3-512 operation\n");
  run_sha3_until_squeeze(kmac, &operation_state, digest);
  check_digest("first run", digest, kExpectedDigest);

  // The digest must be exposed in the STATE window before zeroize
  if (lsu_read_32(CLP_KMAC_STATE_BASE_ADDR) != kExpectedDigest[0]) {
    VPRINTF(ERROR, "first run: digest not visible in STATE before zeroize\n");
    fail();
  }

  VPRINTF(LOW, "Step 1: zeroize after completion\n");
  sha3_zeroize();
  check_zeroized(kmac, "zeroize after completion");

  // ---------------------------------------------------------------------
  // 2. Full SHA3 operation after zeroize
  // ---------------------------------------------------------------------
  VPRINTF(LOW, "Step 2: full SHA3-512 operation after zeroize\n");
  run_sha3_until_squeeze(kmac, &operation_state, digest);
  dif_kmac_end(kmac, &operation_state);
  dif_kmac_poll_status(kmac, KMAC_STATUS_SHA3_IDLE_LOW);

  check_digest("second run", digest, kExpectedDigest);

  // ---------------------------------------------------------------------
  // 3. Third SHA3 operation, zeroize while it is running
  // ---------------------------------------------------------------------
  VPRINTF(LOW, "Step 3: SHA3-512 operation interrupted by zeroize\n");
  dif_kmac_mode_sha3_start(kmac, &operation_state, kMode, kDifKmacMsgEndiannessLittle);
  dif_kmac_absorb(kmac, &operation_state, kMsg, PARTIAL_MSG_LEN, NULL);

  // Make sure the operation is still running
  status = lsu_read_32(kmac + KMAC_STATUS);
  if (!(status & KMAC_STATUS_SHA3_ABSORB_MASK)) {
    VPRINTF(ERROR, "third run: engine not absorbing before zeroize (STATUS = 0x%x)\n", status);
    fail();
  }

  VPRINTF(LOW, "Step 3: zeroize while absorbing (STATUS = 0x%x)\n", status);
  sha3_zeroize();
  check_zeroized(kmac, "zeroize while running");

  // ---------------------------------------------------------------------
  // 4. Repeat the first SHA3 operation and check the digest
  // ---------------------------------------------------------------------
  VPRINTF(LOW, "Step 4: repeat first SHA3-512 operation\n");
  run_sha3_until_squeeze(kmac, &operation_state, digest);
  dif_kmac_end(kmac, &operation_state);
  dif_kmac_poll_status(kmac, KMAC_STATUS_SHA3_IDLE_LOW);

  check_digest("fourth run", digest, kExpectedDigest);

  // ---------------------------------------------------------------------
  // 5. Zeroize at random points
  // ---------------------------------------------------------------------
  run_random_zeroize_test(kmac);

  VPRINTF(LOW, "SHA3 zeroize test passed\n");

  // Write 0xff to STDOUT for TB to terminate test.
  SEND_STDOUT_CTRL(0xff);
  while (1);
}
