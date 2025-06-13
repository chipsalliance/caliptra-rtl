// Copyright lowRISC contributors (OpenTitan project).
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

// Taken from the kmac smoke test in OpenTitan:
// https://github.com/lowRISC/opentitan/blob/master/sw/device/tests/kmac_smoketest.c

#include "caliptra_isr.h"
#include "printf.h"
#include "sha3.h"

#ifdef CPT_VERBOSITY
  enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
  enum printf_verbosity verbosity_g = LOW;
#endif
volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count       = 0;

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

/**
 * SHA-3 test description.
 */
typedef struct sha3_test {
  dif_kmac_mode_sha3_t mode;

  const char *message;
  size_t message_len;

  const uint32_t digest[DIGEST_LEN_SHA3_MAX];
  size_t digest_len;
} sha3_test_t;

/**
 * SHA-3 tests.
 */
const sha3_test_t sha3_tests[] = {
    // Examples taken from NIST FIPS-202 Algorithm Test Vectors:
    // https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/sha3/sha-3bytetestvectors.zip
    {
        .mode = kDifKmacModeSha3Len224,
        .message = NULL,
        .message_len = 0,
        .digest = {0x42034e6b, 0xb7db6736, 0x45156e3b, 0xabb10e4f, 0x9a7f59d4,
                   0x3f8e071b, 0xc76b5a5b},
        .digest_len = DIGEST_LEN_SHA3_224,
    },
    {
        .mode = kDifKmacModeSha3Len256,
        .message = "\xe7\x37\x21\x05",
        .message_len = 32 / 8,
        .digest = {0x8ab6423a, 0x8cf279b0, 0x52c7a34c, 0x90276f29, 0x78fec406,
                   0xd979ebb1, 0x057f7789, 0xae46401e},
        .digest_len = DIGEST_LEN_SHA3_256,
    },
    {
        .mode = kDifKmacModeSha3Len384,
        .message = "\xa7\x48\x47\x93\x0a\x03\xab\xee\xa4\x73\xe1\xf3\xdc\x30"
                   "\xb8\x88\x15",
        .message_len = 136 / 8,
        .digest = {0x29f9a6db, 0xd6f955fe, 0xc0675f6c, 0xf1823baf, 0xb358cf7b,
                   0x16f35267, 0x3f08165c, 0x78d48fea, 0xf20369ee, 0xd20a827f,
                   0xaf5099dd, 0x00678cb4},
        .digest_len = DIGEST_LEN_SHA3_384,
    },
    {
        .mode = kDifKmacModeSha3Len512,
        .message =
            "\x66\x4e\xf2\xe3\xa7\x05\x9d\xaf\x1c\x58\xca\xf5\x20\x08\xc5\x22"
            "\x7e\x85\xcd\xcb\x83\xb4\xc5\x94\x57\xf0\x2c\x50\x8d\x4f\x4f\x69"
            "\xf8\x26\xbd\x82\xc0\xcf\xfc\x5c\xb6\xa9\x7a\xf6\xe5\x61\xc6\xf9"
            "\x69\x70\x00\x52\x85\xe5\x8f\x21\xef\x65\x11\xd2\x6e\x70\x98\x89"
            "\xa7\xe5\x13\xc4\x34\xc9\x0a\x3c\xf7\x44\x8f\x0c\xae\xec\x71\x14"
            "\xc7\x47\xb2\xa0\x75\x8a\x3b\x45\x03\xa7\xcf\x0c\x69\x87\x3e\xd3"
            "\x1d\x94\xdb\xef\x2b\x7b\x2f\x16\x88\x30\xef\x7d\xa3\x32\x2c\x3d"
            "\x3e\x10\xca\xfb\x7c\x2c\x33\xc8\x3b\xbf\x4c\x46\xa3\x1d\xa9\x0c"
            "\xff\x3b\xfd\x4c\xcc\x6e\xd4\xb3\x10\x75\x84\x91\xee\xba\x60\x3a"
            "\x76",
        .message_len = 1160 / 8,
        .digest = {0xf15f82e5, 0xd570c0a3, 0xe7bb2fa5, 0x444a8511, 0x5f295405,
                   0x69797afb, 0xd10879a1, 0xbebf6301, 0xa6521d8f, 0x13a0e876,
                   0x1ca1567b, 0xb4fb0fdf, 0x9f89bc56, 0x4bd127c7, 0x322288d8,
                   0x4e919d54},
        .digest_len = DIGEST_LEN_SHA3_512,
    },
};

/**
 * Run SHA-3 test cases using single blocking absorb/squeeze operations.
 */
void run_sha3_test(uintptr_t kmac) {
  dif_kmac_operation_state_t operation_state;
  for (int i = 0; i < sizeof(sha3_tests) / sizeof(sha3_test_t); ++i) {
    printf("run_sha3_test: processing test with index %d\n", i);
    sha3_test_t test = sha3_tests[i];

    dif_kmac_mode_sha3_start(kmac, &operation_state, test.mode);
    if (test.message_len > 0) {
      dif_kmac_absorb(kmac, &operation_state, test.message,
                      test.message_len, NULL);
    }
    uint32_t out[DIGEST_LEN_SHA3_MAX];
    if (DIGEST_LEN_SHA3_MAX < test.digest_len) {
      printf("test.digest_len (%d) is greater than DIGEST_LEN_SHA3_MAX.\n", test.digest_len);
      while(1);
    }
    dif_kmac_squeeze(kmac, &operation_state, out, test.digest_len, /*processed=*/NULL, /*capacity=*/NULL);
    dif_kmac_end(kmac, &operation_state);

    // Wait for the hardware engine to actually finish. On FPGA, it may take
    // a while until the DONE command gets actually executed (see SecCmdDelay
    // SystemVerilog parameter).
    dif_kmac_poll_status(kmac, KMAC_STATUS_SHA3_IDLE_INDEX);

    for (int j = 0; j < test.digest_len; ++j) {
      if (out[j] != test.digest[j]) {
        printf("test %d: mismatch at %d got=0x%x want=0x%x", i, j, out[j], test.digest[j]);
        while (1);
        return;
      }
    }
  }
}

void main() {

  // Entry message
  VPRINTF(LOW, "----------------------------------\n");
  VPRINTF(LOW, " SHA3 smoke test!\n"                 );
  VPRINTF(LOW, "----------------------------------\n");

  // Call interrupt init
  init_interrupts();

  VPRINTF(LOW, "Running SHA3 tests.\n");
  run_sha3_test(0x10040000);

  // Write 0xff to STDOUT for TB to terminate test.
  SEND_STDOUT_CTRL( 0xff);
  while (1);

}
