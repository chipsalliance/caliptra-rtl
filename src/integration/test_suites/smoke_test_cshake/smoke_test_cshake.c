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
// https://github.com/lowRISC/opentitan/blob/master/sw/device/tests/kmac_mode_cshake_test.c

#include "caliptra_isr.h"
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

/**
 * cSHAKE test description.
 */
typedef struct cshake_test {
  dif_kmac_mode_cshake_t mode;

  const char *message;
  size_t message_len;

  const char *function_name;
  size_t function_name_len;

  const char *customization_string;
  size_t customization_string_len;

  const uint32_t digest[DIGEST_LEN_CSHAKE_MAX];
  size_t digest_len;
} cshake_test_t;

/**
 * cSHAKE tests.
 */
const cshake_test_t cshake_tests[] = {
    {
        .mode = kDifKmacModeCshakeLen128,
        .message = "OpenTitan",
        .message_len = 9,
        .function_name = "",
        .function_name_len = 0,
        .customization_string = "",
        .customization_string_len = 0,
        .digest = {0x235a6522, 0x3bd735ac, 0x77832247, 0xc6b12919},
        .digest_len = 4,  // Rate (r) is 42 words.
    },
    {
        .mode = kDifKmacModeCshakeLen128,
        .message = "OpenTitan",
        .message_len = 9,
        .function_name = "A",
        .function_name_len = 1,
        .customization_string = "",
        .customization_string_len = 0,
        .digest = {0xf2f20928, 0xa2a59a0, 0xfc1e5d5d, 0x1cee38d0},
        .digest_len = 4,  // Rate (r) is 42 words.
    },
    {
        .mode = kDifKmacModeCshakeLen256,
        .message = "OpenTitan",
        .message_len = 9,
        .function_name = "",
        .function_name_len = 0,
        .customization_string = "Ibex",
        .customization_string_len = 4,
        .digest = {0xcd582d56, 0x59e88860, 0xa4344c29, 0x5576778f},
        .digest_len = 4,  // Rate (r) is 34 words.
    },
    {
        .mode = kDifKmacModeCshakeLen256,
        .message = "OpenTitan",
        .message_len = 9,
        .function_name = "Ibex",
        .function_name_len = 4,
        .customization_string =
            "\x00\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0a\x0b\x0c\x0d\x0e\x0f"
            "\x10\x11\x12\x13\x14\x15\x16\x17\x18\x19\x1a\x1b\x1c\x1d\x1e\x1f",
        .customization_string_len = 32,
        .digest = {0xda353307, 0xdf18e570, 0x6211cee0, 0x716e816c},
        .digest_len = 4,  // Rate (r) is 34 words.
    },
};

void run_cshake_test(uintptr_t kmac) {

  // Run cSHAKE test cases using single blocking absorb/squeeze operations.
  for (int i = 0; i < sizeof(cshake_tests) / sizeof(cshake_test_t); ++i) {
    cshake_test_t test = cshake_tests[i];
    printf("run_cshake_test: running test %d.\n", i);
    dif_kmac_operation_state_t kmac_operation_state;

    dif_kmac_function_name_t n;
    dif_kmac_function_name_init(test.function_name, test.function_name_len, &n);

    dif_kmac_customization_string_t s;
    dif_kmac_customization_string_init(test.customization_string, test.customization_string_len, &s);

    // Use NULL for empty strings to exercise that code path.
    dif_kmac_function_name_t *np = test.function_name_len == 0 ? NULL : &n;
    dif_kmac_customization_string_t *sp = test.customization_string_len == 0 ? NULL : &s;

    dif_kmac_mode_cshake_start(kmac, &kmac_operation_state, test.mode, np, sp);
    dif_kmac_absorb(kmac, &kmac_operation_state, test.message, test.message_len, NULL);
    uint32_t out[DIGEST_LEN_CSHAKE_MAX];
    if (DIGEST_LEN_CSHAKE_MAX < test.digest_len) {
      printf("run_cshake_test: Error digest length %d is greater than max %d.\n", test.digest_len, DIGEST_LEN_CSHAKE_MAX);
      while(1);
      return;
    }
    dif_kmac_squeeze(kmac, &kmac_operation_state, out, test.digest_len, /*processed=*/NULL, /*capacity=*/NULL);
    dif_kmac_end(kmac, &kmac_operation_state);

    for (int j = 0; j < test.digest_len; ++j) {
      if (out[j] != test.digest[j]) {
        printf("test %d: mismatch at %d got=0x%x want=0x%x", i, j, out[j], test.digest[j]);
        while (1);
        return;
      }
    }
  }
}

void main(void) {

  // Entry message
  VPRINTF(LOW, "----------------------------------\n");
  VPRINTF(LOW, " cSHAKE smoke test!\n"                 );
  VPRINTF(LOW, "----------------------------------\n");

  // Call interrupt init
  init_interrupts();

  run_cshake_test(0x10040000);

  // Write 0xff to STDOUT for TB to terminate test.
  SEND_STDOUT_CTRL(0xff);
  while (1);
}
