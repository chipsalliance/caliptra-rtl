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

#include <stdint.h>
#include <string.h>

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "printf.h"
#include "riscv-csr.h"
#include "riscv_hw_if.h"

volatile char *stdout = (char *)STDOUT;
volatile uint32_t intr_count = 0;
volatile uint32_t rst_count __attribute__((section(".dccm.persistent"))) = 0;
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

// read data and compare against expected value. If there is no error, return 0
int read_and_compare(uint32_t addr, uint32_t exp_data) {
  uint32_t act_data;
  act_data = lsu_read_32(addr);
  if (act_data != exp_data) {
    printf("Got:%x Want: %x", act_data, exp_data);
    return 1;
  }
  return 0;
}

// poll a register until value read back matches expected value
void poll_reg(uint32_t addr, uint32_t expected_data) {
  uint32_t read_data;

  printf("  - Polling addr=%x until it reads back %x...\n", addr,
         expected_data);
  do {
    read_data = lsu_read_32(addr);
  } while (read_data != expected_data);
}

void end_sim_if_itrng_disabled() {
  uint32_t hw_cfg;
  hw_cfg = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_CONFIG);
  if (hw_cfg & SOC_IFC_REG_CPTRA_HW_CONFIG_ITRNG_EN_MASK) {
    VPRINTF(LOW, "Internal TRNG is enabled, running TRNG smoke test\n");
  } else {
    VPRINTF(FATAL, "Internal TRNG is not enabled, skipping TRNG smoke test\n");
    SEND_STDOUT_CTRL(0xFF);
    while (1)
      ;
  }
}

void enable_csrng() {
  uint32_t read_data;
  printf("Enabling entropy_src\n");
  lsu_write_32(CLP_ENTROPY_SRC_REG_CONF, 0x909099);
  lsu_write_32(CLP_ENTROPY_SRC_REG_MODULE_ENABLE, 0x6);

  printf("Enabling csrng\n");
  lsu_write_32(CLP_CSRNG_REG_CTRL, 0x666);
  lsu_write_32(CLP_CSRNG_REG_CMD_REQ, 0x901);

  printf("  - Waiting for boot done...\n");

  poll_reg(CLP_ENTROPY_SRC_REG_DEBUG_STATUS,
           ENTROPY_SRC_REG_DEBUG_STATUS_MAIN_SM_BOOT_DONE_MASK);
}

int run_entropy_source_seed_test() {
  uint32_t read_data;
  int error;

  printf("\nEntropy Source Seed Test\n");

  printf("Instantiate Command\n");
  lsu_write_32(CLP_CSRNG_REG_CMD_REQ, 0x1003);

  printf("  - Waiting for csrng to generate bits ...\n");
  poll_reg(CLP_CSRNG_REG_GENBITS_VLD, CSRNG_REG_GENBITS_VLD_GENBITS_VLD_MASK);

  error += read_and_compare(CLP_CSRNG_REG_GENBITS, 0x15eb2a44);
  error += read_and_compare(CLP_CSRNG_REG_GENBITS, 0x310851dd);
  error += read_and_compare(CLP_CSRNG_REG_GENBITS, 0xba1365ab);
  error += read_and_compare(CLP_CSRNG_REG_GENBITS, 0x4c7322f4);

  return error;
}

int run_smoke_test() {
  int error;

  printf("\nTRNG Smoke Test\n");

  printf("Uninitiate Command\n");
  lsu_write_32(CLP_CSRNG_REG_CMD_REQ, 0x905);

  poll_reg(CLP_CSRNG_REG_SW_CMD_STS, CSRNG_REG_SW_CMD_STS_CMD_RDY_MASK);

  printf("Initiate Command - Writing 48B of seed\n");
  lsu_write_32(CLP_CSRNG_REG_CMD_REQ, 0x06C1);
  lsu_write_32(CLP_CSRNG_REG_CMD_REQ, 0x73BEC010);
  lsu_write_32(CLP_CSRNG_REG_CMD_REQ, 0x9262474c);
  lsu_write_32(CLP_CSRNG_REG_CMD_REQ, 0x16a30f76);
  lsu_write_32(CLP_CSRNG_REG_CMD_REQ, 0x531b51de);
  lsu_write_32(CLP_CSRNG_REG_CMD_REQ, 0x2ee494e5);
  lsu_write_32(CLP_CSRNG_REG_CMD_REQ, 0xdfec9db3);
  lsu_write_32(CLP_CSRNG_REG_CMD_REQ, 0xcb7a879d);
  lsu_write_32(CLP_CSRNG_REG_CMD_REQ, 0x5600419c);
  lsu_write_32(CLP_CSRNG_REG_CMD_REQ, 0xca79b0b0);
  lsu_write_32(CLP_CSRNG_REG_CMD_REQ, 0xdda33b5c);
  lsu_write_32(CLP_CSRNG_REG_CMD_REQ, 0xa468649e);
  lsu_write_32(CLP_CSRNG_REG_CMD_REQ, 0xdf5d73fa);

  poll_reg(CLP_CSRNG_REG_SW_CMD_STS, CSRNG_REG_SW_CMD_STS_CMD_RDY_MASK);

  printf("Generate Command - 512b\n");
  lsu_write_32(CLP_CSRNG_REG_CMD_REQ, 0x4903);
  poll_reg(CLP_CSRNG_REG_GENBITS_VLD, CSRNG_REG_GENBITS_VLD_GENBITS_VLD_MASK);

  error += read_and_compare(CLP_CSRNG_REG_GENBITS, 0x378FCA1E);
  error += read_and_compare(CLP_CSRNG_REG_GENBITS, 0xcf763d08);
  error += read_and_compare(CLP_CSRNG_REG_GENBITS, 0x17166e90);
  error += read_and_compare(CLP_CSRNG_REG_GENBITS, 0x0b165308);

  poll_reg(CLP_CSRNG_REG_GENBITS_VLD, CSRNG_REG_GENBITS_VLD_GENBITS_VLD_MASK);
  error += read_and_compare(CLP_CSRNG_REG_GENBITS, 0x359fbe3e);
  error += read_and_compare(CLP_CSRNG_REG_GENBITS, 0xa69B1Bf1);
  error += read_and_compare(CLP_CSRNG_REG_GENBITS, 0x14117211);
  error += read_and_compare(CLP_CSRNG_REG_GENBITS, 0xc01a0839);

  poll_reg(CLP_CSRNG_REG_GENBITS_VLD, CSRNG_REG_GENBITS_VLD_GENBITS_VLD_MASK);
  error += read_and_compare(CLP_CSRNG_REG_GENBITS, 0x58d7e45d);
  error += read_and_compare(CLP_CSRNG_REG_GENBITS, 0xc5e00eb8);
  error += read_and_compare(CLP_CSRNG_REG_GENBITS, 0xce7ab38f);
  error += read_and_compare(CLP_CSRNG_REG_GENBITS, 0x6e48e546);

  poll_reg(CLP_CSRNG_REG_GENBITS_VLD, CSRNG_REG_GENBITS_VLD_GENBITS_VLD_MASK);
  error += read_and_compare(CLP_CSRNG_REG_GENBITS, 0x49de93f9);
  error += read_and_compare(CLP_CSRNG_REG_GENBITS, 0x88A65Ec7);
  error += read_and_compare(CLP_CSRNG_REG_GENBITS, 0xc58a553e);
  error += read_and_compare(CLP_CSRNG_REG_GENBITS, 0x5d6e1012);

  poll_reg(CLP_CSRNG_REG_SW_CMD_STS, CSRNG_REG_SW_CMD_STS_CMD_RDY_MASK);

  printf("Generate Command - 512b\n");
  lsu_write_32(CLP_CSRNG_REG_CMD_REQ, 0x4903);
  poll_reg(CLP_CSRNG_REG_GENBITS_VLD, CSRNG_REG_GENBITS_VLD_GENBITS_VLD_MASK);

  error += read_and_compare(CLP_CSRNG_REG_GENBITS, 0xe48bb8cb);
  error += read_and_compare(CLP_CSRNG_REG_GENBITS, 0x1012c84c);
  error += read_and_compare(CLP_CSRNG_REG_GENBITS, 0x5af8a7f1);
  error += read_and_compare(CLP_CSRNG_REG_GENBITS, 0xd1c07cd9);

  poll_reg(CLP_CSRNG_REG_GENBITS_VLD, CSRNG_REG_GENBITS_VLD_GENBITS_VLD_MASK);
  error += read_and_compare(CLP_CSRNG_REG_GENBITS, 0xdf82ab22);
  error += read_and_compare(CLP_CSRNG_REG_GENBITS, 0x771c619b);
  error += read_and_compare(CLP_CSRNG_REG_GENBITS, 0xd40fccb1);
  error += read_and_compare(CLP_CSRNG_REG_GENBITS, 0x87189e99);

  poll_reg(CLP_CSRNG_REG_GENBITS_VLD, CSRNG_REG_GENBITS_VLD_GENBITS_VLD_MASK);
  error += read_and_compare(CLP_CSRNG_REG_GENBITS, 0x510494b3);
  error += read_and_compare(CLP_CSRNG_REG_GENBITS, 0x64f7ac0c);
  error += read_and_compare(CLP_CSRNG_REG_GENBITS, 0x2581f391);
  error += read_and_compare(CLP_CSRNG_REG_GENBITS, 0x80b1dc2f);

  poll_reg(CLP_CSRNG_REG_GENBITS_VLD, CSRNG_REG_GENBITS_VLD_GENBITS_VLD_MASK);

  error += read_and_compare(CLP_CSRNG_REG_GENBITS, 0x793e01c5);
  error += read_and_compare(CLP_CSRNG_REG_GENBITS, 0x87b107ae);
  error += read_and_compare(CLP_CSRNG_REG_GENBITS, 0xdb17514c);
  error += read_and_compare(CLP_CSRNG_REG_GENBITS, 0xa43c41b7);

  poll_reg(CLP_CSRNG_REG_SW_CMD_STS, CSRNG_REG_SW_CMD_STS_CMD_RDY_MASK);

  return error;
}

void main() {
  int error;

  printf("---------------------------\n");
  printf(" TRNG Smoke Test \n");
  printf("---------------------------\n");

  end_sim_if_itrng_disabled();
  enable_csrng();
  error += run_entropy_source_seed_test();
  if (error > 0) printf("Error: %d\n", error);
  error += run_smoke_test();
  if (error > 0) printf("Error: %d\n", error);

  // End the sim in failure
  if (error > 0) printf("%c", 0x1);
}
