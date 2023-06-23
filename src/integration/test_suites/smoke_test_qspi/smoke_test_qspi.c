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

typedef enum { Dummy = 0, RdOnly = 1, WrOnly = 2, BiDir = 3 } direction_t;
typedef enum { Standard = 0, Dual = 1, Quad = 2 } speed_t;
typedef enum { CmdJedecId = 0x9f, CmdReadQuad = 0x6b } cmd_spi_t;

// Parameters
int NUM_QSPI = 2;

// read data and compare against expected value. If there is no error, return 0
int read_and_compare(uint32_t addr, uint32_t exp_data) {
  uint32_t act_data;
  act_data = lsu_read_32(addr);
  if (act_data != exp_data) {
    printf("Got:%x Want: %x\n", act_data, exp_data);
    return 1;
  }
  return 0;
}

void end_sim_if_qspi_disabled() {
  uint32_t hw_cfg;
  hw_cfg = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_CONFIG);
  if (hw_cfg & SOC_IFC_REG_CPTRA_HW_CONFIG_QSPI_EN_MASK) {
    VPRINTF(LOW, "Internal QSPI is enabled, running QSPI smoke test\n");
  } else {
    VPRINTF(FATAL, "Internal QSPI is not enabled, skipping QSPI smoke test\n");
    SEND_STDOUT_CTRL(0xFF);
    while (1)
      ;
  }
}

void set_spi_csid(int host) { lsu_write_32(CLP_SPI_HOST_REG_CSID, host); }

void spi_command(int length, int csaat, speed_t speed, direction_t direction) {
  uint32_t status;

  printf("  - Writing spi_command: len:%d csaat:%d speed:%d direction:%d\n",
         length, csaat, speed, direction);

  // Wait for Status.ready
  do {
    status = lsu_read_32(CLP_SPI_HOST_REG_STATUS);
  } while (0 == (status & SPI_HOST_REG_STATUS_READY_MASK));

  lsu_write_32(CLP_SPI_HOST_REG_COMMAND,
               (direction << SPI_HOST_REG_COMMAND_DIRECTION_LOW) |
                   (speed << SPI_HOST_REG_COMMAND_SPEED_LOW) |
                   (csaat << SPI_HOST_REG_COMMAND_CSAAT_LOW) |
                   (length << SPI_HOST_REG_COMMAND_LEN_LOW));
}

void spi_command_wait() {
  uint32_t status;

  // Wait for Status.active
  do {
    status = lsu_read_32(CLP_SPI_HOST_REG_STATUS);
  } while (0 == (status & SPI_HOST_REG_STATUS_ACTIVE_MASK));
}

int fifo_rx_wait(int queue_depth) {
  uint32_t rxqd, status;
  int timeout = 0;
  do {
    status = lsu_read_32(CLP_SPI_HOST_REG_STATUS);
    rxqd = ((status & SPI_HOST_REG_STATUS_RXQD_MASK) >>
            SPI_HOST_REG_STATUS_RXQD_LOW);
    timeout++;
    if (timeout > 1000) {
      printf(
          "fifo_rx_wait: timed out waiting for queue_depth = %d. status:0x%x "
          "rxqd: %d\n",
          queue_depth, status, rxqd);
      return 1;
    }
  } while (rxqd != queue_depth);
  return 0;
}

void write_tx_fifo(uint32_t data) {
  lsu_write_32(CLP_SPI_HOST_REG_TXDATA, data);
}

// configure_spi_host enables the IP and sets the timing behavior
void enable_spi_host() {
  uint32_t read_data;
  printf("Enabling spi_host\n");
  lsu_write_32(CLP_SPI_HOST_REG_CONTROL,
               (1 << SPI_HOST_REG_CONTROL_SPIEN_LOW) |
                   (1 << SPI_HOST_REG_CONTROL_OUTPUT_EN_LOW) |
                   (0x7f << SPI_HOST_REG_CONTROL_RX_WATERMARK_LOW));
}

void configure_spi_host(int host) {
  uint32_t offset;

  if (host == 0) {
    offset = CLP_SPI_HOST_REG_CONFIGOPTS_0;
  } else {
    offset = CLP_SPI_HOST_REG_CONFIGOPTS_1;
  }

  printf("Configuring spi_host[%d]\n", host);
  lsu_write_32(offset, (0 << SPI_HOST_REG_CONFIGOPTS_0_CPOL_LOW) |
                           (0 << SPI_HOST_REG_CONFIGOPTS_0_CPHA_LOW) |
                           (0 << SPI_HOST_REG_CONFIGOPTS_0_FULLCYC_LOW) |
                           (0 << SPI_HOST_REG_CONFIGOPTS_0_CSNLEAD_LOW) |
                           (0 << SPI_HOST_REG_CONFIGOPTS_0_CSNTRAIL_LOW) |
                           (0 << SPI_HOST_REG_CONFIGOPTS_0_CSNIDLE_LOW) |
                           (0 << SPI_HOST_REG_CONFIGOPTS_0_CLKDIV_LOW));
}

//----------------------------------------------------------------
// run_jedec_id_test()
//
// Configures the spi_host to request the jedec id
// The spiflash device will return 7 bytes of continuous code ('h7f)
// followed by the JedecId ('h1f) and the DeviceId ('h1234)
//----------------------------------------------------------------
int run_jedec_id_test(int host) {
  uint32_t status, rxqd, rx_data;
  uint32_t exp_data[3];
  int error = 0, words;

  exp_data[0] = 0x7f7f7f7f;
  exp_data[1] = 0x1f7f7f7f;
  if (host == 0) {
    exp_data[2] = 0xf10a;
  } else {
    exp_data[2] = 0xf10b;
  }

  // Load the TX FIFO with instructions and data to be transmitted
  write_tx_fifo(CmdJedecId);

  // Specify which device should receive the next command
  set_spi_csid(host);

  // Issue speed, direction and length details for the next command
  // segment.  If a command consists of multiple segments, set csaat to one
  // for all segments except the last one.
  //
  // Issue Command Instruction
  spi_command(0,         // length + 1
              1,         // csaat
              Standard,  // Speed
              WrOnly     // Direction
  );

  // spi flash will return 10 bytes for the jedec command
  spi_command(9,         // length + 1
              0,         // csaat
              Standard,  // Speed
              RdOnly     // Direction
  );

  // Wait for spi commands to finish before reading responses
  spi_command_wait();

  words = sizeof(exp_data) / 4;
  error += fifo_rx_wait(words);

  printf("  - reading data from device...\n");
  for (int ii = 0; ii < words; ii += 1) {
    error += read_and_compare(CLP_SPI_HOST_REG_RXDATA, exp_data[ii]);
  }

  return error;
}

//----------------------------------------------------------------
// run_read_test()
//
// Configures the spi_host to request data from the spi flash
//----------------------------------------------------------------
int run_read_test(int host) {
  uint32_t status, rxqd, rx_data, exp_data;
  uint32_t addr;
  int error = 0;
  int NumBytes = 256;
  int SpiFlashAddr = 0x00ABCD;  // 3B Address

  // Load the TX FIFO with instructions and data to be transmitted
  write_tx_fifo(CmdReadQuad);
  // Upper Bytes are transmitted first
  write_tx_fifo((SpiFlashAddr & 0xff0000) >> 0 | (SpiFlashAddr & 0xff00) |
                (SpiFlashAddr & 0xff) << 16);

  // Specify which device should receive the next command
  set_spi_csid(host);

  // Issue speed, direction and length details for the next command
  // segment.  If a command consists of multiple segments, set csaat to one
  // for all segments except the last one.
  //
  // Issue Command Instruction
  spi_command(0,         // length + 1
              1,         // csaat
              Standard,  // Speed
              WrOnly);   // Direction
  // Issue 3 Byte Address - (Send the CmdEn4B if 4B is needed)
  spi_command(2,         // length + 1
              1,         // csaat
              Standard,  // Speed
              WrOnly);   // Direction

  // Issue 2 Dummy Cycles - This is derived from spiflash.DummyQuad-1
  spi_command(1,       // length + 1
              1,       // csaat
              Quad,    // Speed
              Dummy);  // Direction

  // Request 13 bytes of data
  spi_command(NumBytes - 1,  // length + 1
              0,             // csaat
              Quad,          // Speed
              RdOnly);       // Direction

  // Wait for spi commands to finish before reading responses
  spi_command_wait();

  printf("  - reading data from device...\n");

  error += fifo_rx_wait(NumBytes / 4);

  addr = SpiFlashAddr;
  // Read and compare the bytes for comparison
  for (int ii = 0; ii < NumBytes / 4; ii += 1) {
    // calculate expected data
    exp_data = addr & 0xff;

    // compare
    error += read_and_compare(CLP_SPI_HOST_REG_RXDATA,
                              (exp_data + 3) << 24 | (exp_data + 2) << 16 |
                                  (exp_data + 1) << 8 | (exp_data + 0) << 0);
    addr += 4;
  };
  return error;
}

void main() {
  int error;

  printf("---------------------------\n");
  printf(" QSPI Smoke Test \n");
  printf("---------------------------\n");

  end_sim_if_qspi_disabled();
  enable_spi_host();

  for (int host = 0; host < NUM_QSPI; host++) {
    configure_spi_host(host);
    error += run_jedec_id_test(host);
    if (error > 0) printf("Error: %d\n", error);
    error += run_read_test(host);
    if (error > 0) printf("Error: %d\n", error);
    error += run_read_test(host);
    if (error > 0) printf("Error: %d\n", error);
    error += run_read_test(host);
    if (error > 0) printf("Error: %d\n", error);
  }

  // End the sim in failure
  if (error > 0) printf("%c", 0x1);
}
