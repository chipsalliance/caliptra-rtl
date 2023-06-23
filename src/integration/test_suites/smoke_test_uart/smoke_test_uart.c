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

void end_sim_if_uart_disabled() {
  uint32_t hw_cfg;
  hw_cfg = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_CONFIG);
  if (hw_cfg & SOC_IFC_REG_CPTRA_HW_CONFIG_UART_EN_MASK) {
    VPRINTF(LOW, "Internal UART is enabled, running UART smoke test\n");
  } else {
    VPRINTF(FATAL, "Internal UART is not enabled, skipping UART smoke test\n");
    SEND_STDOUT_CTRL(0xFF);
    while (1)
      ;
  }
}

void uart_tx(uint8_t data) {
  uint32_t status, tx_full, wdata;
  printf("uart_tx >> Sending 0x%x\n", data);
  // Check the TX fifo is not full
  do {
    status = lsu_read_32(CLP_UART_STATUS);
    tx_full = ((status & UART_STATUS_TXFULL_MASK) >> UART_STATUS_TXFULL_LOW);
  } while (tx_full);

  wdata = data;
  lsu_write_32(CLP_UART_WDATA, wdata);
}

uint8_t uart_rx() {
  uint32_t status, rx_empty, data;
  uint8_t rdata;

  // Check the RX Empty
  do {
    status = lsu_read_32(CLP_UART_STATUS);
    rx_empty = ((status & UART_STATUS_RXEMPTY_MASK) >> UART_STATUS_RXEMPTY_LOW);
  } while (rx_empty);

  // read the data
  data = lsu_read_32(CLP_UART_RDATA);
  printf("uart_rx << Receiving 0x%x\n", data);
  rdata = data & 0xff;
  return rdata;
}

// enable uart tx and rx
void enable_uart() {
  uint64_t nco, baud_rate, ip_frequency;
  uint32_t ctrl;

  baud_rate = 115200;
  ip_frequency = 100000000;  // 100 MHz

  // 31:16 NCO
  // 9:8   rxblvl
  // 7     parity_odd
  // 6     parity_even
  // 5     line loopback enable
  // 4     system loopback enable
  // 2     RX Noise Filter
  // 1     Rx Enable
  // 0     Tx Enable
  // NCO Equation: 2^20 * Fbaud
  //              --------------
  //                   Fclk
  // Fbaud = baud rate in bits per second
  // Fclk  = fixed frequency of the IP
  nco = baud_rate << 20;
  nco = nco / ip_frequency;
  printf("nco = %d\n", nco);

  ctrl = ((nco & 0xffff) << UART_CTRL_NCO_LOW) | UART_CTRL_TX_MASK |
         UART_CTRL_RX_MASK;
  lsu_write_32(CLP_UART_CTRL, ctrl);  // Enable RX/TX
}

//----------------------------------------------------------------
// run_loopback_test()
//
// This is a simple test that writes data and checks that data was received.
// TODO: add threads to process read/write in parallel (or interrupts), but also
// add a real uart driver at the top level instead of a loopback wire.
//----------------------------------------------------------------
int run_loopback_test() {
  int error = 0;
  uint8_t rxdata, txdata;

  for (int ii = 0; ii < 10; ii++) {
    txdata = 3 * ii + 7;
    uart_tx(txdata);

    rxdata = uart_rx();

    if (rxdata != txdata) {
      printf("run_loopback_test: Got: 0x%x Want: 0x%x\n", rxdata, txdata);
      error += 1;
    }
  }

  return error;
}

void main() {
  int error;

  printf("---------------------------\n");
  printf(" UART Smoke Test \n");
  printf("---------------------------\n");

  end_sim_if_uart_disabled();
  enable_uart();

  error += run_loopback_test();
  if (error > 0) printf("Error: %d\n", error);

  // End the sim in failure
  if (error > 0) printf("%c", 0x1);
}
