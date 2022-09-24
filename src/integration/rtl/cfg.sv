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
`ifndef CFG_SV
`define CFG_SV
  `define AHB_SLAVES_NUM      4'd10 // Number of slaves AHB
  `define AHB_MASTERS_NUM     4'd1 // Number of masters AHB
  `define AHB_HADDR_SIZE      32 // bit-width AHB address haddr
  `define AHB_HDATA_SIZE      64 // bit-width AHB data
  `define APB_ADDR_WIDTH      32 // bit-width APB address
  `define APB_DATA_WIDTH      32 // bit-width APB data
  `define APB_USER_WIDTH      32 // bit-width APB PAUSER field
  `define QSPI_CS_WIDTH       2
  `define QSPI_IO_WIDTH       4
  `define SOC_SEC_STATE_WIDTH 3
  `define SLAVE_NAMES         {"SWERV_DMA"  , "MBOX"       , "I3C"        , "UART"       , "QSPI"       , "SHA"        , "KEYVAULT"   , "HMAC"       , "ECC"        , "AES_CTRL"   } /* Array of names for peripherals */
  `define SLAVE_BASE_ADDR     {32'h4000_0000, 32'h3000_0000, 32'hFFFF_FFFF, 32'hFFFF_FFFF, 32'hFFFF_FFFF, 32'h1002_0000, 32'h1001_8000, 32'h1001_0000, 32'h1000_8000, 32'h1000_0000} /* Array with slave base address */
  `define SLAVE_MASK_ADDR     {32'h4007_FFFF, 32'h3003_FFFF, 32'hFFFF_FFFF, 32'hFFFF_FFFF, 32'hFFFF_FFFF, 32'h1002_FFFF, 32'h1001_FFFF, 32'h1001_0FFF, 32'h1000_FFFF, 32'h1000_FFFF} /* Array with slave offset address */
  `define SLAVE_ADDR_MASK     (`SLAVE_BASE_ADDR ^ `SLAVE_MASK_ADDR) /* Array indicating meaningful address bits for each slave */
  `define SLAVE_ADDR_WIDTH(n) $clog2((`SLAVE_ADDR_MASK >> (`AHB_HADDR_SIZE*n)) & {`AHB_HADDR_SIZE{1'b1}}) /* Decode address width for each slave from assigned BASE/MASK address */
  `define SLAVE_SEL_AES       0
  `define SLAVE_SEL_ECC       1
  `define SLAVE_SEL_HMAC      2
  `define SLAVE_SEL_KV        3
  `define SLAVE_SEL_SHA       4
  `define SLAVE_SEL_QSPI      5
  `define SLAVE_SEL_UART      6
  `define SLAVE_SEL_I3C       7
  `define SLAVE_SEL_MBOX      8
  `define SLAVE_SEL_DMA       9

  `define KV_NUM_READ 1
  `define KV_NUM_WRITE 2

  `define IMEM_BYTE_SIZE  32768
  `define IMEM_DATA_WIDTH 64
  `define IMEM_DEPTH      `IMEM_BYTE_SIZE / (`IMEM_DATA_WIDTH/8)
  `define IMEM_ADDR_WIDTH $clog2(`IMEM_BYTE_SIZE)

  `define CALIPTRA_TOP        caliptra_top_tb
  `define CALIPTRA_RV_TOP     `CALIPTRA_TOP.caliptra_top_dut

  `define RV_TOP              `CALIPTRA_RV_TOP.rvtop
`endif
