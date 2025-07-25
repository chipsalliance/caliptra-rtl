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
`ifndef CALIPTRA_CFG_SV
`define CALIPTRA_CFG_SV

  `define CALIPTRA

// Uncomment to enable Caliptra Internal TRNG
//`define CALIPTRA_INTERNAL_TRNG

// Uncomment if fuse granularity 32 bits.
//`define CALIPTRA_FUSE_GRANULARITY_32

  `define CALIPTRA_AHB_SLAVES_NUM      5'd16 // Number of slaves AHB
  `define CALIPTRA_AHB_MASTERS_NUM     4'd1 // Number of masters AHB
  `define CALIPTRA_AHB_HADDR_SIZE      32 // bit-width AHB address haddr
  `define CALIPTRA_AHB_HDATA_SIZE      64 // bit-width AHB data
  `define CALIPTRA_AXI_DATA_WIDTH      32 // bit-width AXI data
  `define CALIPTRA_AXI_USER_WIDTH      32 // bit-width AXI USER field
  `define CALIPTRA_AXI_ID_WIDTH        8  // bit-width AXI ID field
  // Overrideable for lint checks
  `ifndef CALIPTRA_AXI_DMA_ADDR_WIDTH
      `define CALIPTRA_AXI_DMA_ADDR_WIDTH  48
  `endif
  `define CALIPTRA_SOC_SEC_STATE_WIDTH 3

  // AHB Address Map
  `define CALIPTRA_SLAVE_NAMES         {"AES"        , "MLDSA"      , "ENTROPY_SRC", "CSRNG"      , "IMEM"       , "SHA256"     , "VEER_ICCM_DMA", "VEER_DCCM_DMA", "SOC_IFC"    , "SHA512"     , "DATAVAULT"  , "PCRVAULT"   , "KEYVAULT"   , "HMAC"       , "ECC"        , "DOE_CTRL"   } /* Array of names for peripherals */
  `define CALIPTRA_SLAVE_BASE_ADDR     {32'h1001_1000, 32'h1003_0000, 32'h2000_3000, 32'h2000_2000, 32'h0000_0000, 32'h1002_8000, 32'h4000_0000  , 32'h5000_0000  , 32'h3000_0000, 32'h1002_0000, 32'h1001_C000, 32'h1001_A000, 32'h1001_8000, 32'h1001_0000, 32'h1000_8000, 32'h1000_0000} /* Array with slave base address */
  `define CALIPTRA_SLAVE_MASK_ADDR     {32'h1001_1FFF, 32'h1003_FFFF, 32'h2000_3FFF, 32'h2000_2FFF, 32'h0001_7FFF, 32'h1002_FFFF, 32'h4003_FFFF  , 32'h5003_FFFF  , 32'h3007_FFFF, 32'h1002_7FFF, 32'h1001_DFFF, 32'h1001_BFFF, 32'h1001_9FFF, 32'h1001_0FFF, 32'h1000_FFFF, 32'h1000_7FFF} /* Array with slave offset address */
  `define CALIPTRA_SLAVE_ADDR_MASK     (`CALIPTRA_SLAVE_BASE_ADDR ^ `CALIPTRA_SLAVE_MASK_ADDR) /* Array indicating meaningful address bits for each slave */
  `define CALIPTRA_SLAVE_ADDR_WIDTH(n) $clog2((`CALIPTRA_SLAVE_ADDR_MASK >> (`CALIPTRA_AHB_HADDR_SIZE*n)) & {`CALIPTRA_AHB_HADDR_SIZE{1'b1}}) /* Decode address width for each slave from assigned BASE/MASK address */
  `define CALIPTRA_SLAVE_SEL_DOE         0
  `define CALIPTRA_SLAVE_SEL_ECC         1
  `define CALIPTRA_SLAVE_SEL_HMAC        2
  `define CALIPTRA_SLAVE_SEL_KV          3
  `define CALIPTRA_SLAVE_SEL_PV          4
  `define CALIPTRA_SLAVE_SEL_DV          5
  `define CALIPTRA_SLAVE_SEL_SHA512      6
  `define CALIPTRA_SLAVE_SEL_SOC_IFC     7
  `define CALIPTRA_SLAVE_SEL_DDMA        8
  `define CALIPTRA_SLAVE_SEL_IDMA        9
  `define CALIPTRA_SLAVE_SEL_SHA256      10
  `define CALIPTRA_SLAVE_SEL_IMEM        11
  `define CALIPTRA_SLAVE_SEL_CSRNG       12
  `define CALIPTRA_SLAVE_SEL_ENTROPY_SRC 13
  `define CALIPTRA_SLAVE_SEL_MLDSA       14
  `define CALIPTRA_SLAVE_SEL_AES         15

  // Interrupt Assignments
  // NOTE Vector 0 is reserved by VeeR
  `define VEER_INTR_VEC_DOE_ERROR     1
  `define VEER_INTR_VEC_DOE_NOTIF     2
  `define VEER_INTR_VEC_ECC_ERROR     3
  `define VEER_INTR_VEC_ECC_NOTIF     4
  `define VEER_INTR_VEC_HMAC_ERROR    5
  `define VEER_INTR_VEC_HMAC_NOTIF    6
  `define VEER_INTR_VEC_KV_ERROR      7
  `define VEER_INTR_VEC_KV_NOTIF      8
  `define VEER_INTR_VEC_SHA512_ERROR  9
  `define VEER_INTR_VEC_SHA512_NOTIF  10
  `define VEER_INTR_VEC_SHA256_ERROR  11
  `define VEER_INTR_VEC_SHA256_NOTIF  12
  `define VEER_INTR_VEC_RSVD0_ERROR   13
  `define VEER_INTR_VEC_RSVD0_NOTIF   14
  `define VEER_INTR_VEC_RSVD1_ERROR   15
  `define VEER_INTR_VEC_RSVD1_NOTIF   16
  `define VEER_INTR_VEC_RSVD2_ERROR   17
  `define VEER_INTR_VEC_RSVD2_NOTIF   18
  `define VEER_INTR_VEC_SOC_IFC_ERROR 19
  `define VEER_INTR_VEC_SOC_IFC_NOTIF 20
  `define VEER_INTR_VEC_SHA_ERROR     21
  `define VEER_INTR_VEC_SHA_NOTIF     22
  `define VEER_INTR_VEC_MLDSA_ERROR   23
  `define VEER_INTR_VEC_MLDSA_NOTIF   24
  `define VEER_INTR_VEC_AXI_DMA_ERROR 25
  `define VEER_INTR_VEC_AXI_DMA_NOTIF 26
  // Used to tie-off unused upper intr bits
  `define VEER_INTR_VEC_MAX_ASSIGNED `VEER_INTR_VEC_AXI_DMA_NOTIF

  //`define CALIPTRA_KV_NUM_READ 6
  //`define CALIPTRA_KV_NUM_WRITE 4

  `define CALIPTRA_IMEM_BYTE_SIZE   98304
  `define CALIPTRA_IMEM_DATA_WIDTH  64
  `define CALIPTRA_IMEM_DEPTH       `CALIPTRA_IMEM_BYTE_SIZE / (`CALIPTRA_IMEM_DATA_WIDTH/8)
  `define CALIPTRA_IMEM_BYTE_ADDR_W $clog2(`CALIPTRA_IMEM_BYTE_SIZE)
  `define CALIPTRA_IMEM_ADDR_WIDTH  $clog2(`CALIPTRA_IMEM_DEPTH)

  `define CALIPTRA_TOP        caliptra_top_tb
  `define CALIPTRA_RV_TOP     `CALIPTRA_TOP.caliptra_top_dut

  `define RV_TOP              `CALIPTRA_RV_TOP.rvtop

  `define CALIPTRA_ICG           cptra_clk_gate
  
`endif

