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
//======================================================================
//
// entropy_src_raw_wrap.sv
// -----------------------
// Thin structural wrapper around entropy_src for the entropy_combiner
// integration testbench.
//
// Its only job is to keep the caliptra_prim_mubi_pkg enum ports (otp_en_*)
// and the other unused interfaces (xht / alerts / interrupts) tied off *inside
// RTL*, mirroring how caliptra_top.sv drives them, while passing the
// cs_aes_halt handshake through to the combiner. Because this module is pure
// structural RTL, it compiles in the design partition, so its MuBi8True
// reference binds to the same caliptra_prim_mubi_pkg as the entropy_src port.
// The testbench then instantiates this wrapper and never crosses the TB/RTL
// enum-type boundary that a direct entropy_src instance would (VCS partition
// compile treats them as different enum types).
//
//======================================================================

module entropy_src_raw_wrap
  import entropy_src_pkg::*;
  import caliptra_prim_mubi_pkg::*;
#(
  parameter AHBDataWidth = 32,
  parameter AHBAddrWidth = 32
) (
  input  logic                     clk_i,
  input  logic                     rst_ni,

  input  logic [AHBAddrWidth-1:0]  haddr_i,
  input  logic [AHBDataWidth-1:0]  hwdata_i,
  input  logic                     hsel_i,
  input  logic                     hwrite_i,
  input  logic                     hready_i,
  input  logic [1:0]               htrans_i,
  input  logic [2:0]               hsize_i,
  output logic                     hresp_o,
  output logic                     hreadyout_o,
  output logic [AHBDataWidth-1:0]  hrdata_o,

  // CSRNG-facing entropy interface (to the combiner)
  input  entropy_src_hw_if_req_t   entropy_src_hw_if_i,
  output entropy_src_hw_if_rsp_t   entropy_src_hw_if_o,

  // cs_aes_halt handshake (to the combiner, which terminates it locally). The
  // SHA3 conditioner asserts cs_aes_halt_o before a Keccak run and waits on
  // cs_aes_halt_i; in raw/bypass mode the conditioner is unused so this is idle.
  output cs_aes_halt_req_t         cs_aes_halt_o,
  input  cs_aes_halt_rsp_t         cs_aes_halt_i,

  // itrng interface (to physical_rng)
  output entropy_src_rng_req_t     entropy_src_rng_o,
  input  entropy_src_rng_rsp_t     entropy_src_rng_i
);

  entropy_src #(
    .AHBDataWidth(AHBDataWidth),
    .AHBAddrWidth(AHBAddrWidth)
  ) u_entropy_src (
    .clk_i                        (clk_i),
    .rst_ni                       (rst_ni),

    .haddr_i                      (haddr_i),
    .hwdata_i                     (hwdata_i),
    .hsel_i                       (hsel_i),
    .hwrite_i                     (hwrite_i),
    .hready_i                     (hready_i),
    .htrans_i                     (htrans_i),
    .hsize_i                      (hsize_i),
    .hresp_o                      (hresp_o),
    .hreadyout_o                  (hreadyout_o),
    .hrdata_o                     (hrdata_o),

    // MuBi enable straps tied in RTL (same as caliptra_top.sv).
    .otp_en_entropy_src_fw_read_i (MuBi8True),
    .otp_en_entropy_src_fw_over_i (MuBi8True),

    .rng_fips_o                   (),
    .entropy_src_hw_if_i          (entropy_src_hw_if_i),
    .entropy_src_hw_if_o          (entropy_src_hw_if_o),
    .entropy_src_rng_o            (entropy_src_rng_o),
    .entropy_src_rng_i            (entropy_src_rng_i),

    .cs_aes_halt_o                (cs_aes_halt_o),
    .cs_aes_halt_i                (cs_aes_halt_i),
    .entropy_src_xht_o            (),
    .entropy_src_xht_i            (entropy_src_xht_rsp_t'('0)),
    .alert_rx_i                   ('0),
    .alert_tx_o                   (),
    .intr_es_entropy_valid_o      (),
    .intr_es_health_test_failed_o (),
    .intr_es_observe_fifo_ready_o (),
    .intr_es_fatal_err_o          ()
  );

endmodule
