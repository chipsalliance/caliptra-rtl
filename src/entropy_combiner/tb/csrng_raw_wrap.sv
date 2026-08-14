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
// csrng_raw_wrap.sv
// -----------------
// Thin structural wrapper around csrng for the combiner+CSRNG integration
// testbench. It ties the RTL enum-typed straps (otp_en_csrng_sw_app_read_i =
// MuBi8True, lc_hw_debug_en_i = On) and the other unused interfaces
// (cs_aes_halt, hw application ports, alerts, interrupts) inside RTL, so the
// testbench never crosses the TB/RTL enum-type boundary (VCS partition compile
// builds separate incompatible enum copies). Mirrors entropy_src_raw_wrap.sv
// and how caliptra_top.sv drives these straps.
//
// Only the AHB command interface and the entropy interface (toward the
// entropy combiner) are exposed to the testbench.
//
//======================================================================

module csrng_raw_wrap
  import entropy_src_pkg::*;
  import caliptra_prim_mubi_pkg::*;
  import lc_ctrl_pkg::*;
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

  // Entropy interface toward the combiner. CSRNG is the consumer: it drives
  // es_req out and receives es_ack/es_bits in.
  output entropy_src_hw_if_req_t   entropy_src_hw_if_o,
  input  entropy_src_hw_if_rsp_t   entropy_src_hw_if_i
);

  csrng #(
    .RndCnstCsKeymgrDivNonProduction('0),
    .RndCnstCsKeymgrDivProduction('0),
    .AHBDataWidth(AHBDataWidth),
    .AHBAddrWidth(AHBAddrWidth)
  ) u_csrng (
    .clk_i                      (clk_i),
    .rst_ni                     (rst_ni),

    .haddr_i                    (haddr_i),
    .hwdata_i                   (hwdata_i),
    .hsel_i                     (hsel_i),
    .hwrite_i                   (hwrite_i),
    .hready_i                   (hready_i),
    .htrans_i                   (htrans_i),
    .hsize_i                    (hsize_i),
    .hresp_o                    (hresp_o),
    .hreadyout_o                (hreadyout_o),
    .hrdata_o                   (hrdata_o),

    // Enum straps tied in RTL (same as caliptra_top.sv / csrng_tb.sv).
    .otp_en_csrng_sw_app_read_i (MuBi8True),
    .lc_hw_debug_en_i           (On),

    .entropy_src_hw_if_o        (entropy_src_hw_if_o),
    .entropy_src_hw_if_i        (entropy_src_hw_if_i),

    .cs_aes_halt_i              (cs_aes_halt_req_t'('0)),
    .cs_aes_halt_o              (),

    // Hardware application interface unused (SW app interface via AHB is used).
    .csrng_cmd_i                ('0),
    .csrng_cmd_o                (),

    .alert_rx_i                 ('0),
    .alert_tx_o                 (),

    .intr_cs_cmd_req_done_o     (),
    .intr_cs_entropy_req_o      (),
    .intr_cs_hw_inst_exc_o      (),
    .intr_cs_fatal_err_o        ()
  );

endmodule
