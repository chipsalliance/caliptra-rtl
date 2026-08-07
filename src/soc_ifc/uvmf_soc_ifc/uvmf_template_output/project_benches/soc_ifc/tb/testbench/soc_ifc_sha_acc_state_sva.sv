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
//----------------------------------------------------------------------
// soc_ifc_sha_acc_state_sva
//
// Observe-only SVA monitor for the SoC-AXI SHA accelerator route. Bound into
// soc_ifc_top, it checks both the arbiter grant policy and the provenance of
// requests that reach the SHA destination interface.
//
// Authorization policy (Caliptra Integration Specification):
//   * Subsystem mode: a SoC-AXI SHA access is authorized only when its AxUSER
//     matches SS_CALIPTRA_DMA_AXI_USER (valid_sha_user).
//   * Passive mode: the SoC-AXI SHA route is unavailable, so no SoC-AXI SHA
//     access is ever authorized (the route must never be granted).
//
// Note: legitimate Caliptra microcontroller (AHB) access to the SHA accelerator
// is unaffected and can still drive the FSM in both modes; these assertions
// intentionally constrain only the SoC-AXI (soc_*) grant path.
//----------------------------------------------------------------------
`include "caliptra_sva.svh"

module soc_ifc_sha_acc_state_sva
    import soc_ifc_pkg::*;
    (
    input logic          clk,
    input logic          rst_b,
    input logic          soc_req_dv,
    input logic [SOC_IFC_ADDR_W-1:0] soc_req_addr,
    input logic          valid_sha_user,
    input logic          soc_sha_gnt,
    input logic          sha_user_match,
    input logic          sha_req_dv,
    input soc_ifc_req_t  sha_req_data,
    input logic [SOC_IFC_USER_W-1:0] sha_dma_axi_user
    );

`ifdef CALIPTRA_MODE_SUBSYSTEM
    localparam bit SS_MODE = 1'b1;
`else
    localparam bit SS_MODE = 1'b0;
`endif

    // A SoC-AXI request targeting the SHA accelerator register range.
    logic soc_sha_addr;
    always_comb soc_sha_addr = soc_req_dv & (soc_req_addr inside {[SHA_REG_START_ADDR[SOC_IFC_ADDR_W-1:0]:SHA_REG_END_ADDR[SOC_IFC_ADDR_W-1:0]]});

    // A SoC-AXI SHA access is authorized only in subsystem mode with a matching
    // AxUSER identity.
    logic soc_sha_authorized;
    always_comb soc_sha_authorized = SS_MODE & valid_sha_user;

    // The SoC-AXI SHA route must only ever be granted to an authorized requester.
    // In passive mode soc_sha_authorized is always 0, so no SoC-AXI SHA access
    // may be granted at all.
    `CALIPTRA_ASSERT(A_soc_sha_grant_requires_authorization,
        soc_sha_gnt |-> soc_sha_authorized,
        clk, !rst_b,
        $sformatf("soc_ifc_sha_acc_state_sva: SoC-AXI SHA route granted without authorization (SS_MODE=%0b valid_sha_user=%0b)", SS_MODE, valid_sha_user))

    // An unauthorized SoC-AXI SHA request must never receive a grant.
    `CALIPTRA_ASSERT(A_illegal_soc_sha_no_grant,
        (soc_sha_addr & ~soc_sha_authorized) |-> ~soc_sha_gnt,
        clk, !rst_b,
        $sformatf("soc_ifc_sha_acc_state_sva: Unauthorized SoC-AXI SHA request received an arbiter grant (addr=0x%0x SS_MODE=%0b valid_sha_user=%0b)", soc_req_addr, SS_MODE, valid_sha_user))

    // Any request identified as a SoC request at the SHA destination must have
    // traversed the subsystem-only route with the configured DMA AxUSER.
    `CALIPTRA_ASSERT(A_downstream_soc_sha_request_authorized,
        (sha_req_dv & sha_req_data.soc_req) |->
            (SS_MODE & (sha_req_data.user == sha_dma_axi_user)),
        clk, !rst_b,
        $sformatf("soc_ifc_sha_acc_state_sva: Unauthorized SoC request reached SHA destination (SS_MODE=%0b user=0x%0x expected=0x%0x)", SS_MODE, sha_req_data.user, sha_dma_axi_user))

    // In passive mode the SoC-AXI SHA route is unavailable and must never grant.
    if (!SS_MODE) begin : gen_passive
        `CALIPTRA_ASSERT_NEVER(A_passive_no_soc_sha_grant,
            soc_sha_gnt,
            clk, !rst_b,
            "soc_ifc_sha_acc_state_sva: SoC-AXI SHA route received an arbiter grant in passive mode")
    end

    //------------------------------------------------------------------
    // Compile-time-specific structural coverage avoids impossible bins in each
    // integration mode. sha_user_match is independent from valid_sha_user
    // because the latter is intentionally tied low in passive mode.
    //------------------------------------------------------------------
`ifdef CALIPTRA_MODE_SUBSYSTEM
    covergroup soc_sha_access_cg @(posedge clk iff (rst_b & soc_sha_addr));
        cp_access_control: coverpoint {sha_user_match, soc_sha_gnt} {
            bins matching_axuser_granted     = {2'b11};
            bins nonmatching_axuser_rejected = {2'b00};
        }
    endgroup

    `CALIPTRA_COVER(C_authorized_soc_request_reaches_sha,
        sha_req_dv & sha_req_data.soc_req &
        (sha_req_data.user == sha_dma_axi_user),
        clk, !rst_b)
`else
    covergroup soc_sha_access_cg @(posedge clk iff (rst_b & soc_sha_addr));
        cp_access_control: coverpoint {sha_user_match, soc_sha_gnt} {
            bins matching_axuser_rejected    = {2'b10};
            bins nonmatching_axuser_rejected = {2'b00};
        }
    endgroup
`endif

    soc_sha_access_cg soc_sha_access_cg_inst = new();

endmodule

bind soc_ifc_top soc_ifc_sha_acc_state_sva i_soc_ifc_sha_acc_state_sva (
    .clk           (soc_ifc_clk_cg                              ),
    .rst_b         (cptra_noncore_rst_b                         ),
    .soc_req_dv    (i_soc_ifc_arb.soc_req_dv                    ),
    .soc_req_addr  (i_soc_ifc_arb.soc_req_data.addr             ),
    .valid_sha_user(i_soc_ifc_arb.valid_sha_user                ),
    .soc_sha_gnt   (i_soc_ifc_arb.soc_sha_gnt                   ),
    .sha_user_match(i_soc_ifc_arb.soc_req_data.user ==
                    soc_ifc_reg_hwif_out.SS_CALIPTRA_DMA_AXI_USER.user.value),
    .sha_req_dv    (sha_req_dv                                  ),
    .sha_req_data  (sha_req_data                                ),
    .sha_dma_axi_user(soc_ifc_reg_hwif_out.SS_CALIPTRA_DMA_AXI_USER.user.value)
);
