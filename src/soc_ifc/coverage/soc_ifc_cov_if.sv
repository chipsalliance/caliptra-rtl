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

`ifndef VERILATOR

interface soc_ifc_cov_if     
    import soc_ifc_pkg::*;
    import soc_ifc_reg_pkg::*;
    (
    input logic clk,
    input logic trng_req,
    input logic ready_for_fuses,
    input logic ready_for_fw_push,
    input logic ready_for_runtime
);

    logic req_collision;
    
    assign req_collision = i_soc_ifc_arb.req_collision;

    covergroup soc_ifc_top_cov_grp @(posedge clk);
        trng_req_cp: coverpoint trng_req;
        ready_for_fuses_cp: coverpoint ready_for_fuses;
        ready_for_fw_push_cp: coverpoint ready_for_fw_push;
        ready_for_runtime_cp: coverpoint ready_for_runtime;
        req_collision_cp: coverpoint req_collision;
    endgroup

    soc_ifc_top_cov_grp soc_ifc_top_cov_grp1 = new();

endinterface

`endif