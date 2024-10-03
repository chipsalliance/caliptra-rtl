//----------------------------------------------------------------------
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

`ifndef __FUSE_CTRL_RESET_SEQUENCE
`define __FUSE_CTRL_RESET_SEQUENCE

`include "uvm_macros.svh"

class fuse_ctrl_otf_reset_sequence extends fuse_ctrl_bench_sequence;

    `uvm_object_utls(fuse_ctrl_otf_reset_sequence)

    // Define type and handle for reset sequence
    typedef fuse_ctrl_in_otf_reset_sequence fuse_ctrl_in_otf_reset_sequence_t;
    fuse_ctrl_in_otf_reset_sequence_t fuse_ctrl_in_otf_reset_s;

    // constructor
    function new(string name = "");
        super.new(name);
    endfunction: new

    virtual task body();
        fuse_ctrl_in_otf_reset_s = fuse_ctrl_in_otf_reset_sequence()::type_id::create("fuse_ctrl_in_otf_reset_s");

        fork
            fuse_ctrl_rst_agent_config.wait_for_reset();
            fuse_ctrl_core_axi_write_in_if_agent_config.wait_for_reset();
            fuse_ctrl_core_axi_write_out_if_agent_config.wait_for_reset();
            fuse_ctrl_prim_axi_write_in_if_agent_config.wait_for_reset();
            fuse_ctrl_prim_axi_write_out_if_agent_config.wait_for_reset();
            fuse_ctrl_core_axi_read_in_if_agent_config.wait_for_reset();
            fuse_ctrl_core_axi_read_out_if_agent_config.wait_for_reset();
            fuse_ctrl_prim_axi_read_in_if_agent_config.wait_for_reset();
            fuse_ctrl_prim_axi_read_out_if_agent_config.wait_for_reset();
            fuse_ctrl_secreg_axi_read_in_if_agent_config.wait_for_reset();
            fuse_ctrl_secreg_axi_read_out_if_agent_config.wait_for_reset();
            fuse_ctrl_in_if_agent_config.wait_for_reset();
            fuse_ctrl_out_if_agent_config.wait_for_reset();
            fuse_ctrl_lc_otp_in_if_agent_config.wait_for_reset();
            fuse_ctrl_lc_otp_out_if_agent_config.wait_for_reset();
        join

        repeat (10) fuse_ctrl_in_otf_reset_s.start(fuse_ctrl_rst_agent_sequencer);

        fork
            fuse_ctrl_rst_agent_config.wait_for_num_clocks(50);
            fuse_ctrl_core_axi_write_in_if_agent_config.wait_for_num_clocks(50);
            fuse_ctrl_core_axi_write_out_if_agent_config.wait_for_num_clocks(50);
            fuse_ctrl_prim_axi_write_in_if_agent_config.wait_for_num_clocks(50);
            fuse_ctrl_prim_axi_write_out_if_agent_config.wait_for_num_clocks(50);
            fuse_ctrl_core_axi_read_in_if_agent_config.wait_for_num_clocks(50);
            fuse_ctrl_core_axi_read_out_if_agent_config.wait_for_num_clocks(50);
            fuse_ctrl_prim_axi_read_in_if_agent_config.wait_for_num_clocks(50);
            fuse_ctrl_prim_axi_read_out_if_agent_config.wait_for_num_clocks(50);
            fuse_ctrl_secreg_axi_read_in_if_agent_config.wait_for_num_clocks(50);
            fuse_ctrl_secreg_axi_read_out_if_agent_config.wait_for_num_clocks(50);
            fuse_ctrl_in_if_agent_config.wait_for_num_clocks(50);
            fuse_ctrl_out_if_agent_config.wait_for_num_clocks(50);
            fuse_ctrl_lc_otp_in_if_agent_config.wait_for_num_clocks(50);
            fuse_ctrl_lc_otp_out_if_agent_config.wait_for_num_clocks(50);
        join

        if (1)
            $display("* TESTCASE PASSED");
        else
            $display("* TESTCASE FAILED");
    endtask

endclass : fuse_ctrl_otf_reset_sequence

`endif
