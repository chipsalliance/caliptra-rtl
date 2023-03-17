//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
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

// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
// DESCRIPTION: Simple pv write/read sequence with warm reset
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//

class pv_wr_rd_rst_sequence #(
    type CONFIG_T
) extends pv_env_sequence_base #(.CONFIG_T(CONFIG_T));

    `uvm_object_param_utils(pv_wr_rd_rst_sequence #(CONFIG_T));

    typedef pv_rst_poweron_sequence pv_rst_agent_poweron_sequence_t;
    pv_rst_agent_poweron_sequence_t pv_rst_agent_poweron_seq;

    typedef pv_rst_warm_rst_sequence pv_rst_warm_rst_sequence_t;
    pv_rst_warm_rst_sequence_t pv_rst_agent_warm_rst_seq;

    typedef pv_write_pcr_entry_sequence pv_write_agent_pcr_entry_sequence_t;
    pv_write_agent_pcr_entry_sequence_t sha512_write_seq;

    typedef pv_read_pcr_entry_sequence pv_read_agent_pcr_entry_sequence_t;
    pv_read_agent_pcr_entry_sequence_t sha512_block_read_seq;

    rand reg [PV_ENTRY_ADDR_W-1:0] sha512_write_entry;    
    
    //Event to indicate dut is out of reset to avoid sending wr/rd during this time
    uvm_event reset_phase;
    uvm_event active_phase;
    
    
    

    function new(string name = "");
        super.new(name);
        pv_rst_agent_poweron_seq = pv_rst_agent_poweron_sequence_t::type_id::create("pv_rst_agent_poweron_seq");
        if(!this.randomize()) `uvm_error("PV WR RD", "Failed to randomize PV RST poweron seq");
        pv_rst_agent_warm_rst_seq = pv_rst_warm_rst_sequence_t::type_id::create("pv_rst_agent_warm_rst_seq");
        if(!this.randomize()) `uvm_error("PV WR RD", "Failed to randomize PV RST poweron seq");
        
        sha512_write_seq = pv_write_agent_pcr_entry_sequence_t::type_id::create("sha512_write_seq");
        if(!this.randomize()) `uvm_error("PV WR RD", "Failed to randomize PV WRITE seq");
        
        sha512_block_read_seq = pv_read_agent_pcr_entry_sequence_t::type_id::create("sha512_block_read_seq");
        if(!this.randomize()) `uvm_error("PV WR RD", "Failed to randomize PV READ seq");
        
    endfunction

    virtual task body();
        uvm_status_e sts;
        //uvm_reg_data_t rd_data;
        int entry = 0; 
        int offset = 0;
        reg [31:0] wr_data, rd_data;

        reset_phase = new();
        active_phase = new();

        std::randomize(sha512_write_entry);


        fork
            
            begin
                if(reset_phase.is_on) begin
                    active_phase.wait_ptrigger;
                end

                repeat(50) begin
                    uvm_config_db#(reg [PV_ENTRY_ADDR_W-1:0])::set(null, "uvm_test_top.environment.pv_sha512_write_agent.sequencer.sha512_write_seq", "local_write_entry",sha512_write_entry);
                    sha512_write_seq.start(configuration.pv_sha512_write_agent_config.sequencer);
                end
            end
            
            begin
                repeat(50) sha512_block_read_seq.start(configuration.pv_sha512_block_read_agent_config.sequencer);
            end
            
            begin
                pv_rst_agent_warm_rst_seq.start(configuration.pv_rst_agent_config.sequencer);
                reset_phase.trigger;
                if(!pv_rst_agent_warm_rst_seq.req.assert_rst) begin
                    reset_phase.reset;
                    active_phase.trigger;
                end
            end

        join
        active_phase.reset;
    endtask

endclass