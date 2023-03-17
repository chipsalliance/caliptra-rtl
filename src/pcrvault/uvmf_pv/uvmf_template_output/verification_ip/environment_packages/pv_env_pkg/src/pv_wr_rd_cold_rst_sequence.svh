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
// DESCRIPTION: PV write/read sequence with cold reset
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//

class pv_wr_rd_cold_rst_sequence #(
    type CONFIG_T
) extends pv_env_sequence_base #(.CONFIG_T(CONFIG_T));

    `uvm_object_param_utils(pv_wr_rd_cold_rst_sequence #(CONFIG_T));

    typedef pv_rst_poweron_sequence pv_rst_agent_poweron_sequence_t;
    pv_rst_agent_poweron_sequence_t pv_rst_agent_poweron_seq;

    typedef pv_rst_cold_rst_sequence pv_rst_cold_rst_sequence_t;
    pv_rst_cold_rst_sequence_t pv_rst_agent_cold_rst_seq;

    typedef pv_write_pcr_entry_sequence pv_write_agent_pcr_entry_sequence_t;
    pv_write_agent_pcr_entry_sequence_t sha512_write_seq;

    typedef pv_read_pcr_entry_sequence pv_read_agent_pcr_entry_sequence_t;
    pv_read_agent_pcr_entry_sequence_t sha512_block_read_seq;

    rand reg [PV_ENTRY_ADDR_W-1:0] sha512_write_entry;    
    
    uvm_event active_phase;
    uvm_event write_event;
    uvm_event read_event;
    
    

    function new(string name = "");
        super.new(name);
        pv_rst_agent_poweron_seq = pv_rst_agent_poweron_sequence_t::type_id::create("pv_rst_agent_poweron_seq");
        if(!this.randomize()) `uvm_error("PV WR RD", "Failed to randomize PV RST poweron seq");
        pv_rst_agent_cold_rst_seq = pv_rst_cold_rst_sequence_t::type_id::create("pv_rst_agent_cold_rst_seq");
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
        reg [PV_DATA_W-1:0] wr_data, rd_data;

        active_phase = new();
        write_event = new();
        read_event = new();

        std::randomize(sha512_write_entry);

        fork
            
            begin
                active_phase.wait_ptrigger;

                repeat(50) begin
                    uvm_config_db#(reg [PV_ENTRY_ADDR_W-1:0])::set(null, "uvm_test_top.environment.pv_sha512_write_agent.sequencer.sha512_write_seq", "local_write_entry",sha512_write_entry);
                    sha512_write_seq.start(configuration.pv_sha512_write_agent_config.sequencer);
                end
                write_event.trigger;
                
            end
            
            begin
                active_phase.wait_ptrigger;

                repeat(50) begin
                    sha512_block_read_seq.start(configuration.pv_sha512_block_read_agent_config.sequencer);
                end
                read_event.trigger;

            end
            
            begin
                // write_event.wait_ptrigger;
                // read_event.wait_ptrigger;
                pv_rst_agent_cold_rst_seq.start(configuration.pv_rst_agent_config.sequencer);
                if(pv_rst_agent_cold_rst_seq.req.set_pwrgood && !pv_rst_agent_cold_rst_seq.req.assert_rst) begin
                    active_phase.trigger;
                end
            end
            

        join
        active_phase.reset;
    endtask

endclass