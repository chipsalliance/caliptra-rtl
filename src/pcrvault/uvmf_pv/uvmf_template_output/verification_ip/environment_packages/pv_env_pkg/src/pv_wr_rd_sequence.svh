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
// DESCRIPTION: PV write/read sequence with forked writes and reads
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//

class pv_wr_rd_sequence #(
    type CONFIG_T
) extends pv_env_sequence_base #(.CONFIG_T(CONFIG_T));

    `uvm_object_param_utils(pv_wr_rd_sequence #(CONFIG_T));

    typedef pv_rst_poweron_sequence pv_rst_agent_poweron_sequence_t;
    pv_rst_agent_poweron_sequence_t pv_rst_agent_poweron_seq;

    typedef pv_write_pcr_entry_sequence pv_write_agent_pcr_entry_sequence_t;
    pv_write_agent_pcr_entry_sequence_t sha512_write_seq;

    typedef pv_read_pcr_entry_sequence pv_read_agent_pcr_entry_sequence_t;
    pv_read_agent_pcr_entry_sequence_t sha512_block_read_seq;
    
    rand reg [PV_ENTRY_ADDR_W-1:0] sha512_write_entry;     
    
    
    function new(string name = "");
        super.new(name);
        pv_rst_agent_poweron_seq = pv_rst_agent_poweron_sequence_t::type_id::create("pv_rst_agent_poweron_seq");
        if(!this.randomize()) `uvm_error("PV WR RD", "Failed to randomize PV RST poweron seq");
                
        sha512_write_seq = pv_write_agent_pcr_entry_sequence_t::type_id::create("sha512_write_seq");
        if(!this.randomize()) `uvm_error("PV WR RD", "Failed to randomize PV WRITE seq");
        
        sha512_block_read_seq = pv_read_agent_pcr_entry_sequence_t::type_id::create("sha512_block_read_seq");
        if(!this.randomize()) `uvm_error("PV WR RD", "Failed to randomize PV READ seq");
        
    endfunction

    virtual task body();
        uvm_status_e sts;
        //uvm_reg_data_t rd_data;
        int wr_entry = 0; 
        int wr_offset = 0;
        int rd_entry = 0;
        int rd_offset = 0;
        reg [31:0] wr_data, rd_data;


        std::randomize(sha512_write_entry);

        //Issue and wait for reset
        if(configuration.pv_rst_agent_config.sequencer != null)
            pv_rst_agent_poweron_seq.start(configuration.pv_rst_agent_config.sequencer);
        else
            `uvm_error("PV WR RD", "pv_rst_agent_config.sequencer is null!")

        //Init PV entries with random data first
        for(wr_entry=0;wr_entry<32;wr_entry++) begin
            for(wr_offset=0;wr_offset<12;wr_offset++) begin
                uvm_config_db#(reg [PV_ENTRY_ADDR_W-1:0])::set(null, "uvm_test_top.environment.pv_sha512_write_agent.sequencer.sha512_write_seq", "local_write_entry",wr_entry);
                uvm_config_db#(reg [PV_ENTRY_SIZE_WIDTH-1:0])::set(null, "uvm_test_top.environment.pv_sha512_write_agent.sequencer.sha512_write_seq", "local_write_offset",wr_offset);
                sha512_write_seq.start(configuration.pv_sha512_write_agent_config.sequencer);
            end
        end

        fork
            begin
                if(configuration.pv_sha512_write_agent_config.sequencer != null) begin
                    for(wr_entry=0;wr_entry<32;wr_entry++) begin
                        for(wr_offset=0;wr_offset<12;wr_offset++) begin
                            uvm_config_db#(reg [PV_ENTRY_ADDR_W-1:0])::set(null, "uvm_test_top.environment.pv_sha512_write_agent.sequencer.sha512_write_seq", "local_write_entry",wr_entry);
                            uvm_config_db#(reg [PV_ENTRY_SIZE_WIDTH-1:0])::set(null, "uvm_test_top.environment.pv_sha512_write_agent.sequencer.sha512_write_seq", "local_write_offset",wr_offset);
                            sha512_write_seq.start(configuration.pv_sha512_write_agent_config.sequencer);
                        end
                    end
                end
                else
                    `uvm_error("PV WR RD", "pv_sha512_write_agent_config.sequencer is null!");
            end
            begin
                if(configuration.pv_sha512_block_read_agent_config.sequencer != null) begin
                    for(rd_entry=0;rd_entry<32;rd_entry++) begin
                        for(rd_offset=0;rd_offset<12;rd_offset++) begin
                            uvm_config_db#(reg [PV_ENTRY_ADDR_W-1:0])::set(null, "uvm_test_top.environment.pv_sha512_block_read_agent.sequencer.sha512_block_read_seq", "local_read_entry",rd_entry);
                            uvm_config_db#(reg [PV_ENTRY_SIZE_WIDTH-1:0])::set(null, "uvm_test_top.environment.pv_sha512_block_read_agent.sequencer.sha512_block_read_seq", "local_read_offset",rd_offset);  
                            sha512_block_read_seq.start(configuration.pv_sha512_block_read_agent_config.sequencer);
                        end
                    end
                end
                else
                    `uvm_error("PV WR RD", "pv_sha512_block_read_agent_config.sequencer is null!");
            end
        join
    endtask

endclass