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
// DESCRIPTION: PV write/read sequence with randomized lock and clear settings
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//

class pv_wr_rd_lock_sequence #(
    type CONFIG_T
) extends pv_env_sequence_base #(.CONFIG_T(CONFIG_T));

    `uvm_object_param_utils(pv_wr_rd_lock_sequence #(CONFIG_T));

    typedef pv_rst_poweron_sequence pv_rst_agent_poweron_sequence_t;
    pv_rst_agent_poweron_sequence_t pv_rst_agent_poweron_seq;

    typedef pv_write_pcr_entry_sequence pv_write_agent_pcr_entry_sequence_t;
    pv_write_agent_pcr_entry_sequence_t sha512_write_seq;

    typedef pv_read_pcr_entry_sequence pv_read_agent_pcr_entry_sequence_t;
    pv_read_agent_pcr_entry_sequence_t sha512_block_read_seq;

    rand reg [PV_ENTRY_ADDR_W-1:0] sha512_write_entry;    
    rand reg[2:0] lock_data;


    function new(string name = "");
        super.new(name);
        pv_rst_agent_poweron_seq = pv_rst_agent_poweron_sequence_t::type_id::create("pv_rst_agent_poweron_seq");
        if(!this.randomize()) `uvm_error("PV_WR_RD_LOCK", "Failed to randomize PV RST poweron seq");
        
        sha512_write_seq = pv_write_agent_pcr_entry_sequence_t::type_id::create("sha512_write_seq");
        if(!this.randomize()) `uvm_error("PV_WR_RD_LOCK", "Failed to randomize PV WRITE seq");
        
        sha512_block_read_seq = pv_read_agent_pcr_entry_sequence_t::type_id::create("sha512_block_read_seq");
        if(!this.randomize()) `uvm_error("PV_WR_RD_LOCK", "Failed to randomize PV READ seq");
        
    endfunction

    virtual task body();
        uvm_status_e sts;
        int write_entry = 0; 
        int write_offset = 0;
        int read_entry = 0; 
        int read_offset = 0;
        reg [31:0] wr_data, rd_data;
        reg_model = configuration.pv_rm;

        std::randomize(sha512_write_entry);

        //Issue and wait for reset
        if(configuration.pv_rst_agent_config.sequencer != null)
            pv_rst_agent_poweron_seq.start(configuration.pv_rst_agent_config.sequencer);
        else
            `uvm_error("PV_WR_RD_LOCK", "pv_rst_agent_config.sequencer is null!")

        //Write to all entries, all offsets, before locking/clearing
        for (write_entry = 0; write_entry < PV_NUM_PCR; write_entry++) begin
            for(write_offset = 0; write_offset < PV_NUM_DWORDS; write_offset++) begin
                uvm_config_db#(reg [PV_ENTRY_ADDR_W-1:0])::set(null, "uvm_test_top.environment.pv_sha512_write_agent.sequencer.sha512_write_seq", "local_write_entry",write_entry);
                uvm_config_db#(reg [PV_ENTRY_SIZE_WIDTH-1:0])::set(null, "uvm_test_top.environment.pv_sha512_write_agent.sequencer.sha512_write_seq", "local_write_offset",write_offset);
                sha512_write_seq.start(configuration.pv_sha512_write_agent_config.sequencer);
            end 
        end

        
        //Set each CTRL reg with random lock data
        for(write_entry = 0; write_entry < PV_NUM_PCR; write_entry++) begin
            // Construct the transaction
            lock_data = $urandom_range(1,3); //Can set one of lock_wr, lock_use, clear or all together
            reg_model.pv_reg_rm.PCR_CTRL[write_entry].write(sts, lock_data, UVM_FRONTDOOR, reg_model.pv_AHB_map, this);
            assert(sts == UVM_IS_OK) else `uvm_error("AHB_LOCK_SET", $sformatf("Failed when writing to PCR_CTRL[%d]",write_entry))
        end
        
        //Read from all entries and offsets after lock/clear
        for (read_entry = 0; read_entry < PV_NUM_PCR; read_entry++) begin
            for (read_offset = 0; read_offset < PV_NUM_DWORDS; read_offset++) begin
                uvm_config_db#(reg [PV_ENTRY_ADDR_W-1:0])::set(null, "uvm_test_top.environment.pv_sha512_block_read_agent.sequencer.sha512_block_read_seq", "local_read_entry",read_entry);
                uvm_config_db#(reg [PV_ENTRY_SIZE_WIDTH-1:0])::set(null, "uvm_test_top.environment.pv_sha512_block_read_agent.sequencer.sha512_block_read_seq", "local_read_offset",read_offset);
                sha512_block_read_seq.start(configuration.pv_sha512_block_read_agent_config.sequencer);  
            end
        end
    

        //Set clear of all CTRL regs  (should not go through for those that have been locked earlier)
        for(write_entry = 0; write_entry < PV_NUM_PCR; write_entry++) begin
            // Construct the transaction
            lock_data = 'h2; //Can set one of lock_wr, lock_use, clear or all together
            reg_model.pv_reg_rm.PCR_CTRL[write_entry].write(sts, lock_data, UVM_FRONTDOOR, reg_model.pv_AHB_map, this);
            assert(sts == UVM_IS_OK) else `uvm_error("AHB_LOCK_SET", $sformatf("Failed when writing to PCR_CTRL[%d]",write_entry))
        end
    
        //Read from all entries and offsets //Should read mix of 0s and data
        for (read_entry = 0; read_entry < PV_NUM_PCR; read_entry++) begin
            for (read_offset = 0; read_offset < PV_NUM_DWORDS; read_offset++) begin
                uvm_config_db#(reg [PV_ENTRY_ADDR_W-1:0])::set(null, "uvm_test_top.environment.pv_sha512_block_read_agent.sequencer.sha512_block_read_seq", "local_read_entry",read_entry);
                uvm_config_db#(reg [PV_ENTRY_SIZE_WIDTH-1:0])::set(null, "uvm_test_top.environment.pv_sha512_block_read_agent.sequencer.sha512_block_read_seq", "local_read_offset",read_offset);
                sha512_block_read_seq.start(configuration.pv_sha512_block_read_agent_config.sequencer);  
            end
        end
    
fork
    begin
        //Write to all entries, random offsets
        for (write_entry = 0; write_entry < PV_NUM_PCR; write_entry++) begin
            repeat(50) begin
                uvm_config_db#(reg [PV_ENTRY_ADDR_W-1:0])::set(null, "uvm_test_top.environment.pv_sha512_write_agent.sequencer.sha512_write_seq", "local_write_entry",write_entry);
                sha512_write_seq.start(configuration.pv_sha512_write_agent_config.sequencer);
            end 
        end
    end
    begin
        //Read from all entries and offsets
        for (read_entry = 0; read_entry < PV_NUM_PCR; read_entry++) begin
            for (read_offset = 0; read_offset < PV_NUM_DWORDS; read_offset++) begin
                uvm_config_db#(reg [PV_ENTRY_ADDR_W-1:0])::set(null, "uvm_test_top.environment.pv_sha512_block_read_agent.sequencer.sha512_block_read_seq", "local_read_entry",read_entry);
                uvm_config_db#(reg [PV_ENTRY_SIZE_WIDTH-1:0])::set(null, "uvm_test_top.environment.pv_sha512_block_read_agent.sequencer.sha512_block_read_seq", "local_read_offset",read_offset);
                sha512_block_read_seq.start(configuration.pv_sha512_block_read_agent_config.sequencer);  
            end
        end
    end
join
    endtask

endclass