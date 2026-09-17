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
// DESCRIPTION: PV write/read with lock settings, then core-only reset.
// Verifies that:
//   - lock clears on core_only_rst_b (resets on core_only_rst_b)
//   - PCR data survives core reset (data resets only on cptra_pwrgood)
//   - fw_update_rst_window is briefly asserted during core reset
//     (driven by the rst driver BFM alongside core_only_rst_b)
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//

class pv_wr_rd_lock_core_rst_sequence #(
    type CONFIG_T
) extends pv_env_sequence_base #(.CONFIG_T(CONFIG_T));

    `uvm_object_param_utils(pv_wr_rd_lock_core_rst_sequence #(CONFIG_T));

    typedef pv_rst_poweron_sequence pv_rst_agent_poweron_sequence_t;
    pv_rst_agent_poweron_sequence_t pv_rst_agent_poweron_seq;

    typedef pv_rst_core_rst_sequence pv_rst_core_rst_sequence_t;
    pv_rst_core_rst_sequence_t pv_rst_agent_core_rst_seq;

    typedef pv_write_pcr_entry_sequence pv_write_agent_pcr_entry_sequence_t;
    pv_write_agent_pcr_entry_sequence_t sha512_write_seq;

    typedef pv_read_pcr_entry_sequence pv_read_agent_pcr_entry_sequence_t;
    pv_read_agent_pcr_entry_sequence_t sha512_block_read_seq;

    rand reg [PV_ENTRY_ADDR_W-1:0] sha512_write_entry;    
    rand reg[2:0] lock_data;

    uvm_event reset_phase;
    uvm_event active_phase;


    function new(string name = "");
        super.new(name);
        pv_rst_agent_poweron_seq = pv_rst_agent_poweron_sequence_t::type_id::create("pv_rst_agent_poweron_seq");
        if(!this.randomize()) `uvm_error("PV_WR_RD_LOCK", "Failed to randomize PV RST poweron seq");

        pv_rst_agent_core_rst_seq = pv_rst_core_rst_sequence_t::type_id::create("pv_rst_agent_core_rst_seq");
        if(!this.randomize()) `uvm_error("PV_WR_RD_LOCK", "Failed to randomize PV_CORE_RST seq");
        
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
        bit reset_flag;
        reg_model = configuration.pv_rm;

        active_phase = new();
        reset_phase = new();

        //Issue and wait for reset
        if(configuration.pv_rst_agent_config.sequencer != null)
            pv_rst_agent_poweron_seq.start(configuration.pv_rst_agent_config.sequencer);
        else
            `uvm_error("PV_WR_RD_LOCK", "pv_rst_agent_config.sequencer is null!")

        //Write to all entries, all offsets
        for (write_entry = 0; write_entry < PV_NUM_PCR; write_entry++) begin
            for(write_offset = 0; write_offset < PV_NUM_DWORDS; write_offset++) begin
                uvm_config_db#(reg [PV_ENTRY_ADDR_W-1:0])::set(null, "uvm_test_top.environment.pv_sha512_write_agent.sequencer.sha512_write_seq", "local_write_entry",write_entry);
                uvm_config_db#(reg [PV_ENTRY_SIZE_WIDTH-1:0])::set(null, "uvm_test_top.environment.pv_sha512_write_agent.sequencer.sha512_write_seq", "local_write_offset",write_offset);
                sha512_write_seq.start(configuration.pv_sha512_write_agent_config.sequencer);
            end 
        end

        //Lock all entries (lock_data = 1 sets lock bit only)
        for(write_entry = 0; write_entry < PV_NUM_PCR; write_entry++) begin
            reg_model.pv_reg_rm.PCR_CTRL[write_entry].write(sts, 32'h1, UVM_FRONTDOOR, reg_model.pv_AHB_map, this);
            assert(sts == UVM_IS_OK) else `uvm_error("AHB_LOCK_SET", $sformatf("Failed when writing to PCR_CTRL[%d]",write_entry))
        end

        //Verify locks are set by reading PCR_CTRL
        for(write_entry = 0; write_entry < PV_NUM_PCR; write_entry++) begin
            reg_model.pv_reg_rm.PCR_CTRL[write_entry].read(sts, rd_data, UVM_FRONTDOOR, reg_model.pv_AHB_map, this);
            assert(sts == UVM_IS_OK) else `uvm_error("AHB_LOCK_READ", $sformatf("Failed when reading PCR_CTRL[%d]",write_entry))
            assert(rd_data[0] == 1'b1) else `uvm_error("LOCK_VERIFY", $sformatf("PCR_CTRL[%d].lock expected 1, got %0b",write_entry,rd_data[0]))
        end

        //Issue core-only reset (also briefly asserts fw_update_rst_window via driver BFM)
        //This should clear all locks but preserve PCR data (cptra_pwrgood stays high)
        pv_rst_agent_core_rst_seq.start(configuration.pv_rst_agent_config.sequencer);

        //Verify locks are cleared after core reset
        for(write_entry = 0; write_entry < PV_NUM_PCR; write_entry++) begin
            reg_model.pv_reg_rm.PCR_CTRL[write_entry].read(sts, rd_data, UVM_FRONTDOOR, reg_model.pv_AHB_map, this);
            assert(sts == UVM_IS_OK) else `uvm_error("AHB_LOCK_READ", $sformatf("Failed when reading PCR_CTRL[%d] after core rst",write_entry))
            assert(rd_data[0] == 1'b0) else `uvm_error("LOCK_CLEAR_VERIFY", $sformatf("PCR_CTRL[%d].lock expected 0 after core rst, got %0b",write_entry,rd_data[0]))
        end

        //Read from all entries and offsets — data should survive core reset
        for (read_entry = 0; read_entry < PV_NUM_PCR; read_entry++) begin
            for (read_offset = 0; read_offset < PV_NUM_DWORDS; read_offset++) begin
                uvm_config_db#(reg [PV_ENTRY_ADDR_W-1:0])::set(null, "uvm_test_top.environment.pv_sha512_block_read_agent.sequencer.sha512_block_read_seq", "local_read_entry",read_entry);
                uvm_config_db#(reg [PV_ENTRY_SIZE_WIDTH-1:0])::set(null, "uvm_test_top.environment.pv_sha512_block_read_agent.sequencer.sha512_block_read_seq", "local_read_offset",read_offset);
                sha512_block_read_seq.start(configuration.pv_sha512_block_read_agent_config.sequencer);   
            end
        end

        //Now that locks are cleared, clear should succeed on all entries
        for(write_entry = 0; write_entry < PV_NUM_PCR; write_entry++) begin
            reg_model.pv_reg_rm.PCR_CTRL[write_entry].write(sts, 32'h2, UVM_FRONTDOOR, reg_model.pv_AHB_map, this);
            assert(sts == UVM_IS_OK) else `uvm_error("AHB_CLEAR_SET", $sformatf("Failed when writing clear to PCR_CTRL[%d]",write_entry))
        end

        //Read all entries — should be zero after clear
        for (read_entry = 0; read_entry < PV_NUM_PCR; read_entry++) begin
            for (read_offset = 0; read_offset < PV_NUM_DWORDS; read_offset++) begin
                uvm_config_db#(reg [PV_ENTRY_ADDR_W-1:0])::set(null, "uvm_test_top.environment.pv_sha512_block_read_agent.sequencer.sha512_block_read_seq", "local_read_entry",read_entry);
                uvm_config_db#(reg [PV_ENTRY_SIZE_WIDTH-1:0])::set(null, "uvm_test_top.environment.pv_sha512_block_read_agent.sequencer.sha512_block_read_seq", "local_read_offset",read_offset);
                sha512_block_read_seq.start(configuration.pv_sha512_block_read_agent_config.sequencer);   
            end
        end
            
        
    endtask

endclass
