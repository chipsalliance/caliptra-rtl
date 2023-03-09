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
// DESCRIPTION: Sets random locks on all CTRL regs (lock_wr/use/clear)
// and issues writes on a random client. Then issues a cold reset before
// issuing reads on a random client
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//

class kv_wr_rd_lock_cold_rst_sequence #(
    type CONFIG_T
) extends kv_env_sequence_base #(.CONFIG_T(CONFIG_T));

    `uvm_object_param_utils(kv_wr_rd_lock_cold_rst_sequence #(CONFIG_T));

    typedef kv_rst_poweron_sequence kv_rst_agent_poweron_sequence_t;
    kv_rst_agent_poweron_sequence_t kv_rst_agent_poweron_seq;

    typedef kv_rst_cold_rst_sequence kv_rst_cold_rst_sequence_t;
    kv_rst_cold_rst_sequence_t kv_rst_agent_cold_rst_seq;

    typedef kv_write_key_entry_sequence kv_write_agent_key_entry_sequence_t;
    kv_write_agent_key_entry_sequence_t hmac_write_seq;
    kv_write_agent_key_entry_sequence_t sha512_write_seq;
    kv_write_agent_key_entry_sequence_t ecc_write_seq;
    kv_write_agent_key_entry_sequence_t doe_write_seq;

    typedef kv_read_key_entry_sequence kv_read_agent_key_entry_sequence_t;
    kv_read_agent_key_entry_sequence_t hmac_key_read_seq;
    kv_read_agent_key_entry_sequence_t hmac_block_read_seq;
    kv_read_agent_key_entry_sequence_t sha512_block_read_seq;
    kv_read_agent_key_entry_sequence_t ecc_privkey_read_seq;
    kv_read_agent_key_entry_sequence_t ecc_seed_read_seq;
    kv_read_agent_key_entry_sequence_t ecc_msg_read_seq;

    rand reg [KV_ENTRY_ADDR_W-1:0] hmac_write_entry, sha512_write_entry, ecc_write_entry, doe_write_entry;    
    rand reg[2:0] lock_data;

    rand reg [1:0] write_id;
    rand reg [2:0] read_id;
    typedef enum {HMAC, SHA512, ECC, DOE} write_agents;
    typedef enum {HMAC_KEY, HMAC_BLOCK, SHA512_BLOCK, ECC_PRIVKEY, ECC_MSG, ECC_SEED} read_agents;

    uvm_event reset_phase;
    uvm_event active_phase;


    function new(string name = "");
        super.new(name);
        kv_rst_agent_poweron_seq = kv_rst_agent_poweron_sequence_t::type_id::create("kv_rst_agent_poweron_seq");
        if(!this.randomize()) `uvm_error("KV_WR_RD_LOCK", "Failed to randomize KV RST poweron seq");

        kv_rst_agent_cold_rst_seq = kv_rst_cold_rst_sequence_t::type_id::create("kv_rst_agent_cold_rst_seq");
        if(!this.randomize()) `uvm_error("KV_WR_RD_LOCK", "Failed to randomize KV_COLD_RST seq");
        
        hmac_write_seq = kv_write_agent_key_entry_sequence_t::type_id::create("hmac_write_seq");
        if(!this.randomize()) `uvm_error("KV_WR_RD_LOCK", "Failed to randomize KV WRITE seq");
        sha512_write_seq = kv_write_agent_key_entry_sequence_t::type_id::create("sha512_write_seq");
        if(!this.randomize()) `uvm_error("KV_WR_RD_LOCK", "Failed to randomize KV WRITE seq");
        ecc_write_seq = kv_write_agent_key_entry_sequence_t::type_id::create("ecc_write_seq");
        if(!this.randomize()) `uvm_error("KV_WR_RD_LOCK", "Failed to randomize KV WRITE seq");
        doe_write_seq = kv_write_agent_key_entry_sequence_t::type_id::create("doe_write_seq");
        if(!this.randomize()) `uvm_error("KV_WR_RD_LOCK", "Failed to randomize KV WRITE seq");
        
        hmac_key_read_seq = kv_read_agent_key_entry_sequence_t::type_id::create("hmac_key_read_seq");
        if(!this.randomize()) `uvm_error("KV_WR_RD_LOCK", "Failed to randomize KV READ seq");
        hmac_block_read_seq = kv_read_agent_key_entry_sequence_t::type_id::create("hmac_block_read_seq");
        if(!this.randomize()) `uvm_error("KV_WR_RD_LOCK", "Failed to randomize KV READ seq");
        sha512_block_read_seq = kv_read_agent_key_entry_sequence_t::type_id::create("sha512_block_read_seq");
        if(!this.randomize()) `uvm_error("KV_WR_RD_LOCK", "Failed to randomize KV READ seq");
        ecc_privkey_read_seq = kv_read_agent_key_entry_sequence_t::type_id::create("ecc_privkey_read_seq");
        if(!this.randomize()) `uvm_error("KV_WR_RD_LOCK", "Failed to randomize KV READ seq");
        ecc_seed_read_seq = kv_read_agent_key_entry_sequence_t::type_id::create("ecc_seed_read_seq");
        if(!this.randomize()) `uvm_error("KV_WR_RD_LOCK", "Failed to randomize KV READ seq");
        ecc_msg_read_seq = kv_read_agent_key_entry_sequence_t::type_id::create("ecc_msg_read_seq");
        if(!this.randomize()) `uvm_error("KV_WR_RD_LOCK", "Failed to randomize KV READ seq");

        
    endfunction

    virtual task body();
        uvm_status_e sts;
        int write_entry = 0; 
        int write_offset = 0;
        int read_entry = 0; 
        int read_offset = 0;
        reg [31:0] wr_data, rd_data;
        bit reset_flag;
        reg_model = configuration.kv_rm;

        active_phase = new();
        reset_phase = new();

        //Issue and wait for reset
        if(configuration.kv_rst_agent_config.sequencer != null)
            kv_rst_agent_poweron_seq.start(configuration.kv_rst_agent_config.sequencer);
        else
            `uvm_error("KV_WR_RD_LOCK", "kv_rst_agent_config.sequencer is null!")

        
        //Set each CTRL reg with random lock data
        for(write_entry = 0; write_entry < KV_NUM_KEYS; write_entry++) begin
            // Construct the transaction
            lock_data = $urandom_range(1,7); //Can set one of lock_wr, lock_use, clear or all together
            reg_model.kv_reg_rm.KEY_CTRL[write_entry].write(sts, lock_data, UVM_FRONTDOOR, reg_model.kv_AHB_map, this);
            assert(sts == UVM_IS_OK) else `uvm_error("AHB_LOCK_SET", $sformatf("Failed when writing to KEY_CTRL[%d]",write_entry))
        end
        
        //Write to all entries, random offsets
        for (write_entry = 0; write_entry < KV_NUM_KEYS; write_entry++) begin
            write_id = $urandom_range(0,3);
            case(write_id)
                HMAC: begin
                    repeat(10) begin
                        uvm_config_db#(reg [KV_ENTRY_ADDR_W-1:0])::set(null, "uvm_test_top.environment.kv_hmac_write_agent.sequencer.hmac_write_seq", "local_write_entry",write_entry);
                        hmac_write_seq.start(configuration.kv_hmac_write_agent_config.sequencer);
                    end
                end
                SHA512: begin
                    repeat(10) begin
                        uvm_config_db#(reg [KV_ENTRY_ADDR_W-1:0])::set(null, "uvm_test_top.environment.kv_sha512_write_agent.sequencer.sha512_write_seq", "local_write_entry",write_entry);
                        sha512_write_seq.start(configuration.kv_sha512_write_agent_config.sequencer);
                    end
                end
                ECC: begin
                    repeat(10) begin
                        uvm_config_db#(reg [KV_ENTRY_ADDR_W-1:0])::set(null, "uvm_test_top.environment.kv_ecc_write_agent.sequencer.ecc_write_seq", "local_write_entry",write_entry);
                        ecc_write_seq.start(configuration.kv_ecc_write_agent_config.sequencer);
                    end
                end
                DOE: begin
                    repeat(10) begin
                        uvm_config_db#(reg [KV_ENTRY_ADDR_W-1:0])::set(null, "uvm_test_top.environment.kv_doe_write_agent.sequencer.doe_write_seq", "local_write_entry",write_entry);
                        doe_write_seq.start(configuration.kv_doe_write_agent_config.sequencer);
                    end
                end
            endcase
        end

        //Issue cold reset after writes
        kv_rst_agent_cold_rst_seq.start(configuration.kv_rst_agent_config.sequencer);

        //Read from all entries and offsets
        for (read_entry = 0; read_entry < KV_NUM_KEYS; read_entry++) begin
            read_id = $urandom_range(0,5);
            for (read_offset = 0; read_offset < KV_NUM_DWORDS; read_offset++) begin
                case(read_id)
                    HMAC_KEY: begin
                        uvm_config_db#(reg [KV_ENTRY_ADDR_W-1:0])::set(null, "uvm_test_top.environment.kv_hmac_key_read_agent.sequencer.hmac_key_read_seq", "local_read_entry",read_entry);
                        uvm_config_db#(reg [KV_ENTRY_SIZE_W-1:0])::set(null, "uvm_test_top.environment.kv_hmac_key_read_agent.sequencer.hmac_key_read_seq", "local_read_offset",read_offset);
                        hmac_key_read_seq.start(configuration.kv_hmac_key_read_agent_config.sequencer);
                    end
                    HMAC_BLOCK: begin
                        uvm_config_db#(reg [KV_ENTRY_ADDR_W-1:0])::set(null, "uvm_test_top.environment.kv_hmac_block_read_agent.sequencer.hmac_block_read_seq", "local_read_entry",read_entry);
                        uvm_config_db#(reg [KV_ENTRY_SIZE_W-1:0])::set(null, "uvm_test_top.environment.kv_hmac_block_read_agent.sequencer.hmac_block_read_seq", "local_read_offset",read_offset);
                        hmac_block_read_seq.start(configuration.kv_hmac_block_read_agent_config.sequencer);
                    end
                    SHA512_BLOCK: begin
                        uvm_config_db#(reg [KV_ENTRY_ADDR_W-1:0])::set(null, "uvm_test_top.environment.kv_sha512_block_read_agent.sequencer.sha512_block_read_seq", "local_read_entry",read_entry);
                        uvm_config_db#(reg [KV_ENTRY_SIZE_W-1:0])::set(null, "uvm_test_top.environment.kv_sha512_block_read_agent.sequencer.sha512_block_read_seq", "local_read_offset",read_offset);
                        sha512_block_read_seq.start(configuration.kv_sha512_block_read_agent_config.sequencer);
                    end
                    ECC_PRIVKEY: begin
                        uvm_config_db#(reg [KV_ENTRY_ADDR_W-1:0])::set(null, "uvm_test_top.environment.kv_ecc_privkey_read_agent.sequencer.ecc_privkey_read_seq", "local_read_entry",read_entry);
                        uvm_config_db#(reg [KV_ENTRY_SIZE_W-1:0])::set(null, "uvm_test_top.environment.kv_ecc_privkey_read_agent.sequencer.ecc_privkey_read_seq", "local_read_offset",read_offset);
                        ecc_privkey_read_seq.start(configuration.kv_ecc_privkey_read_agent_config.sequencer);
                    end
                    ECC_MSG: begin
                        uvm_config_db#(reg [KV_ENTRY_ADDR_W-1:0])::set(null, "uvm_test_top.environment.kv_ecc_msg_read_agent.sequencer.ecc_msg_read_seq", "local_read_entry",read_entry);
                        uvm_config_db#(reg [KV_ENTRY_SIZE_W-1:0])::set(null, "uvm_test_top.environment.kv_ecc_msg_read_agent.sequencer.ecc_msg_read_seq", "local_read_offset",read_offset);
                        ecc_msg_read_seq.start(configuration.kv_ecc_msg_read_agent_config.sequencer);
                    end
                    ECC_SEED: begin
                        uvm_config_db#(reg [KV_ENTRY_ADDR_W-1:0])::set(null, "uvm_test_top.environment.kv_ecc_seed_read_agent.sequencer.ecc_seed_read_seq", "local_read_entry",read_entry);
                        uvm_config_db#(reg [KV_ENTRY_SIZE_W-1:0])::set(null, "uvm_test_top.environment.kv_ecc_seed_read_agent.sequencer.ecc_seed_read_seq", "local_read_offset",read_offset);
                        ecc_seed_read_seq.start(configuration.kv_ecc_seed_read_agent_config.sequencer);
                    end
                endcase
            end
        end
            
        
    endtask

endclass