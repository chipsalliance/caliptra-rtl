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
// and issues writes on a random client. Then issues reads on a random client
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//

class kv_wr_rd_lock_sequence #(
    type CONFIG_T
) extends kv_env_sequence_base #(.CONFIG_T(CONFIG_T));

    `uvm_object_param_utils(kv_wr_rd_lock_sequence #(CONFIG_T));

    typedef kv_rst_poweron_sequence kv_rst_agent_poweron_sequence_t;
    kv_rst_agent_poweron_sequence_t kv_rst_agent_poweron_seq;

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

    rand reg [KV_ENTRY_ADDR_W-1:0] hmac_write_entry, sha512_write_entry, ecc_write_entry, doe_write_entry;    
    rand reg[2:0] lock_data;

    rand reg [1:0] write_id;
    rand reg [2:0] read_id;
    typedef enum {HMAC, SHA512, ECC, DOE} write_agents;
    typedef enum {HMAC_KEY, HMAC_BLOCK, SHA512_BLOCK, ECC_PRIVKEY, ECC_SEED} read_agents;


    function new(string name = "");
        super.new(name);
        kv_rst_agent_poweron_seq = kv_rst_agent_poweron_sequence_t::type_id::create("kv_rst_agent_poweron_seq");
        if(!this.randomize()) `uvm_error("KV_WR_RD_LOCK", "Failed to randomize KV RST poweron seq");
        
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

        
    endfunction

    virtual task body();
        uvm_status_e sts;
        int write_entry = 0; 
        int write_offset = 0;
        int read_entry = 0; 
        int read_offset = 0;
        reg [31:0] wr_data, rd_data;
        reg_model = configuration.kv_rm;

        std::randomize(hmac_write_entry) with {
            hmac_write_entry != sha512_write_entry;
            hmac_write_entry != ecc_write_entry;
            hmac_write_entry != doe_write_entry;
        };

        std::randomize(sha512_write_entry) with {
            sha512_write_entry != hmac_write_entry;
            sha512_write_entry != ecc_write_entry;
            sha512_write_entry != doe_write_entry;
        };

        std::randomize(ecc_write_entry) with {
            ecc_write_entry != hmac_write_entry;
            ecc_write_entry != sha512_write_entry;
            ecc_write_entry != doe_write_entry;
        };

        std::randomize(doe_write_entry) with {
            doe_write_entry != hmac_write_entry;
            doe_write_entry != sha512_write_entry;
            doe_write_entry != ecc_write_entry;
        };

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
                    ECC_SEED: begin
                        uvm_config_db#(reg [KV_ENTRY_ADDR_W-1:0])::set(null, "uvm_test_top.environment.kv_ecc_seed_read_agent.sequencer.ecc_seed_read_seq", "local_read_entry",read_entry);
                        uvm_config_db#(reg [KV_ENTRY_SIZE_W-1:0])::set(null, "uvm_test_top.environment.kv_ecc_seed_read_agent.sequencer.ecc_seed_read_seq", "local_read_offset",read_offset);
                        ecc_seed_read_seq.start(configuration.kv_ecc_seed_read_agent_config.sequencer);
                    end
                endcase
            end
        end

        //TODO: this needs env clean up! (Emulate 1 clk delay between key_entry_clear and wr_resp_error)
        // //clear x write
        // // fork

        // //Issue and wait for reset
        // if(configuration.kv_rst_agent_config.sequencer != null)
        //     kv_rst_agent_poweron_seq.start(configuration.kv_rst_agent_config.sequencer);
        // else
        //     `uvm_error("KV_WR_RD_LOCK", "kv_rst_agent_config.sequencer is null!")
            
        // // begin
        //     //Set each CTRL reg with random lock data
        //     for(int write_entry_temp = 0; write_entry_temp < KV_NUM_KEYS; write_entry_temp++) begin
        //         // if (write_entry_temp < KV_NUM_KEYS-1) begin
        //             // lock_data = $urandom_range(1,7); //Can set one of lock_wr, lock_use, clear or all together
        //             reg_model.kv_reg_rm.KEY_CTRL[write_entry_temp].write(sts, 'h4, UVM_FRONTDOOR, reg_model.kv_AHB_map, this);
        //             `uvm_info("KNU_LOCK", $sformatf("Setting KEY CTRL: %d", write_entry_temp), UVM_MEDIUM)
        //             assert(sts == UVM_IS_OK) else `uvm_error("AHB_LOCK_SET", $sformatf("Failed when writing to KEY_CTRL[%d]",write_entry_temp))
        //         // end

        //         for (int write_offset_temp = 0; write_offset_temp < KV_NUM_DWORDS; write_offset_temp++) begin
        //             // Construct the transaction
        //             uvm_config_db#(reg [KV_ENTRY_ADDR_W-1:0])::set(null, "uvm_test_top.environment.kv_hmac_write_agent.sequencer.hmac_write_seq", "local_write_entry",write_entry_temp);
        //             uvm_config_db#(reg [KV_ENTRY_SIZE_W-1:0])::set(null, "uvm_test_top.environment.kv_hmac_write_agent.sequencer.hmac_write_seq", "local_write_offset",write_offset_temp);
        //             `uvm_info("KNU_WRITE", $sformatf("Writing to entry: %0d, offset: %0d", write_entry_temp, write_offset_temp), UVM_MEDIUM)
        //             hmac_write_seq.start(configuration.kv_hmac_write_agent_config.sequencer);
        //         end

                
        //     end
        // // end

        // // begin
        //     //Write to all entries, random offsets
        //     // for (int write_entry_temp = 0; write_entry_temp < KV_NUM_KEYS; write_entry_temp++) begin
                
        //     // end

        // // end
        // // join

    endtask

endclass