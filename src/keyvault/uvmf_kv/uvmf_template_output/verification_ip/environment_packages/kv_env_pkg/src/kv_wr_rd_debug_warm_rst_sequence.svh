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
// DESCRIPTION: Performs KV writes while randomly issuing debug unlock
// via input pin or CLEAR_SECRETS reg. A warm reset is issued after the
// writes and then all entries/dwords are read
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//

class kv_wr_rd_debug_warm_rst_sequence #(
    type CONFIG_T
) extends kv_env_sequence_base #(.CONFIG_T(CONFIG_T));

    `uvm_object_param_utils(kv_wr_rd_debug_warm_rst_sequence #(CONFIG_T));

    typedef kv_rst_poweron_sequence kv_rst_agent_poweron_sequence_t;
    kv_rst_agent_poweron_sequence_t kv_rst_agent_poweron_seq;
    kv_rst_agent_poweron_sequence_t kv_rst_agent_poweron_seq_2;

    typedef kv_rst_warm_rst_sequence kv_rst_warm_rst_sequence_t;
    kv_rst_warm_rst_sequence_t kv_rst_agent_warm_rst_seq;

    typedef kv_rst_debug_sequence kv_rst_agent_debug_sequence_t;
    kv_rst_agent_debug_sequence_t kv_rst_agent_debug_seq;

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
    rand int unsigned wait_cycles_from_seq;
    rand bit debug_type;
    rand reg [1:0] clear_secrets_data;

    typedef enum {SECURITY_STATE, CLEAR_SECRETS} debug_inputs;

    function new(string name = "");
        super.new(name);
        kv_rst_agent_poweron_seq = kv_rst_agent_poweron_sequence_t::type_id::create("kv_rst_agent_poweron_seq");
        if(!this.randomize()) `uvm_error("KV WR RD", "Failed to randomize KV RST poweron seq");
        kv_rst_agent_poweron_seq_2 = kv_rst_agent_poweron_sequence_t::type_id::create("kv_rst_agent_poweron_seq_2");
        if(!this.randomize()) `uvm_error("KV WR RD", "Failed to randomize KV RST poweron seq");
        kv_rst_agent_warm_rst_seq = kv_rst_warm_rst_sequence_t::type_id::create("kv_rst_agent_warm_rst_seq");
        if(!this.randomize()) `uvm_error("KV_WR_RD_LOCK", "Failed to randomize KV_WARM_RST seq");

        kv_rst_agent_debug_seq = kv_rst_agent_debug_sequence_t::type_id::create("kv_rst_agent_debug_seq");
        if(!this.randomize()) `uvm_error("KV WR RD", "Failed to randomize KV RST debug seq");
        
        hmac_write_seq = kv_write_agent_key_entry_sequence_t::type_id::create("hmac_write_seq");
        if(!this.randomize()) `uvm_error("KV WR RD", "Failed to randomize KV WRITE seq");
        sha512_write_seq = kv_write_agent_key_entry_sequence_t::type_id::create("sha512_write_seq");
        if(!this.randomize()) `uvm_error("KV WR RD", "Failed to randomize KV WRITE seq");
        ecc_write_seq = kv_write_agent_key_entry_sequence_t::type_id::create("ecc_write_seq");
        if(!this.randomize()) `uvm_error("KV WR RD", "Failed to randomize KV WRITE seq");
        doe_write_seq = kv_write_agent_key_entry_sequence_t::type_id::create("doe_write_seq");
        if(!this.randomize()) `uvm_error("KV WR RD", "Failed to randomize KV WRITE seq");
        
        hmac_key_read_seq = kv_read_agent_key_entry_sequence_t::type_id::create("hmac_key_read_seq");
        if(!this.randomize()) `uvm_error("KV WR RD", "Failed to randomize KV READ seq");
        hmac_block_read_seq = kv_read_agent_key_entry_sequence_t::type_id::create("hmac_block_read_seq");
        if(!this.randomize()) `uvm_error("KV WR RD", "Failed to randomize KV READ seq");
        sha512_block_read_seq = kv_read_agent_key_entry_sequence_t::type_id::create("sha512_block_read_seq");
        if(!this.randomize()) `uvm_error("KV WR RD", "Failed to randomize KV READ seq");
        ecc_privkey_read_seq = kv_read_agent_key_entry_sequence_t::type_id::create("ecc_privkey_read_seq");
        if(!this.randomize()) `uvm_error("KV WR RD", "Failed to randomize KV READ seq");
        ecc_seed_read_seq = kv_read_agent_key_entry_sequence_t::type_id::create("ecc_seed_read_seq");
        if(!this.randomize()) `uvm_error("KV WR RD", "Failed to randomize KV READ seq");
        ecc_msg_read_seq = kv_read_agent_key_entry_sequence_t::type_id::create("ecc_msg_read_seq");
        if(!this.randomize()) `uvm_error("KV WR RD", "Failed to randomize KV READ seq");
        //kv_rst_agent_poweron_seq_2 = kv_rst_agent_poweron_sequence_t::type_id::create("kv_rst_agent_poweron_seq_2");
        
    endfunction

    virtual task body();
        uvm_status_e sts;
        //uvm_reg_data_t rd_data;
        int write_entry = 0; 
        int write_offset = 0;
        int read_entry = 0; 
        int read_offset = 0;
        reg [31:0] wr_data, rd_data;
        reg_model = configuration.kv_rm;


        //Issue and wait for reset
        if(configuration.kv_rst_agent_config.sequencer != null)
            kv_rst_agent_poweron_seq.start(configuration.kv_rst_agent_config.sequencer);
        else
            `uvm_error("KV WR RD", "kv_rst_agent_config.sequencer is null!")
        
        
                //Unlock debug mode or clear secrets randomly
                
                    std::randomize(debug_type); //0 - security state, 1 - clear secrets
                    
                    std::randomize(wait_cycles_from_seq) with {
                        wait_cycles_from_seq >= 5;
                        wait_cycles_from_seq <= 50;
                    };

                    std::randomize(clear_secrets_data); //wren, debug_value0/1

                    //Wait for random delay before starting debug txn
                    configuration.kv_rst_agent_config.wait_for_num_clocks(wait_cycles_from_seq);

                    case(debug_type)
                        SECURITY_STATE: begin
                            //start debug seq on rst agent
                            kv_rst_agent_debug_seq.start(configuration.kv_rst_agent_config.sequencer);
                        end
                        CLEAR_SECRETS: begin
                            reg_model.kv_reg_rm.CLEAR_SECRETS.write(sts, clear_secrets_data, UVM_FRONTDOOR, reg_model.kv_AHB_map, this);
                            assert(sts == UVM_IS_OK) else `uvm_error("AHB_CLEAR_SECRETS_SET", "Failed when writing to CLEAR_SECRETS reg!")
                        end
                    endcase
                
            

            
                //Write to all entries
                for (write_entry = 0; write_entry < KV_NUM_KEYS; write_entry++) begin
                    for(write_offset = 0; write_offset < KV_NUM_DWORDS; write_offset++) begin
                        uvm_config_db#(reg [KV_ENTRY_ADDR_W-1:0])::set(null, "uvm_test_top.environment.kv_sha512_write_agent.sequencer.sha512_write_seq", "local_write_entry",write_entry);
                        uvm_config_db#(reg [KV_ENTRY_SIZE_W-1:0])::set(null, "uvm_test_top.environment.kv_sha512_write_agent.sequencer.sha512_write_seq", "local_write_offset",write_offset);
                        sha512_write_seq.start(configuration.kv_sha512_write_agent_config.sequencer);
                    end
                end
                    
            
            //Issue warm reset before reading
            kv_rst_agent_warm_rst_seq.start(configuration.kv_rst_agent_config.sequencer);

            //Read all entries
            for (read_entry = 0; read_entry < KV_NUM_KEYS; read_entry++) begin
                for (read_offset = 0; read_offset < KV_NUM_DWORDS; read_offset++) begin
                    uvm_config_db#(reg [KV_ENTRY_ADDR_W-1:0])::set(null, "uvm_test_top.environment.kv_sha512_block_read_agent.sequencer.sha512_block_read_seq", "local_read_entry",read_entry);
                    uvm_config_db#(reg [KV_ENTRY_SIZE_W-1:0])::set(null, "uvm_test_top.environment.kv_sha512_block_read_agent.sequencer.sha512_block_read_seq", "local_read_offset",read_offset);
                    sha512_block_read_seq.start(configuration.kv_sha512_block_read_agent_config.sequencer);
                end
            end
            
        
    endtask
endclass