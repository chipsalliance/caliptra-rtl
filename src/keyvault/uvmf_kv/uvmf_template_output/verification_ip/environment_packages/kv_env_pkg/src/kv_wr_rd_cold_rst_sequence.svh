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
// DESCRIPTION: Executes random writes and reads on a random clients 
// and then issues a cold reset before continuing to write and read on
// other clients
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//

class kv_wr_rd_cold_rst_sequence #(
    type CONFIG_T
) extends kv_env_sequence_base #(.CONFIG_T(CONFIG_T));

    `uvm_object_param_utils(kv_wr_rd_cold_rst_sequence #(CONFIG_T));

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

    rand reg [KV_ENTRY_ADDR_W-1:0] hmac_write_entry, sha512_write_entry, ecc_write_entry, doe_write_entry;    
    //constraint valid_entry {hmac_write_entry != sha512_write_entry != ecc_write_entry != doe_write_entry;}
    rand reg [1:0] write_id;
    rand reg [2:0] read_id;
    typedef enum {HMAC, SHA512, ECC, DOE} write_agents;
    typedef enum {HMAC_KEY, HMAC_BLOCK, SHA512_BLOCK, ECC_PRIVKEY, ECC_SEED} read_agents;

    uvm_event active_phase;
    uvm_event write_event;
    uvm_event read_event;
    
    

    function new(string name = "");
        super.new(name);
        kv_rst_agent_poweron_seq = kv_rst_agent_poweron_sequence_t::type_id::create("kv_rst_agent_poweron_seq");
        if(!this.randomize()) `uvm_error("KV WR RD", "Failed to randomize KV RST poweron seq");
        kv_rst_agent_cold_rst_seq = kv_rst_cold_rst_sequence_t::type_id::create("kv_rst_agent_cold_rst_seq");
        if(!this.randomize()) `uvm_error("KV WR RD", "Failed to randomize KV RST poweron seq");
        
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
        
    endfunction

    virtual task body();
        uvm_status_e sts;
        //uvm_reg_data_t rd_data;
        int entry = 0; 
        int offset = 0;
        reg [KV_DATA_W-1:0] wr_data, rd_data;

        active_phase = new();
        write_event = new();
        read_event = new();

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

        // std::randomize(write_id) with {write_id inside [0:3]};
        // std::randomize(read_id) with {read_id inside [0:5]};
        write_id = $urandom_range(0,3);
        read_id = $urandom_range(0,4);

        fork
            begin
                //Wait for reset to finish if rand write_id is not current client id
                if(write_id != ECC)
                    active_phase.wait_ptrigger;
                //Do the writes
                repeat(10) begin
                    uvm_config_db#(reg [KV_ENTRY_ADDR_W-1:0])::set(null, "uvm_test_top.environment.kv_ecc_write_agent.sequencer.ecc_write_seq", "local_write_entry",ecc_write_entry);
                    ecc_write_seq.start(configuration.kv_ecc_write_agent_config.sequencer); 
                end
                //Trigger event after writes are done
                if(write_id == ECC)
                    write_event.trigger;
                
            end
            begin
                if(read_id != ECC_PRIVKEY)
                    active_phase.wait_ptrigger;

                repeat(10) begin
                    ecc_privkey_read_seq.start(configuration.kv_ecc_privkey_read_agent_config.sequencer);
                end
                if(read_id == ECC_PRIVKEY)
                    read_event.trigger;
                
            end
            begin
                if(write_id != DOE)
                    active_phase.wait_ptrigger;

                repeat(10) begin
                    uvm_config_db#(reg [KV_ENTRY_ADDR_W-1:0])::set(null, "uvm_test_top.environment.kv_doe_write_agent.sequencer.doe_write_seq", "local_write_entry",doe_write_entry);
                    doe_write_seq.start(configuration.kv_doe_write_agent_config.sequencer);
                end
                if(write_id == DOE)
                    write_event.trigger;
                
            end
            begin
                if(write_id != SHA512)
                    active_phase.wait_ptrigger;

                repeat(10) begin
                    uvm_config_db#(reg [KV_ENTRY_ADDR_W-1:0])::set(null, "uvm_test_top.environment.kv_sha512_write_agent.sequencer.sha512_write_seq", "local_write_entry",sha512_write_entry);
                    sha512_write_seq.start(configuration.kv_sha512_write_agent_config.sequencer);
                end
                if(write_id == SHA512)
                    write_event.trigger;
                
            end
            begin
                if(read_id != HMAC_BLOCK)
                    active_phase.wait_ptrigger;

                repeat(10) begin
                    hmac_block_read_seq.start(configuration.kv_hmac_block_read_agent_config.sequencer);
                end
                if(read_id == HMAC_BLOCK)
                    read_event.trigger;
                
            end
            begin
                if(write_id != HMAC)
                    active_phase.wait_ptrigger;

                repeat(10) begin
                    uvm_config_db#(reg [KV_ENTRY_ADDR_W-1:0])::set(null, "uvm_test_top.environment.kv_hmac_write_agent.sequencer.hmac_write_seq", "local_write_entry",hmac_write_entry);
                    hmac_write_seq.start(configuration.kv_hmac_write_agent_config.sequencer);
                end
                if(write_id == HMAC)
                    write_event.trigger;
                
            end
            begin
                if(read_id != SHA512_BLOCK)
                    active_phase.wait_ptrigger;

                repeat(10) begin
                    sha512_block_read_seq.start(configuration.kv_sha512_block_read_agent_config.sequencer);
                end
                if(read_id == SHA512_BLOCK)
                    read_event.trigger;

            end
            begin
                if(read_id != HMAC_KEY)
                    active_phase.wait_ptrigger;

                repeat(10) begin
                    hmac_key_read_seq.start(configuration.kv_hmac_key_read_agent_config.sequencer);
                end
                if(read_id == HMAC_KEY)
                    read_event.trigger;
            end
            begin
                if(read_id != ECC_SEED)
                    active_phase.wait_ptrigger;

                repeat(10) begin
                    ecc_seed_read_seq.start(configuration.kv_ecc_seed_read_agent_config.sequencer);
                end
                if(read_id == ECC_SEED)
                    read_event.trigger;
                
            end
            
            begin
                write_event.wait_ptrigger;
                read_event.wait_ptrigger;
                kv_rst_agent_cold_rst_seq.start(configuration.kv_rst_agent_config.sequencer);
                if(kv_rst_agent_cold_rst_seq.req.set_pwrgood && !kv_rst_agent_cold_rst_seq.req.assert_rst) begin
                    active_phase.trigger;
                end
            end
            

        join
        active_phase.reset;
        configuration.kv_rst_agent_config.wait_for_num_clocks(1000);
        configuration.kv_hmac_write_agent_config.wait_for_num_clocks(1000);
        configuration.kv_sha512_write_agent_config.wait_for_num_clocks(1000);
        configuration.kv_ecc_write_agent_config.wait_for_num_clocks(1000);
        configuration.kv_doe_write_agent_config.wait_for_num_clocks(1000);
        configuration.kv_hmac_key_read_agent_config.wait_for_num_clocks(1000);
        configuration.kv_hmac_block_read_agent_config.wait_for_num_clocks(1000);
        configuration.kv_sha512_block_read_agent_config.wait_for_num_clocks(1000);
        configuration.kv_ecc_privkey_read_agent_config.wait_for_num_clocks(1000);
        configuration.kv_ecc_seed_read_agent_config.wait_for_num_clocks(1000);
    endtask

endclass