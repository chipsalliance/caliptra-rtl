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
// DESCRIPTION: Issues random writes and reads
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//

class kv_wr_rd_sequence #(
    type CONFIG_T
) extends kv_env_sequence_base #(.CONFIG_T(CONFIG_T));

    `uvm_object_param_utils(kv_wr_rd_sequence #(CONFIG_T));

    typedef kv_rst_poweron_sequence kv_rst_agent_poweron_sequence_t;
    kv_rst_agent_poweron_sequence_t kv_rst_agent_poweron_seq;
    kv_rst_agent_poweron_sequence_t kv_rst_agent_poweron_seq_2;

    typedef kv_write_key_entry_sequence kv_write_agent_key_entry_sequence_t;
    kv_write_agent_key_entry_sequence_t hmac_write_seq;
    kv_write_agent_key_entry_sequence_t sha512_write_seq;
    kv_write_agent_key_entry_sequence_t ecc_write_seq;
    kv_write_agent_key_entry_sequence_t doe_write_seq;

    typedef kv_read_key_entry_sequence kv_read_agent_key_entry_sequence_t;
    kv_read_agent_key_entry_sequence_t hmac_key_read_seq;
    kv_read_agent_key_entry_sequence_t hmac_block_read_seq;
    kv_read_agent_key_entry_sequence_t mldsa_key_read_seq;
    kv_read_agent_key_entry_sequence_t ecc_privkey_read_seq;
    kv_read_agent_key_entry_sequence_t ecc_seed_read_seq;
    kv_read_agent_key_entry_sequence_t aes_key_read_seq;


    function new(string name = "");
        super.new(name);
        kv_rst_agent_poweron_seq = kv_rst_agent_poweron_sequence_t::type_id::create("kv_rst_agent_poweron_seq");
        if(!this.randomize()) `uvm_error("KV WR RD", "Failed to randomize KV RST poweron seq");
        kv_rst_agent_poweron_seq_2 = kv_rst_agent_poweron_sequence_t::type_id::create("kv_rst_agent_poweron_seq_2");
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
        mldsa_key_read_seq = kv_read_agent_key_entry_sequence_t::type_id::create("mldsa_key_read_seq");
        if(!this.randomize()) `uvm_error("KV WR RD", "Failed to randomize KV READ seq");
        ecc_privkey_read_seq = kv_read_agent_key_entry_sequence_t::type_id::create("ecc_privkey_read_seq");
        if(!this.randomize()) `uvm_error("KV WR RD", "Failed to randomize KV READ seq");
        ecc_seed_read_seq = kv_read_agent_key_entry_sequence_t::type_id::create("ecc_seed_read_seq");
        if(!this.randomize()) `uvm_error("KV WR RD", "Failed to randomize KV READ seq");
        aes_key_read_seq = kv_read_agent_key_entry_sequence_t::type_id::create("aes_key_read_seq");
        if(!this.randomize()) `uvm_error("KV WR RD", "Failed to randomize KV READ seq");
        //kv_rst_agent_poweron_seq_2 = kv_rst_agent_poweron_sequence_t::type_id::create("kv_rst_agent_poweron_seq_2");
        
    endfunction

    virtual task body();
        uvm_status_e sts;
        //uvm_reg_data_t rd_data;
        int entry = 0; 
        int offset = 0;
        reg [31:0] wr_data, rd_data;

        gen_rand_entries();

        //Issue and wait for reset
        if(configuration.kv_rst_agent_config.sequencer != null)
            kv_rst_agent_poweron_seq.start(configuration.kv_rst_agent_config.sequencer);
        else
            `uvm_error("KV WR RD", "kv_rst_agent_config.sequencer is null!")

        fork
            begin
                if(configuration.kv_ecc_write_agent_config.sequencer != null)
                    repeat(10) begin
                        uvm_config_db#(reg [KV_ENTRY_ADDR_W-1:0])::set(null, "uvm_test_top.environment.kv_ecc_write_agent.sequencer.ecc_write_seq", "local_write_entry",ecc_write_entry);
                        ecc_write_seq.start(configuration.kv_ecc_write_agent_config.sequencer);
                        
                    end
                else
                    `uvm_error("KV WR RD", "kv_ecc_write_agent_config.sequencer is null!");
            end
            begin
                if(configuration.kv_ecc_privkey_read_agent_config.sequencer != null)
                    repeat(10) ecc_privkey_read_seq.start(configuration.kv_ecc_privkey_read_agent_config.sequencer);
                else
                    `uvm_error("KV WR RD", "kv_ecc_privkey_read_agent_config.sequencer is null!");
            end
        join
            begin
                if(configuration.kv_doe_write_agent_config.sequencer != null)
                    repeat(10) begin
                        uvm_config_db#(reg [KV_ENTRY_ADDR_W-1:0])::set(null, "uvm_test_top.environment.kv_doe_write_agent.sequencer.doe_write_seq", "local_write_entry",doe_write_entry);
                        doe_write_seq.start(configuration.kv_doe_write_agent_config.sequencer);
                    end
                else
                    `uvm_error("KV WR RD", "kv_doe_write_agent_config.sequencer is null!");
            end
        fork
            begin
                if(configuration.kv_sha512_write_agent_config.sequencer != null)
                    repeat(10) begin
                        uvm_config_db#(reg [KV_ENTRY_ADDR_W-1:0])::set(null, "uvm_test_top.environment.kv_sha512_write_agent.sequencer.sha512_write_seq", "local_write_entry",sha512_write_entry);
                        sha512_write_seq.start(configuration.kv_sha512_write_agent_config.sequencer);
                    end
                else
                    `uvm_error("KV WR RD", "kv_sha512_write_agent_config.sequencer is null!");
            end
            begin
                if(configuration.kv_hmac_block_read_agent_config.sequencer != null)
                    repeat(10) hmac_block_read_seq.start(configuration.kv_hmac_block_read_agent_config.sequencer);
                else
                    `uvm_error("KV WR RD", "kv_hmac_block_read_agent_config.sequencer is null!");
            end
        join
        fork
            begin
                if(configuration.kv_hmac_write_agent_config.sequencer != null)
                    repeat(10) begin
                        uvm_config_db#(reg [KV_ENTRY_ADDR_W-1:0])::set(null, "uvm_test_top.environment.kv_hmac_write_agent.sequencer.hmac_write_seq", "local_write_entry",hmac_write_entry);
                        hmac_write_seq.start(configuration.kv_hmac_write_agent_config.sequencer);
                    end
                else
                    `uvm_error("KV WR RD", "kv_hmac_write_agent_config.sequencer is null!");
            end
            begin
                if(configuration.kv_mldsa_key_read_agent_config.sequencer != null)
                    repeat(10) mldsa_key_read_seq.start(configuration.kv_mldsa_key_read_agent_config.sequencer);
                else
                    `uvm_error("KV WR RD", "kv_mldsa_key_read_agent_config.sequencer is null!");
            end
            begin
                if(configuration.kv_hmac_key_read_agent_config.sequencer != null)
                    repeat(10) hmac_key_read_seq.start(configuration.kv_hmac_key_read_agent_config.sequencer);
                else
                    `uvm_error("KV WR RD", "kv_hmac_key_read_agent_config.sequencer is null!");
            end
            begin
                if(configuration.kv_ecc_seed_read_agent_config.sequencer != null)
                    repeat(10) ecc_seed_read_seq.start(configuration.kv_ecc_seed_read_agent_config.sequencer);
                else
                    `uvm_error("KV WR RD", "kv_ecc_seed_read_agent_config.sequencer is null!");
            end
            begin
                if(configuration.kv_aes_key_read_agent_config.sequencer != null)
                    repeat(10) aes_key_read_seq.start(configuration.kv_aes_key_read_agent_config.sequencer);
                else
                    `uvm_error("KV WR RD", "kv_aes_key_read_agent_config.sequencer is null!");
            end
        join
        
        queue_writes();
    endtask

endclass