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
// DESCRIPTION: Performs KV writes and reads while randomly issuing debug unlock
// via input pin or CLEAR_SECRETS reg.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//

class kv_env_scan_off_sequence #(
    type CONFIG_T
) extends kv_env_sequence_base #(.CONFIG_T(CONFIG_T));

    `uvm_object_param_utils(kv_env_scan_off_sequence #(CONFIG_T));

    typedef kv_rst_poweron_sequence kv_rst_agent_poweron_sequence_t;
    kv_rst_agent_poweron_sequence_t kv_rst_agent_poweron_seq;
    kv_rst_agent_poweron_sequence_t kv_rst_agent_poweron_seq_2;

    typedef kv_rst_debug_sequence kv_rst_agent_debug_sequence_t;
    kv_rst_agent_debug_sequence_t kv_rst_agent_debug_seq;
    typedef kv_rst_debug_on_sequence kv_rst_agent_debug_on_sequence_t;
    kv_rst_agent_debug_on_sequence_t kv_rst_agent_debug_on_seq;
    typedef kv_rst_scan_off_sequence kv_rst_agent_scan_off_sequence_t;
    kv_rst_agent_scan_off_sequence_t kv_rst_agent_scan_off_seq;

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
    rand int unsigned wait_cycles_from_seq;
    rand bit debug_type;
    rand reg [1:0] clear_secrets_data;

    typedef enum {SECURITY_STATE, CLEAR_SECRETS} debug_inputs;

    function new(string name = "");
        super.new(name);
        kv_rst_agent_poweron_seq = kv_rst_agent_poweron_sequence_t::type_id::create("kv_rst_agent_poweron_seq");
        if(!this.randomize()) `uvm_error("KV_ENV_scan_off", "Failed to randomize KV RST poweron seq");
        kv_rst_agent_poweron_seq_2 = kv_rst_agent_poweron_sequence_t::type_id::create("kv_rst_agent_poweron_seq_2");
        if(!this.randomize()) `uvm_error("KV_ENV_scan_off", "Failed to randomize KV RST poweron seq");

        kv_rst_agent_debug_seq = kv_rst_agent_debug_sequence_t::type_id::create("kv_rst_agent_debug_seq");
        if(!this.randomize()) `uvm_error("KV_ENV_scan_off", "Failed to randomize KV RST debug seq");
        kv_rst_agent_debug_on_seq = kv_rst_agent_debug_on_sequence_t::type_id::create("kv_rst_agent_debug_on_seq");
        if(!this.randomize()) `uvm_error("KV_ENV_scan_off", "Failed to randomize KV RST debug on seq");
        kv_rst_agent_scan_off_seq = kv_rst_agent_scan_off_sequence_t::type_id::create("kv_rst_agent_scan_off_seq");
        if(!this.randomize()) `uvm_error("KV_ENV_scan_off", "Failed to randomize KV RST debug off seq");
        
        hmac_write_seq = kv_write_agent_key_entry_sequence_t::type_id::create("hmac_write_seq");
        if(!this.randomize()) `uvm_error("KV_ENV_scan_off", "Failed to randomize KV WRITE seq");
        sha512_write_seq = kv_write_agent_key_entry_sequence_t::type_id::create("sha512_write_seq");
        if(!this.randomize()) `uvm_error("KV_ENV_scan_off", "Failed to randomize KV WRITE seq");
        ecc_write_seq = kv_write_agent_key_entry_sequence_t::type_id::create("ecc_write_seq");
        if(!this.randomize()) `uvm_error("KV_ENV_scan_off", "Failed to randomize KV WRITE seq");
        doe_write_seq = kv_write_agent_key_entry_sequence_t::type_id::create("doe_write_seq");
        if(!this.randomize()) `uvm_error("KV_ENV_scan_off", "Failed to randomize KV WRITE seq");
        
        hmac_key_read_seq = kv_read_agent_key_entry_sequence_t::type_id::create("hmac_key_read_seq");
        if(!this.randomize()) `uvm_error("KV_ENV_scan_off", "Failed to randomize KV READ seq");
        hmac_block_read_seq = kv_read_agent_key_entry_sequence_t::type_id::create("hmac_block_read_seq");
        if(!this.randomize()) `uvm_error("KV_ENV_scan_off", "Failed to randomize KV READ seq");
        sha512_block_read_seq = kv_read_agent_key_entry_sequence_t::type_id::create("sha512_block_read_seq");
        if(!this.randomize()) `uvm_error("KV_ENV_scan_off", "Failed to randomize KV READ seq");
        ecc_privkey_read_seq = kv_read_agent_key_entry_sequence_t::type_id::create("ecc_privkey_read_seq");
        if(!this.randomize()) `uvm_error("KV_ENV_scan_off", "Failed to randomize KV READ seq");
        ecc_seed_read_seq = kv_read_agent_key_entry_sequence_t::type_id::create("ecc_seed_read_seq");
        if(!this.randomize()) `uvm_error("KV_ENV_scan_off", "Failed to randomize KV READ seq");
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


        kv_rst_agent_scan_off_seq.start(configuration.kv_rst_agent_config.sequencer);
                        
    endtask
endclass