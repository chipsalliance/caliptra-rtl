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
//
//----------------------------------------------------------------------
//
// DESCRIPTION: Executes sequences that cover following cases
// In order KV write/read
// Random KV write/read
// Random KV write/read + warm reset
// Random KV write/read + cold reset
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//

class kv_rand_wr_rd_test_sequence extends kv_bench_sequence_base;

    `uvm_object_utils( kv_rand_wr_rd_test_sequence );

    typedef kv_rst_poweron_sequence kv_rst_poweron_sequence_t;
    rand kv_rst_poweron_sequence_t kv_rst_poweron_seq;

    typedef kv_wr_rd_sequence #(.CONFIG_T(kv_env_configuration_t))kv_wr_rd_sequence_t;
    rand kv_wr_rd_sequence_t kv_wr_rd_seq;

    typedef kv_key_wr_rd_basic_sequence #(.CONFIG_T(kv_env_configuration_t))kv_key_wr_rd_basic_sequence_t;
    rand kv_key_wr_rd_basic_sequence_t kv_key_wr_rd_basic_seq;

    typedef kv_wr_rd_rst_sequence #(.CONFIG_T(kv_env_configuration_t))kv_wr_rd_rst_sequence_t;
    rand kv_wr_rd_rst_sequence_t kv_wr_rd_rst_seq;

    typedef kv_wr_rd_cold_rst_sequence #(.CONFIG_T(kv_env_configuration_t))kv_wr_rd_cold_rst_sequence_t;
    rand kv_wr_rd_cold_rst_sequence_t kv_wr_rd_cold_rst_seq;

    typedef kv_wr_rd_lock_sequence #(.CONFIG_T(kv_env_configuration_t)) kv_wr_rd_lock_sequence_t;
    rand kv_wr_rd_lock_sequence_t kv_wr_rd_lock_seq;
    
    typedef kv_wr_rd_lock_warm_rst_sequence #(.CONFIG_T(kv_env_configuration_t)) kv_wr_rd_lock_warm_rst_sequence_t;
    rand kv_wr_rd_lock_warm_rst_sequence_t kv_wr_rd_lock_warm_rst_seq;

    typedef kv_wr_rd_lock_cold_rst_sequence #(.CONFIG_T(kv_env_configuration_t)) kv_wr_rd_lock_cold_rst_sequence_t;
    rand kv_wr_rd_lock_cold_rst_sequence_t kv_wr_rd_lock_cold_rst_seq;

    typedef kv_wr_rd_lock_core_rst_sequence #(.CONFIG_T(kv_env_configuration_t)) kv_wr_rd_lock_core_rst_sequence_t;
    rand kv_wr_rd_lock_core_rst_sequence_t kv_wr_rd_lock_core_rst_seq;

    typedef kv_wr_rd_debug_sequence #(.CONFIG_T(kv_env_configuration_t)) kv_wr_rd_debug_sequence_t;
    rand kv_wr_rd_debug_sequence_t kv_wr_rd_debug_seq;

    typedef kv_wr_rd_debug_lock_sequence #(.CONFIG_T(kv_env_configuration_t)) kv_wr_rd_debug_lock_sequence_t;
    rand kv_wr_rd_debug_lock_sequence_t kv_wr_rd_debug_lock_seq;

    typedef kv_wr_rd_debug_warm_rst_sequence #(.CONFIG_T(kv_env_configuration_t)) kv_wr_rd_debug_warm_rst_sequence_t;
    rand kv_wr_rd_debug_warm_rst_sequence_t kv_wr_rd_debug_warm_rst_seq;

    typedef kv_wr_rd_debug_cold_rst_sequence #(.CONFIG_T(kv_env_configuration_t)) kv_wr_rd_debug_cold_rst_sequence_t;
    rand kv_wr_rd_debug_cold_rst_sequence_t kv_wr_rd_debug_cold_rst_seq;

    typedef kv_wr_rd_debug_core_rst_sequence #(.CONFIG_T(kv_env_configuration_t)) kv_wr_rd_debug_core_rst_sequence_t;
    rand kv_wr_rd_debug_core_rst_sequence_t kv_wr_rd_debug_core_rst_seq;

    //Responder sequences:
    typedef kv_read_responder_sequence kv_hmac_key_read_agent_responder_seq_t;
    kv_hmac_key_read_agent_responder_seq_t kv_hmac_key_read_agent_responder_seq;

    function new(string name = "" );
        super.new(name);
    endfunction

    virtual task body();

        kv_wr_rd_seq = kv_wr_rd_sequence_t::type_id::create("kv_wr_rd_seq");
        kv_wr_rd_rst_seq = kv_wr_rd_rst_sequence_t::type_id::create("kv_wr_rd_rst_seq");
        kv_wr_rd_cold_rst_seq = kv_wr_rd_cold_rst_sequence_t::type_id::create("kv_wr_rd_cold_rst_seq");
        kv_key_wr_rd_basic_seq = kv_key_wr_rd_basic_sequence_t::type_id::create("kv_key_wr_rd_basic_seq");
        kv_wr_rd_lock_seq = kv_wr_rd_lock_sequence_t::type_id::create("kv_wr_rd_lock_seq");
        kv_wr_rd_lock_warm_rst_seq = kv_wr_rd_lock_warm_rst_sequence_t::type_id::create("kv_wr_rd_lock_warm_rst_seq");
        kv_wr_rd_lock_cold_rst_seq = kv_wr_rd_lock_cold_rst_sequence_t::type_id::create("kv_wr_rd_lock_cold_rst_seq");
        kv_wr_rd_lock_core_rst_seq = kv_wr_rd_lock_core_rst_sequence_t::type_id::create("kv_wr_rd_lock_core_rst_seq");
        kv_wr_rd_debug_seq = kv_wr_rd_debug_sequence_t::type_id::create("kv_wr_rd_debug_seq");
        kv_wr_rd_debug_lock_seq = kv_wr_rd_debug_lock_sequence_t::type_id::create("kv_wr_rd_debug_lock_seq");
        kv_wr_rd_debug_warm_rst_seq = kv_wr_rd_debug_warm_rst_sequence_t::type_id::create("kv_wr_rd_debug_warm_rst_seq");
        kv_wr_rd_debug_cold_rst_seq = kv_wr_rd_debug_cold_rst_sequence_t::type_id::create("kv_wr_rd_debug_cold_rst_seq");
        kv_wr_rd_debug_core_rst_seq = kv_wr_rd_debug_core_rst_sequence_t::type_id::create("kv_wr_rd_debug_core_rst_seq");

        if(!kv_wr_rd_seq.randomize())
            `uvm_fatal("KV WR RD SEQ", "kv_rand_wr_rd_test_sequence::body() - kv_wr_rd_seq randomization failed");
        if(!kv_key_wr_rd_basic_seq.randomize())
            `uvm_fatal("KV BASIC WR RD SEQ", "kv_rand_wr_rd_test_sequence::body() - kv_key_wr_rd_basic_seq randomization failed");
        if(!kv_wr_rd_rst_seq.randomize())
            `uvm_fatal("KV WR RD RST SEQ", "kv_rand_wr_rd_test_sequence::body() - kv_wr_rd_rst_seq randomization failed");
        if(!kv_wr_rd_cold_rst_seq.randomize())
            `uvm_fatal("KV WR RD COLD RST SEQ", "kv_rand_wr_rd_test_sequence::body() - kv_wr_rd_cold_rst_seq randomization failed");
        if(!kv_wr_rd_lock_seq.randomize())
            `uvm_fatal("KV_WR_RD_LOCK_SEQ", "kv_rand_wr_rd_test_sequence::body() - kv_wr_rd_lock_seq randomization failed");

        reg_model.reset();
        
        //First write to all regs with random values
        `uvm_info("TOP", "Basic sequence",UVM_MEDIUM);
        kv_key_wr_rd_basic_seq.start(top_configuration.vsqr);
        `uvm_info("TOP", "WR RD sequence",UVM_MEDIUM);
        kv_wr_rd_seq.start(top_configuration.vsqr);
        `uvm_info("TOP", "wr rd warm rst sequence",UVM_MEDIUM);
        kv_wr_rd_rst_seq.start(top_configuration.vsqr);
        `uvm_info("TOP", "wr rd cold rst sequence",UVM_MEDIUM);
        kv_wr_rd_cold_rst_seq.start(top_configuration.vsqr);
        

        if(1) $display("** TESTCASE PASSED");
        else  $display("** TESTCASE FAILED");
    endtask

endclass