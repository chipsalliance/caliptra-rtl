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
// DESCRIPTION: This file contains the top level sequence used in  kv_rand_test.
// It is derived from the example_derived_test_sequence
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//

class kv_rand_test_sequence extends kv_bench_sequence_base;

    `uvm_object_utils( kv_rand_test_sequence );

    typedef kv_rst_poweron_sequence kv_rst_poweron_sequence_t;
    rand kv_rst_poweron_sequence_t kv_rst_poweron_seq;

    function new(string name = "" );
        super.new(name);
    endfunction

    virtual task body();

        kv_rst_poweron_seq = kv_rst_poweron_sequence_t::type_id::create("kv_rst_poweron_seq");
        kv_hmac_write_agent_random_seq = kv_hmac_write_agent_random_seq_t::type_id::create("kv_hmac_write_agent_random_seq");
        kv_sha512_write_agent_random_seq = kv_sha512_write_agent_random_seq_t::type_id::create("kv_sha512_write_agent_random_seq");
        kv_ecc_write_agent_random_seq = kv_ecc_write_agent_random_seq_t::type_id::create("kv_ecc_write_agent_random_seq");
        kv_doe_write_agent_random_seq = kv_doe_write_agent_random_seq_t::type_id::create("kv_doe_write_agent_random_seq");

        if(!kv_rst_poweron_seq.randomize())
            `uvm_fatal("SEQ", "kv_rand_test_sequence::body() - kv_rst_poweron_seq randomization failed");
        if(!kv_hmac_write_agent_random_seq.randomize())
            `uvm_fatal("SEQ", "kv_rand_test_sequence::body() - kv_hmac_write_agent_random_seq randomization failed");
        if(!kv_sha512_write_agent_random_seq.randomize())
            `uvm_fatal("SEQ", "kv_rand_test_sequence::body() - kv_sha512_write_agent_random_seq randomization failed");
        if(!kv_ecc_write_agent_random_seq.randomize())
            `uvm_fatal("SEQ", "kv_rand_test_sequence::body() - kv_ecc_write_agent_random_seq randomization failed");
        if(!kv_doe_write_agent_random_seq.randomize())
            `uvm_fatal("SEQ", "kv_rand_test_sequence::body() - kv_doe_write_agent_random_seq randomization failed");

        reg_model.reset();

        kv_rst_agent_config.wait_for_reset();
        kv_hmac_write_agent_config.wait_for_reset();
        kv_sha512_write_agent_config.wait_for_reset();
        kv_ecc_write_agent_config.wait_for_reset();
        kv_doe_write_agent_config.wait_for_reset();

        kv_rst_agent_config.wait_for_num_clocks(10);
        kv_rst_poweron_seq.start(kv_rst_agent_sequencer);

        
        kv_hmac_write_agent_config.wait_for_num_clocks(10);
        kv_hmac_write_agent_random_seq.start(kv_hmac_write_agent_sequencer);

        kv_sha512_write_agent_random_seq.start(kv_sha512_write_agent_sequencer);
        
        kv_ecc_write_agent_random_seq.start(kv_ecc_write_agent_sequencer);
        
        kv_doe_write_agent_random_seq.start(kv_doe_write_agent_sequencer);
        kv_doe_write_agent_config.wait_for_num_clocks(400);

        if(1) $display("** TESTCASE PASSED");
        else  $display("** TESTCASE FAILED");
    endtask

endclass