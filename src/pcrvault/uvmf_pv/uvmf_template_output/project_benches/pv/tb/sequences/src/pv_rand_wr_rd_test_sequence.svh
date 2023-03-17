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
// DESCRIPTION: This file contains the top level sequence used in  pv_rand_wr_rd_test.
// It is derived from the example_derived_test_sequence
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//

class pv_rand_wr_rd_test_sequence extends pv_bench_sequence_base;

    `uvm_object_utils( pv_rand_wr_rd_test_sequence );

    typedef pv_rst_poweron_sequence pv_rst_poweron_sequence_t;
    rand pv_rst_poweron_sequence_t pv_rst_poweron_seq;

    typedef pv_wr_rd_sequence #(.CONFIG_T(pv_env_configuration_t))pv_wr_rd_sequence_t;
    rand pv_wr_rd_sequence_t pv_wr_rd_seq;

    typedef pv_pcr_wr_rd_basic_sequence #(.CONFIG_T(pv_env_configuration_t))pv_pcr_wr_rd_basic_sequence_t;
    rand pv_pcr_wr_rd_basic_sequence_t pv_pcr_wr_rd_basic_seq;

    typedef pv_wr_rd_rst_sequence #(.CONFIG_T(pv_env_configuration_t))pv_wr_rd_rst_sequence_t;
    rand pv_wr_rd_rst_sequence_t pv_wr_rd_rst_seq;

    typedef pv_wr_rd_cold_rst_sequence #(.CONFIG_T(pv_env_configuration_t))pv_wr_rd_cold_rst_sequence_t;
    rand pv_wr_rd_cold_rst_sequence_t pv_wr_rd_cold_rst_seq;

    typedef pv_wr_rd_ahb_sequence #(.CONFIG_T(pv_env_configuration_t))pv_wr_rd_ahb_sequence_t;
    rand pv_wr_rd_ahb_sequence_t pv_wr_rd_ahb_seq;

    typedef pv_wr_rd_lock_sequence #(.CONFIG_T(pv_env_configuration_t)) pv_wr_rd_lock_sequence_t;
    rand pv_wr_rd_lock_sequence_t pv_wr_rd_lock_seq;
    
    typedef pv_wr_rd_lock_warm_rst_sequence #(.CONFIG_T(pv_env_configuration_t)) pv_wr_rd_lock_warm_rst_sequence_t;
    rand pv_wr_rd_lock_warm_rst_sequence_t pv_wr_rd_lock_warm_rst_seq;

    typedef pv_wr_rd_lock_cold_rst_sequence #(.CONFIG_T(pv_env_configuration_t)) pv_wr_rd_lock_cold_rst_sequence_t;
    rand pv_wr_rd_lock_cold_rst_sequence_t pv_wr_rd_lock_cold_rst_seq;



    function new(string name = "" );
        super.new(name);
    endfunction

    virtual task body();

        pv_wr_rd_seq = pv_wr_rd_sequence_t::type_id::create("pv_wr_rd_seq");
        pv_wr_rd_rst_seq = pv_wr_rd_rst_sequence_t::type_id::create("pv_wr_rd_rst_seq");
        pv_wr_rd_cold_rst_seq = pv_wr_rd_cold_rst_sequence_t::type_id::create("pv_wr_rd_cold_rst_seq");
        pv_wr_rd_ahb_seq = pv_wr_rd_ahb_sequence_t::type_id::create("pv_wr_rd_ahb_seq");
        pv_pcr_wr_rd_basic_seq = pv_pcr_wr_rd_basic_sequence_t::type_id::create("pv_pcr_wr_rd_basic_seq");
        pv_wr_rd_lock_seq = pv_wr_rd_lock_sequence_t::type_id::create("pv_wr_rd_lock_seq");
        pv_wr_rd_lock_warm_rst_seq = pv_wr_rd_lock_warm_rst_sequence_t::type_id::create("pv_wr_rd_lock_warm_rst_seq");
        pv_wr_rd_lock_cold_rst_seq = pv_wr_rd_lock_cold_rst_sequence_t::type_id::create("pv_wr_rd_lock_cold_rst_seq");
        
        if(!pv_wr_rd_seq.randomize())
            `uvm_fatal("PV WR RD SEQ", "pv_rand_wr_rd_test_sequence::body() - pv_wr_rd_seq randomization failed");
        if(!pv_pcr_wr_rd_basic_seq.randomize())
            `uvm_fatal("PV BASIC WR RD SEQ", "pv_rand_wr_rd_test_sequence::body() - pv_pcr_wr_rd_basic_seq randomization failed");
        if(!pv_wr_rd_rst_seq.randomize())
            `uvm_fatal("PV WR RD RST SEQ", "pv_rand_wr_rd_test_sequence::body() - pv_wr_rd_rst_seq randomization failed");
        if(!pv_wr_rd_cold_rst_seq.randomize())
            `uvm_fatal("PV WR RD COLD RST SEQ", "pv_rand_wr_rd_test_sequence::body() - pv_wr_rd_cold_rst_seq randomization failed");
        if(!pv_wr_rd_lock_seq.randomize())
            `uvm_fatal("PV_WR_RD_LOCK_SEQ", "pv_rand_wr_rd_test_sequence::body() - pv_wr_rd_lock_seq randomization failed");

        reg_model.reset();
        
        //First write to all regs with random values
        `uvm_info("TOP", "Basic sequence",UVM_MEDIUM);
        pv_pcr_wr_rd_basic_seq.start(top_configuration.vsqr);
        `uvm_info("TOP", "WR RD sequence",UVM_MEDIUM);
        pv_wr_rd_seq.start(top_configuration.vsqr);
         `uvm_info("TOP", "wr rd warm rst sequence",UVM_MEDIUM);
         pv_wr_rd_rst_seq.start(top_configuration.vsqr);
         `uvm_info("TOP", "wr rd cold rst sequence",UVM_MEDIUM);
         pv_wr_rd_cold_rst_seq.start(top_configuration.vsqr);
         `uvm_info("TOP", "WR RD AHB sequence",UVM_MEDIUM);
        pv_wr_rd_ahb_seq.start(top_configuration.vsqr);
        

        if(1) $display("** TESTCASE PASSED");
        else  $display("** TESTCASE FAILED");
    endtask

endclass