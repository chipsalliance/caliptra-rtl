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

//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
// DESCRIPTION: Base sequence to perform a mailbox command within the
//              soc_ifc environment.
//              Extended to provide additional functionality.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_env_axi_uvm_gen_b2b_rand_sequence extends soc_ifc_env_axi_uvm_b2b_rand_sequence;
    `uvm_object_utils( soc_ifc_env_axi_uvm_gen_b2b_rand_sequence )

    aaxi_cfg_info aaxi_ci;

    extern virtual task read_reg();
    extern virtual task write_reg(int id);

    function new(string name = "");
        super.new(name);
    endfunction

    virtual task pre_body();
        super.pre_body();
    endtask


endclass

task soc_ifc_env_axi_uvm_gen_b2b_rand_sequence::read_reg();
    
    aaxi_master_tr trans;
    reg [31:0] base;
    automatic int k;

    base = 'h30000;

    // `uvm_info("[Read reg]", "setting maxwaits", UVM_MEDIUM)
    // aaxi_ci.maxwaits = 50;
    // aaxi_ci.total_outstanding_depth = 10;
    // aaxi_ci.id_outstanding_depth = 10;
    `uvm_info("[Read reg]", $sformatf("maxwait = %d, outstanding depth = %d", aaxi_ci.maxwaits, aaxi_ci.total_outstanding_depth), UVM_MEDIUM)

    for (int i = 0; i < 10; i++) begin
        k = i;
        trans = aaxi_master_tr::type_id::create("trans");
        start_item(trans);
        trans.randomize();

        trans.kind = AAXI_READ;
        trans.vers = AAXI4;
        trans.addr = base + (k*4);
        trans.id = 0;
        trans.len = 0;
        trans.size = $urandom_range(0,2);
        trans.burst = $urandom_range(0,1);
        trans.ar_valid_delay = $urandom_range(aaxi_ci.minwaits, aaxi_ci.maxwaits);
        trans.resp_valid_ready_delay = $urandom_range(aaxi_ci.minwaits, aaxi_ci.maxwaits);
        
        `uvm_info("KNU_GEN_RW", $sformatf("Starting AAXI read txn with addr = %h", trans.addr), UVM_MEDIUM)
        
        finish_item(trans);
        // wait(10);
    end
    for (int i = 0; i < 10; i++) begin
        get_response(rsp);
    end

endtask

task soc_ifc_env_axi_uvm_gen_b2b_rand_sequence::write_reg(int id);
    aaxi_master_tr trans;
    reg [31:0] base;
    automatic int k;

    base = 'h30000;

    // aaxi_ci.maxwaits = 50;
    // aaxi_ci.total_outstanding_depth = 10;
    // aaxi_ci.id_outstanding_depth = 10;

    for (int i = 0; i < 10; i++) begin
        k = i;
    // repeat(10) begin
        // trans = aaxi_master_tr::type_id::create("trans");

        // start_item(trans);
        // trans.randomize();
        `uvm_create(trans);

        trans.kind = AAXI_WRITE;
        trans.vers = AAXI4;
        trans.addr = base + (k*4);
        trans.id = id+k;
        trans.len = 0;
        trans.size = 2;
        trans.burst = AAXI_BURST_FIXED;
        for (int j = 0; j < 4; j++)
            trans.data.push_back($urandom());
        
        trans.aw_valid_delay = 0; //$urandom_range(configuration.aaxi_ci.minwaits, configuration.aaxi_ci.maxwaits);
        trans.adw_valid_delay = 0; //10*3;
        // trans.b_valid_ready_delay = $urandom_range(configuration.aaxi_ci.minwaits, configuration.aaxi_ci.maxwaits);
        trans.b_ready_delay = 10;
        trans.b_valid_ready_delay = 10;
        trans.resp_valid_ready_delay = 0;
        `uvm_info("KNU_GEN_RW", $sformatf("Starting AAXI write txn with addr = %h, wdata = %h", trans.addr, {trans.data[3], trans.data[2], trans.data[1], trans.data[0]}), UVM_MEDIUM)
     
        // finish_item(trans);
        `uvm_send(trans);
        // #10;
        // wait(10);
    end
    // repeat(10) begin
    for (int i = 0; i < 10; i++) begin
        `uvm_info("KNU_RESP", $sformatf("queuing get response for txn %0d", i), UVM_MEDIUM)
        get_response(rsp);
        `uvm_info("KNU_RESP", $sformatf("received response for txn %0d", i), UVM_MEDIUM)
    end
endtask
