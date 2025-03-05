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
    extern virtual task read_write_reg(int id);

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
        
        finish_item(trans);
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

    for (int i = 0; i < 10; i++) begin
        k = i;

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
        
        trans.aw_valid_delay = $urandom_range(aaxi_ci.minwaits, aaxi_ci.maxwaits);
        trans.adw_valid_delay = $urandom_range(aaxi_ci.minwaits, aaxi_ci.maxwaits);
        trans.b_ready_delay = $urandom_range(aaxi_ci.minwaits, aaxi_ci.maxwaits);
        trans.b_valid_ready_delay = $urandom_range(aaxi_ci.minwaits, aaxi_ci.maxwaits);
        trans.resp_valid_ready_delay = $urandom_range(aaxi_ci.minwaits, aaxi_ci.maxwaits);
     
        `uvm_send(trans);
    end
    
    for (int i = 0; i < 10; i++) begin
        get_response(rsp);
    end
endtask


task soc_ifc_env_axi_uvm_gen_b2b_rand_sequence::read_write_reg(int id);
    aaxi_master_tr trans;
    reg [31:0] base, prev_addr;
    automatic int k;
    bit is_write;

    base = 'h30010;

    prev_addr = base;
    for (int i = 0; i < 20; i++) begin
        k = i;

        if (k%2 == 0) begin
            is_write = 1;
            prev_addr = prev_addr + 4; //update addr only for writes
        end
        else is_write = 0;

        `uvm_create(trans);

        trans.kind = is_write ? AAXI_WRITE : AAXI_READ;
        trans.vers = AAXI4;
        trans.addr = prev_addr;
        trans.id = id+k;
        trans.len = 0;
        trans.size = 2;
        trans.burst = AAXI_BURST_FIXED;

        if (is_write) begin
            for (int j = 0; j < 4; j++) begin
                trans.data.push_back($urandom());
                trans.strobes[j] = 1; //$urandom_range(0,1);
            end
        end
        trans.ar_valid_delay = $urandom_range(aaxi_ci.minwaits, aaxi_ci.maxwaits);
        trans.aw_valid_delay = $urandom_range(aaxi_ci.minwaits, aaxi_ci.maxwaits);
        trans.adw_valid_delay = $urandom_range(aaxi_ci.minwaits, aaxi_ci.maxwaits);
        trans.b_ready_delay = $urandom_range(aaxi_ci.minwaits, aaxi_ci.maxwaits);
        trans.b_valid_ready_delay = $urandom_range(aaxi_ci.minwaits, aaxi_ci.maxwaits);
        trans.resp_valid_ready_delay = $urandom_range(aaxi_ci.minwaits, aaxi_ci.maxwaits);
        
        `uvm_send(trans);
    end

    for (int i = 0; i < 20; i++) begin
        get_response(rsp);
    end
endtask