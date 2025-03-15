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
// DESCRIPTION: Base sequence to perform an AXI rd/wr command within the
//              soc_ifc environment.
//              Extended to provide additional functionality.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_env_axi_uvm_gen_b2b_rand_sequence extends soc_ifc_env_axi_uvm_b2b_rand_sequence;
    `uvm_object_utils( soc_ifc_env_axi_uvm_gen_b2b_rand_sequence )

    aaxi_cfg_info aaxi_ci;
    soc_ifc_reg_model_top reg_model;

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
    
    aaxi_master_tr trans, rsp;
    uvm_reg regs[$];

    reg_model.soc_ifc_reg_rm.soc_ifc_reg_AXI_map.get_registers(regs, UVM_HIER);

    foreach(regs[idx]) begin
        trans = aaxi_master_tr::type_id::create("trans");
        start_item(trans);
        trans.randomize();

        trans.kind = AAXI_READ;
        trans.vers = AAXI4;
        trans.addr = regs[idx].get_address(reg_model.soc_ifc_AXI_map);
        trans.id = $urandom();
        trans.aruser = $urandom();
        trans.len = 0;
        trans.size = $urandom_range(0,2);
        trans.burst = $urandom_range(0,1);
        trans.ar_valid_delay = $urandom_range(aaxi_ci.minwaits, aaxi_ci.maxwaits);
        trans.resp_valid_ready_delay = $urandom_range(aaxi_ci.minwaits, aaxi_ci.maxwaits);
        
        finish_item(trans);
    end
    foreach(regs[idx]) begin
        get_response(rsp);
    end

endtask

task soc_ifc_env_axi_uvm_gen_b2b_rand_sequence::write_reg(int id);
    aaxi_master_tr trans;
    uvm_reg regs[$];
    uvm_reg blocklist[], reg_list[];
    int del_idx[$];

    reg_list = '{
        reg_model.soc_ifc_reg_rm.CPTRA_HW_ERROR_ENC,
        reg_model.soc_ifc_reg_rm.CPTRA_FW_ERROR_ENC,
        reg_model.soc_ifc_reg_rm.CPTRA_FW_EXTENDED_ERROR_INFO[0],
        reg_model.soc_ifc_reg_rm.CPTRA_FW_EXTENDED_ERROR_INFO[1],
        reg_model.soc_ifc_reg_rm.CPTRA_FW_EXTENDED_ERROR_INFO[2],
        reg_model.soc_ifc_reg_rm.CPTRA_FW_EXTENDED_ERROR_INFO[3],
        reg_model.soc_ifc_reg_rm.CPTRA_FW_EXTENDED_ERROR_INFO[4],
        reg_model.soc_ifc_reg_rm.CPTRA_FW_EXTENDED_ERROR_INFO[5],
        reg_model.soc_ifc_reg_rm.CPTRA_FW_EXTENDED_ERROR_INFO[6],
        reg_model.soc_ifc_reg_rm.CPTRA_FW_EXTENDED_ERROR_INFO[7],
        reg_model.soc_ifc_reg_rm.CPTRA_TIMER_CONFIG,
        reg_model.soc_ifc_reg_rm.CPTRA_DBG_MANUF_SERVICE_REG,
        reg_model.soc_ifc_reg_rm.CPTRA_WDT_CFG[0],
        reg_model.soc_ifc_reg_rm.CPTRA_WDT_CFG[1],
        reg_model.soc_ifc_reg_rm.CPTRA_RSVD_REG[0],
        reg_model.soc_ifc_reg_rm.CPTRA_RSVD_REG[1]
    };
    
    foreach(reg_list[idx]) begin

        `uvm_create(trans);

        trans.kind = AAXI_WRITE;
        trans.vers = AAXI4;
        trans.addr = reg_list[idx].get_address(reg_model.soc_ifc_AXI_map);
        trans.id = $urandom();
        trans.awuser = $urandom();
        trans.len = 0;
        trans.size = 2;
        trans.burst = AAXI_BURST_FIXED;
        for (int j = 0; j < 4; j++) begin
            trans.data.push_back($urandom());
        end
        
        trans.aw_valid_delay = $urandom_range(aaxi_ci.minwaits, aaxi_ci.maxwaits);
        trans.adw_valid_delay = $urandom_range(aaxi_ci.minwaits, aaxi_ci.maxwaits);
        trans.b_ready_delay = $urandom_range(aaxi_ci.minwaits, aaxi_ci.maxwaits);
        trans.b_valid_ready_delay = $urandom_range(aaxi_ci.minwaits, aaxi_ci.maxwaits);
        trans.resp_valid_ready_delay = $urandom_range(aaxi_ci.minwaits, aaxi_ci.maxwaits);
     
        `uvm_send(trans);
    end
    
    foreach(reg_list[idx]) begin
        get_response(rsp);
    end
endtask


task soc_ifc_env_axi_uvm_gen_b2b_rand_sequence::read_write_reg(int id);
    aaxi_master_tr trans;
    uvm_reg regs[$];
    uvm_reg blocklist[], reg_list[];
    int del_idx[$];
    automatic bit is_write;

    reg_list = '{
        reg_model.soc_ifc_reg_rm.CPTRA_HW_ERROR_ENC,
        reg_model.soc_ifc_reg_rm.CPTRA_FW_ERROR_ENC,
        reg_model.soc_ifc_reg_rm.CPTRA_FW_EXTENDED_ERROR_INFO[0],
        reg_model.soc_ifc_reg_rm.CPTRA_FW_EXTENDED_ERROR_INFO[1],
        reg_model.soc_ifc_reg_rm.CPTRA_FW_EXTENDED_ERROR_INFO[2],
        reg_model.soc_ifc_reg_rm.CPTRA_FW_EXTENDED_ERROR_INFO[3],
        reg_model.soc_ifc_reg_rm.CPTRA_FW_EXTENDED_ERROR_INFO[4],
        reg_model.soc_ifc_reg_rm.CPTRA_FW_EXTENDED_ERROR_INFO[5],
        reg_model.soc_ifc_reg_rm.CPTRA_FW_EXTENDED_ERROR_INFO[6],
        reg_model.soc_ifc_reg_rm.CPTRA_FW_EXTENDED_ERROR_INFO[7],
        reg_model.soc_ifc_reg_rm.CPTRA_TIMER_CONFIG,
        reg_model.soc_ifc_reg_rm.CPTRA_DBG_MANUF_SERVICE_REG,
        reg_model.soc_ifc_reg_rm.CPTRA_WDT_CFG[0],
        reg_model.soc_ifc_reg_rm.CPTRA_WDT_CFG[1],
        reg_model.soc_ifc_reg_rm.CPTRA_RSVD_REG[0],
        reg_model.soc_ifc_reg_rm.CPTRA_RSVD_REG[1]
    };

    is_write = 1;
    
    foreach(reg_list[idx]) begin

        `uvm_create(trans);

        trans.kind = is_write ? AAXI_WRITE : AAXI_READ;
        trans.vers = AAXI4;
        trans.addr = reg_list[idx].get_address(reg_model.soc_ifc_AXI_map);
        trans.id = $urandom();
        trans.len = 0;
        trans.size = 2;
        trans.burst = AAXI_BURST_FIXED;

        if (is_write) begin
            for (int j = 0; j < 4; j++) begin
                trans.data.push_back($urandom());
                trans.strobes[j] = 1;
            end
            trans.awuser = $urandom();
        end
        else trans.aruser = $urandom(); 

        trans.ar_valid_delay = $urandom_range(aaxi_ci.minwaits, aaxi_ci.maxwaits);
        trans.aw_valid_delay = $urandom_range(aaxi_ci.minwaits, aaxi_ci.maxwaits);
        trans.adw_valid_delay = $urandom_range(aaxi_ci.minwaits, aaxi_ci.maxwaits);
        trans.b_ready_delay = $urandom_range(aaxi_ci.minwaits, aaxi_ci.maxwaits);
        trans.b_valid_ready_delay = $urandom_range(aaxi_ci.minwaits, aaxi_ci.maxwaits);
        trans.resp_valid_ready_delay = $urandom_range(aaxi_ci.minwaits, aaxi_ci.maxwaits);
        
        `uvm_send(trans);

        is_write = ~is_write;
    end

    foreach(reg_list[idx]) begin
        get_response(rsp);
    end
endtask