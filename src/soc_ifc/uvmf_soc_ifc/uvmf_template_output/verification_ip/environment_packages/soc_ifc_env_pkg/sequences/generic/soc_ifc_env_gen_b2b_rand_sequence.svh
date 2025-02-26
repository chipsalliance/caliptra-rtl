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
class soc_ifc_env_gen_b2b_rand_sequence extends soc_ifc_env_b2b_rand_sequence;
    `uvm_object_utils( soc_ifc_env_gen_b2b_rand_sequence )


    extern virtual task read_reg();
    extern virtual task write_reg();

    function new(string name = "");
        super.new(name);
    endfunction

    virtual task pre_body();
        super.pre_body();
        reg_model = configuration.soc_ifc_rm;
    endtask


endclass

task soc_ifc_env_gen_b2b_rand_sequence::read_reg();
    aaxi_master_tr trans;
    uvm_reg regs[$];
    uvm_reg blocklist[];
    int del_idx[$];

    byte unsigned ii;
    int reg_select;
    uvm_reg_data_t rand_data;
    uvm_status_e rand_sts;


    reg_model.soc_ifc_reg_rm.soc_ifc_reg_AXI_map.get_registers(regs, UVM_HIER);
    foreach(regs[idx]) begin
        `uvm_info("KNU_GEN_RW", $sformatf("reg name = %s", regs[idx].get_name), UVM_MEDIUM)
    end

    //TODO: predictor needs update for these regs
    blocklist = '{reg_model.soc_ifc_reg_rm.CPTRA_HW_CAPABILITIES,
                  reg_model.soc_ifc_reg_rm.CPTRA_FW_CAPABILITIES,
                  reg_model.soc_ifc_reg_rm.CPTRA_CAP_LOCK};

    foreach(blocklist[idx]) begin
        del_idx = regs.find_first_index(found_reg) with (found_reg == blocklist[idx]);
        `uvm_info("KNU_GEN_RW", "Found a blocklist reg, deleting", UVM_MEDIUM)
        regs.delete(del_idx.pop_front());
    end

    foreach(regs[idx]) begin
        trans = aaxi_master_tr::type_id::create("trans");

        `uvm_info("KNU_GEN_RW", $sformatf("Building AAXI txn for reg addr %h", regs[idx].get_address(reg_model.soc_ifc_AXI_map)), UVM_MEDIUM)
        trans.kind = AAXI_READ;
        trans.vers = AAXI4;
        trans.addr = regs[idx].get_address(reg_model.soc_ifc_AXI_map);
        trans.id = 0;
        trans.len = 0;
        trans.size = 2; //$urandom_range(0,7);
        trans.burst = $urandom_range(0,1);
        trans.ar_valid_delay = $urandom_range(configuration.aaxi_ci.minwaits, configuration.aaxi_ci.maxwaits);
        trans.resp_valid_ready_delay = $urandom_range(configuration.aaxi_ci.minwaits, configuration.aaxi_ci.maxwaits);
        
        `uvm_info("KNU_GEN_RW", "Starting AAXI read txn", UVM_MEDIUM)
        start_item(trans);
        finish_item(trans);
        wait(10);
    end

endtask

task soc_ifc_env_gen_b2b_rand_sequence::write_reg();
    aaxi_master_tr trans;
    uvm_reg regs[$];
    uvm_reg blocklist[];
    int del_idx[$];

    byte unsigned ii;
    int reg_select;
    uvm_reg_data_t rand_data;
    uvm_status_e rand_sts;

    reg_model.soc_ifc_reg_rm.soc_ifc_reg_AXI_map.get_registers(regs, UVM_HIER);
    // foreach(regs[idx]) begin
    //     `uvm_info("KNU_GEN_RW", $sformatf("reg name = %s", regs[idx].get_name), UVM_MEDIUM)
    // end

    //TODO: predictor needs update for these regs
    blocklist = '{reg_model.soc_ifc_reg_rm.CPTRA_HW_CAPABILITIES,
                  reg_model.soc_ifc_reg_rm.CPTRA_FW_CAPABILITIES,
                  reg_model.soc_ifc_reg_rm.CPTRA_CAP_LOCK};

    foreach(blocklist[idx]) begin
        del_idx = regs.find_first_index(found_reg) with (found_reg == blocklist[idx]);
        `uvm_info("KNU_GEN_RW", "Found a blocklist reg, deleting", UVM_MEDIUM)
        regs.delete(del_idx.pop_front());
    end

    foreach(regs[idx]) begin
        trans = aaxi_master_tr::type_id::create("trans");

        `uvm_info("KNU_GEN_RW", $sformatf("Building write AAXI txn for reg addr %h", regs[idx].get_address(reg_model.soc_ifc_AXI_map)), UVM_MEDIUM)
        trans.kind = AAXI_WRITE;
        trans.vers = AAXI4;
        trans.addr = regs[idx].get_address(reg_model.soc_ifc_AXI_map);
        trans.id = 0;
        trans.len = 0;
        trans.size = 2;
        trans.burst = 0;
        for (int i = 0; i < 4; i++)
            trans.data[i] = $urandom();
        trans.aw_valid_delay = $urandom_range(configuration.aaxi_ci.minwaits, configuration.aaxi_ci.maxwaits);
        trans.b_valid_ready_delay = $urandom_range(configuration.aaxi_ci.minwaits, configuration.aaxi_ci.maxwaits);
        
        `uvm_info("KNU_GEN_RW", "Starting AAXI write txn", UVM_MEDIUM)
        start_item(trans);
        finish_item(trans);
        wait(10);
    end
endtask