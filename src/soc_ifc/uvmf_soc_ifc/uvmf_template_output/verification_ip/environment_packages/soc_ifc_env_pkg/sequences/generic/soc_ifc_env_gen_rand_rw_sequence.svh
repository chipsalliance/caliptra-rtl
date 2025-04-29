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
class soc_ifc_env_gen_rand_rw_sequence extends soc_ifc_env_generic_2_sequence_base;
    `uvm_object_utils( soc_ifc_env_gen_rand_rw_sequence )

    rand int num_regs;
    soc_ifc_reg_model_top reg_model;
    aaxi_cfg_info aaxi_ci;
    uvm_reg_data_t reg_write_data[$];
    uvm_reg_data_t act_read_data;
    uvm_reg_data_t exp_write_data;

    extern virtual task read_reg();
    extern virtual task write_reg();

    function new(string name = "");
        super.new(name);
    endfunction

    virtual task pre_body();
        super.pre_body();
    endtask


endclass

task soc_ifc_env_gen_rand_rw_sequence::read_reg();
    aaxi_master_tr trans, rsp;
    uvm_reg blocklist[], reg_list[];
    int del_idx[$];

    automatic int i;

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

        trans = aaxi_master_tr::type_id::create("trans");
        start_item(trans);
        trans.randomize();

        trans.kind = AAXI_READ;
        trans.vers = AAXI4;
        trans.addr = reg_list[idx].get_address(reg_model.soc_ifc_AXI_map);
        trans.id = $urandom();
        trans.len = 0;
        trans.size = $urandom_range(0,2); 
        trans.burst = $urandom_range(0,1);
        trans.ar_valid_delay = $urandom_range(aaxi_ci.minwaits,aaxi_ci.maxwaits-1); 
        trans.resp_valid_ready_delay = $urandom_range(aaxi_ci.minwaits,aaxi_ci.maxwaits-1);
        
        finish_item(trans);
        get_response(rsp);

        exp_write_data = reg_list[idx].get_mirrored_value();
        case(trans.size)
            0: begin
                act_read_data = {24'h0,rsp.data[0]};
                exp_write_data = {24'h0, exp_write_data[7:0]};
            end
            1: begin
                act_read_data = {16'h0,rsp.data[1],rsp.data[0]};
                exp_write_data = {16'h0, exp_write_data[15:0]};
            end
            2: begin
                act_read_data = {rsp.data[3],rsp.data[2],rsp.data[1],rsp.data[0]};
                exp_write_data = exp_write_data;
            end
            default: begin
                act_read_data = {rsp.data[3],rsp.data[2],rsp.data[1],rsp.data[0]};
                exp_write_data = exp_write_data;
            end
        endcase
        if (act_read_data == exp_write_data)
            `uvm_info("SOC_IFC_GEN_RW_MATCH", "Read data matches write data", UVM_MEDIUM)
        else
            `uvm_error("SOC_IFC_GEN_RW_MISMATCH", $sformatf("Read data %h does not match write data %h for addr %h", act_read_data, exp_write_data, reg_list[idx].get_address(reg_model.soc_ifc_AXI_map)))

    end
endtask

task soc_ifc_env_gen_rand_rw_sequence::write_reg();
    aaxi_master_tr trans, rsp;
    uvm_reg regs[$];
    uvm_reg blocklist[], reg_list[];
    int del_idx[$];

    reg [7:0] random_byte;

    automatic int i;
    automatic bit strb;
    automatic bit zero_strb;
    automatic bit [3:0] wstrb;

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

        trans = aaxi_master_tr::type_id::create("trans");
        start_item(trans);
        trans.randomize();

        trans.kind = AAXI_WRITE;
        trans.vers = AAXI4;
        trans.addr = reg_list[idx].get_address(reg_model.soc_ifc_AXI_map);
        trans.id = 0;
        trans.len = 0;
        trans.size = $urandom_range(0,2);
        trans.burst = $urandom_range(0,1);
        trans.awuser = $urandom();

        //populate data and strobes
        for (int i=0; i<(1 << trans.size); i++) begin
            random_byte = $urandom();
            trans.data[i] = random_byte;
            strb = $urandom_range(0,1);
            trans.strobes[i] = strb;
        end

        trans.adw_valid_delay = $urandom_range(aaxi_ci.minwaits,aaxi_ci.maxwaits-1);
        trans.aw_valid_delay = $urandom_range(aaxi_ci.minwaits,aaxi_ci.maxwaits-1);
        trans.b_valid_ready_delay = $urandom_range(aaxi_ci.minwaits,aaxi_ci.maxwaits-1);
    
        finish_item(trans);
        get_response(rsp);

    end

endtask