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
    extern virtual task outstanding_write_reg();

    function new(string name = "");
        super.new(name);
    endfunction

    virtual task pre_body();
        super.pre_body();
        // reg_model = configuration.soc_ifc_rm;
    endtask


endclass

task soc_ifc_env_gen_rand_rw_sequence::read_reg();
    aaxi_master_tr trans, rsp;
    uvm_reg regs[$];
    uvm_reg blocklist[], compare_list[];
    int del_idx[$];
    automatic bit found;

    automatic int i;

    reg_model.soc_ifc_reg_rm.soc_ifc_reg_AXI_map.get_registers(regs, UVM_HIER);

    //TODO: predictor needs update for these regs - remove after merging with main
    blocklist = '{reg_model.soc_ifc_reg_rm.CPTRA_HW_CAPABILITIES,
                  reg_model.soc_ifc_reg_rm.CPTRA_FW_CAPABILITIES,
                  reg_model.soc_ifc_reg_rm.CPTRA_CAP_LOCK};

    compare_list = '{reg_model.soc_ifc_reg_rm.CPTRA_FW_ERROR_FATAL,
                     reg_model.soc_ifc_reg_rm.CPTRA_FW_ERROR_NON_FATAL,
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
                     reg_model.soc_ifc_reg_rm.CPTRA_TRNG_DATA[0],
                     reg_model.soc_ifc_reg_rm.CPTRA_TRNG_DATA[1],
                     reg_model.soc_ifc_reg_rm.CPTRA_TRNG_DATA[2],
                     reg_model.soc_ifc_reg_rm.CPTRA_TRNG_DATA[3],
                     reg_model.soc_ifc_reg_rm.CPTRA_TRNG_DATA[4],
                     reg_model.soc_ifc_reg_rm.CPTRA_TRNG_DATA[5],
                     reg_model.soc_ifc_reg_rm.CPTRA_TRNG_DATA[6],
                     reg_model.soc_ifc_reg_rm.CPTRA_TRNG_DATA[7],
                     reg_model.soc_ifc_reg_rm.CPTRA_TRNG_DATA[8],
                     reg_model.soc_ifc_reg_rm.CPTRA_TRNG_DATA[9],
                     reg_model.soc_ifc_reg_rm.CPTRA_TRNG_DATA[10],
                     reg_model.soc_ifc_reg_rm.CPTRA_TRNG_DATA[11],
                     reg_model.soc_ifc_reg_rm.CPTRA_TIMER_CONFIG,
                     reg_model.soc_ifc_reg_rm.CPTRA_BOOTFSM_GO,
                     reg_model.soc_ifc_reg_rm.CPTRA_DBG_MANUF_SERVICE_REG,
                     reg_model.soc_ifc_reg_rm.CPTRA_CLK_GATING_EN,
                     reg_model.soc_ifc_reg_rm.CPTRA_WDT_CFG[0],
                     reg_model.soc_ifc_reg_rm.CPTRA_WDT_CFG[1],
                     reg_model.soc_ifc_reg_rm.CPTRA_iTRNG_ENTROPY_CONFIG_0,
                     reg_model.soc_ifc_reg_rm.CPTRA_iTRNG_ENTROPY_CONFIG_1,
                     reg_model.soc_ifc_reg_rm.CPTRA_RSVD_REG[0],
                     reg_model.soc_ifc_reg_rm.CPTRA_RSVD_REG[1]
};

    foreach(blocklist[idx]) begin
      del_idx = regs.find_first_index(found_reg) with (found_reg == blocklist[idx]);
      `uvm_info("KNU_GEN_RW", "Found a blocklist reg, deleting", UVM_MEDIUM)
      regs.delete(del_idx.pop_front());
    end

    // automatic index;

    foreach(regs[idx]) begin
        
        // index = idx;
        found = 0;

        trans = aaxi_master_tr::type_id::create("trans");
        start_item(trans);
        trans.randomize();

        trans.kind = AAXI_READ;
        trans.vers = AAXI4;
        trans.addr = regs[idx].get_address(reg_model.soc_ifc_AXI_map);
        trans.id = 0;
        trans.len = 0; //$urandom_range(0,1); //0;
        trans.size = $urandom_range(0,2); 
        trans.burst = $urandom_range(0,1);
        trans.ar_valid_delay = $urandom_range(aaxi_ci.minwaits,aaxi_ci.maxwaits-1); //0; //$urandom_range(configuration.aaxi_ci.minwaits, configuration.aaxi_ci.maxwaits-1);
        trans.resp_valid_ready_delay = $urandom_range(aaxi_ci.minwaits,aaxi_ci.maxwaits-1); //$urandom_range(configuration.aaxi_ci.minwaits, configuration.aaxi_ci.maxwaits-1);
        
        `uvm_info("KNU_GEN_RW", "Starting AAXI read txn", UVM_MEDIUM)
        
        finish_item(trans);
        get_response(rsp);

        foreach(compare_list[j]) begin
            if ((compare_list[j] == regs[idx])) begin
                found = 1;
                break;
            end
        end

        if (found) begin
            case(trans.size)
                0: begin
                    act_read_data = {'h00,'h00,'h00,rsp.data[0]};
                    exp_write_data = {'h00,'h00,'h00,reg_write_data[idx][7:0]};
                end
                1: begin
                    act_read_data = {'h00,'h00,rsp.data[1],rsp.data[0]};
                    exp_write_data = {'h00,'h00,reg_write_data[idx][15:0]};
                end
                2: begin
                    act_read_data = {rsp.data[3],rsp.data[2],rsp.data[1],rsp.data[0]};
                    exp_write_data = reg_write_data[idx];
                end
                default: begin
                    act_read_data = {rsp.data[3],rsp.data[2],rsp.data[1],rsp.data[0]};
                    exp_write_data = reg_write_data[idx];
                end
            endcase
            if (act_read_data == exp_write_data)
                `uvm_info("KNU_GEN_RW", "Read data matches write data", UVM_MEDIUM)
            else
                `uvm_error("KNU_GEN_RW", $sformatf("Read data %h does not match write data %h", act_read_data, exp_write_data))
        end
    end
endtask

task soc_ifc_env_gen_rand_rw_sequence::write_reg();
    aaxi_master_tr trans, rsp;
    uvm_reg regs[$];
    uvm_reg blocklist[];
    int del_idx[$];

    reg [7:0] random_byte;
    reg[3:0][7:0] random_dword;

    automatic int i;
    automatic bit strb;

    reg_model.soc_ifc_reg_rm.soc_ifc_reg_AXI_map.get_registers(regs, UVM_HIER);

    //TODO: predictor needs update for these regs - remove after merging with main
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
        start_item(trans);
        trans.randomize();

        trans.kind = AAXI_WRITE;
        trans.vers = AAXI4;
        trans.addr = regs[idx].get_address(reg_model.soc_ifc_AXI_map);
        trans.id = 0;
        trans.len = 0; //$urandom_range(0,1); //scbd drain error TODO
        trans.size = $urandom_range(0,2); 
        trans.burst = $urandom_range(0,1); //0; //burst type of wrap requires non-zero len TODO
        for (int i = 0; i < 4; i++) begin
            random_byte = $urandom();
            if ((i==0) & (regs[idx] == reg_model.soc_ifc_reg_rm.internal_hw_error_fatal_mask)) begin
                random_byte[3] = 0;
                `uvm_info("KNU_ERR", $sformatf("Random byte = %h", random_byte), UVM_MEDIUM)
            end
            trans.data.push_back(random_byte);
            strb = $urandom_range(0,1);
            if (strb == 1)
                random_dword[i] = random_byte;
            else
                random_dword[i] = 8'h00;
            trans.strobes.push_back(strb);
            `uvm_info("KNU_STRB", $sformatf("strb = %0d for index i = %0d --> random dword at index = %h", strb, i, random_dword[i]), UVM_MEDIUM)
        end

        trans.adw_valid_delay = $urandom_range(aaxi_ci.minwaits,aaxi_ci.maxwaits-1); //$urandom_range(configuration.aaxi_ci.minwaits, configuration.aaxi_ci.maxwaits-1);
        trans.aw_valid_delay = $urandom_range(aaxi_ci.minwaits,aaxi_ci.maxwaits-1); //$urandom_range(configuration.aaxi_ci.minwaits, configuration.aaxi_ci.maxwaits-1);
        trans.b_valid_ready_delay = $urandom_range(aaxi_ci.minwaits,aaxi_ci.maxwaits-1); //$urandom_range(configuration.aaxi_ci.minwaits, configuration.aaxi_ci.maxwaits-1);

        `uvm_info("KNU_ERR", $sformatf("Random dword = %h %h %h %h", random_dword[3], random_dword[2], random_dword[1], random_dword[0]), UVM_MEDIUM)
        // reg_write_data[idx] = random_dword[3:0];
        case(trans.size)
            0: begin
                reg_write_data[idx] = {'h00,'h00,'h00,random_dword[0]};
            end
            1: begin
                reg_write_data[idx] = {'h00,'h00,random_dword[1:0]};
            end
            2: begin
                reg_write_data[idx] = random_dword[3:0];
            end
            default: begin
                reg_write_data[idx] = random_dword[3:0];
            end
        endcase
        `uvm_info("KNU_GEN_RW", "Starting AAXI write txn", UVM_MEDIUM)

        finish_item(trans);
        get_response(rsp);
    end
endtask

task soc_ifc_env_gen_rand_rw_sequence::outstanding_write_reg();
    aaxi_master_tr trans;
    reg [7:0] random_byte;

    aaxi_ci.uvm_resp = 0;

    for (int k = 0; k < 4; k++) begin
    trans = aaxi_master_tr::type_id::create("trans");
    start_item(trans);
    trans.randomize();

    trans.uvm_tr_ctrl = AAXI_TRCTRL_ADDR_AND_DATA;

    trans.kind = AAXI_WRITE;
    trans.vers = AAXI4;
    trans.addr = 'h30000;
    trans.id = 0;
    trans.len = 0; //$urandom_range(0,1); //scbd drain error TODO
    trans.size = $urandom_range(0,2); 
    trans.burst = $urandom_range(0,1); //0; //burst type of wrap requires non-zero len TODO
    for (int i = 0; i < 4; i++) begin
        random_byte = $urandom();
        // if ((i==0) & (regs[idx] == reg_model.soc_ifc_reg_rm.internal_hw_error_fatal_mask)) begin
        //     random_byte[3] = 0;
        //     `uvm_info("KNU_ERR", $sformatf("Random byte = %h", random_byte), UVM_MEDIUM)
        // end
        trans.data.push_back(random_byte);
        trans.strobes[i] = $urandom_range(0,1);
        // if (trans.strobes[i])
        //     random_dword[i] = random_byte;
        // else
        //     random_dword[i] = 8'h00;
    end

    // trans.adw_valid_delay = $urandom_range(aaxi_ci.minwaits,aaxi_ci.maxwaits-1); //$urandom_range(configuration.aaxi_ci.minwaits, configuration.aaxi_ci.maxwaits-1);
    // trans.aw_valid_delay = $urandom_range(aaxi_ci.minwaits,aaxi_ci.maxwaits-1); //$urandom_range(configuration.aaxi_ci.minwaits, configuration.aaxi_ci.maxwaits-1);
    trans.b_valid_ready_delay = 100; //$urandom_range(aaxi_ci.minwaits,aaxi_ci.maxwaits-1); //$urandom_range(configuration.aaxi_ci.minwaits, configuration.aaxi_ci.maxwaits-1);

    finish_item(trans);
    #10;
    end

endtask
/*
task soc_ifc_env_gen_rand_rw_sequence::read_reg();
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
        start_item(trans);
        trans.randomize();

        `uvm_info("KNU_GEN_RW", $sformatf("Building AAXI txn for reg addr %h", regs[idx].get_address(reg_model.soc_ifc_AXI_map)), UVM_MEDIUM)
        trans.kind = AAXI_READ;
        trans.vers = AAXI4;
        trans.addr = regs[idx].get_address(reg_model.soc_ifc_AXI_map);
        trans.id = 0;
        trans.len = 0;
        trans.size = 1; //$urandom_range(0,7);
        trans.burst = 0; //$urandom_range(0,1);
        trans.ar_valid_delay = $urandom_range(configuration.aaxi_ci.minwaits, configuration.aaxi_ci.maxwaits-1);
        trans.resp_valid_ready_delay = $urandom_range(configuration.aaxi_ci.minwaits, configuration.aaxi_ci.maxwaits-1);
        
        `uvm_info("KNU_GEN_RW", "Starting AAXI read txn", UVM_MEDIUM)
        
        finish_item(trans);
        // wait(10); //look soc ifc ctrl config (wait for cycles)
    end

endtask

task soc_ifc_env_gen_rand_rw_sequence::write_reg();
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
        start_item(trans);
        trans.randomize();
        
        `uvm_info("KNU_GEN_RW", $sformatf("Building write AAXI txn for reg addr %h", regs[idx].get_address(reg_model.soc_ifc_AXI_map)), UVM_MEDIUM)
        trans.kind = AAXI_WRITE;
        trans.vers = AAXI4;
        trans.addr = regs[idx].get_address(reg_model.soc_ifc_AXI_map);
        trans.id = 0;
        trans.len = 0;
        trans.size = 2;
        trans.burst = 0;
        for (int i = 0; i < 4; i++) begin
            trans.data.push_back($urandom());
            trans.strobes[i] = $urandom_range(0,1);
        end
        trans.adw_valid_delay = $urandom_range(configuration.aaxi_ci.minwaits, configuration.aaxi_ci.maxwaits-1);
        trans.aw_valid_delay = $urandom_range(configuration.aaxi_ci.minwaits, configuration.aaxi_ci.maxwaits-1);
        trans.b_valid_ready_delay = $urandom_range(configuration.aaxi_ci.minwaits, configuration.aaxi_ci.maxwaits-1);
        
        `uvm_info("KNU_GEN_RW", "Starting AAXI write txn", UVM_MEDIUM)
        
        finish_item(trans);
        // wait(10);
    end
endtask
    */