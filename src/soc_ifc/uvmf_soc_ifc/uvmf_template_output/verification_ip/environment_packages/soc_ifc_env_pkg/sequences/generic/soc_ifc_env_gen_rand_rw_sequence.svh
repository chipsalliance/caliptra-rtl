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
    uvm_reg regs[$];
    uvm_reg blocklist[], compare_list[];
    int del_idx[$];
    automatic bit found;

    automatic int i;

    reg_model.soc_ifc_reg_rm.soc_ifc_reg_AXI_map.get_registers(regs, UVM_HIER);

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
                    //  reg_model.soc_ifc_reg_rm.CPTRA_TRNG_DATA[0], //skip checking because this requires valid axi user
                    //  reg_model.soc_ifc_reg_rm.CPTRA_TRNG_DATA[1],
                    //  reg_model.soc_ifc_reg_rm.CPTRA_TRNG_DATA[2],
                    //  reg_model.soc_ifc_reg_rm.CPTRA_TRNG_DATA[3],
                    //  reg_model.soc_ifc_reg_rm.CPTRA_TRNG_DATA[4],
                    //  reg_model.soc_ifc_reg_rm.CPTRA_TRNG_DATA[5],
                    //  reg_model.soc_ifc_reg_rm.CPTRA_TRNG_DATA[6],
                    //  reg_model.soc_ifc_reg_rm.CPTRA_TRNG_DATA[7],
                    //  reg_model.soc_ifc_reg_rm.CPTRA_TRNG_DATA[8],
                    //  reg_model.soc_ifc_reg_rm.CPTRA_TRNG_DATA[9],
                    //  reg_model.soc_ifc_reg_rm.CPTRA_TRNG_DATA[10],
                    //  reg_model.soc_ifc_reg_rm.CPTRA_TRNG_DATA[11],
                     reg_model.soc_ifc_reg_rm.CPTRA_TIMER_CONFIG,
                    //  reg_model.soc_ifc_reg_rm.CPTRA_BOOTFSM_GO,
                     reg_model.soc_ifc_reg_rm.CPTRA_DBG_MANUF_SERVICE_REG,
                    //  reg_model.soc_ifc_reg_rm.CPTRA_CLK_GATING_EN,
                     reg_model.soc_ifc_reg_rm.CPTRA_WDT_CFG[0],
                     reg_model.soc_ifc_reg_rm.CPTRA_WDT_CFG[1],
                    //  reg_model.soc_ifc_reg_rm.CPTRA_iTRNG_ENTROPY_CONFIG_0,
                    //  reg_model.soc_ifc_reg_rm.CPTRA_iTRNG_ENTROPY_CONFIG_1,
                     reg_model.soc_ifc_reg_rm.CPTRA_RSVD_REG[0],
                     reg_model.soc_ifc_reg_rm.CPTRA_RSVD_REG[1]
};


    foreach(regs[idx]) begin
        
        found = 0;

        trans = aaxi_master_tr::type_id::create("trans");
        start_item(trans);
        trans.randomize();

        trans.kind = AAXI_READ;
        trans.vers = AAXI4;
        trans.addr = regs[idx].get_address(reg_model.soc_ifc_AXI_map);
        trans.id = $urandom();
        trans.len = 0;
        trans.size = $urandom_range(0,2); 
        trans.burst = $urandom_range(0,1);
        trans.ar_valid_delay = $urandom_range(aaxi_ci.minwaits,aaxi_ci.maxwaits-1); 
        trans.resp_valid_ready_delay = $urandom_range(aaxi_ci.minwaits,aaxi_ci.maxwaits-1);
        
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
                    act_read_data = {24'h0,rsp.data[0]};
                    exp_write_data = {24'h0,reg_write_data[idx][7:0]};
                end
                1: begin
                    act_read_data = {16'h0,rsp.data[1],rsp.data[0]};
                    exp_write_data = {16'h0,reg_write_data[idx][15:0]};
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
                `uvm_info("SOC_IFC_GEN_RW_MATCH", "Read data matches write data", UVM_MEDIUM)
            else
                `uvm_error("SOC_IFC_GEN_RW_MISMATCH", $sformatf("Read data %h does not match write data %h", act_read_data, exp_write_data))
            `uvm_info("WRDATA_DBG", $sformatf("reg_write_data = %h, exp write data = %h", reg_write_data[idx], exp_write_data), UVM_MEDIUM)
        end
    end
endtask

task soc_ifc_env_gen_rand_rw_sequence::write_reg();
    aaxi_master_tr trans, rsp;
    uvm_reg regs[$];
    uvm_reg blocklist[];
    uvm_reg_data_t mirror_data;
    reg [31:0] mirror_data_mask;
    int del_idx[$];

    reg [7:0] random_byte;
    reg[3:0][7:0] random_dword, mirror_data_reg;

    automatic int i;
    automatic bit strb;
    automatic bit zero_strb;
    automatic bit [3:0] wstrb;

    reg_model.soc_ifc_reg_rm.soc_ifc_reg_AXI_map.get_registers(regs, UVM_HIER);
    
    foreach(regs[idx]) begin
        zero_strb = 1;
        mirror_data_mask = 32'h0000_00FF;
        mirror_data = regs[idx].get_mirrored_value();

        trans = aaxi_master_tr::type_id::create("trans");
        start_item(trans);
        trans.randomize();

        trans.kind = AAXI_WRITE;
        trans.vers = AAXI4;
        trans.addr = regs[idx].get_address(reg_model.soc_ifc_AXI_map);
        trans.id = 0;
        trans.len = 0;
        trans.size = $urandom_range(0,2);
        trans.burst = $urandom_range(0,1);
        trans.awuser = $urandom();

        //populate data and strobes
        for (int i=0; i<4; i++) begin
            random_byte = $urandom();
            if ((i==0) & (regs[idx] == reg_model.soc_ifc_reg_rm.internal_hw_error_fatal_mask)) begin
                random_byte[3] = 0;
            end
            trans.data[i] = random_byte;
            strb = $urandom_range(0,1);
            $display("************strb = %h", strb);
            trans.strobes[i] = strb;
            random_dword[i] = random_byte;
        end

        trans.adw_valid_delay = $urandom_range(aaxi_ci.minwaits,aaxi_ci.maxwaits-1);
        trans.aw_valid_delay = $urandom_range(aaxi_ci.minwaits,aaxi_ci.maxwaits-1);
        trans.b_valid_ready_delay = $urandom_range(aaxi_ci.minwaits,aaxi_ci.maxwaits-1);
        `uvm_info("KNU_RANDOM_DWORD", $sformatf("random_dword = %h", random_dword[3:0]), UVM_MEDIUM)
        for (int i =0; i < 4; i++)
            `uvm_info("KNU_RANDOM_DWORD", $sformatf("txn data = %h strb = %h", trans.data[i], trans.strobes[i]), UVM_MEDIUM)

        //Calculate wstrb based on strobes and size
        for (int i=0; i<4; i++) begin
            if (trans.strobes[i])
                wstrb[i] = 1;
            else
                wstrb[i] = 0;
        end
        case(trans.size)
            0: wstrb = {3'b000, wstrb[0]};
            1: wstrb = {2'b00, wstrb[1:0]};
            default: wstrb = wstrb[3:0];
        endcase

        $display("********wstrb = %4b", wstrb);

        //adjust data based on wstrb
        
        for (int i=0; i<4; i++) begin
            mirror_data_mask = 32'h0000_00FF;
            if (!wstrb[i]) begin
                mirror_data_mask = mirror_data_mask << ((i)*8);
                random_dword[i] = ((mirror_data & mirror_data_mask) >> ((i)*8));
            end
        end
        //Save write data for comparison during read
        reg_write_data[idx] = random_dword;
        
        `uvm_info("KNU_GEN_RW_WRITE", $sformatf("reg_write_data = %h", reg_write_data[idx]), UVM_MEDIUM)

        for (int i =0; i<4; i++) begin
            if (trans.strobes[i])//((trans.strobes[3] | trans.strobes[2] | trans.strobes[1] | trans.strobes[0]) == 0)
                zero_strb = 0;
                `uvm_info("FORLOOP", $sformatf("Inside for loop, zero_strb = %h", zero_strb), UVM_MEDIUM)
            end
            if (zero_strb) begin
                reg_write_data[idx] = regs[idx].get_mirrored_value();
                $display("*******inside zero strb block!, reg write data = %h", reg_write_data[idx]);
            end
            `uvm_info("KNU_GEN_RW_WRITE", $sformatf("reg_write_data = %h, mirror data = %h %h", reg_write_data[idx], mirror_data, regs[idx].get_mirrored_value()), UVM_MEDIUM)
    
            finish_item(trans);
            get_response(rsp);

    end
/*
    foreach(regs[idx]) begin
        zero_strb = 1;
        mirror_data_mask = 32'h0000_00FF;
        mirror_data = regs[idx].get_mirrored_value();
        `uvm_info("KNU_MIR_DATA", $sformatf("mirror data = %h", mirror_data), UVM_MEDIUM)

        // strb = $urandom_range(0,15);
        
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
        trans.awuser = $urandom();
        
        for (int i = 0; i < 4; i++) begin
            random_byte = $urandom();
            if ((i==0) & (regs[idx] == reg_model.soc_ifc_reg_rm.internal_hw_error_fatal_mask)) begin
                random_byte[3] = 0;
            end
            trans.data.push_back(random_byte);
            strb = $urandom_range(0,1);
            $display("************strb = %h", strb);
            if (strb == 1)
                random_dword[3-i] = random_byte;
            else begin
                mirror_data_mask = mirror_data_mask << ((3-i)*8);
                random_dword[3-i] = ((mirror_data & mirror_data_mask) >> ((3-i)*8)); //Grab mirrored value if strobe is 0
            end
            trans.strobes.push_back(strb);
            // `uvm_info("KNU_FORLOOP", $sformatf("i=%0d, random byte = %h, trans.data = %h, strb = %h, trans strobe = %h", i, random_byte, trans.data.pop_back(), strb, trans.strobes.pop_back()), UVM_MEDIUM)
        end

        trans.adw_valid_delay = $urandom_range(aaxi_ci.minwaits,aaxi_ci.maxwaits-1);
        trans.aw_valid_delay = $urandom_range(aaxi_ci.minwaits,aaxi_ci.maxwaits-1);
        trans.b_valid_ready_delay = $urandom_range(aaxi_ci.minwaits,aaxi_ci.maxwaits-1);
        `uvm_info("KNU_RANDOM_DWORD", $sformatf("random_dword = %h", random_dword[3:0]), UVM_MEDIUM)
        for (int i =0; i < 4; i++)
        `uvm_info("KNU_RANDOM_DWORD", $sformatf("txn data = %h", trans.data[i]), UVM_MEDIUM)
        case(trans.size)
            0: begin
                reg_write_data[idx] = {24'h0,random_dword[3]};
            end
            1: begin
                reg_write_data[idx] = {16'h0,random_dword[3:2]};
            end
            2: begin
                reg_write_data[idx] = {random_dword[0],random_dword[1],random_dword[2],random_dword[3]};
            end
            default: begin
                reg_write_data[idx] = {random_dword[0],random_dword[1],random_dword[2],random_dword[3]};
            end
        endcase
        `uvm_info("KNU_GEN_RW_WRITE", $sformatf("reg_write_data = %h", reg_write_data[idx]), UVM_MEDIUM)
        //If all strobes = 0, just get mirrored value of reg and save it instead of the randomized value
        for (int i =0; i<4; i++) begin
        //     `uvm_info("KNU_STRB", $sformatf("strobes = %h %h", trans.strobes.pop_front(), trans.strobes[i]), UVM_MEDIUM)
        // end
            if (trans.strobes.pop_front())//((trans.strobes[3] | trans.strobes[2] | trans.strobes[1] | trans.strobes[0]) == 0)
                zero_strb = 0;
            `uvm_info("FORLOOP", $sformatf("Inside for loop, zero_strb = %h", zero_strb), UVM_MEDIUM)
            
        end
        if (zero_strb) begin
            reg_write_data[idx] = regs[idx].get_mirrored_value();
            $display("*******inside zero strb block!, reg write data = %h", reg_write_data[idx]);
        end
        `uvm_info("KNU_GEN_RW_WRITE", $sformatf("reg_write_data = %h, mirror data = %h %h", reg_write_data[idx], mirror_data, regs[idx].get_mirrored_value()), UVM_MEDIUM)

        finish_item(trans);
        get_response(rsp);
    end
        */
endtask