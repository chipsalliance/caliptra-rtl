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
class soc_ifc_env_b2b_rand_sequence extends soc_ifc_env_sequence_base #(.CONFIG_T(soc_ifc_env_configuration_t));


    `uvm_object_utils( soc_ifc_env_b2b_rand_sequence )
  
    uvm_status_e reg_sts;

    extern virtual task read_reg();
    extern virtual task write_reg();

    function new(string name = "");
        super.new(name);
    endfunction

    virtual task pre_body();
        super.pre_body();
        if (configuration == null)
            `uvm_info("KNU_CONFIG", "config is null inside b2b rand seq", UVM_MEDIUM)
        reg_model = configuration.soc_ifc_rm;
    endtask

    virtual task body();
        fork
        // `uvm_info("KNU_GEN2", "wait 1000 cycles", UVM_MEDIUM)
        // wait(1000);
            begin
                `uvm_info("KNU_B2B_RAND", "Starting write task", UVM_MEDIUM)
                write_reg();
            end
            begin
                `uvm_info("KNU_B2B_RAND", "Starting read task", UVM_MEDIUM)
                read_reg();
                wait(1000);
            end
        join
        wait(1000);
    endtask
  
endclass

task soc_ifc_env_b2b_rand_sequence::read_reg();
    aaxi_master_tr trans, trans1;

    trans = aaxi_master_tr::type_id::create("trans"); //new();
    trans1 = aaxi_master_tr::type_id::create("trans1"); //new();

    trans.kind = AAXI_READ;
                    trans.vers = AAXI4;
                    trans.addr = reg_model.soc_ifc_reg_rm.CPTRA_HW_CONFIG.get_address(reg_model.soc_ifc_AXI_map); //'h300e0; //`CLP_SOC_IFC_REG_CPTRA_HW_CONFIG; //reg_model.soc_ifc_reg_rm.CPTRA_HW_CONFIG.get_address(reg_model.soc_ifc_AXI_map);
                    trans.id = 0;
                    trans.len = 0;
                    trans.size = 2;
                    trans.burst = 0;
                    trans.resp_valid_ready_delay = 10;

                    trans1.kind = AAXI_READ;
                    trans1.vers = AAXI4;
                    trans1.addr = 'h30128; //`CLP_SOC_IFC_REG_CPTRA_HW_CONFIG; //reg_model.soc_ifc_reg_rm.CPTRA_HW_CONFIG.get_address(reg_model.soc_ifc_AXI_map);
                    trans1.id = 0;
                    trans1.len = 0;
                    trans1.size = 2;
                    trans1.burst = 0;
                    trans1.resp_valid_ready_delay = 5;

                    start_item(trans);
                    finish_item(trans);

                    start_item(trans1);
                    finish_item(trans1);
endtask

task soc_ifc_env_b2b_rand_sequence::write_reg();
    aaxi_master_tr trans, trans1;

    trans = aaxi_master_tr::type_id::create("trans"); //new();
    trans1 = aaxi_master_tr::type_id::create("trans1"); //new();
    trans.kind = AAXI_WRITE;
                trans.vers = AAXI4;
                trans.addr = reg_model.soc_ifc_reg_rm.CPTRA_HW_CONFIG.get_address(reg_model.soc_ifc_AXI_map); //'h30110; //`CLP_SOC_IFC_REG_CPTRA_HW_CONFIG; //reg_model.soc_ifc_reg_rm.CPTRA_HW_CONFIG.get_address(reg_model.soc_ifc_AXI_map);
                trans.id = 0;
                trans.len = 0;
                trans.size = 2;
                trans.burst = 0;
                // trans.resp_valid_ready_delay = 10;
                // trans.wstrbQ[0] = 'h3; //TODO: not working
                trans.data[0] = 'hab;
                trans.data[1] = 'hcd;
                trans.data[2] = 'hef;
                trans.data[3] = 'h88;

                // `uvm_info("KNU_CLASS", "read reg2", UVM_MEDIUM)
                trans1.kind = AAXI_WRITE;
                trans1.vers = AAXI4;
                trans1.addr = 'h30120; //`CLP_SOC_IFC_REG_CPTRA_HW_CONFIG; //reg_model.soc_ifc_reg_rm.CPTRA_HW_CONFIG.get_address(reg_model.soc_ifc_AXI_map);
                trans1.id = 0;
                trans1.len = 0;
                trans1.size = 2;
                trans1.burst = 0;
                // trans1.resp_valid_ready_delay = 5;
                // trans1.wstrbQ[0] = 'h3; //TODO: not working
                trans1.data[0] = 'h11;
                trans1.data[1] = 'h22;
                trans1.data[2] = 'h33;
                trans1.data[3] = 'h44;

                // fork
                //     begin
                        // `uvm_info("KNU_CLASS", "write reg1", UVM_MEDIUM)
                start_item(trans);
                finish_item(trans);
                
                    // end
                    // begin
                        // `uvm_info("KNU_CLASS", "write reg2", UVM_MEDIUM)
                start_item(trans1);
                finish_item(trans1);
                
                //     end
                    
                // join
    // end
endtask

