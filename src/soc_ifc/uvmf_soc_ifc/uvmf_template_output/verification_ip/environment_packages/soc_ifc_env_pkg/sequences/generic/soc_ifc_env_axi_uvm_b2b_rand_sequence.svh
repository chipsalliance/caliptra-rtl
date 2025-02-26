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
class soc_ifc_env_axi_uvm_b2b_rand_sequence extends aaxi_uvm_seq_base; //soc_ifc_env_sequence_base #(.CONFIG_T(soc_ifc_env_configuration_t));


    `uvm_object_utils( soc_ifc_env_axi_uvm_b2b_rand_sequence )
  
    uvm_status_e reg_sts;

    extern virtual task read_reg();
    extern virtual task write_reg(int id);

    function new(string name = "");
        super.new(name);
        // uvm_config_db #(aaxi_uvm_sequencer)::get(uvm_root::get(),"*", "aaxi_uvm_sequencer", aaxi_uvm_sequencer);
    endfunction

    virtual task pre_body();
        super.pre_body();
        // if (configuration == null)
        //     `uvm_info("KNU_CONFIG", "config is null inside b2b rand seq", UVM_MEDIUM)
        // reg_model = configuration.soc_ifc_rm;
    endtask

    virtual task body();
        // aaxi_master_tr txn;

        // txn = aaxi_master_tr::type_id::create("txn");
        // start_item(txn);
        // txn.randomize();
        // //fuse wr done force
        // `uvm_info("KNU", "Setting fuse wr done", UVM_MEDIUM)
        // txn.kind = AAXI_WRITE;
        // txn.vers = AAXI4;
        // txn.addr = 'h300b0;
        // txn.id = 0;
        // txn.len = 0;
        // txn.size = 2;
        // txn.burst = 0;
        // txn.data.push_back('h01);
        // txn.data.push_back('h00);
        // txn.data.push_back('h00);
        // txn.data.push_back('h00);

        
        // finish_item(txn);

        // fork
        //     begin
        //         `uvm_info("KNU_B2B_RAND", "Starting write task 1", UVM_MEDIUM)
        //         write_reg(0); //declare local auto var to assign rand id TODO
        //     end
        //     begin
        //         `uvm_info("KNU_B2B_RAND", "Starting write task 2", UVM_MEDIUM)
        //         write_reg(1); //read_reg();
        //     end
            
        //     //write_reg(1);
        // join
        // wait(1000);

        write_reg(0);
    endtask
  
endclass

task soc_ifc_env_axi_uvm_b2b_rand_sequence::read_reg();
endtask
/*
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
*/
task soc_ifc_env_axi_uvm_b2b_rand_sequence::write_reg(int id);
endtask
/*
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
*/
