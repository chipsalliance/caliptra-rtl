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
//----------------------------------------------------------
// Custom reg predictor for pcrvault
//----------------------------------------------------------
import pv_reg_adapter_functions_pkg::*;
class pv_reg_predictor#(type BUSTYPE=int) extends uvm_reg_predictor #(.BUSTYPE(BUSTYPE));

    `uvm_component_param_utils(pv_reg_predictor#(BUSTYPE))

    //bus_in_local = input bus transaction of type "BUSTYPE"
    //This predictor will look for corresponding register or memory for the input address
    //If found, it calls predict() method with bus data as input
    //The register mirror is updated (based on configured access RW, RO, etc)
    //Predictor also converts bus txn to uvm_reg_item and sends on reg_ap port

    uvm_analysis_imp #(BUSTYPE, pv_reg_predictor#(BUSTYPE)) bus_in_local;

    uvm_analysis_port #(uvm_reg_item) reg_ap_local;

    uvm_reg_map map;

    uvm_reg_adapter adapter;

    //Create new instance of this type
    function new (string name, uvm_component parent);
        super.new(name, parent);
        bus_in_local = new("bus_in_local", this);
        reg_ap_local = new("reg_ap_local", this);
    endfunction

    //Function write
    virtual function void write(BUSTYPE tr);

        uvm_reg pv_reg;
        uvm_reg_data_t pv_reg_data;
        uvm_reg_item pv_reg_item;
        uvm_reg_map_info pv_reg_info;
        uvm_reg_field pv_reg_data_field;

        uvm_reg pv_reg_ctrl;
        uvm_reg_data_t pv_reg_ctrl_data;
        uvm_reg_item pv_reg_ctrl_item;
        
        uvm_reg_bus_op rw;
        uvm_reg_bus_op rw_ctrl;
        reg [63:0] addr;
        reg [8:0] entry_offset;

        uvm_reg val_reg;
        uvm_reg_data_t val_reg_data;
        uvm_reg_item val_reg_item;

        logic lock;
        logic clear;

        //Pass variables to parent
        super.reg_ap = reg_ap_local;
        super.map = map;
        super.adapter = adapter;
        
        //Convert bus txn to reg model txn
        adapter.bus2reg(tr,rw);

        //-----------------------------------------------
        //rw contains PCR entry info. Below steps are to
        //derive corresponding CTRL reg info
        //-----------------------------------------------
        if (rw.kind == UVM_WRITE) begin
            //Read val_reg - TODO: needed?
            val_reg = map.get_reg_by_offset('h1_0000);
            val_reg_data = val_reg.get();

            //TODO: how can writes be delayed by a clock to mimic design?
            //PCR regs are always written, no locks or clear_secrets to block writes
            
            //If write is to a CTRL reg, only set clear if lock = 0
            `uvm_info("PV_REG_OUT", $sformatf("addr = %h, new data = %h", rw.addr, rw.data),UVM_MEDIUM);
            if ((rw.addr >= `PV_REG_PCR_CTRL_0) && (rw.addr < `PV_REG_PCR_ENTRY_0_0)) begin
                //Read existing content of CTRL reg and see if lock has been set previously
                pv_reg = map.get_reg_by_offset(rw.addr);
                pv_reg_data = pv_reg.get_mirrored_value();
                lock = pv_reg_data[0];
                `uvm_info("PV_REG", $sformatf("addr = %h, new data = %h, old data = %h, lock = %h", rw.addr, rw.data, pv_reg_data, lock),UVM_MEDIUM);
                if(!lock) begin
                    super.write(tr);
                    $display("Done writing to CTRL reg!");
                end
            end

            //--------------------------------
            //PCR regs are configured as RO in the reg block provided by RDL. This is in line with AHB accesses
            //However, to be able to write via SHA512 interface, the access policy needs to be RW. The following
            //is a workaround to write to regs. Reconfiguring the regs with a different access policy gives errors
            //since the same address is being used in AHB and SHA512 maps.
            //--------------------------------
            //Steps to write to PCR regs:
            //1. Get uvm_reg by offset (rw.addr)
            //2. Get data field of the reg
            //3. Get access policy of the data field and name of the map being used
            //4. If map != AHB and access == RO, change access to RW temporarily
            //5. super.write to reg
            //6. Change access policy back to RO
            else begin //ENTRY reg access
                //Get rights of reg being accessed
                pv_reg = map.get_reg_by_offset(rw.addr);
                pv_reg_data_field = pv_reg.get_field_by_name("data");
                //$display("Rights = %s, Info rights = %s", pv_reg.get_rights(), pv_reg_info.rights);
                //$display("Rights = %s, Info rights = %s, map = %s", pv_reg.get_rights(), pv_reg_data_field.get_access(map), map.get_full_name());
                if (map.get_name != "pv_AHB_map") begin
                    if(pv_reg_data_field.get_access(map) == "RO") begin
                        pv_reg_data_field.set_access("RW");
                        super.write(tr);
                        pv_reg_data_field.set_access("RO");
                    end
                end
                else begin
                    super.write(tr);
                end
            end
            //-----------------------------------------------
            //Predict val reg data so it gets updated in reg model
            //-----------------------------------------------
            // val_reg_item = new;
            // val_reg_item.element_kind = UVM_REG;
            // val_reg_item.element = val_reg;
            // val_reg_item.path = UVM_PREDICT;
            // val_reg_item.map = map;
            // val_reg_item.kind = UVM_WRITE;
            // val_reg_item.value[0] |= 1'b0; //Clear bit is single pulse, so make it 0.

            // val_reg.do_predict(val_reg_item, UVM_PREDICT_DIRECT);
            
        end
        else begin //UVM_READ
            super.write(tr);
        end

    endfunction

    
endclass
