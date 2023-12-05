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
// Custom reg predictor for keyvault
//----------------------------------------------------------
import kv_reg_adapter_functions_pkg::*;
class kv_reg_predictor#(type BUSTYPE=int) extends uvm_reg_predictor #(.BUSTYPE(BUSTYPE));

    `uvm_component_param_utils(kv_reg_predictor#(BUSTYPE))

    //bus_in_local = input bus transaction of type "BUSTYPE"
    //This predictor will look for corresponding register or memory for the input address
    //If found, it calls predict() method with bus data as input
    //The register mirror is updated (based on configured access RW, RO, etc)
    //Predictor also converts bus txn to uvm_reg_item and sends on reg_ap port

    uvm_analysis_imp #(BUSTYPE, kv_reg_predictor#(BUSTYPE)) bus_in_local;

    uvm_analysis_port #(uvm_reg_item) reg_ap_local;

    uvm_reg_map map;

    uvm_reg_adapter adapter;

    extern function logic [(KV_NUM_READ + $clog2(KV_NUM_DWORDS))-1 :0] parse_wr_transaction(uvm_sequence_item bus_item);

    //Create new instance of this type
    function new (string name, uvm_component parent);
        super.new(name, parent);
        bus_in_local = new("bus_in_local", this);
        reg_ap_local = new("reg_ap_local", this);
    endfunction

    //Function write
    virtual function void write(BUSTYPE tr);

        uvm_reg kv_reg;
        uvm_reg_data_t kv_reg_data;

        uvm_reg kv_reg_ctrl;
        uvm_reg_data_t kv_reg_ctrl_data;
        uvm_reg_item kv_reg_ctrl_item;

        uvm_reg clear_secrets_reg;
        uvm_reg_data_t clear_secrets_data;
        uvm_reg_item clear_secrets_item;
        
        uvm_reg_bus_op rw;
        uvm_reg_bus_op rw_ctrl;
        reg [63:0] addr;
        reg [8:0] entry_offset;

        uvm_reg val_reg;
        uvm_reg_data_t val_reg_data;
        uvm_reg_item val_reg_item;

        uvm_reg val_ctrl, val_ctrl_derived;
        uvm_reg_data_t val_ctrl_data, val_ctrl_derived_data;
        uvm_reg_item val_ctrl_item;

        logic lock_wr;
        logic lock_use;
        logic clear;

        logic [KV_NUM_READ-1:0] write_dest_valid;
        logic [$clog2(KV_NUM_DWORDS)-1:0] last_dword;

        uvm_reg rg;

        //Pass variables to parent
        super.reg_ap = reg_ap_local;
        super.map = map;
        super.adapter = adapter;
        
        //Convert bus txn to reg model txn
        adapter.bus2reg(tr,rw);

        //-----------------------------------------------
        //rw contains KEY entry info. Below steps are to
        //derive corresponding CTRL reg info
        //-----------------------------------------------
        if (rw.kind == UVM_WRITE) begin
            //Get write_dest_valid and last_dword data from tx
            {write_dest_valid, last_dword} = parse_wr_transaction(tr);

            //Convert reg addr to entry/offset
            entry_offset = convert_addr_to_kv(rw.addr);

            //Calculate CTRL addr based on entry info
            addr = convert_kv_to_ctrl_addr(entry_offset);

            //-----------------------------------------------
            //Below steps are to read CTRL reg data from reg model
            //and append dest valid to it (we want to keep lock bits same)
            //-----------------------------------------------
            //Build rw_ctrl (reg model txn for CTRL reg)
            rw_ctrl = rw;
            rw_ctrl.addr = uvm_reg_addr_t'(addr); 
            
            kv_reg = map.get_reg_by_offset(rw.addr, (rw.kind == UVM_READ));
            kv_reg_ctrl = map.get_reg_by_offset(rw_ctrl.addr, (rw_ctrl.kind == UVM_READ));
            
            //TODO: reg null check?
            //Read CTRL reg data
            kv_reg_ctrl_data = kv_reg_ctrl.get_mirrored_value();
            //Append dest valid to it
            kv_reg_ctrl_data = {kv_reg_ctrl_data[31:21], last_dword, kv_reg_ctrl_data[16:14], /*5'h1F*/write_dest_valid, kv_reg_ctrl_data[8:0]};
            rw_ctrl.data = kv_reg_ctrl_data;

            //-----------------------------------------------
            //Read val reg first
            //-----------------------------------------------
            val_reg = map.get_reg_by_offset('h1_0000);
            val_reg_data = val_reg.get();
            
            val_ctrl = map.get_reg_by_offset('h1_0004);
            val_ctrl_data = val_ctrl.get();

            val_ctrl_derived = map.get_reg_by_offset('h1_0008);
            val_ctrl_derived_data = val_ctrl_derived.get();

            
            //-----------------------------------------------
            //Update val_ctrl reg to reset clear bit for the entry that is being written
            //-----------------------------------------------
            val_ctrl_data[entry_offset[4:0]] = 'b0; //Reset clear bit of current entry

            val_ctrl_item = new;
            val_ctrl_item.element_kind = UVM_REG;
            val_ctrl_item.element = val_ctrl;
            val_ctrl_item.path = UVM_PREDICT;
            val_ctrl_item.map = map;
            val_ctrl_item.kind = UVM_WRITE;
            val_ctrl_item.value[0] |= val_ctrl_data;

            //Update CTRL reg 
            val_ctrl.do_predict(val_ctrl_item, UVM_PREDICT_DIRECT);

            //-----------------------------------------------
            //Update val_ctrl_derived reg to reset clear bits for all other entries except current one
            //This will be used to hold the clear until writes are finished to current entry
            //-----------------------------------------------
            for (int i = 0; i < KV_NUM_KEYS; i++) begin
                val_ctrl_derived_data[i] /*[entry_offset[4:0]]*/ = (val_ctrl_derived_data[i] & (i == entry_offset[4:0])); //'b0; //Reset clear bit of current entry
            end

            val_ctrl_item = new;
            val_ctrl_item.element_kind = UVM_REG;
            val_ctrl_item.element = val_ctrl_derived;
            val_ctrl_item.path = UVM_PREDICT;
            val_ctrl_item.map = map;
            val_ctrl_item.kind = UVM_WRITE;
            val_ctrl_item.value[0] |= val_ctrl_derived_data;

            //Update CTRL reg 
            val_ctrl_derived.do_predict(val_ctrl_item, UVM_PREDICT_DIRECT);

            //-----------------------------------------------
            //Check clear secrets and lock_wr/use before writing
            //-----------------------------------------------
            clear_secrets_reg = map.get_reg_by_offset(`KV_REG_CLEAR_SECRETS);
            clear_secrets_data = clear_secrets_reg.get_mirrored_value();


            lock_wr = kv_reg_ctrl_data[0];
            lock_use = kv_reg_ctrl_data[1];

            //TODO: how can writes be delayed by a clock to mimic design?
            //If lock_wr, lock_use, debug mode or clear secrets is enabled, do not write to reg model

            //TODO: Revisit lock and clear condition
            //TODO: Can write to regs during debug mode. Remove check after updating sequences
            `uvm_info("KV_REG_PRED", $sformatf("OUTSIDE, lock_wr = %0d, lock_use = %0d, clear_secrets_wren = %0d, val_reg_data = %b", lock_wr, lock_use, clear_secrets_data[0], val_reg_data), UVM_FULL)
            if (!lock_wr && !lock_use && !(clear_secrets_data[0] && val_reg_data[2]) && !val_reg_data[0]) begin
                `uvm_info("KV_REG_PRED", "Writing to KEY_ENTRY", UVM_FULL)
                super.write(tr);

                `uvm_info("KV_REG_PRED", "Updating KEY_CTRL", UVM_FULL)
                
                //-----------------------------------------------
                //Predict ctrl reg data so it gets updated in reg model
                //-----------------------------------------------
                kv_reg_ctrl_item = new;
                kv_reg_ctrl_item.element_kind = UVM_REG;
                kv_reg_ctrl_item.element = kv_reg_ctrl;
                kv_reg_ctrl_item.path = UVM_PREDICT;
                kv_reg_ctrl_item.map = map;
                kv_reg_ctrl_item.kind = UVM_WRITE;
                kv_reg_ctrl_item.value[0] |= kv_reg_ctrl_data;

                //Update CTRL reg 
                kv_reg_ctrl.do_predict(kv_reg_ctrl_item, UVM_PREDICT_DIRECT);
            end
            else begin
                `uvm_info("KV_REG_PRED", "Skipping write to KEY_ENTRY", UVM_FULL)
                `uvm_info("KV_REG_PRED", $sformatf("lock_wr = %0d, lock_use = %0d, clear_secrets_data = %0d, val_reg_data = %b", lock_wr, lock_use, clear_secrets_data[0], val_reg_data), UVM_FULL)
            end
            
            //-----------------------------------------------
            //Clear secrets wren bit back to 0 (single pulse behv) - do this if clear_secrets reg is not being written to in the same cycle
            //-----------------------------------------------
            if(val_reg_data[1]) begin
                `uvm_info("KV_REG_PRED", "Clear_secrets bit is reset after a single pulse", UVM_FULL)
                clear_secrets_item = new;
                clear_secrets_item.element_kind = UVM_REG;
                clear_secrets_item.element = clear_secrets_reg;
                clear_secrets_item.path = UVM_PREDICT;
                clear_secrets_item.map = map;
                clear_secrets_item.kind = UVM_WRITE;
                clear_secrets_item.value[0] |= {clear_secrets_data[1], 1'b0}; //Keep debug value as is, only set wren back to 0

                clear_secrets_reg.do_predict(clear_secrets_item, UVM_PREDICT_DIRECT);
            end
            //-----------------------------------------------
            //Predict val reg data so it gets updated in reg model
            //-----------------------------------------------
            val_reg_item = new;
            val_reg_item.element_kind = UVM_REG;
            val_reg_item.element = val_reg;
            val_reg_item.path = UVM_PREDICT;
            val_reg_item.map = map;
            val_reg_item.kind = UVM_WRITE;
            val_reg_item.value[0] |= {val_reg_data[2],1'b0,val_reg_data[0]}; //Clear and clear_secrets_bit are single pulse, so make them 0. Keep debug_mode as is

            val_reg.do_predict(val_reg_item, UVM_PREDICT_DIRECT);
            
        end
        else begin //UVM_READ
            super.write(tr);
        end

        rg = map.get_reg_by_offset(rw.addr, (rw.kind == UVM_READ));
        rg.sample_values();
        rg = map.get_reg_by_offset(rw_ctrl.addr, (rw_ctrl.kind == UVM_READ));
        rg.sample_values();

    endfunction

    
endclass

function logic [(KV_NUM_READ + $clog2(KV_NUM_DWORDS))-1 :0] kv_reg_predictor::parse_wr_transaction(uvm_sequence_item bus_item);
    kv_write_transaction #(
      .KV_WRITE_REQUESTOR("HMAC")
    )
    trans_h;

    if (!$cast(trans_h, bus_item)) begin
      `uvm_fatal("ADAPT","Provided bus_item is not of the correct type")
    //   return;
    end
    // pragma uvmf custom bus2reg begin
    parse_wr_transaction = {trans_h.write_dest_valid, trans_h.write_offset};
    // pragma uvmf custom bus2reg end

endfunction: parse_wr_transaction