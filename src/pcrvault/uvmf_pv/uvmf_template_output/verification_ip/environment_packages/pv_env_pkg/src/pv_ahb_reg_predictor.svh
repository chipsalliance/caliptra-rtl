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
// Custom ahb reg predictor for pcrvault
//----------------------------------------------------------

class pv_ahb_reg_predictor #(type T = int,
    int AHB_NUM_MASTERS = 1, 
    int AHB_NUM_MASTER_BITS = 1, 
    int AHB_NUM_SLAVES = 2, 
    int AHB_ADDRESS_WIDTH = 32, 
    int AHB_WDATA_WIDTH = 32, 
    int AHB_RDATA_WIDTH = 32) extends ahb_reg_predictor #(.T(T),
                                                            .AHB_NUM_MASTERS(AHB_NUM_MASTERS),
                                                            .AHB_NUM_MASTER_BITS(AHB_NUM_MASTER_BITS),
                                                            .AHB_NUM_SLAVES(AHB_NUM_SLAVES),
                                                            .AHB_ADDRESS_WIDTH(AHB_ADDRESS_WIDTH),
                                                            .AHB_WDATA_WIDTH(AHB_WDATA_WIDTH),
                                                            .AHB_RDATA_WIDTH(AHB_RDATA_WIDTH)
                                                            );


    `uvm_component_param_utils(pv_ahb_reg_predictor #(T, AHB_NUM_MASTERS, AHB_NUM_MASTER_BITS, AHB_NUM_SLAVES, AHB_ADDRESS_WIDTH, AHB_WDATA_WIDTH, AHB_RDATA_WIDTH))
    //uvm_analysis_imp #(pv_ahb_reg_predictor #(T, AHB_NUM_MASTERS, AHB_NUM_MASTER_BITS, AHB_NUM_SLAVES, AHB_ADDRESS_WIDTH, AHB_WDATA_WIDTH, AHB_RDATA_WIDTH)) bus_item_export_local;

    function new(string name, uvm_component parent);
        super.new(name, parent);
      //  bus_item_export_local = new("bus_item_export_local", this);
    endfunction

    virtual function void write(mvc_sequence_item_base tr);
        T ahb_txn;
        uvm_reg pv_reg;
        uvm_reg_data_t pv_reg_data;
        logic lock;

        $cast(ahb_txn, tr);
        if(ahb_txn.RnW == AHB_WRITE) begin
            if((ahb_txn.address >= `PV_REG_PCR_CTRL_0) && (ahb_txn.address < `PV_REG_PCR_ENTRY_0_0)) begin
                //`uvm_info("PV_AHB_REG", $sformatf("addr = %h, new data = %h", ahb_txn.address, ahb_txn.data[0]),UVM_MEDIUM);
                pv_reg = map.get_reg_by_offset(ahb_txn.address);
                pv_reg_data = pv_reg.get_mirrored_value();
                lock = pv_reg_data[0];
                `uvm_info("PV_AHB_REG", $sformatf("addr = %h, new data = %h, old data = %h, lock = %h", ahb_txn.address, ahb_txn.data[0], pv_reg_data, lock),UVM_MEDIUM);
                if(!lock)
                    super.write(tr);
            end
            else super.write(tr);
        end
        else begin
            super.write(tr);
        end

    endfunction
endclass                                                            