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

//---------------------------------------------------------------
// CLASS: caliptra_reg2axi_adapter
//
// This is the adapter used for AXI interface in Caliptra soc_ifc
// environment.
// This converts the reg items to AXI bus specific items and 
// vice-versa.
// This class is derived from AVERY AAXI VIP aaxi_uvm_mem_adapter
// and adds functionality to drive AxUSER field
//
//---------------------------------------------------------------

class caliptra_reg2axi_adapter extends aaxi_uvm_mem_adapter;
    `uvm_object_utils_begin(caliptra_reg2axi_adapter)
    `uvm_object_utils_end

    // Stores the addr_user value captured from the most
    // recent call to bus2reg.
    // This allows us to capture AxUSER during calls to 'write' of
    // axi_reg_predictor, and access this value in the prediction
    // callbacks for each reg field.
    caliptra_axi_user bus2reg_user_obj;

    function new(string name = "reg2axi_adapter");
        super.new(name);
        bus2reg_user_obj = new();
    endfunction

    // Function: reg2bus
    //
    // This converts the reg items to AXI bus specific items. 
    // Only addition to AXI VIP is overriding AxUSER using item.extension
    //
    function uvm_sequence_item reg2bus(const ref uvm_reg_bus_op rw);
        bit unsigned [aaxi_pkg::AAXI_AWUSER_WIDTH-1:0] addr_user = '1; // FIXME default val
        bit unsigned [15:0] ar_valid_delay = 1;
        bit unsigned [15:0] resp_valid_ready_delay = 1;
        bit unsigned [7:0] len = 0;
        bit unsigned [1:0] burst = 0;

        caliptra_axi_user user_obj;
        uvm_sequence_item super_item = super.reg2bus(rw);
        aaxi_master_tr    trans;
        uvm_reg_item      item = get_item();
        if (!$cast(trans,super_item))
            `uvm_error("reg2bus", "uvm_reg_item returned from super.reg2bus failed in cast to aaxi_master_tr!")
        if (item.extension == null)
            `uvm_error("reg2bus", "uvm_reg_item provided to caliptra_reg2axi_adapter contains null extension object, which is needed to derive the AxUSER field")
        else if (!$cast(user_obj, item.extension))
            `uvm_error("reg2bus", "uvm_reg_item provided to caliptra_reg2axi_adapter contains invalid extension object, which is needed to derive the AxUSER field")
        else begin
            addr_user = user_obj.get_addr_user();
            ar_valid_delay = user_obj.get_ar_valid_delay();
            resp_valid_ready_delay = user_obj.get_resp_valid_ready_delay();
            len = user_obj.get_len();
            burst = user_obj.get_burst();
        end
        trans.aruser = addr_user;
        trans.awuser = addr_user;
        
        trans.ar_valid_delay = ar_valid_delay;
        trans.resp_valid_ready_delay = resp_valid_ready_delay;
        trans.len = len;
        trans.burst = burst;

        `uvm_info(get_name(),
                  $psprintf("\n\treg2bus rw.addr = 'h%0h, rw.is_write = %0x, rw.n_bits = %0d, rw.data = 'h%h, rw.axuser = 'h%x", 
                  rw.addr, rw.kind inside {UVM_WRITE, UVM_BURST_WRITE}, rw.n_bits, rw.data, addr_user), UVM_FULL);
        return trans;
    endfunction

    // Function: bus2reg
    //
    // This converts the AXI bus specific items to reg items. 
    // Only difference from AXI VIP is grabbing AxUSER and storing to local var
    //
    virtual function void bus2reg(uvm_sequence_item bus_item,
                                  ref uvm_reg_bus_op rw);
        aaxi_master_tr trans;

        if (!$cast(trans, bus_item)) begin
            `uvm_fatal("AAXI_FATAL","bus_item is not an aaxi_master_tr type")
            return;
        end

        super.bus2reg(bus_item,rw);

        if (trans.kind == AAXI_WRITE)
            bus2reg_user_obj.set_addr_user(trans.awuser);
        else
            bus2reg_user_obj.set_addr_user(trans.aruser);

        `uvm_info(get_name(), $psprintf("\n\tbus2reg rw.addr = 'h%0h, rw.n_bits = %0d, rw.data = 'h%h", 
            rw.addr, rw.n_bits, rw.data), UVM_HIGH);

    endfunction: bus2reg

endclass
