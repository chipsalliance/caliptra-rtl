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

//---------------------------------------------------------------
// CLASS: caliptra_reg2apb_adapter
//
// This is the adapter used for APB interface in Caliptra soc_ifc
// environment.
// This converts the reg items to APB bus specific items and 
// vice-versa.
// This class is derived from Mentor Graphics APB5 QVIP reg2apb_adapter
// and adds functionality to drive PAUSER field
//
//---------------------------------------------------------------
class caliptra_reg2apb_adapter #(
    type T            = int, 
    int SLAVE_COUNT   = 1 , 
    int ADDRESS_WIDTH = 32 ,
    int WDATA_WIDTH   = 32 , 
    int RDATA_WIDTH   = 32
) extends reg2apb_adapter #(
    .T            (T            ),
    .SLAVE_COUNT  (SLAVE_COUNT  ),
    .ADDRESS_WIDTH(ADDRESS_WIDTH),
    .WDATA_WIDTH  (WDATA_WIDTH  ), 
    .RDATA_WIDTH  (RDATA_WIDTH  )
);

   typedef caliptra_reg2apb_adapter #(T, 
                             SLAVE_COUNT, 
                             ADDRESS_WIDTH, 
                             WDATA_WIDTH, 
                             RDATA_WIDTH) this_t; 
  `uvm_object_param_utils(this_t)
   `m_uvm_get_type_name_func(this_t)

    // Stores the addr_user value captured from the most
    // recent call to bus2reg.
    // This allows us to capture PAUSER during calls to 'write' of
    // apb_reg_predictor, and access this value in the prediction
    // callbacks for each reg field.
    caliptra_apb_user bus2reg_user_obj;

  function new(string name = "reg2apb_adapter");
    super.new(name);
    bus2reg_user_obj = new();
  endfunction

  // Function: reg2bus
  //
  // This converts the reg items to APB bus specific items. 
  // Only difference from APB VIP is overriding addr_user using item.extension
  //
  virtual function uvm_sequence_item reg2bus(const ref uvm_reg_bus_op rw);
    int bus_width;
    int slv_id;
    addr_map_entry_s entry;
    bit unsigned [apb5_master_0_params::PAUSER_WIDTH-1:0] addr_user = '1; // FIXME default val
    caliptra_apb_user user_obj;

    T apb = T::type_id::create("apb");

    uvm_reg_item       item = get_item();
    uvm_sequencer_base seqr = item.map.get_sequencer();
    if (item.extension == null)
        `uvm_error("reg2bus", "uvm_reg_item provided to caliptra_reg2apb_adapter contains null extension object, which is needed to derive the PAUSER field")
    else if (!$cast(user_obj, item.extension))
        `uvm_error("reg2bus", "uvm_reg_item provided to caliptra_reg2apb_adapter contains invalid extension object, which is needed to derive the PAUSER field")
    else
        addr_user = user_obj.get_addr_user();

    apb.set_sequencer(seqr);
    cfg = cfg_t::get_config(seqr);

    slv_id = ((en_addr_map == 0) || (cfg.addr_map == null) || (!cfg.addr_map.lookup(rw.addr,entry))) ? (SLAVE_COUNT - 1) : entry.id;

    if ((rw.kind == UVM_WRITE) || (rw.kind == UVM_BURST_WRITE)) begin
      if (!apb.randomize() with {apb.slave_id         == slv_id;
                                 apb.addr             == rw.addr;
                                 apb.addr_user        == local::addr_user;
                                 apb.prot             == 3'b000;
                                 apb.read_or_write    == APB3_TRANS_WRITE;
                                 apb.wr_data          == rw.data;
                                 apb.strb             == '1;} )
        `uvm_fatal("reg2bus","bad constraints in UVM_WRITE")

      if((supports_byte_enable == 1) && cfg.m_bfm.config_apb4_enable) begin
        bus_width = $size(apb.wr_data)/8;

        for(int i=0; ((i<bus_width) && (i<$size(rw.byte_en))); ++i) begin
          if((apb.strb[i] == 1) && (rw.byte_en[i] == 0))
            apb.strb[i] = 0;
        end
      end

      if (!cfg.m_bfm.config_apb4_enable)
        apb.strb = 4'h0;
    end else begin
      if (!apb.randomize() with {apb.slave_id         == slv_id;
                                 apb.addr             == rw.addr;
                                 apb.addr_user        == local::addr_user;
                                 apb.prot             == 3'b000;
                                 apb.read_or_write    == APB3_TRANS_READ;
                                 apb.strb             == '0;} )
        `uvm_fatal("reg2bus","bad constraints in UVM_READ")
    end

    `uvm_info("reg2bus",$sformatf("do register access: %p",rw),UVM_MEDIUM)
    return apb;
  endfunction: reg2bus

  // Function: bus2reg
  //
  // This converts the APB bus specific items to reg items. 
  // Only difference from APB VIP is grabbing addr_user and storing to local var
  //
  virtual function void bus2reg(uvm_sequence_item bus_item,
                                ref uvm_reg_bus_op rw);
    T apb;
    if (!$cast(apb, bus_item))
    begin
      `uvm_fatal("NOT_APB_TYPE","Provided bus_item is not of the correct type")
      return;
    end

    super.bus2reg(bus_item,rw);

    bus2reg_user_obj.set_addr_user(apb.addr_user);

  endfunction: bus2reg

endclass
