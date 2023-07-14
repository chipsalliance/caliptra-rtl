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

// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
// DESCRIPTION:
// This sequences randomizes the soc_ifc_ctrl transaction and sends it
// to the UVM driver.
//
// This sequence constructs and randomizes a soc_ifc_ctrl_transaction.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_ctrl_reset_sequence_base
  extends soc_ifc_ctrl_sequence_base ;

  `uvm_object_utils( soc_ifc_ctrl_reset_sequence_base )

  // pragma uvmf custom class_item_additional begin
  bit warm_reset_only = 1'b0;
  bit set_bootfsm_breakpoint;
  bit [7:0] [31:0] cptra_obf_key ;
  // pragma uvmf custom class_item_additional end

  //*****************************************************************
  function new(string name = "");
    super.new(name);
  endfunction: new

  // ****************************************************************************
  // TASK : assert_cold_rst()
  // Invoked by body()
  //
  virtual task assert_cold_rst();
      // Initialize first transaction with pwrgood = 0, cptra_rst_b = 0 (asserted)
      req=soc_ifc_ctrl_transaction::type_id::create("pwr_req");
      start_item(req);
      // Randomize the transaction
      if(!req.randomize()) `uvm_fatal("SOC_IFC_CTRL_RST", "soc_ifc_ctrl_reset_sequence_base::body()-soc_ifc_ctrl_transaction randomization failed")
      req.set_pwrgood = 1'b0;
      req.assert_rst = 1'b1; // active-low assertion
      // Send the transaction to the soc_ifc_ctrl_driver_bfm via the sequencer and soc_ifc_ctrl_driver.
      finish_item(req);
      `uvm_info("SOC_IFC_CTRL_RST", {"Response:",req.convert2string()},UVM_MEDIUM)
      this.cptra_obf_key          = req.cptra_obf_key_rand;
      this.set_bootfsm_breakpoint = req.set_bootfsm_breakpoint;
  endtask

  // ****************************************************************************
  // TASK : assert_warm_rst()
  // Invoked by body()
  //
  virtual task assert_warm_rst();
      // Set pwrgood = 1, cptra_rst_b = 0 (asserted)
      req=soc_ifc_ctrl_transaction::type_id::create("rst_req");
      start_item(req);
      // Randomize the transaction
      if(!req.randomize()) `uvm_fatal("SOC_IFC_CTRL_RST", "soc_ifc_ctrl_reset_sequence_base::body()-soc_ifc_ctrl_transaction randomization failed")
      req.set_pwrgood = 1'b1;
      req.assert_rst = 1'b1; // active-low assertion
      if (warm_reset_only) begin
          this.cptra_obf_key     = req.cptra_obf_key_rand;
          this.set_bootfsm_breakpoint = req.set_bootfsm_breakpoint;
      end
      else begin
          req.cptra_obf_key_rand = this.cptra_obf_key;
          req.set_bootfsm_breakpoint = this.set_bootfsm_breakpoint;
      end
      // Send the transaction to the soc_ifc_ctrl_driver_bfm via the sequencer and soc_ifc_ctrl_driver.
      finish_item(req);
      `uvm_info("SOC_IFC_CTRL_RST", {"Response:",req.convert2string()},UVM_MEDIUM)
  endtask

  // ****************************************************************************
  // TASK : deassert_rst()
  // Invoked by body()
  //
  virtual task deassert_rst();
      // Deassert cptra_rst_b, completing the reset
      req=soc_ifc_ctrl_transaction::type_id::create("rst_release_req");
      start_item(req);
      // Randomize the transaction
      if(!req.randomize()) `uvm_fatal("SOC_IFC_CTRL_RST", "soc_ifc_ctrl_reset_sequence_base::body()-soc_ifc_ctrl_transaction randomization failed")
      req.set_pwrgood = 1'b1;
      req.assert_rst = 1'b0;
      req.cptra_obf_key_rand          = this.cptra_obf_key;
      req.set_bootfsm_breakpoint      = this.set_bootfsm_breakpoint;
      req.wait_cycles = 0;
      // Send the transaction to the soc_ifc_ctrl_driver_bfm via the sequencer and soc_ifc_ctrl_driver.
      finish_item(req);
      `uvm_info("SOC_IFC_CTRL_RST", {"Response:",req.convert2string()},UVM_MEDIUM)

  endtask

  // ****************************************************************************
  // TASK : body()
  // This task is automatically executed when this sequence is started using the
  // start(sequencerHandle) task.
  //
  task body();

      if (!warm_reset_only)
          assert_cold_rst();

      assert_warm_rst();
      deassert_rst();

  endtask

endclass: soc_ifc_ctrl_reset_sequence_base
