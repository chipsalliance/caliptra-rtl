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
// Firmware-update-reset window sequence.
//
// Models the real BOOT_FW_RST scenario (soc_ifc_boot_fsm): the fw-update reset
// window asserts together with the core (uc) reset, while the KV noncore reset
// (rst_b) stays HIGH so the KV remains ALIVE and error-responds/masks accesses
// during the window. This is distinct from a warm reset (which resets the KV).
//
//   assert_rst        = 0  -> KV rst_b stays high (KV alive)
//   assert_core_rst   = 1  -> core_only_rst_b asserted (uc reset)
//   assert_fw_upd_rst = 1  -> fw_update_rst_window asserted
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class kv_rst_fw_upd_rst_sequence extends kv_rst_sequence_base;

    `uvm_object_utils( kv_rst_fw_upd_rst_sequence )

    //*****************************************************************
  function new(string name = "");
    super.new(name);
  endfunction: new

  // ****************************************************************************
  // TASK : body()
  // This task is automatically executed when this sequence is started using the
  // start(sequencerHandle) task.
  //

  task body();

    // Assert fw-update reset window (KV stays alive)
    req=kv_rst_transaction::type_id::create("fw_upd_req");
    start_item(req);
    if(!req.randomize()) `uvm_fatal("KV_RST_FW_UPD_RST", "kv_rst_fw_upd_rst_sequence::body()-kv_rst_transaction randomization failed")
    `uvm_info("KV_RST_FW_UPD_RST", "Asserting fw-update reset window (KV alive)", UVM_MEDIUM)
    req.set_pwrgood = 1'b1;
    req.assert_rst = 1'b0;
    req.assert_core_rst = 1'b1;
    req.assert_fw_upd_rst = 1'b1;
    req.debug_mode = 1'b0;
    req.scan_mode = 1'b0;

    finish_item(req);
    `uvm_info("KV_RST_FW_UPD_RST", {"Response:",req.convert2string()},UVM_MEDIUM)

    // Deassert fw-update reset window
    req=kv_rst_transaction::type_id::create("fw_upd_deassert_req");
    start_item(req);
    if(!req.randomize()) `uvm_fatal("KV_RST_FW_UPD_RST", "kv_rst_fw_upd_rst_sequence::body()-kv_rst_transaction randomization failed")
    `uvm_info("KV_RST_FW_UPD_RST", "Deasserting fw-update reset window", UVM_MEDIUM)
    req.set_pwrgood = 1'b1;
    req.assert_rst = 1'b0;
    req.assert_core_rst = 1'b0;
    req.assert_fw_upd_rst = 1'b0;
    req.debug_mode = 1'b0;
    req.scan_mode = 1'b0;

    finish_item(req);
    `uvm_info("KV_RST_FW_UPD_RST", {"Response:",req.convert2string()},UVM_MEDIUM)

  endtask

endclass
