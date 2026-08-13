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

// Enforces the recovery agent's single-address FIXED-read protocol and
// injects SLVERR on empty reads. The pre-data callback also provides the only
// point early enough to lower availability before the final R beat completes.
class soc_ifc_recovery_fifo_callback extends aaxi_callbacks;

  `uvm_object_utils(soc_ifc_recovery_fifo_callback)

  soc_ifc_recovery_fifo_model model;

  // Construct a recovery protocol callback with no model attached.
  function new(string name = "soc_ifc_recovery_fifo_callback");
    super.new(name);
  endfunction

  // Recovery data is a single-address streaming FIFO. Reject addressing or
  // burst modes that would turn it into ordinary incrementing memory.
  virtual task read_address_channel_rx(aaxi_device_class bfm,
                                       ref aaxi_slave_tr tn);
    if (model == null)
      `uvm_fatal("RECOVERY_FIFO", "Recovery FIFO callback model is null")
    if (tn.addr != model.configuration.fifo_data_addr)
      `uvm_error("RECOVERY_FIFO",
        $sformatf("Recovery FIFO read used unexpected address 0x%0h", tn.addr))
    if (tn.burst != AAXI_BURST_FIXED)
      `uvm_error("RECOVERY_FIFO",
        $sformatf("Recovery FIFO read used non-FIXED burst %0d", tn.burst))
  endtask

  // Prepare one R beat and lower availability before the final staged beat.
  virtual task pre_rdata_beat_tx(aaxi_device_class bfm,
                                 ref aaxi_slave_tr tn);
    if (model == null)
      `uvm_fatal("RECOVERY_FIFO", "Recovery FIFO callback model is null")
    if (model.front_fifo_empty()) begin
      tn.resp = AAXI_RESP_SLVERR;
      if (!model.underflow_reported) begin
        `uvm_error("RECOVERY_FIFO",
          "DMA attempted to read the empty recovery FIFO")
        model.underflow_reported = 1'b1;
      end
    end else
      // Avery invokes this before presenting the beat. Drop availability here,
      // rather than at RVALID/RREADY, so the DMA sees it low before the final
      // staged transfer fully completes.
      model.note_read_beat_committed();
  endtask

endclass
