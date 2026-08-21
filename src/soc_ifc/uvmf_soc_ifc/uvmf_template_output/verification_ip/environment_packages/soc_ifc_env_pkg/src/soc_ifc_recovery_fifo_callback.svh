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

// Supplies recovery-specific behavior that a generic Avery FIFO does not know.
// soc_ifc_environment registers this object on the recovery subordinate in
// addition to the generic R-delay callback. Avery invokes it for reads reaching
// that subordinate, allowing the model to check the single-address FIXED-burst
// contract, report empty-FIFO accesses, and synchronize recovery_data_avail
// with beat creation.
//
// This callback does not own storage or refill timing. It delegates queue state
// to soc_ifc_recovery_fifo_model; the agent's clocked run_phase accounts accepted
// handshakes and schedules later refills.
class soc_ifc_recovery_fifo_callback extends aaxi_callbacks;

  `uvm_object_utils(soc_ifc_recovery_fifo_callback)

  soc_ifc_recovery_fifo_model model;

  // Construct a recovery protocol callback with no model attached.
  function new(string name = "soc_ifc_recovery_fifo_callback");
    super.new(name);
  endfunction

  // Check each accepted AR against the streaming-port contract. Recovery data
  // is consumed repeatedly from one address, so report addressing or burst
  // modes that do not match the intended FIFO semantics.
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

  // Prepare one R beat before Avery sends it. An empty model marks the response
  // as SLVERR and reports one underflow per load, clear, or reset generation.
  // For valid data, commit notification is deliberately earlier than the
  // RVALID/RREADY accounting performed by the agent.
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
