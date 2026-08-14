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

// Adds configurable response latency to an Avery AXI subordinate without
// changing endpoint storage behavior. soc_ifc_axi_sram_agent creates one
// instance for both B and R responses; soc_ifc_recovery_fifo_agent creates an
// R-only instance. soc_ifc_environment registers each object on the matching
// subordinate BFM during connect_phase, after which Avery invokes these hooks
// while processing subordinate responses.
//
// The callback points to configuration-owned soc_ifc_axi_delay_range objects.
// Code holding the configuration can therefore alter a range at runtime without
// replacing the callback. A null policy means "do not assign that transaction
// delay field", which permits the same class to serve read-only and read/write
// endpoints.
//
// TODO: Evaluate replacing this callback with Avery's built-in delay
// support: auto_slave_delay with minwaits/maxwaits, config_slave_delay with
// fixed B/R controls randomized only while the endpoint is idle, or the
// aaxi_slave_delays delay database. Compare READY-channel coupling, outstanding
// transaction safety, runtime policy updates, and per-R-beat randomization.
class soc_ifc_axi_response_delay_callback extends aaxi_callbacks;

  `uvm_object_utils(soc_ifc_axi_response_delay_callback)

  soc_ifc_axi_delay_range b_delay; // Optional write-response latency policy.
  soc_ifc_axi_delay_range r_delay; // Optional read-beat latency policy.

  // Construct a response-delay callback with no policies attached.
  function new(string name = "soc_ifc_axi_response_delay_callback");
    super.new(name);
  endfunction

  // Assign Avery's BVALID delay field in its pre-write-response hook. Avery
  // defines this field relative to the final WVALID/WREADY handshake, so this
  // callback changes response timing without changing stored write data.
  virtual task pre_write_resp_tx(aaxi_device_class bfm,
                                 ref aaxi_slave_tr tn,
                                 inout bit is_drop);
    if (b_delay != null) begin
      tn.b_valid_delay = b_delay.next_delay();
    end
  endtask

  // Select the AR-to-first-RVALID delay when Avery accepts the read address.
  // Avery's callback example uses a_resp_valid_delay for the first beat and
  // leaves later-beat timing to pre_rdata_beat_tx().
  virtual task read_address_channel_rx(aaxi_device_class bfm,
                                       ref aaxi_slave_tr tn);
    if (r_delay != null)
      tn.a_resp_valid_delay = r_delay.next_delay();
  endtask

  // Select one inter-beat delay immediately before Avery handles each later R
  // beat. cur_beat is zero for the first beat, whose delay was selected above;
  // subsequent beats use the matching resp_valid_delay index.
  virtual task pre_rdata_beat_tx(aaxi_device_class bfm,
                                 ref aaxi_slave_tr tn);
    if (r_delay != null && tn.cur_beat > 0)
      tn.resp_valid_delay[tn.cur_beat] = r_delay.next_delay();
  endtask

endclass
