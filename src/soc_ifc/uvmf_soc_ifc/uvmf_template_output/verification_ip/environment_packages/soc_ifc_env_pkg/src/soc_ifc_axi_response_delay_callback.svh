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

// Programs endpoint-owned B and R delay policies into Avery transactions.
class soc_ifc_axi_response_delay_callback extends aaxi_callbacks;

  `uvm_object_utils(soc_ifc_axi_response_delay_callback)

  soc_ifc_axi_delay_range b_delay;
  soc_ifc_axi_delay_range r_delay;

  // Construct a response-delay callback with no policies attached.
  function new(string name = "soc_ifc_axi_response_delay_callback");
    super.new(name);
  endfunction

  // Select B delay when Avery prepares the response, after write data has been
  // accepted but before BVALID scheduling is finalized.
  virtual task pre_write_resp_tx(aaxi_device_class bfm,
                                 ref aaxi_slave_tr tn,
                                 inout bit is_drop);
    if (b_delay != null) begin
      tn.b_valid_delay = b_delay.next_delay();
    end
  endtask

  // Select all R delays when the AR request is accepted.
  virtual task read_address_channel_rx(aaxi_device_class bfm,
                                       ref aaxi_slave_tr tn);
    if (r_delay != null) begin
      // Avery stores the AR-to-first-R delay separately from delays between
      // later R beats. resp_valid_delay is indexed by the subsequent AXI beat,
      // so index zero is unused after the separately configured first beat.
      tn.ar_handshake_rvalid_delay = r_delay.next_delay();
      for (int beat = 1; beat <= tn.len; beat++) begin
        tn.resp_valid_delay[beat] = r_delay.next_delay();
      end
    end
  endtask

endclass
