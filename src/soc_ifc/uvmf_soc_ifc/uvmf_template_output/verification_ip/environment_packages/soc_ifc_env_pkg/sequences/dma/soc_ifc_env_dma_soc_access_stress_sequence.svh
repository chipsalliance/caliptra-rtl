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

// Stresses unauthorized SoC-AXI accesses to DMA registers while legitimate AHB
// firmware traffic keeps the DMA active.
//
// The SoC access sequence continuously selects DMA CSRs and random read/write
// operations. In parallel, a shortened transfer-stress sequence provides valid
// DMA activity across routes. Predictor/scoreboard logic checks SLVERR and the
// arbiter assertion checks that SoC traffic never receives the DMA client.
// Concurrency is therefore the central behavior of this test, not incidental
// background traffic.
class soc_ifc_env_dma_soc_access_stress_sequence
  extends soc_ifc_env_dma_sequence_base;

  `uvm_object_utils(soc_ifc_env_dma_soc_access_stress_sequence)

  // Construct the concurrent SoC-access stress sequence.
  function new(string name = "soc_ifc_env_dma_soc_access_stress_sequence");
    super.new(name);
  endfunction

  // Run unauthorized SoC accesses alongside legitimate DMA transfers.
  virtual task body();
    soc_ifc_env_dma_reg_soc_access_sequence soc_access_sequence;
    soc_ifc_env_dma_transfer_stress_sequence transfer_sequence;

    soc_access_sequence =
      soc_ifc_env_dma_reg_soc_access_sequence::type_id::create(
        "soc_access_sequence");
    transfer_sequence =
      soc_ifc_env_dma_transfer_stress_sequence::type_id::create(
        "transfer_sequence");

    // A bounded workload supplies varied DMA activity without duplicating the
    // long response-pressure goals of the standalone transfer stress test.
    transfer_sequence.num_transfers = 10;
    transfer_sequence.max_transfer_words = 512;
    transfer_sequence.include_delayed_write_pressure = 1'b0;
    transfer_sequence.randomize_response_delays = 1'b1;
    transfer_sequence.limit_response_delays_to_short = 1'b1;

    `uvm_info("DMA_SOC_STRESS",
      $sformatf(
        "Starting concurrent SoC-access stress with %0d DMA transfers up to %0d words",
        transfer_sequence.num_transfers,
        transfer_sequence.max_transfer_words), UVM_LOW)

    // start() blocks until its sequence finishes, so the unbounded SoC access
    // loop must run in a sibling process. The transfer process calls stop() only
    // after all legitimate DMA activity has completed.
    fork
      soc_access_sequence.start(m_sequencer, this);
      begin
        transfer_sequence.start(m_sequencer, this);
        soc_access_sequence.stop();
      end
    join
    `uvm_info("DMA_SOC_STRESS",
      "Completed concurrent SoC-access and DMA transfer stress", UVM_LOW)
  endtask

endclass
