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

// Executes one 64 KiB AXI-memory DMA copy with a fixed 255-cycle B-response
// delay and no R-response delay. This keeps long-transfer data integrity and
// completion coverage separate from the concurrent SoC-access regression.
class soc_ifc_env_dma_long_transfer_sequence
  extends soc_ifc_env_dma_transfer_stress_sequence;

  `uvm_object_utils(soc_ifc_env_dma_long_transfer_sequence)

  int unsigned long_transfer_words = 16384;

  // Construct the long-transfer sequence.
  function new(string name = "soc_ifc_env_dma_long_transfer_sequence");
    super.new(name);
  endfunction

  // Configure endpoint timing and execute one long AXI-memory transfer.
  virtual task body();
    soc_ifc_dma_xfer_item item;
    bit err;
    int unsigned b_delay_cycles;
    int unsigned r_delay_cycles;

    if (reg_model == null)
      reg_model = configuration.soc_ifc_rm;
    if (!std::randomize(b_delay_cycles, r_delay_cycles) with {
          b_delay_cycles inside {[255:255]};
          r_delay_cycles inside {[0:0]};
        })
      `uvm_fatal("DMA_LONG_SEQ",
        "Failed to randomize long-transfer response delays")

    configuration.axi_sram_config.set_b_response_delay(
      b_delay_cycles, b_delay_cycles);
    configuration.axi_sram_config.set_r_response_delay(
      r_delay_cycles, r_delay_cycles);
    configuration.recovery_fifo_config.set_r_response_delay(0, 0);
    configuration.recovery_fifo_config.set_refill_delay(0, 0);

    item = create_stress_item("long_transfer_item", long_transfer_words);
    if (!item.randomize() with {
          num_words == long_transfer_words;
          transfer_mode == DMA_XFER_AXI_MEMORY;
        })
      `uvm_fatal("DMA_LONG_SEQ",
        "Failed to randomize maximum AXI-memory transfer")

    `uvm_info("DMA_LONG_SEQ",
      $sformatf(
        "Starting %0d-word AXI-memory transfer with B delay %0d and R delay %0d",
        long_transfer_words, b_delay_cycles, r_delay_cycles), UVM_LOW)
    dma_transfer_and_verify(item, err);

    configuration.axi_sram_config.set_b_response_delay(0, 0);
    configuration.axi_sram_config.set_r_response_delay(0, 0);
    `uvm_info("DMA_LONG_SEQ",
      "Completed maximum AXI-memory transfer", UVM_LOW)
  endtask

endclass
