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

// Runs a long DMA copy with a long R-response and short B-response delay.
class soc_ifc_env_dma_long_transfer_long_r_resp_short_b_resp_sequence
  extends soc_ifc_env_dma_sequence_base;

  `uvm_object_utils(
    soc_ifc_env_dma_long_transfer_long_r_resp_short_b_resp_sequence)

  int unsigned long_transfer_words = 16384;

  // Construct the long-R-response sequence.
  function new(
      string name =
        "soc_ifc_env_dma_long_transfer_long_r_resp_short_b_resp_sequence");
    super.new(name);
  endfunction

  // Run one long transfer with randomized long-R and short-B delays.
  virtual task body();
    soc_ifc_dma_xfer_item item;
    bit err;
    int unsigned b_delay_cycles;
    int unsigned r_delay_cycles;

    if (reg_model == null)
      reg_model = configuration.soc_ifc_rm;
    if (!std::randomize(b_delay_cycles, r_delay_cycles) with {
          b_delay_cycles inside {[0:3]};
          r_delay_cycles inside {[192:255]};
        })
      `uvm_fatal("DMA_LONG_R_RESP_SEQ",
        "Failed to randomize long-R/short-B response delays")

    configuration.axi_sram_config.set_b_response_delay(
      b_delay_cycles, b_delay_cycles);
    configuration.axi_sram_config.set_r_response_delay(
      r_delay_cycles, r_delay_cycles);
    configuration.recovery_fifo_config.set_r_response_delay(0, 0);
    configuration.recovery_fifo_config.set_refill_delay(0, 0);

    item = soc_ifc_dma_xfer_item::type_id::create(
      "long_r_resp_transfer_item");
    item.configure(configuration.axi_sram_config.base_addr,
                   configuration.axi_sram_config.limit_addr -
                     configuration.axi_sram_config.base_addr + 1,
                   long_transfer_words,
                   configuration.recovery_fifo_config.fifo_data_addr);
    if (!item.randomize() with {
          num_words == long_transfer_words;
          transfer_mode == DMA_XFER_AXI_MEMORY;
        })
      `uvm_fatal("DMA_LONG_R_RESP_SEQ",
        "Failed to randomize long-R/short-B AXI-memory transfer")

    `uvm_info("DMA_LONG_R_RESP_SEQ",
      $sformatf(
        "Starting %0d-word AXI-memory transfer with R delay %0d and B delay %0d",
        long_transfer_words, r_delay_cycles, b_delay_cycles), UVM_LOW)
    dma_transfer_and_verify(item, err);

    configuration.axi_sram_config.set_b_response_delay(0, 0);
    configuration.axi_sram_config.set_r_response_delay(0, 0);
    if (!err)
      `uvm_info("DMA_LONG_R_RESP_SEQ",
        "Completed long-R/short-B AXI-memory transfer", UVM_LOW)
  endtask

endclass
