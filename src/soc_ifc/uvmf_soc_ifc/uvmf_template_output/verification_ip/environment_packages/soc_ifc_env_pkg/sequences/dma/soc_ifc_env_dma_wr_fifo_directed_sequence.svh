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

// Runs a fixed firmware WR_FIFO transfer with unauthorized SoC DMA accesses.
class soc_ifc_env_dma_wr_fifo_directed_sequence
  extends soc_ifc_env_dma_sequence_base;

  `uvm_object_utils(soc_ifc_env_dma_wr_fifo_directed_sequence)

  localparam int unsigned NUM_WORDS = 256;

  // Construct the directed WR_FIFO sequence.
  function new(string name = "soc_ifc_env_dma_wr_fifo_directed_sequence");
    super.new(name);
  endfunction

  // Build the fixed transfer with geometry owned by the current AXI SRAM agent.
  protected function soc_ifc_dma_xfer_item create_directed_item();
    soc_ifc_dma_xfer_item item;

    item = soc_ifc_dma_xfer_item::type_id::create("wr_fifo_item");
    item.configure(
      configuration.axi_sram_config.base_addr,
      configuration.axi_sram_config.limit_addr -
        configuration.axi_sram_config.base_addr + 1,
      NUM_WORDS,
      configuration.recovery_fifo_config.fifo_data_addr);
    item.transfer_mode = DMA_XFER_WRITE_FIFO;
    item.num_words = NUM_WORDS;
    item.src_offset = 0;
    item.dst_offset = 0;
    item.block_size_bytes = 0;
    item.payload = new[NUM_WORDS];
    foreach (item.payload[w])
      item.payload[w] = 32'hA5A5_0000 | w;
    return item;
  endfunction

  // Run the directed transfer and security traffic through shared sequences.
  virtual task body();
    bit err;
    soc_ifc_dma_xfer_item item;
    soc_ifc_env_dma_reg_soc_access_sequence soc_access_sequence;

    if (reg_model == null)
      reg_model = configuration.soc_ifc_rm;

    dma_read_cap();
    item = create_directed_item();
    soc_access_sequence =
      soc_ifc_env_dma_reg_soc_access_sequence::type_id::create(
        "soc_access_sequence");

    `uvm_info("DMA_WRFIFO_DIR",
      $sformatf(
        "Starting directed %0d-word WR_FIFO transfer with random SoC accesses",
        NUM_WORDS), UVM_LOW)

    fork
      soc_access_sequence.start(m_sequencer, this);
      begin
        dma_transfer_and_verify(item, err);
        soc_access_sequence.stop();
      end
    join

    if (err)
      `uvm_error("DMA_WRFIFO_DIR",
        "Directed firmware WR_FIFO transfer reported a DMA error")

    `uvm_info("DMA_WRFIFO_DIR",
      "Completed directed WR_FIFO and SoC-access rejection test", UVM_LOW)
  endtask

endclass
