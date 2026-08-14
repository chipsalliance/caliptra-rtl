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
//
//----------------------------------------------------------------------
// DESCRIPTION: Directed, non-random WR_FIFO / write_data DMA sequence.
//
// Focuses on the AXI DMA write-data FIFO (wr_route=AHB_FIFO) and the write_data
// register, deterministically (no randomization) so it runs quickly. It forks
// two concurrent activities:
//   1. Functional: the microcontroller pushes a fixed payload through write_data
//      over AHB and the DMA writes it to the destination SRAM; verified by the
//      bounded AXI SRAM backdoor.
//   2. Security (in parallel, while the DMA transfer is active): the SoC-AXI side
//      CONTINUOUSLY writes EVERY DMA register (including write_data) with fixed
//      data and a fixed AxUSER, repeating until the transfer completes. The DMA
//      block is Caliptra-uC-only, so all of these must be rejected (SLVERR) and
//      must not disturb the transfer. Verified passively by the predictor +
//      scoreboard and the bound assertion soc_ifc_arb.ERR_ARB_SOC_DMA_GNT. The
//      stimulus values/targets are fixed (no randomization); only the number of
//      passes adapts to the transfer duration.
//----------------------------------------------------------------------

class soc_ifc_env_dma_wr_fifo_directed_sequence extends soc_ifc_env_dma_sequence_base;

  `uvm_object_utils( soc_ifc_env_dma_wr_fifo_directed_sequence )

  // Deterministic transfer / stimulus parameters (no randomization).
  localparam int unsigned NUM_WORDS = 256;                // longer transfer -> more overlap
  localparam bit [31:0]   SOC_WDATA = 32'hDEAD_BEEF;      // fixed SoC-AXI write payload

  function new(string name = "" );
    super.new(name);
  endfunction

  virtual task body();
    caliptra_axi_user axi_user_obj;
    uvm_reg           soc_regs[$];
    bit               err;
    bit               xfer_done;
    soc_ifc_dma_xfer_item item;

    if (reg_model == null)
      reg_model = configuration.soc_ifc_rm;

    dma_read_cap(); // FIFO max depth, needed by the AHB_FIFO write route

    // Directed item: fixed route/size/offsets and a fixed-pattern payload.
    item = soc_ifc_dma_xfer_item::type_id::create("item");
    item.configure(configuration.dma_axi_sram_backdoor.get_base_addr(),
                   configuration.dma_axi_sram_backdoor.get_size_bytes());
    item.route      = XFER_WR_FIFO;
    item.num_words  = NUM_WORDS;
    item.src_offset = 0;
    item.dst_offset = 0;
    item.payload    = new[NUM_WORDS];
    foreach (item.payload[w]) item.payload[w] = 32'hA5A5_0000 | w;

    axi_user_obj = new("axi_user_obj");
    axi_user_obj.set_addr_user('1); // any SoC user is rejected for the DMA block
    // Fixed order/count: every register in the DMA AXI map (includes write_data).
    reg_model.axi_dma_reg_rm.axi_dma_reg_AXI_map.get_registers(soc_regs);

    // Run the uC WR_FIFO transfer while the SoC-AXI side continuously writes every
    // DMA register in parallel until the transfer completes. All SoC writes are
    // rejected and must not disturb the transfer.
    xfer_done = 1'b0;
    fork
      begin : UC_WR_FIFO_XFER
        dma_transfer_and_verify(item, err);
        if (err)
          `uvm_error("DMA_WRFIFO_DIR", "uC WR_FIFO transfer through write_data reported a DMA error")
        xfer_done = 1'b1; // signal the SoC-AXI writer to stop
      end
      begin : SOC_AXI_WRITES
        uvm_status_e sts;
        int unsigned num_soc_writes = 0;
        // Fixed data / order / AxUSER (no randomization); repeat the full register
        // pass until the transfer is done so the SoC-AXI accesses span the whole
        // active transfer.
        while (!xfer_done) begin
          foreach (soc_regs[i]) begin
            if (xfer_done) break;
            soc_regs[i].write(sts, SOC_WDATA, UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(axi_user_obj));
            num_soc_writes++;
          end
        end
        `uvm_info("DMA_WRFIFO_DIR", $sformatf("Issued %0d fixed SoC-AXI writes to DMA registers during the transfer (all expected rejected: SLVERR)", num_soc_writes), UVM_LOW)
      end
    join

    `uvm_info("DMA_WRFIFO_DIR", "Completed directed WR_FIFO / write_data test", UVM_LOW)
  endtask

endclass
