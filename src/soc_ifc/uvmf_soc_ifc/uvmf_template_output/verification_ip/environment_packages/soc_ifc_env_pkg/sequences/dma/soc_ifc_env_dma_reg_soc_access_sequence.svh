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
// DESCRIPTION: Reusable SoC-AXI access sequence against the AXI DMA registers.
//
// Continuously drives SoC-AXI reads/writes to every DMA register with random
// AxUSERs. The DMA block is Caliptra-uC-only, so every access must be rejected;
// that is checked passively by the predictor + scoreboard (predicted SLVERR) and
// the bound assertion soc_ifc_arb.ERR_ARB_SOC_DMA_GNT.
//
// Standalone and composable: a test can fork it as background traffic and end it
// via stop(), or bound it with num_accesses.
//----------------------------------------------------------------------

// Generates unauthorized SoC-AXI accesses to the firmware-only DMA registers.
class soc_ifc_env_dma_reg_soc_access_sequence extends soc_ifc_env_dma_sequence_base;

  `uvm_object_utils( soc_ifc_env_dma_reg_soc_access_sequence )

  // 0 = run until stop() is called; otherwise stop after this many accesses.
  int unsigned num_accesses = 0;

  protected bit stop_access;

  // Construct the SoC-access sequence.
  function new(string name = "" );
    super.new(name);
  endfunction

  // Request the access loop to finish after its current frontdoor operation.
  // This is cooperative termination: no sequence is killed while a RAL access
  // owns the SoC AXI sequencer.
  virtual function void stop();
    stop_access = 1'b1;
  endfunction

  // Drive accesses until the configured count is reached or stop() is called.
  virtual task body();
    uvm_reg           soc_regs[$];
    caliptra_axi_user axi_user_obj;
    uvm_status_e      sts;
    uvm_reg_data_t    rdata;
    uvm_reg_data_t    wdata;
    int               sel;
    int unsigned      count;

    if (reg_model == null)
      reg_model = configuration.soc_ifc_rm;

    // Use the generated DMA AXI map so new registers automatically participate
    // in attack traffic without maintaining a hand-authored address list.
    reg_model.axi_dma_reg_rm.axi_dma_reg_AXI_map.get_registers(soc_regs);
    axi_user_obj = new("axi_user_obj");
    stop_access  = 1'b0;
    count        = 0;
    `uvm_info("DMA_SOC_SEQ",
      $sformatf(
        "Starting unauthorized SoC-AXI DMA register accesses (limit=%0d; 0 means run until stopped)",
        num_accesses), UVM_LOW)

    if (soc_regs.size() == 0)
      `uvm_fatal("DMA_SOC_SEQ", "DMA AXI register map contains no registers")

    while (!stop_access && (num_accesses == 0 || count < num_accesses)) begin
      sel = $urandom_range(soc_regs.size()-1, 0);
      if (!axi_user_obj.randomize())
        `uvm_fatal("DMA_SOC_SEQ", "Failed to randomize AxUSER")
      if ($urandom_range(1,0)) begin
        soc_regs[sel].read(sts, rdata, UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(axi_user_obj));
      end
      else begin
        if (!std::randomize(wdata))
          `uvm_fatal("DMA_SOC_SEQ", "Failed to randomize write data")
        soc_regs[sel].write(sts, wdata, UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(axi_user_obj));
      end
      count++;
    end

    `uvm_info("DMA_SOC_SEQ", $sformatf("Completed %0d SoC-AXI DMA register accesses (all expected rejected)", count), UVM_LOW)
  endtask

endclass
