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
// DESCRIPTION: Prosecutor stimulus for bug-dma-soc-axi-access.md.
//
// The Caliptra AXI DMA assist register block (0x3002_2000-0x3002_2FFF) is
// Caliptra-uC-only: it is programmed by the microcontroller over AHB. No SoC
// agent on the AXI subordinate interface should be able to read or write it.
//
// This sequence:
//   1. (uC/AHB) Seeds the writable DMA config registers with known values and
//      reads them back to establish a baseline.
//   2. (SoC/AXI) Drives reads and writes to a representative set of DMA
//      registers using random foreign AxUSERs. Each access is checked by the
//      predictor + scoreboard: the predictor predicts a rejected response
//      (SLVERR) for any AXI access to the DMA block, and the scoreboard compares
//      it against the actual response. Against current RTL the arbiter grants
//      these accesses (OKAY != predicted SLVERR -> scoreboard error); once the
//      SoC->DMA path is gated they are rejected (SLVERR) and the scoreboard
//      matches.
//   3. (uC/AHB) Re-reads the config registers and checks they are UNCHANGED --
//      i.e. the SoC AXI activity did not corrupt uC-visible DMA state. This
//      integrity check must hold on both current and fixed RTL, and guards
//      against any missing swwel write-protection on a DMA field.
//----------------------------------------------------------------------

class soc_ifc_env_dma_reg_axs_invalid_sequence extends soc_ifc_env_sequence_base #(.CONFIG_T(soc_ifc_env_configuration_t));

  `uvm_object_utils( soc_ifc_env_dma_reg_axs_invalid_sequence )

  function new(string name = "" );
    super.new(name);
  endfunction

  //==========================================
  // Task: pre_body - grab the register model handle.
  //==========================================
  virtual task pre_body();
    super.pre_body();
    reg_model = configuration.soc_ifc_rm;
  endtask

  //==========================================
  // Task: body
  //==========================================
  virtual task body();
    uvm_reg           integ_regs[$]; // writable, side-effect-free DMA config regs
    uvm_reg           soc_regs[$];   // registers probed over SoC-AXI
    caliptra_axi_user axi_user_obj;
    uvm_status_e      reg_sts;
    uvm_reg_data_t    rdata;
    uvm_reg_data_t    wdata;
    uvm_reg_data_t    baseline[$];

    if (reg_model == null)
        reg_model = configuration.soc_ifc_rm;

    // Writable, side-effect-free config registers (sw=rw, hw=r) used for the
    // uC-visible integrity check.
    integ_regs.push_back(reg_model.axi_dma_reg_rm.src_addr_l);
    integ_regs.push_back(reg_model.axi_dma_reg_rm.dst_addr_l);
    integ_regs.push_back(reg_model.axi_dma_reg_rm.byte_count);
    integ_regs.push_back(reg_model.axi_dma_reg_rm.block_size);

    // Registers probed over SoC-AXI: read-only identifier (leak evidence),
    // status, the FIFO-pop read register, control, the write-data FIFO, plus
    // the writable config registers (which the SoC also attempts to corrupt).
    soc_regs.push_back(reg_model.axi_dma_reg_rm.id        );
    soc_regs.push_back(reg_model.axi_dma_reg_rm.status0   );
    soc_regs.push_back(reg_model.axi_dma_reg_rm.read_data );
    soc_regs.push_back(reg_model.axi_dma_reg_rm.ctrl      );
    soc_regs.push_back(reg_model.axi_dma_reg_rm.write_data);
    foreach (integ_regs[i]) soc_regs.push_back(integ_regs[i]);

    axi_user_obj = new("axi_user_obj");

    //------------------------------------------------------------------
    // Phase 1: uC (AHB) seed + baseline read of DMA config registers.
    //------------------------------------------------------------------
    foreach (integ_regs[i]) begin
        if (!std::randomize(wdata))
            `uvm_fatal("DMA_AXS_SEQ", "Failed to randomize uC seed data")
        integ_regs[i].write(reg_sts, wdata, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    end
    foreach (integ_regs[i]) begin
        integ_regs[i].read(reg_sts, rdata, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
        baseline.push_back(rdata);
        `uvm_info("DMA_AXS_SEQ",
                  $sformatf("uC(AHB) baseline DMA %-11s = 0x%08x", integ_regs[i].get_name(), rdata),
                  UVM_LOW)
    end

    //------------------------------------------------------------------
    // Phase 2: SoC (AXI) reads/writes with random foreign AxUSERs.
    //          The predictor + scoreboard are the checker (each access is
    //          predicted as rejected/SLVERR and compared against the DUT).
    //------------------------------------------------------------------
    foreach (soc_regs[i]) begin
        // SoC-AXI READ (any AxUSER; a SoC access to the DMA block must be rejected)
        if (!axi_user_obj.randomize())
            `uvm_fatal("DMA_AXS_SEQ", "Failed to randomize AxUSER")
        soc_regs[i].read(reg_sts, rdata, UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(axi_user_obj));

        // SoC-AXI WRITE (attempt to corrupt; any AxUSER)
        if (!std::randomize(wdata))
            `uvm_fatal("DMA_AXS_SEQ", "Failed to randomize write data")
        if (!axi_user_obj.randomize())
            `uvm_fatal("DMA_AXS_SEQ", "Failed to randomize AxUSER")
        soc_regs[i].write(reg_sts, wdata, UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(axi_user_obj));
    end

    //------------------------------------------------------------------
    // Phase 3: uC (AHB) re-read config registers; require them UNCHANGED.
    //          SoC AXI activity must not corrupt uC-visible DMA state.
    //------------------------------------------------------------------
    foreach (integ_regs[i]) begin
        integ_regs[i].read(reg_sts, rdata, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
        if (rdata !== baseline[i]) begin
            `uvm_error("DMA_AXS_SEQ",
                       $sformatf("INTEGRITY VIOLATION (bug-dma-soc-axi-access): DMA %s changed after SoC-AXI activity: baseline=0x%08x now=0x%08x. SoC must not modify DMA state.",
                                 integ_regs[i].get_name(), baseline[i], rdata))
        end
        else begin
            `uvm_info("DMA_AXS_SEQ",
                      $sformatf("uC(AHB) integrity OK  DMA %-11s = 0x%08x (unchanged)", integ_regs[i].get_name(), rdata),
                      UVM_LOW)
        end
    end

    `uvm_info("DMA_AXS_SEQ",
              "Completed SoC-AXI DMA register accesses + uC integrity check. The predictor+scoreboard check that every SoC-AXI DMA access is rejected (SLVERR).",
              UVM_LOW)
  endtask

endclass
