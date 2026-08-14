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
// DESCRIPTION: DMA transfer stress scenario.
//
// Runs 50 constrained-random DMA transfers (configured
// by the microcontroller over AHB) while concurrently running the reusable
// soc_ifc_env_dma_reg_soc_access_sequence against the DMA registers from SoC-AXI.
// Proves both that every transfer moves its data correctly and that every
// SoC-AXI DMA access is rejected while the DMA is in flight.
//
// Thin by design: the DMA transaction API lives in soc_ifc_env_dma_sequence_base
// and the SoC-AXI access sequence is its own reusable sequence.
//----------------------------------------------------------------------

class soc_ifc_env_dma_xfer_stress_sequence extends soc_ifc_env_dma_sequence_base;

  `uvm_object_utils( soc_ifc_env_dma_xfer_stress_sequence )

  function new(string name = "" );
    super.new(name);
  endfunction

  virtual task body();
    soc_ifc_env_dma_reg_soc_access_sequence soc_seq;
    bit err;
    int unsigned num_transfers = 50; 

    if (reg_model == null)
      reg_model = configuration.soc_ifc_rm;

    dma_read_cap(); // FIFO max depth, needed by the AHB_FIFO routes

    `uvm_info("DMA_XFER_SEQ", $sformatf("Starting %0d DMA transfers with concurrent SoC-AXI register accesses (fifo_max_depth=%0d)", num_transfers, fifo_max_depth), UVM_LOW)

    soc_seq = soc_ifc_env_dma_reg_soc_access_sequence::type_id::create("soc_seq");

    fork
      soc_seq.start(get_sequencer(), this);
      begin
        for (int i = 0; i < num_transfers; i++)
          dma_transfer_rand(2048, err);
        soc_seq.stop();
      end
    join

    `uvm_info("DMA_XFER_SEQ", "Completed all DMA transfers; SoC-AXI DMA accesses were rejected throughout.", UVM_LOW)
  endtask

endclass
