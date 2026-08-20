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
// DESCRIPTION: DMA transfer size and response-delay stress scenario.
//
// Runs constrained-random DMA transfers configured through the firmware-facing
// AHB register map. The sequence varies transfer route/source, FIFO-relative
// size, and the response timing of the SRAM and recovery agents.
//
// Each item is executed by dma_transfer_and_verify(), which prepares source
// data, programs the DUT, waits for completion, and compares the final data.
// Bound assertions independently check response accounting and the subsystem
// outstanding-transaction limits. Functional coverage records observed AXI
// pressure and request/response overlap.
//
// Thin by design: the DMA transaction API lives in soc_ifc_env_dma_sequence_base
// while this sequence owns only stress policy and scenario selection.
//----------------------------------------------------------------------

// Selects transfer-size buckets used by the DMA stress workload.
typedef enum int {
  DMA_STRESS_SIZE_SMALL,
  DMA_STRESS_SIZE_MEDIUM,
  DMA_STRESS_SIZE_MAXIMUM
} dma_stress_size_range_e;

// Runs bounded DMA route, size, and endpoint-delay stress.
class soc_ifc_env_dma_transfer_stress_sequence
  extends soc_ifc_env_dma_sequence_base;

  `uvm_object_utils(soc_ifc_env_dma_transfer_stress_sequence)

  int unsigned num_transfers = 10;
  int unsigned max_transfer_words = 2048;
  bit include_delayed_write_pressure = 1'b1;
  bit randomize_response_delays = 1'b1;
  bit limit_response_delays_to_short = 1'b0;

  // Construct the transfer-stress sequence.
  function new(string name = "soc_ifc_env_dma_transfer_stress_sequence");
    super.new(name);
  endfunction

  // Create one legal item with the full SRAM window and recovery source enabled.
  // Scenario helpers add route and size intent through inline constraints.
  protected function soc_ifc_dma_xfer_item create_stress_item(
      input string name,
      input int unsigned max_transfer_words);
    soc_ifc_dma_xfer_item item;

    item = soc_ifc_dma_xfer_item::type_id::create(name);
    item.configure(configuration.axi_sram_config.base_addr,
                   configuration.axi_sram_config.limit_addr -
                     configuration.axi_sram_config.base_addr + 1,
                   max_transfer_words,
                   configuration.recovery_fifo_config.fifo_data_addr);
    return item;
  endfunction

  // Randomize and execute one ordinary transfer.
  //
  // size_range determines only num_words. The item randomizes one of its five
  // semantic transfer modes directly with equal weights. Addresses, payload,
  // and legal recovery block size remain randomized. Recovery block size is
  // additionally limited by front-FIFO capacity so data_avail never promises
  // an unstorable block.
  protected task run_randomized_transfer_in_size_range(
      input int unsigned max_transfer_words,
      input dma_stress_size_range_e size_range,
      input bit constrain_mode,
      input dma_transfer_mode_e required_mode,
      output bit err);
    soc_ifc_dma_xfer_item item;
    int unsigned small_max;
    int unsigned maximum_min;
    int unsigned range_min;
    int unsigned range_max;
    int unsigned recovery_block_size_limit;

    if (fifo_max_depth == 0)
      `uvm_fatal("DMA_XFER_SEQ",
        "DMA FIFO depth is zero during stress randomization")
    if (max_transfer_words < 4)
      `uvm_fatal("DMA_XFER_SEQ",
        "DMA stress maximum must be at least four words")
    small_max = max_transfer_words / 4;
    if (small_max > (2 * fifo_max_depth))
      small_max = 2 * fifo_max_depth;
    maximum_min = max_transfer_words - small_max;
    item = create_stress_item("stress_item", max_transfer_words);

    case (size_range)
      DMA_STRESS_SIZE_SMALL:
        begin range_min = 1; range_max = small_max; end
      DMA_STRESS_SIZE_MEDIUM:
        begin range_min = small_max + 1; range_max = maximum_min - 1; end
      DMA_STRESS_SIZE_MAXIMUM:
        begin range_min = maximum_min; range_max = max_transfer_words; end
      default:
        `uvm_fatal("DMA_XFER_SEQ",
          $sformatf("Unsupported DMA stress size range %0d", size_range))
    endcase

    // Convert front-FIFO DWORD capacity to the byte units used by the DMA CSR.
    recovery_block_size_limit =
      configuration.recovery_fifo_config.depth_dwords * 4;
    if (recovery_block_size_limit > 64)
      recovery_block_size_limit = 64;
    if (!item.randomize() with {
          num_words inside {[range_min:range_max]};
          if (constrain_mode)
            transfer_mode == required_mode;
          transfer_mode inside {
            DMA_XFER_READ_FIFO,
            DMA_XFER_WRITE_FIFO,
            DMA_XFER_MAILBOX
          } -> num_words <= (2 * fifo_max_depth);
          transfer_mode == DMA_XFER_AXI_RECOVERY ->
            block_size_bytes <= recovery_block_size_limit;
        })
      `uvm_fatal("DMA_XFER_SEQ",
        $sformatf("Failed to randomize DMA transfer in size range %s",
                  size_range.name()))

    `uvm_info("DMA_XFER_SEQ",
      $sformatf("Randomized stress transfer: %s",
                item.convert2string()), UVM_HIGH)
    dma_transfer_and_verify(item, err);
  endtask

  // Exercise DMA completion with a maximum memory-to-memory AXI transfer while
  // B responses are delayed long enough to test the subsystem's two-write
  // outstanding limit and cross the historical four-bit counter boundary if
  // the manager fails to throttle. The read delay remains randomized.
  protected task run_delayed_write_response_pressure_transfer(
      input int unsigned max_transfer_words,
      output bit err);
    soc_ifc_dma_xfer_item item;
    int unsigned b_delay_cycles;
    int unsigned r_delay_cycles;

    if (!std::randomize(b_delay_cycles, r_delay_cycles) with {
          b_delay_cycles inside {[8192:12288]};
          r_delay_cycles inside {[0:3]};
        })
      `uvm_fatal("DMA_XFER_SEQ",
        "Failed to randomize delayed-write response pressure timing")
    configuration.axi_sram_config.set_b_response_delay(
      b_delay_cycles, b_delay_cycles);
    configuration.axi_sram_config.set_r_response_delay(
      r_delay_cycles, r_delay_cycles);
    configuration.recovery_fifo_config.set_r_response_delay(0, 0);
    configuration.recovery_fifo_config.set_refill_delay(0, 0);
    item = create_stress_item("pressure_item", max_transfer_words);
    if (!item.randomize() with {
          num_words == max_transfer_words;
          transfer_mode == DMA_XFER_AXI_MEMORY;
        })
      `uvm_fatal("DMA_XFER_SEQ",
        "Failed to randomize DMA pressure transfer")

    `uvm_info("DMA_XFER_SEQ",
      $sformatf(
        "Starting delayed-write pressure transfer with B delay %0d and R delay %0d: %s",
        b_delay_cycles, r_delay_cycles,
                item.convert2string()), UVM_LOW)
    dma_transfer_and_verify(item, err);
  endtask

  // Run the configured stress workload and restore endpoint delay defaults.
  virtual task body();
    bit err;
    int unsigned b_delay_cycles;
    int unsigned sram_r_delay_cycles;
    int unsigned recovery_r_delay_cycles;
    int unsigned recovery_refill_delay_cycles;
    int unsigned first_random_transfer;
    dma_stress_size_range_e size_range;
    bit constrain_mode;
    dma_transfer_mode_e required_mode;

    if (reg_model == null)
      reg_model = configuration.soc_ifc_rm;
    if (num_transfers == 0)
      `uvm_fatal("DMA_XFER_SEQ",
        "DMA transfer stress requires at least one transfer")

    dma_read_cap(); // FIFO max depth, needed by the AHB_FIFO routes

    `uvm_info("DMA_XFER_SEQ",
      $sformatf(
        "Starting %0d DMA transfers up to %0d words with randomized B/R delays",
        num_transfers, max_transfer_words), UVM_LOW)

    // The optional pressure case consumes one entry from num_transfers so the
    // configured count remains the total workload size.
    first_random_transfer = 0;
    if (include_delayed_write_pressure) begin
      run_delayed_write_response_pressure_transfer(
        max_transfer_words, err);
      first_random_transfer = 1;
    end

    for (int i = first_random_transfer; i < num_transfers; i++) begin
      // Ensure every semantic route appears at least once. Item geometry,
      // payload, addresses, and timing remain randomized in these transfers.
      constrain_mode = (i >= 1) && (i <= 5);
      case (i)
        1: required_mode = DMA_XFER_AXI_RECOVERY;
        2: required_mode = DMA_XFER_READ_FIFO;
        3: required_mode = DMA_XFER_WRITE_FIFO;
        4: required_mode = DMA_XFER_MAILBOX;
        5: required_mode = DMA_XFER_AXI_MEMORY;
        default: required_mode = DMA_XFER_AXI_MEMORY;
      endcase

      // Select a FIFO-relative size bucket here. The item independently
      // randomizes its semantic transfer mode with equal weights.
      if (constrain_mode)
        size_range = DMA_STRESS_SIZE_SMALL;
      else if (!std::randomize(size_range) with {
                 size_range dist {
                   DMA_STRESS_SIZE_SMALL   := 40,
                   DMA_STRESS_SIZE_MEDIUM  := 40,
                   DMA_STRESS_SIZE_MAXIMUM := 20
                 };
               })
        `uvm_fatal("DMA_XFER_SEQ", "Failed to randomize DMA stress size range")
      if (randomize_response_delays) begin
        // Delay values configure live agent policy objects. Setting every
        // channel is intentional because only channels used by the selected
        // transfer mode produce responses.
        if (limit_response_delays_to_short) begin
          if (!std::randomize(b_delay_cycles,
                              sram_r_delay_cycles,
                              recovery_r_delay_cycles,
                              recovery_refill_delay_cycles) with {
                b_delay_cycles inside {[0:127]};
                sram_r_delay_cycles inside {[0:10]};
                recovery_r_delay_cycles inside {[0:10]};
                recovery_refill_delay_cycles inside {[0:10]};
              })
            `uvm_fatal("DMA_XFER_SEQ",
              "Failed to randomize short DMA stress response delays")
        end else begin
          if (!std::randomize(b_delay_cycles,
                              sram_r_delay_cycles,
                              recovery_r_delay_cycles,
                              recovery_refill_delay_cycles) with {
                b_delay_cycles dist {
                  0          := 10,
                  [1:15]     :/ 35,
                  [16:255]   :/ 35,
                  [256:1024] :/ 20
                };
                sram_r_delay_cycles dist {
                  0      := 10,
                  [1:31] :/ 90
                };
                recovery_r_delay_cycles dist {
                  0        := 5,
                  [1:31]   :/ 90,
                  [32:127] :/ 5
                };
                recovery_refill_delay_cycles dist {
                  0        := 10,
                  [1:15]   :/ 50,
                  [16:127] :/ 40
                };
              })
            `uvm_fatal("DMA_XFER_SEQ",
              "Failed to randomize DMA stress response delays")
        end
      end else begin
        b_delay_cycles = 0;
        sram_r_delay_cycles = 0;
        recovery_r_delay_cycles = 0;
        recovery_refill_delay_cycles = 0;
      end
      configuration.axi_sram_config.set_b_response_delay(
        b_delay_cycles, b_delay_cycles);
      configuration.axi_sram_config.set_r_response_delay(
        sram_r_delay_cycles, sram_r_delay_cycles);
      configuration.recovery_fifo_config.set_r_response_delay(
        recovery_r_delay_cycles, recovery_r_delay_cycles);
      configuration.recovery_fifo_config.set_refill_delay(
        recovery_refill_delay_cycles, recovery_refill_delay_cycles);
      run_randomized_transfer_in_size_range(
        max_transfer_words, size_range,
        constrain_mode, required_mode, err);
    end

    // Avoid leaking mutable delay policy into a later sequence in the same test.
    configuration.axi_sram_config.set_b_response_delay(0, 0);
    configuration.axi_sram_config.set_r_response_delay(0, 0);
    configuration.recovery_fifo_config.set_r_response_delay(0, 0);
    configuration.recovery_fifo_config.set_refill_delay(0, 0);
    `uvm_info("DMA_XFER_SEQ",
      "Completed randomized DMA size and response-delay stress", UVM_LOW)
  endtask

endclass
