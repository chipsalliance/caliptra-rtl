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

// Implements the complete testbench endpoint behind the streaming recovery
// interface. It is connected in two directions:
//   * virtual sequences send load/clear/query commands through sequencer/driver;
//   * AXI reads reach the model through the Avery recovery subordinate, where
//     this endpoint requires the streaming protocol's FIXED burst form.
//
// The model owns image and FIFO state, callback validates/prepares Avery reads,
// delay_callback controls R-channel pacing, and this component's run_phase
// observes accepted beats and schedules producer refills. soc_ifc_environment
// binds all three services to the same Avery subordinate during connect_phase.
class soc_ifc_recovery_fifo_agent extends uvm_agent;

  `uvm_component_utils(soc_ifc_recovery_fifo_agent)

  soc_ifc_recovery_fifo_config configuration;
  soc_ifc_recovery_fifo_model model;
  soc_ifc_recovery_fifo_callback callback;
  soc_ifc_axi_response_delay_callback delay_callback;
  soc_ifc_recovery_fifo_sequencer sequencer;
  soc_ifc_recovery_fifo_driver driver;

  bit refill_pending;                  // A drained chunk awaits restaging.
  bit reset_active;                    // Prevents repeated clear during reset.
  int unsigned refill_cycles_remaining;// Countdown to the next staged chunk.
  int unsigned refill_elapsed_cycles;  // Independent check of selected delay.
  int unsigned refill_count;           // Number of completed delayed refills.
  int unsigned selected_refill_delay;  // Policy sample for current countdown.
  int unsigned observed_generation;    // Detects model changes from other processes.

  // Sample actual agent state on each recovery clock. Coverage distinguishes
  // final chunks, refill events, availability transitions, and underflow while
  // runtime checks below enforce the corresponding invariants.
  covergroup recovery_fifo_cg with function sample(
      bit image_complete,
      bit final_chunk_staged,
      bit recovery_data_avail,
      bit recovery_image_activated,
      bit read_beat,
      bit refill_event,
      bit underflow,
      int unsigned refill_delay);
    option.per_instance = 1;
    image_complete_cp: coverpoint image_complete;
    final_chunk_cp: coverpoint final_chunk_staged;
    data_avail_cp: coverpoint recovery_data_avail;
    image_activated_cp: coverpoint recovery_image_activated;
    read_beat_cp: coverpoint read_beat;
    refill_event_cp: coverpoint refill_event;
    underflow_cp: coverpoint underflow;
    refill_delay_cp: coverpoint refill_delay {
      bins zero = {0};
      bins short_delay = {[1:10]};
      bins long_delay = {[11:$]};
    }
    availability_cross: cross final_chunk_cp, data_avail_cp,
                             read_beat_cp;
  endgroup

  // Construct the recovery FIFO agent and its coverage model.
  function new(string name = "soc_ifc_recovery_fifo_agent",
               uvm_component parent = null);
    super.new(name, parent);
    recovery_fifo_cg = new();
  endfunction

  // Store the shared endpoint configuration before build_phase. The fabric
  // consumes this same object for address routing, while this agent consumes
  // FIFO geometry, sideband interface, and delay policies.
  function void set_config(soc_ifc_recovery_fifo_config configuration);
    this.configuration = configuration;
  endfunction

  // Build the complete active recovery agent: item path, image/FIFO model,
  // protocol callback, response-delay callback, and coverage state.
  // No Avery queue is registered until bind_bfm() receives the subordinate.
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (configuration == null)
      `uvm_fatal("RECOVERY_FIFO", "Recovery FIFO configuration is null")
    model = soc_ifc_recovery_fifo_model::type_id::create("model");
    model.configure(configuration);
    observed_generation = model.generation;
    callback =
      soc_ifc_recovery_fifo_callback::type_id::create("callback");
    callback.model = model;
    delay_callback =
      soc_ifc_axi_response_delay_callback::type_id::create(
        "delay_callback");
    delay_callback.r_delay = configuration.r_delay;
    sequencer =
      soc_ifc_recovery_fifo_sequencer::type_id::create(
        "sequencer", this);
    driver =
      soc_ifc_recovery_fifo_driver::type_id::create("driver", this);
    driver.model = model;
  endfunction

  // Connect only the item request path. Model and callback relationships are
  // direct agent-owned handles because they are private implementation details,
  // not transaction streams.
  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    driver.seq_item_port.connect(sequencer.seq_item_export);
  endfunction

  // Register the model's finite front FIFO with the Avery subordinate used by
  // the DUT DMA. Callback registration remains in soc_ifc_environment because
  // it is a cross-component connection rather than model initialization.
  function void bind_bfm(aaxi_device_class bfm);
    model.bind_bfm(bfm);
    `uvm_info("RECOVERY_FIFO",
      $sformatf(
        "Bound recovery FIFO at 0x%0h with front depth %0d DWORDs",
        configuration.fifo_data_addr,
        configuration.depth_dwords), UVM_LOW)
  endfunction

  // A load, clear, or reset increments the model generation and invalidates any
  // countdown selected for the prior image. Canceling here prevents stale data
  // from being staged after a new operation replaces agent state.
  protected function void cancel_pending_refill();
    refill_pending = 1'b0;
    refill_cycles_remaining = 0;
    refill_elapsed_cycles = 0;
    selected_refill_delay = 0;
  endfunction

  // Complete a scheduled refill by moving the next model chunk into Avery.
  // Compare an elapsed counter with the countdown selection so off-by-one
  // errors in zero, fixed, and random delay handling are caught where timing is
  // implemented rather than hidden in the storage model.
  protected function bit refill_front_fifo();
    int unsigned staged_dwords;
    if (refill_elapsed_cycles != selected_refill_delay)
      `uvm_error("RECOVERY_FIFO",
        $sformatf(
          "Recovery refill used %0d delay cycles, expected %0d",
          refill_elapsed_cycles, selected_refill_delay))
    staged_dwords = model.stage_next_chunk();
    if (staged_dwords == 0)
      `uvm_error("RECOVERY_FIFO",
        "Refill was requested with no backing image data")
    refill_pending = 1'b0;
    refill_cycles_remaining = 0;
    refill_count++;
    return staged_dwords != 0;
  endfunction

  // Observe recovery-clock activity continuously. Avery callbacks run in the
  // subordinate's transaction processes, so this clocked loop is responsible
  // for the separate RVALID/RREADY acceptance event and for turning a drained
  // front chunk into a refill after the configured producer delay.
  virtual task run_phase(uvm_phase phase);
    bit read_beat;
    bit refill_event;
    bit front_fifo_emptied;

    forever begin
      @(posedge configuration.vif.clk);
      read_beat = 1'b0;
      refill_event = 1'b0;
      front_fifo_emptied = 1'b0;

      if (!configuration.vif.rst_n) begin
        // Clear once on reset entry. Re-clearing every reset cycle would keep
        // changing generation and obscure whether a real command replaced data.
        if (!reset_active)
          model.clear();
        reset_active = 1'b1;
        observed_generation = model.generation;
        cancel_pending_refill();
      end else begin
        reset_active = 1'b0;
        // Driver commands execute in a separate UVM process and can update
        // generation between clock edges. Detect that change before processing
        // pending countdown state.
        if (observed_generation != model.generation) begin
          observed_generation = model.generation;
          cancel_pending_refill();
        end

        // Occupancy changes only on an accepted R beat, never on RVALID alone.
        // The callback has already lowered availability if this is the final
        // staged beat.
        if (model.bfm.ports.RVALID && model.bfm.ports.RREADY) begin
          read_beat = 1'b1;
          if (model.front_fifo_dwords_available == 1 &&
              configuration.vif.recovery_data_avail !== 1'b0)
            `uvm_error("RECOVERY_FIFO",
              "recovery_data_avail was high at final staged R handshake")
          front_fifo_emptied = model.note_read_beat_handshake();
          if (front_fifo_emptied &&
              model.backing_dwords_remaining() != 0) begin
            // Select a new delay per drained chunk. This models an independently
            // paced recovery producer rather than AXI R-channel backpressure.
            selected_refill_delay =
              configuration.refill_delay.next_delay();
            refill_elapsed_cycles = 0;
            if (selected_refill_delay == 0)
              refill_event = refill_front_fifo();
            else begin
              refill_pending = 1'b1;
              refill_cycles_remaining = selected_refill_delay;
            end
          end
        end else if (refill_pending) begin
          // Delay starts on the cycle after the emptying handshake. A selected
          // zero delay is handled in the handshake branch and never enters this
          // countdown path.
          refill_elapsed_cycles++;
          if (refill_cycles_remaining == 1)
            refill_event = refill_front_fifo();
          else
            refill_cycles_remaining--;
        end

        if (configuration.vif.recovery_data_avail &&
            model.front_fifo_empty())
          `uvm_error("RECOVERY_FIFO",
            "recovery_data_avail asserted while front FIFO is empty")
        if (configuration.vif.recovery_image_activated !==
            model.final_chunk_staged)
          `uvm_error("RECOVERY_FIFO",
            "recovery_image_activated did not match final chunk state")
        if (model.front_fifo_dwords_available >
            configuration.depth_dwords)
          `uvm_error("RECOVERY_FIFO",
            "Front FIFO occupancy exceeded configured depth")
      end

      recovery_fifo_cg.sample(
        model.image_complete(),
        model.final_chunk_staged,
        configuration.vif.recovery_data_avail,
        configuration.vif.recovery_image_activated,
        read_beat,
        refill_event,
        model.underflow_reported,
        selected_refill_delay);
    end
  endtask

  // Report incomplete endpoint state at test end. This checker treats any
  // loaded recovery image as expected to be fully consumed before the test ends.
  virtual function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    // Tests using this agent must consume every loaded image. These end-state
    // checks replace sequence-side peeks into model internals and identify
    // recovery scenarios that leave stale state behind.
    if (refill_pending)
      `uvm_error("RECOVERY_FIFO",
        "Test ended with a recovery refill pending")
    if (configuration.vif.recovery_data_avail !== 1'b0)
      `uvm_error("RECOVERY_FIFO",
        "Test ended with recovery_data_avail asserted")
    if (!model.image_complete())
      `uvm_error("RECOVERY_FIFO",
        $sformatf("Test ended with %0d recovery DWORDs remaining",
                  model.image_dwords_remaining()))
  endfunction

endclass
