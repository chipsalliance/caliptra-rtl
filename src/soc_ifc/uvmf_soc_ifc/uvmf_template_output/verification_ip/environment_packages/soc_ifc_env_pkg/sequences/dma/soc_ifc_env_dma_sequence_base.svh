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
// DESCRIPTION: Reusable base for soc_ifc AXI DMA environment sequences.
//
// Provides the DMA transaction API (arm/status/fifo/mbox helpers,
// dma_transfer_and_verify, dma_transfer_rand) for derived DMA sequences. SRAM
// agent access goes through the virtual sequencer, so no agent hierarchy
// or vendor backend is hard-coded here.
//----------------------------------------------------------------------

// Provides reusable DMA programming, storage access, and data checking.
class soc_ifc_env_dma_sequence_base
  extends soc_ifc_env_sequence_base #(
    .CONFIG_T(soc_ifc_env_configuration_t)
  );

  `uvm_object_utils( soc_ifc_env_dma_sequence_base )

  // DMA internal FIFO max depth (in words), read once from cap.fifo_max_depth.
  protected int unsigned fifo_max_depth;

  // Running count of transfers issued, used for log/error context.
  protected int unsigned transfer_id;

  // Mode of the transfer currently using the shared polling helpers.
  protected dma_transfer_mode_e active_transfer_mode;

  // Runtime coordination point used to reach agent-owned item sequencers
  // without storing component handles in configuration.
  protected soc_ifc_virtual_sequencer active_vsqr;

  // Construct the reusable DMA sequence base.
  function new(string name = "" );
    super.new(name);
  endfunction

  // Establish configuration and typed access to both storage-agent sequencers.
  // Every DMA route uses at least one agent for source setup or destination
  // checking, so missing either alias is a construction error.
  virtual task pre_body();
    super.pre_body();
    if (!$cast(active_vsqr, m_sequencer))
      `uvm_fatal("DMA_SEQ_BASE",
        "DMA virtual sequence must run on soc_ifc_virtual_sequencer")
    reg_model = configuration.soc_ifc_rm;
    if (active_vsqr.axi_sram_sequencer == null)
      `uvm_fatal("DMA_SEQ_BASE",
        "AXI SRAM agent sequencer is null")
    if (active_vsqr.recovery_fifo_sequencer == null)
      `uvm_fatal("DMA_SEQ_BASE",
        "Recovery FIFO agent sequencer is null")
  endtask

  // Write one DWORD at a byte offset relative to the SRAM base. The helper
  // blocks until the SRAM driver updates Avery memory; it does not generate DUT
  // AXI traffic.
  virtual task axi_sram_write32(input longint unsigned offset,
                                input bit [31:0] data);
    soc_ifc_axi_sram_access_sequence seq;
    seq = soc_ifc_axi_sram_access_sequence::type_id::create(
      "axi_sram_write_seq");
    seq.operation = AXI_SRAM_WRITE;
    seq.offset = offset;
    seq.data = data;
    seq.start(active_vsqr.axi_sram_sequencer);
  endtask

  // Read one DWORD from the shared Avery SRAM memory after earlier item
  // operations complete. The response returns through the SRAM item path.
  virtual task axi_sram_read32(input longint unsigned offset,
                               output bit [31:0] data);
    soc_ifc_axi_sram_access_sequence seq;
    seq = soc_ifc_axi_sram_access_sequence::type_id::create(
      "axi_sram_read_seq");
    seq.operation = AXI_SRAM_READ;
    seq.offset = offset;
    seq.start(active_vsqr.axi_sram_sequencer);
    data = seq.data;
  endtask

  // Replace recovery-agent contents with one complete image. block_size_bytes
  // is the same byte unit programmed into the DMA CSR; the agent derives DWORD
  // staging thresholds and final-partial behavior.
  virtual task recovery_fifo_load_image(
      input bit [31:0] payload[],
      input int unsigned block_size_bytes);
    soc_ifc_recovery_fifo_command_sequence seq;
    seq = soc_ifc_recovery_fifo_command_sequence::type_id::create(
      "recovery_fifo_load_image_seq");
    seq.operation = RECOVERY_FIFO_LOAD_IMAGE;
    seq.payload = payload;
    seq.block_size_bytes = block_size_bytes;
    seq.start(active_vsqr.recovery_fifo_sequencer);
  endtask

  //==========================================
  // DMA register API (uC / AHB side).
  //==========================================
  // Read cap.fifo_max_depth in data-width words. AHB FIFO push/pop flow control
  // and FIFO-relative stress ranges use this capability rather than duplicating
  // the RTL depth as a testbench constant.
  virtual task dma_read_cap();
    uvm_status_e   sts;
    uvm_reg_data_t cap_val;
    reg_model.axi_dma_reg_rm.cap.read(sts, cap_val, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    fifo_max_depth = int'((cap_val >> reg_model.axi_dma_reg_rm.cap.fifo_max_depth.get_lsb_pos()) &
                          ((1 << reg_model.axi_dma_reg_rm.cap.fifo_max_depth.get_n_bits()) - 1));
    if (fifo_max_depth == 0) begin
      `uvm_fatal("DMA_SEQ_BASE",
        "cap.fifo_max_depth read as 0; this is not expected")
    end
    `uvm_info("DMA_SEQ_BASE",
      $sformatf("DMA capability reports FIFO depth %0d words",
                fifo_max_depth), UVM_LOW)
  endtask

  // Program one DMA operation over the firmware-facing AHB RAL map. Addresses
  // and byte_count/block_size are byte units; route values are RDL enum
  // encodings. ctrl is written last so go observes a complete configuration.
  // This task starts the operation but does not wait for completion.
  virtual task dma_arm(input bit [63:0] src_addr,
                       input bit [63:0] dst_addr,
                       input int unsigned byte_count,
                       input int unsigned block_size_bytes,
                       input bit [1:0]  rd_route,
                       input bit [2:0]  wr_route,
                       input bit        rd_fixed = 1'b0,
                       input bit        wr_fixed = 1'b0);
    uvm_status_e   sts;
    uvm_reg_data_t ctrl_val;
    reg_model.axi_dma_reg_rm.src_addr_l.write(sts, src_addr[31:0],  UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    reg_model.axi_dma_reg_rm.src_addr_h.write(sts, src_addr[63:32], UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    reg_model.axi_dma_reg_rm.dst_addr_l.write(sts, dst_addr[31:0],  UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    reg_model.axi_dma_reg_rm.dst_addr_h.write(sts, dst_addr[63:32], UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    reg_model.axi_dma_reg_rm.byte_count.write(sts, byte_count,      UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    reg_model.axi_dma_reg_rm.block_size.write(sts, block_size_bytes, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    // Compose ctrl (go=1 + routes, all other fields 0) from RAL field positions and
    // issue one explicit write. Explicit compose (vs set()/update()) is deterministic
    // and avoids re-writing any stale desired state in other ctrl fields.
    ctrl_val = (uvm_reg_data_t'(1)        << reg_model.axi_dma_reg_rm.ctrl.go.get_lsb_pos())       |
               (uvm_reg_data_t'(rd_route) << reg_model.axi_dma_reg_rm.ctrl.rd_route.get_lsb_pos()) |
               (uvm_reg_data_t'(wr_route) << reg_model.axi_dma_reg_rm.ctrl.wr_route.get_lsb_pos()) |
               (uvm_reg_data_t'(rd_fixed) << reg_model.axi_dma_reg_rm.ctrl.rd_fixed.get_lsb_pos()) |
               (uvm_reg_data_t'(wr_fixed) << reg_model.axi_dma_reg_rm.ctrl.wr_fixed.get_lsb_pos());
    reg_model.axi_dma_reg_rm.ctrl.write(sts, ctrl_val, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
  endtask

  // Recover the DMA from a sticky DMA_ERROR state before a new scenario.
  // ctrl.flush resets the FSM and internal FIFO and self-clears; issuing it while
  // idle is intentional so every transfer starts from the same state.
  virtual task dma_flush();
    uvm_status_e   sts;
    uvm_reg_data_t ctrl_val;
    ctrl_val = (uvm_reg_data_t'(1) << reg_model.axi_dma_reg_rm.ctrl.flush.get_lsb_pos());
    reg_model.axi_dma_reg_rm.ctrl.write(sts, ctrl_val, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
  endtask

  // Read status0 over AHB and decode the value observed from the DUT. busy and
  // error describe operation state; fifo_depth is populated data-width words.
  // Field locations come from RAL rather than duplicated bit constants.
  virtual task dma_read_status(output bit busy, output bit err, output int unsigned fifo_depth);
    uvm_status_e   sts;
    uvm_reg_data_t d;
    reg_model.axi_dma_reg_rm.status0.read(sts, d, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    busy       = d[reg_model.axi_dma_reg_rm.status0.busy.get_lsb_pos()];
    err        = d[reg_model.axi_dma_reg_rm.status0.error.get_lsb_pos()];
    fifo_depth = int'((d >> reg_model.axi_dma_reg_rm.status0.fifo_depth.get_lsb_pos()) &
                      ((1 << reg_model.axi_dma_reg_rm.status0.fifo_depth.get_n_bits()) - 1));
  endtask

  // Select a bounded checkpoint interval for a status-poll budget.
  protected function int unsigned dma_poll_progress_interval(
      input int unsigned max_polls);
    if (max_polls == 0)
      return 10000;
    return ((max_polls / 50) + ((max_polls % 50) != 0));
  endfunction

  // Report ten coarse milestones for long word-processing loops.
  protected function void dma_report_word_progress(
      input string operation,
      input int unsigned completed_words,
      input int unsigned total_words);
    int unsigned interval;

    if (total_words < 100)
      return;
    interval = (total_words + 9) / 10;
    if ((completed_words < total_words) &&
        ((completed_words % interval) == 0))
      `uvm_info("DMA_XFER_PROGRESS",
        $sformatf(
          "Transfer %0d mode=%s: %s progress %0d/%0d words; continuing",
          transfer_id, active_transfer_mode.name(), operation,
          completed_words, total_words), UVM_LOW)
  endfunction

  // Derive a conservative status-poll budget from transfer size and the live
  // endpoint delay policies. The safety factor covers AXI handshakes, AHB
  // polling overhead, and route-specific control latency.
  protected function int unsigned dma_transfer_max_polls(
      input soc_ifc_dma_xfer_item item);
    longint unsigned num_words;
    longint unsigned read_delay_cycles;
    longint unsigned write_delay_cycles;
    longint unsigned refill_delay_cycles;
    longint unsigned write_bursts;
    longint unsigned refill_events;
    longint unsigned estimated_cycles;
    longint unsigned poll_budget;

    num_words = item.num_words;
    read_delay_cycles = 0;
    write_delay_cycles = 0;
    refill_delay_cycles = 0;

    case (item.transfer_mode)
      DMA_XFER_AXI_MEMORY,
      DMA_XFER_READ_FIFO,
      DMA_XFER_MAILBOX:
        read_delay_cycles = configuration.axi_sram_config.r_delay.max_cycles;
      DMA_XFER_AXI_RECOVERY:
        begin
          read_delay_cycles =
            configuration.recovery_fifo_config.r_delay.max_cycles;
          refill_delay_cycles =
            configuration.recovery_fifo_config.refill_delay.max_cycles;
        end
      default: begin end
    endcase

    case (item.transfer_mode)
      DMA_XFER_AXI_MEMORY,
      DMA_XFER_AXI_RECOVERY,
      DMA_XFER_WRITE_FIFO,
      DMA_XFER_MAILBOX:
        write_delay_cycles = configuration.axi_sram_config.b_delay.max_cycles;
      default: begin end
    endcase

    write_bursts = (num_words + 63) / 64;
    refill_events = 0;
    if (item.transfer_mode == DMA_XFER_AXI_RECOVERY)
      refill_events =
        ((num_words * 4) +
         (configuration.recovery_fifo_config.depth_dwords * 4) - 1) /
        (configuration.recovery_fifo_config.depth_dwords * 4);

    estimated_cycles =
      2_048 +
      (num_words * (read_delay_cycles + 2)) +
      (write_bursts * (write_delay_cycles + 64)) +
      (refill_events * (refill_delay_cycles + 64));
    poll_budget = estimated_cycles * 4;
    if (poll_budget > 32'hffff_ffff)
      return 32'hffff_ffff;
    return int'(poll_budget);
  endfunction

  // Poll status0 until the DMA becomes idle or reports an error. Zero preserves
  // unlimited polling for callers that do not require a local timeout.
  virtual task dma_wait_idle(output bit err,
                             input int unsigned max_polls = 0);
    bit busy;
    int unsigned fd;
    int unsigned poll_count;
    int unsigned progress_interval;
    poll_count = 0;
    progress_interval = dma_poll_progress_interval(max_polls);
    `uvm_info("DMA_XFER_PROGRESS",
      $sformatf(
        "Transfer %0d mode=%s: entering DMA idle wait with max_status_polls=%0d",
        transfer_id, active_transfer_mode.name(), max_polls), UVM_LOW)
    do begin
      dma_read_status(busy, err, fd);
      poll_count++;
      if (busy &&
          !err &&
          ((poll_count % progress_interval) == 0))
        `uvm_info("DMA_XFER_PROGRESS",
          $sformatf(
            "Transfer %0d mode=%s: DMA still busy after %0d/%0d status polls (fifo_depth=%0d)",
            transfer_id, active_transfer_mode.name(), poll_count, max_polls,
            fd), UVM_LOW)
      if (busy &&
          !err &&
          max_polls != 0 &&
          poll_count >= max_polls)
        `uvm_fatal("DMA_XFER_TIMEOUT",
          $sformatf(
            "DMA transfer %0d remained busy after %0d status polls (fifo_depth=%0d)",
            transfer_id, poll_count, fd))
    end while (busy && !err);
    `uvm_info("DMA_XFER_PROGRESS",
      $sformatf(
        "Transfer %0d mode=%s: DMA idle wait exited after %0d status polls (busy=%0b error=%0b fifo_depth=%0d)",
        transfer_id, active_transfer_mode.name(), poll_count, busy, err, fd),
      UVM_LOW)
    // Detection only; callers are the contextual error reporter.
  endtask

  // Push one DWORD through the firmware write_data register for
  // wr_route=AHB_FIFO. Polling provides backpressure when the FIFO is full.
  // On DMA error, return without writing and propagate err to the caller.
  virtual task dma_fifo_push(input bit [31:0] data,
                             output bit err,
                             input int unsigned max_polls = 0);
    uvm_status_e sts;
    bit busy;
    int unsigned fd;
    int unsigned poll_count;
    err = 1'b0;
    poll_count = 0;
    // Wait until the FIFO has room (depth != max), aborting on a DMA error.
    do begin
      dma_read_status(busy, err, fd);
      if (err) return;
      poll_count++;
      if (fd == fifo_max_depth &&
          max_polls != 0 &&
          poll_count >= max_polls)
        `uvm_fatal("DMA_XFER_TIMEOUT",
          $sformatf(
            "DMA transfer %0d FIFO push remained blocked after %0d status polls",
            transfer_id, poll_count))
    end while (fd == fifo_max_depth);
    reg_model.axi_dma_reg_rm.write_data.write(sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
  endtask

  // Pop one DWORD through the firmware read_data register for
  // rd_route=AHB_FIFO. Polling waits for nonempty status before reading.
  // On DMA error, return zero data and propagate err to the caller.
  virtual task dma_fifo_pop(output bit [31:0] data,
                            output bit err,
                            input int unsigned max_polls = 0);
    uvm_status_e   sts;
    uvm_reg_data_t d;
    bit busy;
    int unsigned fd;
    int unsigned poll_count;
    err  = 1'b0;
    data = '0;
    poll_count = 0;
    // Wait until the FIFO has data (depth != 0), aborting on a DMA error.
    do begin
      dma_read_status(busy, err, fd);
      if (err) return;
      poll_count++;
      if (fd == 0 &&
          max_polls != 0 &&
          poll_count >= max_polls)
        `uvm_fatal("DMA_XFER_TIMEOUT",
          $sformatf(
            "DMA transfer %0d FIFO pop remained blocked after %0d status polls",
            transfer_id, poll_count))
    end while (fd == 0);
    reg_model.axi_dma_reg_rm.read_data.read(sts, d, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    data = d[31:0];
  endtask

  // Acquire the mailbox lock for the microcontroller over AHB. Reading mbox_lock
  // returns zero and atomically grants a previously free lock. DMA mailbox
  // routes require this ownership; ok is false when another requester owns it.
  virtual task dma_mbox_lock_acquire(output bit ok);
    uvm_status_e   sts;
    uvm_reg_data_t d;
    reg_model.mbox_csr_rm.mbox_lock.read(sts, d, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    ok = (d[0] == 1'b0);
  endtask

  // Release the microcontroller mailbox lock after both directions of a mailbox
  // round trip, including error exits that acquired the lock successfully.
  virtual task dma_mbox_unlock();
    uvm_status_e sts;
    reg_model.mbox_csr_rm.mbox_unlock.write(sts, 1, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
  endtask

  // Execute and self-check one previously randomized transfer item. The task
  // prepares source storage, flushes sticky DMA state, programs the selected
  // route, waits for completion, and compares destination data. Protocol or DMA
  // errors are reported with route context and returned through err.
  virtual task dma_transfer_and_verify(input  soc_ifc_dma_xfer_item item,
                                       output bit                   err);
    int unsigned num_words;
    int unsigned byte_count;
    localparam bit [63:0] mbox_addr = 64'h0;
    bit [63:0]   src_addr;
    bit [63:0]   dst_addr;
    bit [31:0]   rd_data;
    bit          lock_ok;
    int unsigned max_polls;
    int unsigned mismatch_count;
    int unsigned first_mismatch_word;
    bit [31:0]   first_mismatch_data;

    if (item == null)
      `uvm_fatal("DMA_XFER_SEQ",
        "dma_transfer_and_verify received a null item")
    err       = 1'b0;
    num_words = item.payload.size();
    src_addr  = item.src_addr();
    dst_addr  = item.dst_addr();
    if (num_words == 0) begin
      `uvm_fatal("DMA_XFER_SEQ", "dma_transfer_and_verify called with empty payload")
    end
    if (item.num_words != num_words)
      `uvm_fatal("DMA_XFER_SEQ",
        $sformatf("Item num_words=%0d but payload contains %0d words",
                  item.num_words, num_words))
    byte_count = num_words * 4;
    max_polls = dma_transfer_max_polls(item);
    transfer_id++;
    active_transfer_mode = item.transfer_mode;
    mismatch_count = 0;

    `uvm_info("DMA_XFER_SEQ",
      $sformatf(
        "Preparing DMA transfer %0d mode=%s words=%0d bytes=%0d max_status_polls=%0d",
        transfer_id, item.transfer_mode.name(), num_words, byte_count,
        max_polls), UVM_LOW)

    // Start each transfer from a clean DMA state so a prior transfer's error
    // (status0.error / DMA_ERROR, which is sticky until flushed) cannot cascade
    // into this one and mask/inflate the real failure count.
    dma_flush();

    case (item.transfer_mode)
      DMA_XFER_AXI_MEMORY: begin
        // Source SRAM -> DMA -> destination SRAM, both through AXI.
        `uvm_info("DMA_XFER_SEQ",
          $sformatf(
            "Transfer %0d: preloading %0d source SRAM words",
            transfer_id, num_words), UVM_LOW)
        for (int w = 0; w < num_words; w++) begin
          axi_sram_write32(item.src_offset + (w*4), item.payload[w]);
          dma_report_word_progress("source SRAM preload", w + 1, num_words);
        end
        `uvm_info("DMA_XFER_SEQ",
          $sformatf(
            "Transfer %0d: source preload complete; arming AXI-to-AXI DMA and polling status0",
            transfer_id), UVM_LOW)
        dma_arm(src_addr, dst_addr, byte_count,
                0,
                axi_dma_reg__ctrl__rd_route__rd_route_e__AXI_WR,
                axi_dma_reg__ctrl__wr_route__wr_route_e__AXI_RD);
        dma_wait_idle(err, max_polls);
        if (err) begin
          `uvm_error("DMA_XFER_SEQ",
            $sformatf("DMA error during transfer %0d mode=%s",
                      transfer_id, item.transfer_mode.name()))
          return;
        end
        `uvm_info("DMA_XFER_SEQ",
          $sformatf(
            "Transfer %0d: DMA idle; reading back %0d destination words",
            transfer_id, num_words), UVM_LOW)
        for (int w = 0; w < num_words; w++) begin
          axi_sram_read32(item.dst_offset + (w*4), rd_data);
          if (rd_data !== item.payload[w]) begin
            if (mismatch_count == 0) begin
              first_mismatch_word = w;
              first_mismatch_data = rd_data;
            end
            mismatch_count++;
          end
          dma_report_word_progress(
            "destination SRAM readback", w + 1, num_words);
        end
        if (mismatch_count != 0)
          `uvm_error("DMA_XFER_SEQ",
            $sformatf("AXI2AXI xfer %0d had %0d/%0d data mismatches; first at word %0d: exp=0x%08x got=0x%08x",
                      transfer_id, mismatch_count, num_words,
                      first_mismatch_word, item.payload[first_mismatch_word],
                      first_mismatch_data))
      end
      DMA_XFER_AXI_RECOVERY: begin
        // Recovery FIFO -> DMA -> destination SRAM. The fixed source address,
        // block size, and availability handshake model the recovery interface.
        `uvm_info("DMA_XFER_SEQ",
          $sformatf(
            "Transfer %0d: loading %0d recovery words in %0d-byte blocks",
            transfer_id, num_words, item.block_size_bytes), UVM_LOW)
        recovery_fifo_load_image(item.payload, item.block_size_bytes);
        `uvm_info("DMA_XFER_SEQ",
          $sformatf(
            "Transfer %0d: recovery image loaded; arming recovery-to-SRAM DMA and polling status0",
            transfer_id), UVM_LOW)
        dma_arm(src_addr, dst_addr, byte_count,
                item.block_size_bytes,
                axi_dma_reg__ctrl__rd_route__rd_route_e__AXI_WR,
                axi_dma_reg__ctrl__wr_route__wr_route_e__AXI_RD,
                item.read_is_fixed());
        dma_wait_idle(err, max_polls);
        if (err) begin
          `uvm_error("DMA_XFER_SEQ",
            $sformatf("DMA error during transfer %0d mode=%s",
                      transfer_id, item.transfer_mode.name()))
          return;
        end
        `uvm_info("DMA_XFER_SEQ",
          $sformatf(
            "Transfer %0d: DMA idle; reading back %0d destination words",
            transfer_id, num_words), UVM_LOW)
        for (int w = 0; w < num_words; w++) begin
          axi_sram_read32(item.dst_offset + (w*4), rd_data);
          if (rd_data !== item.payload[w]) begin
            if (mismatch_count == 0) begin
              first_mismatch_word = w;
              first_mismatch_data = rd_data;
            end
            mismatch_count++;
          end
        end
        if (mismatch_count != 0)
          `uvm_error("DMA_XFER_SEQ",
            $sformatf("Recovery xfer %0d had %0d/%0d data mismatches; first at word %0d: exp=0x%08x got=0x%08x",
                      transfer_id, mismatch_count, num_words,
                      first_mismatch_word, item.payload[first_mismatch_word],
                      first_mismatch_data))
      end
      DMA_XFER_READ_FIFO: begin
        // Source SRAM -> DMA FIFO; uC pops each word over AHB and compares.
        `uvm_info("DMA_XFER_SEQ",
          $sformatf(
            "Transfer %0d: preloading %0d source words before AHB FIFO reads",
            transfer_id, num_words), UVM_LOW)
        for (int w = 0; w < num_words; w++)
          axi_sram_write32(item.src_offset + (w*4), item.payload[w]);
        `uvm_info("DMA_XFER_SEQ",
          $sformatf(
            "Transfer %0d: DMA armed; popping and checking %0d AHB FIFO words",
            transfer_id, num_words), UVM_LOW)
        dma_arm(src_addr, 64'h0, byte_count, 0,
                axi_dma_reg__ctrl__rd_route__rd_route_e__AHB_FIFO,
                axi_dma_reg__ctrl__wr_route__wr_route_e__DISABLE);
        for (int w = 0; w < num_words; w++) begin
          dma_fifo_pop(rd_data, err, max_polls);
          if (err) begin
            `uvm_error("DMA_XFER_SEQ",
              $sformatf("DMA error during transfer %0d mode=%s",
                        transfer_id, item.transfer_mode.name()))
            return;
          end
          if (rd_data !== item.payload[w])
            `uvm_error("DMA_XFER_SEQ", $sformatf("RD_FIFO xfer %0d word %0d mismatch: exp=0x%08x got=0x%08x", transfer_id, w, item.payload[w], rd_data))
        end
        `uvm_info("DMA_XFER_SEQ",
          $sformatf(
            "Transfer %0d: all AHB FIFO words checked; waiting for DMA idle",
            transfer_id), UVM_LOW)
        dma_wait_idle(err, max_polls);
        if (err) begin
          `uvm_error("DMA_XFER_SEQ",
            $sformatf("DMA error during transfer %0d mode=%s",
                      transfer_id, item.transfer_mode.name()))
          return;
        end
      end
      DMA_XFER_WRITE_FIFO: begin
        // uC pushes each word over AHB into the DMA FIFO -> destination SRAM.
        `uvm_info("DMA_XFER_SEQ",
          $sformatf(
            "Transfer %0d: arming DMA and pushing %0d AHB FIFO words",
            transfer_id, num_words), UVM_LOW)
        dma_arm(64'h0, dst_addr, byte_count, 0,
                axi_dma_reg__ctrl__rd_route__rd_route_e__DISABLE,
                axi_dma_reg__ctrl__wr_route__wr_route_e__AHB_FIFO);
        for (int w = 0; w < num_words; w++) begin
          dma_fifo_push(item.payload[w], err, max_polls);
          if (err) begin
            `uvm_error("DMA_XFER_SEQ",
              $sformatf("DMA error during transfer %0d mode=%s",
                        transfer_id, item.transfer_mode.name()))
            return;
          end
        end
        `uvm_info("DMA_XFER_SEQ",
          $sformatf(
            "Transfer %0d: all AHB FIFO words submitted; waiting for DMA idle",
            transfer_id), UVM_LOW)
        dma_wait_idle(err, max_polls);
        if (err) begin
          `uvm_error("DMA_XFER_SEQ",
            $sformatf("DMA error during transfer %0d mode=%s",
                      transfer_id, item.transfer_mode.name()))
          return;
        end
        `uvm_info("DMA_XFER_SEQ",
          $sformatf(
            "Transfer %0d: DMA idle; reading back %0d destination words",
            transfer_id, num_words), UVM_LOW)
        for (int w = 0; w < num_words; w++) begin
          axi_sram_read32(item.dst_offset + (w*4), rd_data);
          if (rd_data !== item.payload[w])
            `uvm_error("DMA_XFER_SEQ", $sformatf("WR_FIFO xfer %0d word %0d mismatch: exp=0x%08x got=0x%08x", transfer_id, w, item.payload[w], rd_data))
        end
      end
      DMA_XFER_MAILBOX: begin
        // Mailbox round-trip under one uC lock: src SRAM -> mailbox (rd MBOX),
        // then mailbox -> dst SRAM (wr MBOX).
        `uvm_info("DMA_XFER_SEQ",
          $sformatf(
            "Transfer %0d: acquiring mailbox lock and preloading %0d source words",
            transfer_id, num_words), UVM_LOW)
        dma_mbox_lock_acquire(lock_ok);
        if (!lock_ok) begin
          `uvm_error("DMA_XFER_SEQ", $sformatf("Failed to acquire mailbox lock for xfer %0d", transfer_id))
          return;
        end
        for (int w = 0; w < num_words; w++)
          axi_sram_write32(item.src_offset + (w*4), item.payload[w]);
        `uvm_info("DMA_XFER_SEQ",
          $sformatf(
            "Transfer %0d: arming SRAM-to-mailbox phase and polling status0",
            transfer_id), UVM_LOW)
        dma_arm(src_addr, mbox_addr, byte_count, 0,
                axi_dma_reg__ctrl__rd_route__rd_route_e__MBOX,
                axi_dma_reg__ctrl__wr_route__wr_route_e__DISABLE);
        dma_wait_idle(err, max_polls);
        if (err) begin
          dma_mbox_unlock();
          `uvm_error("DMA_XFER_SEQ",
            $sformatf("DMA error during transfer %0d mode=%s (SRAM->mbox)",
                      transfer_id, item.transfer_mode.name()))
          return;
        end
        `uvm_info("DMA_XFER_SEQ",
          $sformatf(
            "Transfer %0d: arming mailbox-to-SRAM phase and polling status0",
            transfer_id), UVM_LOW)
        dma_arm(mbox_addr, dst_addr, byte_count, 0,
                axi_dma_reg__ctrl__rd_route__rd_route_e__DISABLE,
                axi_dma_reg__ctrl__wr_route__wr_route_e__MBOX);
        dma_wait_idle(err, max_polls);
        dma_mbox_unlock();
        if (err) begin
          `uvm_error("DMA_XFER_SEQ",
            $sformatf("DMA error during transfer %0d mode=%s (mbox->SRAM)",
                      transfer_id, item.transfer_mode.name()))
          return;
        end
        `uvm_info("DMA_XFER_SEQ",
          $sformatf(
            "Transfer %0d: mailbox round trip complete; reading back %0d destination words",
            transfer_id, num_words), UVM_LOW)
        for (int w = 0; w < num_words; w++) begin
          axi_sram_read32(item.dst_offset + (w*4), rd_data);
          if (rd_data !== item.payload[w])
            `uvm_error("DMA_XFER_SEQ", $sformatf("MBOX xfer %0d word %0d mismatch: exp=0x%08x got=0x%08x", transfer_id, w, item.payload[w], rd_data))
        end
      end
      default: begin
        `uvm_fatal("DMA_XFER_SEQ",
          $sformatf("Unsupported DMA transfer mode %s",
                    item.transfer_mode.name()))
      end
    endcase

    `uvm_info("DMA_XFER_SEQ",
      $sformatf("Completed DMA transfer %0d mode=%s byte_count=%0d",
                transfer_id, item.transfer_mode.name(), byte_count), UVM_LOW)
  endtask

endclass
