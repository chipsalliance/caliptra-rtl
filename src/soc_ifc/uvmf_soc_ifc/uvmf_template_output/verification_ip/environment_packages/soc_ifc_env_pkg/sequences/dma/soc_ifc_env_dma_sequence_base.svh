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
// Encapsulates the DMA transaction-level API so derived DMA sequences/tests
// compose it instead of re-implementing it (mirrors the reuse pattern of
// soc_ifc_env_mbox_sequence_base):
//   - dma_arm / dma_read_status / dma_wait_idle / dma_fifo_push / dma_fifo_pop
//   - dma_read_cap (FIFO max depth), dma_transfer_and_verify (one transfer +
//     self-check across the AXI2AXI / AHB_FIFO / MBOX routes), and the
//     dma_transfer_rand wrapper (drives a constrained-random soc_ifc_dma_xfer_item)
//   - dma_mbox_lock_acquire / dma_mbox_unlock for the MBOX route
//   - the bounded AXI SRAM backdoor (sram_bkdr_write / sram_bkdr_read)
//
// The DMA AXI manager port is backed in hdl_top by a caliptra_axi_sram
// (i_dma_axi_sram) with AW=18 (256KB window); its storage is the caliptra_sram
// byte array i_sram.ram, indexed [word][byte].
//----------------------------------------------------------------------

class soc_ifc_env_dma_sequence_base extends soc_ifc_env_sequence_base #(.CONFIG_T(soc_ifc_env_configuration_t));

  `uvm_object_utils( soc_ifc_env_dma_sequence_base )

  // ---- Bounded AXI SRAM (hdl_top.i_dma_axi_sram) geometry / backdoor ----
  // AW=18 -> 256KB window. Storage is caliptra_sram's byte array:
  //   logic [7:0] ram [DEPTH][NUM_BYTES-1:0], indexed [word][byte].
  localparam int          SRAM_LOCAL_AW = 18;
  localparam bit [63:0]   SRAM_WIN_MASK = (64'h1 << SRAM_LOCAL_AW) - 1;
  localparam string       SRAM_PATH     = "hdl_top.i_dma_axi_sram.i_sram.ram";

  // Non-overlapping source/destination windows (4-byte aligned, high bits zero).
  localparam bit [63:0]   SRC_BASE = 64'h0000_0000;
  localparam bit [63:0]   DST_BASE = 64'h0001_0000; // 64KB offset

  // Mailbox address used as the intermediate for MBOX-route transfers (within the
  // mailbox direct-access span).
  localparam bit [63:0]   MBOX_ADDR = 64'h0000_0000;

  // DMA internal FIFO max depth (in words), read once from cap.fifo_max_depth.
  protected int unsigned fifo_max_depth;

  // Running count of transfers issued via this sequence, used for log/error context.
  protected int unsigned transfer_id;

  function new(string name = "" );
    super.new(name);
  endfunction

  virtual task pre_body();
    super.pre_body();
    reg_model = configuration.soc_ifc_rm;
  endtask

  //==========================================
  // Backdoor helpers into the bounded AXI SRAM.
  // caliptra_sram stores per byte: ram[word][byte] = word_data[8*byte +: 8].
  //==========================================
  protected function int unsigned sram_word_index(input bit [63:0] byte_addr);
    return int'((byte_addr & SRAM_WIN_MASK) >> 2);
  endfunction

  virtual task sram_bkdr_write(input bit [63:0] byte_addr, input bit [31:0] data);
    string path;
    int unsigned idx;
    idx = sram_word_index(byte_addr);
    for (int b = 0; b < 4; b++) begin
      path = $sformatf("%s[%0d][%0d]", SRAM_PATH, idx, b);
      if (!uvm_hdl_deposit(path, data[8*b +: 8]))
        `uvm_error("DMA_SEQ_BASE", $sformatf("uvm_hdl_deposit failed for %s", path))
    end
  endtask

  virtual function bit [31:0] sram_bkdr_read(input bit [63:0] byte_addr);
    string path;
    int unsigned idx;
    logic [63:0] val;
    bit [31:0]   word;
    idx = sram_word_index(byte_addr);
    word = '0;
    for (int b = 0; b < 4; b++) begin
      path = $sformatf("%s[%0d][%0d]", SRAM_PATH, idx, b);
      if (!uvm_hdl_read(path, val))
        `uvm_error("DMA_SEQ_BASE", $sformatf("uvm_hdl_read failed for %s", path))
      word[8*b +: 8] = val[7:0];
    end
    return word;
  endfunction

  //==========================================
  // DMA register API (uC / AHB side).
  //==========================================
  // Read cap.fifo_max_depth (words) into fifo_max_depth.
  virtual task dma_read_cap();
    uvm_status_e   sts;
    uvm_reg_data_t cap_val;
    reg_model.axi_dma_reg_rm.cap.read(sts, cap_val, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    fifo_max_depth = int'((cap_val >> reg_model.axi_dma_reg_rm.cap.fifo_max_depth.get_lsb_pos()) &
                          ((1 << reg_model.axi_dma_reg_rm.cap.fifo_max_depth.get_n_bits()) - 1));
    if (fifo_max_depth == 0) begin
      fifo_max_depth = 1; // guard against unexpected 0 to avoid a stuck push loop
      `uvm_warning("DMA_SEQ_BASE", "cap.fifo_max_depth read as 0; defaulting to 1")
    end
  endtask

  // Program the DMA config registers and set ctrl.go over AHB.
  virtual task dma_arm(input bit [63:0] src_addr,
                       input bit [63:0] dst_addr,
                       input int unsigned byte_count,
                       input int unsigned block_size,
                       input bit [1:0]  rd_route,
                       input bit [2:0]  wr_route);
    uvm_status_e   sts;
    uvm_reg_data_t ctrl_val;
    reg_model.axi_dma_reg_rm.src_addr_l.write(sts, src_addr[31:0],  UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    reg_model.axi_dma_reg_rm.src_addr_h.write(sts, src_addr[63:32], UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    reg_model.axi_dma_reg_rm.dst_addr_l.write(sts, dst_addr[31:0],  UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    reg_model.axi_dma_reg_rm.dst_addr_h.write(sts, dst_addr[63:32], UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    reg_model.axi_dma_reg_rm.byte_count.write(sts, byte_count,      UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    reg_model.axi_dma_reg_rm.block_size.write(sts, block_size,      UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    // Compose ctrl (go=1 + routes, all other fields 0) from RAL field positions and
    // issue one explicit write. Explicit compose (vs set()/update()) is deterministic
    // and avoids re-writing any stale desired state in other ctrl fields.
    ctrl_val = (uvm_reg_data_t'(1)        << reg_model.axi_dma_reg_rm.ctrl.go.get_lsb_pos())       |
               (uvm_reg_data_t'(rd_route) << reg_model.axi_dma_reg_rm.ctrl.rd_route.get_lsb_pos()) |
               (uvm_reg_data_t'(wr_route) << reg_model.axi_dma_reg_rm.ctrl.wr_route.get_lsb_pos());
    reg_model.axi_dma_reg_rm.ctrl.write(sts, ctrl_val, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
  endtask

  // Recover the DMA from a DMA_ERROR state: ctrl.flush resets the FSM to IDLE and
  // clears the FIFO (see axi_dma_ctrl). Harmless when idle (flush self-clears).
  virtual task dma_flush();
    uvm_status_e   sts;
    uvm_reg_data_t ctrl_val;
    ctrl_val = (uvm_reg_data_t'(1) << reg_model.axi_dma_reg_rm.ctrl.flush.get_lsb_pos());
    reg_model.axi_dma_reg_rm.ctrl.write(sts, ctrl_val, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
  endtask

  // Read status0 over AHB, returning busy/error/fifo_depth. Parse the value read
  // back from the DUT (d); field positions/widths come from the RAL model.
  virtual task dma_read_status(output bit busy, output bit err, output int unsigned fifo_depth);
    uvm_status_e   sts;
    uvm_reg_data_t d;
    reg_model.axi_dma_reg_rm.status0.read(sts, d, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    busy       = d[reg_model.axi_dma_reg_rm.status0.busy.get_lsb_pos()];
    err        = d[reg_model.axi_dma_reg_rm.status0.error.get_lsb_pos()];
    fifo_depth = int'((d >> reg_model.axi_dma_reg_rm.status0.fifo_depth.get_lsb_pos()) &
                      ((1 << reg_model.axi_dma_reg_rm.status0.fifo_depth.get_n_bits()) - 1));
  endtask

  // Poll status0 until the DMA is idle (busy==0) or reports an error.
  virtual task dma_wait_idle(output bit err);
    bit busy;
    int unsigned fd;
    do begin
      dma_read_status(busy, err, fd);
    end while (busy && !err);
    // Detection only; callers are the contextual error reporter.
  endtask

  // Push one payload word into the DMA FIFO over AHB (wr_route=AHB_FIFO).
  // err is set (and the wait loop broken) if the DMA reports status0.error.
  virtual task dma_fifo_push(input bit [31:0] data, output bit err);
    uvm_status_e sts;
    bit busy;
    int unsigned fd;
    err = 1'b0;
    // Wait until the FIFO has room (depth != max), aborting on a DMA error.
    do begin
      dma_read_status(busy, err, fd);
      if (err) return;
    end while (fd == fifo_max_depth);
    reg_model.axi_dma_reg_rm.write_data.write(sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
  endtask

  // Pop one payload word from the DMA FIFO over AHB (rd_route=AHB_FIFO).
  // err is set (and the wait loop broken) if the DMA reports status0.error.
  virtual task dma_fifo_pop(output bit [31:0] data, output bit err);
    uvm_status_e   sts;
    uvm_reg_data_t d;
    bit busy;
    int unsigned fd;
    err  = 1'b0;
    data = '0;
    // Wait until the FIFO has data (depth != 0), aborting on a DMA error.
    do begin
      dma_read_status(busy, err, fd);
      if (err) return;
    end while (fd == 0);
    reg_model.axi_dma_reg_rm.read_data.read(sts, d, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    data = d[31:0];
  endtask

  // Acquire the mailbox lock for the microcontroller over AHB. Reading mbox_lock
  // returns 0 and grants the lock when it was free; the DMA MBOX route requires
  // the uC to hold the lock (uc_has_lock in mbox.sv). ok=1 if acquired.
  virtual task dma_mbox_lock_acquire(output bit ok);
    uvm_status_e   sts;
    uvm_reg_data_t d;
    reg_model.mbox_csr_rm.mbox_lock.read(sts, d, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    ok = (d[0] == 1'b0);
  endtask

  virtual task dma_mbox_unlock();
    uvm_status_e sts;
    reg_model.mbox_csr_rm.mbox_unlock.write(sts, 1, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
  endtask

  //==========================================
  // Core: run one DMA transfer for `route`, moving caller-supplied `payload`
  // from `src_addr` to `dst_addr`, then verify the moved data. byte_count is
  // derived from the payload length; `err` returns a DMA status error
  // (status0.error) and data mismatches are reported as uvm_errors. block_size
  // is fixed at 0; a non-zero block_size selects SS recovery mode, which stalls
  // waiting for recovery_data_avail (see axi_dma_ctrl.sv).
  //==========================================
  virtual task dma_transfer_and_verify(input  dma_route_e route,
                                       input  bit [31:0]  payload[$],
                                       input  bit [63:0]  src_addr = SRC_BASE,
                                       input  bit [63:0]  dst_addr = DST_BASE,
                                       output bit         err);
    int unsigned num_words;
    int unsigned byte_count;
    localparam int unsigned block_size = 0;
    bit [31:0]   rd_data;
    bit          lock_ok;

    err       = 1'b0;
    num_words = payload.size();
    if (num_words == 0) begin
      `uvm_fatal("DMA_XFER_SEQ", "dma_transfer_and_verify called with empty payload")
    end
    byte_count = num_words * 4;
    transfer_id++;

    // Start each transfer from a clean DMA state so a prior transfer's error
    // (status0.error / DMA_ERROR, which is sticky until flushed) cannot cascade
    // into this one and mask/inflate the real failure count.
    dma_flush();

    case (route)
      XFER_AXI2AXI: begin
        // Source SRAM -> DMA -> destination SRAM (both over AXI).
        for (int w = 0; w < num_words; w++)
          sram_bkdr_write(src_addr + (w*4), payload[w]);
        dma_arm(src_addr, dst_addr, byte_count, block_size,
                axi_dma_reg__ctrl__rd_route__rd_route_e__AXI_WR,
                axi_dma_reg__ctrl__wr_route__wr_route_e__AXI_RD);
        dma_wait_idle(err);
        if (err) begin
          `uvm_error("DMA_XFER_SEQ", $sformatf("DMA reported error (status0.error) during xfer %0d route=%s", transfer_id, route.name()))
          return;
        end
        for (int w = 0; w < num_words; w++) begin
          rd_data = sram_bkdr_read(dst_addr + (w*4));
          if (rd_data !== payload[w])
            `uvm_error("DMA_XFER_SEQ", $sformatf("AXI2AXI xfer %0d word %0d mismatch: exp=0x%08x got=0x%08x", transfer_id, w, payload[w], rd_data))
        end
      end
      XFER_RD_FIFO: begin
        // Source SRAM -> DMA FIFO; uC pops each word over AHB and compares.
        for (int w = 0; w < num_words; w++)
          sram_bkdr_write(src_addr + (w*4), payload[w]);
        dma_arm(src_addr, 64'h0, byte_count, block_size,
                axi_dma_reg__ctrl__rd_route__rd_route_e__AHB_FIFO,
                axi_dma_reg__ctrl__wr_route__wr_route_e__DISABLE);
        for (int w = 0; w < num_words; w++) begin
          dma_fifo_pop(rd_data, err);
          if (err) begin
            `uvm_error("DMA_XFER_SEQ", $sformatf("DMA reported error (status0.error) during xfer %0d route=%s", transfer_id, route.name()))
            return;
          end
          if (rd_data !== payload[w])
            `uvm_error("DMA_XFER_SEQ", $sformatf("RD_FIFO xfer %0d word %0d mismatch: exp=0x%08x got=0x%08x", transfer_id, w, payload[w], rd_data))
        end
        dma_wait_idle(err);
        if (err) begin
          `uvm_error("DMA_XFER_SEQ", $sformatf("DMA reported error (status0.error) during xfer %0d route=%s", transfer_id, route.name()))
          return;
        end
      end
      XFER_WR_FIFO: begin
        // uC pushes each word over AHB into the DMA FIFO -> destination SRAM.
        dma_arm(64'h0, dst_addr, byte_count, block_size,
                axi_dma_reg__ctrl__rd_route__rd_route_e__DISABLE,
                axi_dma_reg__ctrl__wr_route__wr_route_e__AHB_FIFO);
        for (int w = 0; w < num_words; w++) begin
          dma_fifo_push(payload[w], err);
          if (err) begin
            `uvm_error("DMA_XFER_SEQ", $sformatf("DMA reported error (status0.error) during xfer %0d route=%s", transfer_id, route.name()))
            return;
          end
        end
        dma_wait_idle(err);
        if (err) begin
          `uvm_error("DMA_XFER_SEQ", $sformatf("DMA reported error (status0.error) during xfer %0d route=%s", transfer_id, route.name()))
          return;
        end
        for (int w = 0; w < num_words; w++) begin
          rd_data = sram_bkdr_read(dst_addr + (w*4));
          if (rd_data !== payload[w])
            `uvm_error("DMA_XFER_SEQ", $sformatf("WR_FIFO xfer %0d word %0d mismatch: exp=0x%08x got=0x%08x", transfer_id, w, payload[w], rd_data))
        end
      end
      XFER_MBOX: begin
        // Mailbox round-trip (both MBOX directions) under one uC lock:
        //   src SRAM -> mailbox (rd_route=MBOX), then mailbox -> dst SRAM
        //   (wr_route=MBOX). Verified via the SRAM backdoor.
        dma_mbox_lock_acquire(lock_ok);
        if (!lock_ok) begin
          `uvm_error("DMA_XFER_SEQ", $sformatf("Failed to acquire mailbox lock for xfer %0d", transfer_id))
          return;
        end
        for (int w = 0; w < num_words; w++)
          sram_bkdr_write(src_addr + (w*4), payload[w]);
        dma_arm(src_addr, MBOX_ADDR, byte_count, block_size,
                axi_dma_reg__ctrl__rd_route__rd_route_e__MBOX,
                axi_dma_reg__ctrl__wr_route__wr_route_e__DISABLE);
        dma_wait_idle(err);
        if (err) begin
          dma_mbox_unlock();
          `uvm_error("DMA_XFER_SEQ", $sformatf("DMA reported error (status0.error) during xfer %0d route=%s (SRAM->mbox)", transfer_id, route.name()))
          return;
        end
        dma_arm(MBOX_ADDR, dst_addr, byte_count, block_size,
                axi_dma_reg__ctrl__rd_route__rd_route_e__DISABLE,
                axi_dma_reg__ctrl__wr_route__wr_route_e__MBOX);
        dma_wait_idle(err);
        dma_mbox_unlock();
        if (err) begin
          `uvm_error("DMA_XFER_SEQ", $sformatf("DMA reported error (status0.error) during xfer %0d route=%s (mbox->SRAM)", transfer_id, route.name()))
          return;
        end
        for (int w = 0; w < num_words; w++) begin
          rd_data = sram_bkdr_read(dst_addr + (w*4));
          if (rd_data !== payload[w])
            `uvm_error("DMA_XFER_SEQ", $sformatf("MBOX xfer %0d word %0d mismatch: exp=0x%08x got=0x%08x", transfer_id, w, payload[w], rd_data))
        end
      end
      default: begin
        `uvm_fatal("DMA_XFER_SEQ", $sformatf("dma_transfer_and_verify called with non-concrete route %s", route.name()))
      end
    endcase

    `uvm_info("DMA_XFER_SEQ", $sformatf("Completed DMA transfer %0d route=%s byte_count=%0d", transfer_id, route.name(), byte_count), UVM_LOW)
  endtask

  //==========================================
  // Convenience wrapper: randomize a soc_ifc_dma_xfer_item (route, size, and
  // non-overlapping window-fitted addresses) and a payload, then run+verify.
  //==========================================
  virtual task dma_transfer_rand(output bit err);
    soc_ifc_dma_xfer_item item;
    bit [31:0]            payload[$];

    item = soc_ifc_dma_xfer_item::type_id::create("item");
    if (!item.randomize())
      `uvm_fatal("DMA_XFER_SEQ", "Failed to randomize soc_ifc_dma_xfer_item")

    `uvm_info("DMA_XFER_SEQ", $sformatf("Randomized transfer: %s", item.convert2string()), UVM_HIGH)

    payload.delete();
    for (int w = 0; w < item.num_words; w++)
      payload.push_back($urandom());

    dma_transfer_and_verify(item.route, payload, item.src_addr, item.dst_addr, err);
  endtask

endclass
