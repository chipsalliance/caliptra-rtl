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

// Minimal directed testbench for the maximum supported 2 GiB AXI-to-AXI DMA
// operation. The bench intentionally avoids allocating source or destination
// memory. Read data is generated from the current source address and write data
// is checked against a small queue of accepted read beats before being
// discarded. This preserves every AXI transfer while keeping host memory use
// independent of BYTE_COUNT.
//
// The test checks:
// - DMA register programming and command acceptance.
// - Every AXI address, burst attribute, data beat, last indication, and response.
// - Exact 2 GiB totals on both read and write channels.
// - Internal byte counters, credits, FIFO depth, and pending-response counters.
// - Error and completion interrupts.
// - Active and final DMA status registers and interrupt event counters.
module axi_dma_2gib_tb;

  import axi_pkg::*;
  import soc_ifc_pkg::*;

  // Source occupies [0x8000_0000:0xffff_ffff]. Place the destination above
  // 4 GiB so the two 2 GiB ranges are disjoint.
  localparam int unsigned BYTE_COUNT = 32'h8000_0000;
  localparam logic [63:0] SRC_ADDR = 64'h0000_0000_8000_0000;
  localparam logic [63:0] DST_ADDR = 64'h0000_0001_0000_0000;
  // The measured transfer takes about 554 million clocks. Leave substantial
  // margin for future control-path changes while still detecting a hang.
  localparam int unsigned WATCHDOG_CYCLES = 800_000_000;

  // AXI DMA register offsets.
  localparam logic [11:0] DMA_CTRL_ADDR = 12'h008;
  localparam logic [11:0] DMA_STATUS0_ADDR = 12'h00c;
  localparam logic [11:0] DMA_STATUS1_ADDR = 12'h010;
  localparam logic [11:0] DMA_SRC_ADDR_L_ADDR = 12'h014;
  localparam logic [11:0] DMA_SRC_ADDR_H_ADDR = 12'h018;
  localparam logic [11:0] DMA_DST_ADDR_L_ADDR = 12'h01c;
  localparam logic [11:0] DMA_DST_ADDR_H_ADDR = 12'h020;
  localparam logic [11:0] DMA_BYTE_COUNT_ADDR = 12'h024;
  localparam logic [11:0] DMA_BLOCK_SIZE_ADDR = 12'h028;
  localparam logic [11:0] DMA_GLOBAL_INTR_EN_ADDR = 12'h800;
  localparam logic [11:0] DMA_ERROR_INTR_EN_ADDR = 12'h804;
  localparam logic [11:0] DMA_NOTIF_INTR_EN_ADDR = 12'h808;
  localparam logic [11:0] DMA_ERROR_INTERNAL_INTR_ADDR = 12'h814;
  localparam logic [11:0] DMA_NOTIF_INTERNAL_INTR_ADDR = 12'h818;
  localparam logic [11:0] DMA_ERROR_COUNT_FIRST_ADDR = 12'h900;
  localparam logic [11:0] DMA_ERROR_COUNT_LAST_ADDR = 12'h924;
  localparam logic [11:0] DMA_NOTIF_TXN_DONE_COUNT_ADDR = 12'h980;

  // DMA register access interface.
  logic clk;
  logic rst_n;
  logic cptra_pwrgood;
  logic dv;
  soc_ifc_req_t req_data;
  logic req_hold;
  logic [SOC_IFC_DATA_W-1:0] rdata;
  logic error;
  logic notif_intr;
  logic error_intr;

  // AXI interface shared by the DMA manager and the lightweight responders.
  axi_if #(.AW(64), .DW(32), .IW(1), .UW(32)) m_axi_if (
    .clk(clk),
    .rst_n(rst_n)
  );

  // Read responder state. Only one read burst is accepted at a time. This is
  // sufficient to sustain one read beat per clock after each address handshake.
  logic read_active;
  logic [7:0] read_beats_left;
  logic [63:0] read_addr;

  // Write responder state. Write data is consumed without backing storage and
  // one OKAY response is generated after the final beat of each burst.
  logic write_active;
  logic [7:0] write_beats_left;
  logic bvalid;

  // End-to-end payload scoreboard. The queue contains only data accepted on R
  // but not yet observed on W. Its size is bounded by the small RTL DMA FIFO,
  // not by the 2 GiB transfer size.
  logic [31:0] expected_wdata_q[$];

  // Independent testbench accounting for address requests and data handshakes.
  // These 64-bit counters prove that completion was not reported after a
  // wrapped or truncated 32-bit RTL counter.
  longint unsigned ar_bytes;
  longint unsigned aw_bytes;
  longint unsigned read_data_bytes;
  longint unsigned write_data_bytes;
  longint unsigned expected_ar_addr;
  longint unsigned expected_aw_addr;
  int unsigned ar_bursts;
  int unsigned aw_bursts;
  int unsigned b_responses;

  // Previous RTL counter values used to detect unexpected rollover or an
  // increase in a decrementing counter while the DMA is active.
  logic scoreboard_active;
  logic [31:0] prev_rd_bytes_requested;
  logic [31:0] prev_wr_bytes_requested;
  logic [31:0] prev_bytes_remaining;
  logic [31:0] prev_rd_fifo_bytes_remaining;

  // Unitless delay is intentional. This compile target contains generated
  // packages without timeunit declarations, so a local timeunit is rejected by
  // VCS. A nonzero unitless delay provides deterministic clock advancement.
  initial begin
    clk = 1'b0;
    forever #1 clk = ~clk;
  end

  // Instantiate only the DMA and tie off unused mailbox, AES, recovery, and
  // KeyVault paths. The AXI-to-AXI route does not depend on those interfaces.
  axi_dma_top #(
    .AW(64),
    .DW(32),
    .UW(32),
    .IW(1)
  ) dut (
    .clk,
    .cptra_pwrgood,
    .rst_n,
    .recovery_data_avail(1'b0),
    .recovery_image_activated(1'b0),
    .mbox_lock(1'b1),
    .sha_lock(1'b1),
    .debugUnlock_or_scan_mode_switch(1'b0),
    .ocp_lock_in_progress(1'b0),
    .key_release_addr('0),
    .key_release_size('0),
    .aes_input_ready(1'b0),
    .aes_output_valid(1'b0),
    .aes_status_idle(1'b1),
    .aes_req_dv(),
    .aes_req_hold(1'b0),
    .aes_req_data(),
    .aes_rdata('0),
    .aes_err(1'b0),
    .kv_read(),
    .kv_rd_resp('0),
    .axuser('0),
    .m_axi_w_if(m_axi_if.w_mgr),
    .m_axi_r_if(m_axi_if.r_mgr),
    .dv,
    .req_data,
    .req_hold,
    .rdata,
    .error,
    .mb_dv(),
    .mb_hold(1'b0),
    .mb_error(1'b0),
    .mb_data(),
    .mb_rdata('0),
    .notif_intr,
    .error_intr
  );

  // Stateless AXI read subordinate.
  //
  // ARREADY is withdrawn while a burst is active. RDATA is derived from the
  // current source address, which creates deterministic nonconstant data
  // without storing a 2 GiB source image.
  assign m_axi_if.arready = !read_active;
  assign m_axi_if.rvalid = read_active;
  assign m_axi_if.rdata = read_addr[31:0];
  assign m_axi_if.rresp = AXI_RESP_OKAY;
  assign m_axi_if.rid = '0;
  assign m_axi_if.ruser = '0;
  assign m_axi_if.rlast = read_active && (read_beats_left == 0);

  // Stateless AXI write subordinate.
  //
  // WREADY remains asserted for maximum throughput. AWREADY is blocked until
  // the previous burst response completes so this responder needs only one
  // burst context.
  assign m_axi_if.awready = !write_active && !bvalid;
  assign m_axi_if.wready = 1'b1;
  assign m_axi_if.bvalid = bvalid;
  assign m_axi_if.bresp = AXI_RESP_OKAY;
  assign m_axi_if.bid = '0;
  assign m_axi_if.buser = '0;

  // Capture one read burst and produce exactly ARLEN+1 beats.
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      read_active <= 1'b0;
      read_beats_left <= '0;
      read_addr <= '0;
    end else begin
      if (m_axi_if.arvalid && m_axi_if.arready) begin
        read_active <= 1'b1;
        read_beats_left <= m_axi_if.arlen;
        read_addr <= m_axi_if.araddr;
      end else if (m_axi_if.rvalid && m_axi_if.rready) begin
        if (read_beats_left == 0)
          read_active <= 1'b0;
        else begin
          read_beats_left <= read_beats_left - 1'b1;
          read_addr <= read_addr + 4;
        end
      end
    end
  end

  // Each read DWORD is the low 32 bits of its absolute source address. The
  // address-dependent pattern catches missing, duplicated, or reordered beats.
  function automatic logic [31:0] expected_read_data(
      input longint unsigned byte_offset);
    return (SRC_ADDR + byte_offset);
  endfunction

  // Global error and interrupt checks.
  always_ff @(posedge clk or negedge rst_n) begin
    if (rst_n) begin
      if (error)
        $fatal(1, "AXI_DMA_2GIB: register interface error asserted");
      if (error_intr)
        $fatal(1, "AXI_DMA_2GIB: unexpected DMA error interrupt");
      if (notif_intr &&
          !(dut.i_axi_dma_ctrl.ctrl_fsm_ps inside {2'b10, 2'b00}))
        $fatal(1, "AXI_DMA_2GIB: notification interrupt asserted early");
    end
  end

  // Read-address scoreboard.
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      ar_bytes <= 0;
      expected_ar_addr <= SRC_ADDR;
      ar_bursts <= 0;
    end else if (m_axi_if.arvalid && m_axi_if.arready) begin
      if (m_axi_if.araddr != expected_ar_addr)
        $fatal(1,
          "AXI_DMA_2GIB: unexpected ARADDR exp=0x%016x got=0x%016x",
          expected_ar_addr, m_axi_if.araddr);
      if (m_axi_if.arburst != AXI_BURST_INCR || m_axi_if.arsize != 3'd2)
        $fatal(1, "AXI_DMA_2GIB: unexpected ARBURST/ARSIZE");
      if ((m_axi_if.araddr[11:0] + ((m_axi_if.arlen + 1) * 4)) > 4096)
        $fatal(1, "AXI_DMA_2GIB: read burst crossed 4 KiB boundary");
      if ((ar_bytes + ((m_axi_if.arlen + 1) * 4)) > BYTE_COUNT)
        $fatal(1, "AXI_DMA_2GIB: read address requests exceeded 2 GiB");
      ar_bytes <= ar_bytes + ((m_axi_if.arlen + 1) * 4);
      expected_ar_addr <= expected_ar_addr + ((m_axi_if.arlen + 1) * 4);
      ar_bursts <= ar_bursts + 1;
    end
  end

  // Write-address scoreboard.
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      aw_bytes <= 0;
      expected_aw_addr <= DST_ADDR;
      aw_bursts <= 0;
    end else if (m_axi_if.awvalid && m_axi_if.awready) begin
      if (m_axi_if.awaddr != expected_aw_addr)
        $fatal(1,
          "AXI_DMA_2GIB: unexpected AWADDR exp=0x%016x got=0x%016x",
          expected_aw_addr, m_axi_if.awaddr);
      if (m_axi_if.awburst != AXI_BURST_INCR || m_axi_if.awsize != 3'd2)
        $fatal(1, "AXI_DMA_2GIB: unexpected AWBURST/AWSIZE");
      if ((m_axi_if.awaddr[11:0] + ((m_axi_if.awlen + 1) * 4)) > 4096)
        $fatal(1, "AXI_DMA_2GIB: write burst crossed 4 KiB boundary");
      if ((aw_bytes + ((m_axi_if.awlen + 1) * 4)) > BYTE_COUNT)
        $fatal(1, "AXI_DMA_2GIB: write address requests exceeded 2 GiB");
      aw_bytes <= aw_bytes + ((m_axi_if.awlen + 1) * 4);
      expected_aw_addr <= expected_aw_addr + ((m_axi_if.awlen + 1) * 4);
      aw_bursts <= aw_bursts + 1;
    end
  end

  // End-to-end read/write payload scoreboard. R and W are intentionally kept
  // in one process so simultaneous queue push/pop ordering is deterministic.
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      expected_wdata_q.delete();
      read_data_bytes <= 0;
      write_data_bytes <= 0;
    end else begin
      if (m_axi_if.rvalid && m_axi_if.rready) begin
        if (m_axi_if.rresp != AXI_RESP_OKAY || m_axi_if.rid != '0)
          $fatal(1, "AXI_DMA_2GIB: unexpected read response");
        if (m_axi_if.rlast != (read_beats_left == 0))
          $fatal(1, "AXI_DMA_2GIB: RLAST did not match ARLEN");
        if (m_axi_if.rdata !== expected_read_data(read_data_bytes))
          $fatal(1,
            "AXI_DMA_2GIB: unexpected read data at byte 0x%08x",
            read_data_bytes);
        if ((read_data_bytes + 4) > BYTE_COUNT)
          $fatal(1, "AXI_DMA_2GIB: read data exceeded 2 GiB");
        expected_wdata_q.push_back(m_axi_if.rdata);
        read_data_bytes <= read_data_bytes + 4;
      end

      if (m_axi_if.wvalid && m_axi_if.wready) begin
        if (m_axi_if.wlast != (write_beats_left == 0))
          $fatal(1, "AXI_DMA_2GIB: WLAST did not match AWLEN");
        if (m_axi_if.wstrb != '1)
          $fatal(1, "AXI_DMA_2GIB: unexpected write strobe");
        if (expected_wdata_q.size() == 0)
          $fatal(1, "AXI_DMA_2GIB: write data arrived before read data");
        if (m_axi_if.wdata !== expected_wdata_q[0])
          $fatal(1,
            "AXI_DMA_2GIB: write data mismatch at byte 0x%08x exp=0x%08x got=0x%08x",
            write_data_bytes, expected_wdata_q[0], m_axi_if.wdata);
        void'(expected_wdata_q.pop_front());
        if ((write_data_bytes + 4) > BYTE_COUNT)
          $fatal(1, "AXI_DMA_2GIB: write data exceeded 2 GiB");
        write_data_bytes <= write_data_bytes + 4;
      end
    end
  end

  // Write-response scoreboard.
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      b_responses <= 0;
    end else if (m_axi_if.bvalid && m_axi_if.bready) begin
      if (m_axi_if.bresp != AXI_RESP_OKAY || m_axi_if.bid != '0)
        $fatal(1, "AXI_DMA_2GIB: unexpected write response");
      if (b_responses >= aw_bursts)
        $fatal(1, "AXI_DMA_2GIB: write response without address request");
      b_responses <= b_responses + 1;
    end
  end

  // Internal DMA counter, FIFO, and credit invariants.
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      scoreboard_active <= 1'b0;
      prev_rd_bytes_requested <= 0;
      prev_wr_bytes_requested <= 0;
      prev_bytes_remaining <= BYTE_COUNT;
      prev_rd_fifo_bytes_remaining <= BYTE_COUNT;
    end else if (dut.i_axi_dma_ctrl.ctrl_fsm_ps == 2'b01) begin
      if ($isunknown({
            dut.i_axi_dma_ctrl.rd_bytes_requested,
            dut.i_axi_dma_ctrl.wr_bytes_requested,
            dut.i_axi_dma_ctrl.bytes_remaining,
            dut.i_axi_dma_ctrl.rd_fifo_bytes_remaining,
            dut.i_axi_dma_ctrl.fifo_depth,
            dut.i_axi_dma_ctrl.rd_credits,
            dut.i_axi_dma_ctrl.wr_credits,
            dut.i_axi_dma_ctrl.wr_resp_pending}))
        $fatal(1, "AXI_DMA_2GIB: unknown DMA counter or credit state");
      if (!scoreboard_active) begin
        scoreboard_active <= 1'b1;
      end else begin
        if (dut.i_axi_dma_ctrl.rd_bytes_requested <
            prev_rd_bytes_requested)
          $fatal(1, "AXI_DMA_2GIB: rd_bytes_requested rolled over");
        if (dut.i_axi_dma_ctrl.wr_bytes_requested <
            prev_wr_bytes_requested)
          $fatal(1, "AXI_DMA_2GIB: wr_bytes_requested rolled over");
        if (dut.i_axi_dma_ctrl.bytes_remaining > prev_bytes_remaining)
          $fatal(1, "AXI_DMA_2GIB: bytes_remaining increased");
        if (dut.i_axi_dma_ctrl.rd_fifo_bytes_remaining >
            prev_rd_fifo_bytes_remaining)
          $fatal(1, "AXI_DMA_2GIB: rd_fifo_bytes_remaining increased");
      end
      prev_rd_bytes_requested <= dut.i_axi_dma_ctrl.rd_bytes_requested;
      prev_wr_bytes_requested <= dut.i_axi_dma_ctrl.wr_bytes_requested;
      prev_bytes_remaining <= dut.i_axi_dma_ctrl.bytes_remaining;
      prev_rd_fifo_bytes_remaining <=
        dut.i_axi_dma_ctrl.rd_fifo_bytes_remaining;
      if (dut.i_axi_dma_ctrl.rd_bytes_requested > BYTE_COUNT ||
          dut.i_axi_dma_ctrl.wr_bytes_requested > BYTE_COUNT ||
          dut.i_axi_dma_ctrl.bytes_remaining > BYTE_COUNT ||
          dut.i_axi_dma_ctrl.rd_fifo_bytes_remaining > BYTE_COUNT)
        $fatal(1, "AXI_DMA_2GIB: DMA byte counter exceeded 2 GiB");
      if (dut.i_axi_dma_ctrl.fifo_depth > 128 ||
          dut.i_axi_dma_ctrl.rd_credits > 128 ||
          dut.i_axi_dma_ctrl.wr_credits > 128)
        $fatal(1, "AXI_DMA_2GIB: FIFO depth or credit counter overflow");
    end
  end

  // Capture one write burst and generate an OKAY response after WLAST.
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      write_active <= 1'b0;
      write_beats_left <= '0;
      bvalid <= 1'b0;
    end else begin
      if (m_axi_if.awvalid && m_axi_if.awready) begin
        write_active <= 1'b1;
        write_beats_left <= m_axi_if.awlen;
      end
      if (m_axi_if.wvalid && m_axi_if.wready) begin
        if (write_beats_left == 0) begin
          write_active <= 1'b0;
          bvalid <= 1'b1;
        end else
          write_beats_left <= write_beats_left - 1'b1;
      end
      if (bvalid && m_axi_if.bready)
        bvalid <= 1'b0;
    end
  end

  // Drive one firmware-side DMA register write. Stimulus changes only on the
  // falling edge so the generated register block samples stable values.
  task automatic write_reg(input logic [11:0] addr,
                           input logic [31:0] data);
    @(negedge clk);
    req_data = '0;
    req_data.addr = addr;
    req_data.wdata = data;
    req_data.wstrb = '1;
    req_data.write = 1'b1;
    dv = 1'b1;
    do @(posedge clk); while (req_hold);
    @(negedge clk);
    dv = 1'b0;
  endtask

  // Read one DMA register through the same firmware-side interface. Data is
  // sampled on the falling edge after the request has been accepted.
  task automatic read_reg(input logic [11:0] addr,
                          output logic [31:0] data);
    @(negedge clk);
    req_data = '0;
    req_data.addr = addr;
    dv = 1'b1;
    do @(posedge clk); while (req_hold);
    @(negedge clk);
    data = rdata;
    dv = 1'b0;
  endtask

  // Apply power-good before releasing the DMA reset. Check the actual RTL FSM
  // before programming any command so reset integration failures terminate
  // immediately.
  task automatic reset_dut();
    cptra_pwrgood = 1'b0;
    rst_n = 1'b0;
    dv = 1'b0;
    req_data = '0;
    repeat (5) @(posedge clk);
    @(negedge clk);
    cptra_pwrgood = 1'b1;
    repeat (5) @(posedge clk);
    @(negedge clk);
    rst_n = 1'b1;
    repeat (5) @(posedge clk);
    if ($isunknown(dut.i_axi_dma_ctrl.ctrl_fsm_ps))
      $fatal(1, "AXI_DMA_2GIB: DMA FSM is unknown after reset");
    if (dut.i_axi_dma_ctrl.ctrl_fsm_ps != 2'b00)
      $fatal(1, "AXI_DMA_2GIB: DMA FSM did not reset to IDLE");
  endtask

  // Program a non-fixed AXI-to-AXI transfer. Enable every error interrupt and
  // only the transaction-done notification so any error event is immediately
  // visible while FIFO transition notifications remain masked.
  task automatic program_dma();
    write_reg(DMA_SRC_ADDR_L_ADDR, SRC_ADDR[31:0]);
    write_reg(DMA_SRC_ADDR_H_ADDR, SRC_ADDR[63:32]);
    write_reg(DMA_DST_ADDR_L_ADDR, DST_ADDR[31:0]);
    write_reg(DMA_DST_ADDR_H_ADDR, DST_ADDR[63:32]);
    write_reg(DMA_BYTE_COUNT_ADDR, BYTE_COUNT);
    write_reg(DMA_BLOCK_SIZE_ADDR, 32'h0);
    write_reg(DMA_GLOBAL_INTR_EN_ADDR, 32'h3);
    write_reg(DMA_ERROR_INTR_EN_ADDR, 32'h3ff);
    write_reg(DMA_NOTIF_INTR_EN_ADDR, 32'h1);
    write_reg(DMA_CTRL_ADDR, 32'h0303_0001);
  endtask

  // Require explicit entry into DMA_WAIT_DATA. This prevents an IDLE command
  // programming failure from being mistaken for successful completion.
  task automatic wait_for_dma_start();
    $display("AXI_DMA_2GIB: started byte_count=0x%08x", BYTE_COUNT);
    for (int unsigned start_cycle = 0; start_cycle < 100; start_cycle++) begin
      @(posedge clk);
      if (dut.i_axi_dma_ctrl.ctrl_fsm_ps == 2'b01)
        break;
      if (dut.i_axi_dma_ctrl.ctrl_fsm_ps == 2'b11) begin
        $display("* TESTCASE FAILED");
        $fatal(1, "AXI_DMA_2GIB: DMA command was rejected");
      end
      if (start_cycle == 99) begin
        $display("* TESTCASE FAILED");
        $fatal(1, "AXI_DMA_2GIB: DMA did not enter WAIT_DATA");
      end
    end
  endtask

  // Cross-check the firmware-visible status registers against the internal
  // state used by the cycle-level scoreboard.
  task automatic check_active_status(input int unsigned cycle);
    logic [31:0] status0;
    logic [31:0] status1;

    read_reg(DMA_STATUS0_ADDR, status0);
    read_reg(DMA_STATUS1_ADDR, status1);
    if (status0[1:0] != 2'b01 ||
        status0[17:16] != 2'b01 ||
        status1 != dut.i_axi_dma_ctrl.bytes_remaining)
      $fatal(1,
        "AXI_DMA_2GIB: unexpected active status0=0x%08x status1=0x%08x rtl_remaining=0x%08x",
        status0, status1, dut.i_axi_dma_ctrl.bytes_remaining);
    $display(
      "AXI_DMA_2GIB: cycle=%0d remaining=0x%08x fsm=0x%0x",
      cycle, dut.i_axi_dma_ctrl.bytes_remaining,
      dut.i_axi_dma_ctrl.ctrl_fsm_ps);
  endtask

  // Validate all completion conditions after the DMA returns to IDLE.
  task automatic check_final_results();
    logic [31:0] status0;
    logic [31:0] status1;
    logic [31:0] error_status;
    logic [31:0] notif_status;
    logic [31:0] count_value;

    // The FSM is allowed to report completion only after every independent
    // address, data, and response total reaches exactly 2 GiB.
    @(negedge clk);
    if (ar_bytes != BYTE_COUNT || aw_bytes != BYTE_COUNT ||
        read_data_bytes != BYTE_COUNT ||
        write_data_bytes != BYTE_COUNT)
      $fatal(1,
        "AXI_DMA_2GIB: early completion ar=0x%08x aw=0x%08x read=0x%08x write=0x%08x",
        ar_bytes, aw_bytes, read_data_bytes, write_data_bytes);
    if (expected_ar_addr != (SRC_ADDR + BYTE_COUNT) ||
        expected_aw_addr != (DST_ADDR + BYTE_COUNT))
      $fatal(1, "AXI_DMA_2GIB: final AXI address was unexpected");
    if (expected_wdata_q.size() != 0)
      $fatal(1, "AXI_DMA_2GIB: %0d expected write words remain",
             expected_wdata_q.size());
    if (ar_bursts != aw_bursts || aw_bursts != b_responses)
      $fatal(1,
        "AXI_DMA_2GIB: burst/response mismatch AR=%0d AW=%0d B=%0d",
        ar_bursts, aw_bursts, b_responses);
    if (dut.i_axi_dma_ctrl.rd_bytes_requested != 0 ||
        dut.i_axi_dma_ctrl.wr_bytes_requested != 0 ||
        dut.i_axi_dma_ctrl.rd_fifo_bytes_remaining != 0 ||
        dut.i_axi_dma_ctrl.fifo_depth != 0 ||
        dut.i_axi_dma_ctrl.wr_resp_pending != 0)
      $fatal(1,
        "AXI_DMA_2GIB: unexpected final DMA counters rd_req=0x%08x wr_req=0x%08x rd_remaining=0x%08x fifo_depth=%0d wr_pending=%0d",
        dut.i_axi_dma_ctrl.rd_bytes_requested,
        dut.i_axi_dma_ctrl.wr_bytes_requested,
        dut.i_axi_dma_ctrl.rd_fifo_bytes_remaining,
        dut.i_axi_dma_ctrl.fifo_depth,
        dut.i_axi_dma_ctrl.wr_resp_pending);

    // Transaction-done is a sticky event. Allow it to propagate through the
    // generated interrupt registers, then verify the external interrupt,
    // final status CSRs, all error status/count registers, and the single
    // expected completion count.
    repeat (2) @(posedge clk);
    if (!notif_intr || error_intr)
      $fatal(1,
        "AXI_DMA_2GIB: unexpected final interrupts notif=%0b error=%0b",
        notif_intr, error_intr);
    read_reg(DMA_STATUS0_ADDR, status0);
    read_reg(DMA_STATUS1_ADDR, status1);
    read_reg(DMA_ERROR_INTERNAL_INTR_ADDR, error_status);
    read_reg(DMA_NOTIF_INTERNAL_INTR_ADDR, notif_status);
    if (status0 != 0 || status1 != 0 || error_status != 0 ||
        !notif_status[0])
      $fatal(1,
        "AXI_DMA_2GIB: unexpected final CSRs status0=0x%08x status1=0x%08x error_status=0x%08x notif_status=0x%08x",
        status0, status1, error_status, notif_status);
    for (logic [11:0] count_addr = DMA_ERROR_COUNT_FIRST_ADDR;
         count_addr <= DMA_ERROR_COUNT_LAST_ADDR;
         count_addr += 4) begin
      read_reg(count_addr, count_value);
      if (count_value != 0)
        $fatal(1,
          "AXI_DMA_2GIB: error count at 0x%03x was 0x%08x",
          count_addr, count_value);
    end
    read_reg(DMA_NOTIF_TXN_DONE_COUNT_ADDR, count_value);
    if (count_value != 1)
      $fatal(1,
        "AXI_DMA_2GIB: transaction-done count was %0d, expected 1",
        count_value);
  endtask

  // Monitor the complete transfer. CSR checks every 10 million loop
  // iterations provide bounded progress visibility without per-beat logging.
  task automatic monitor_dma_to_completion();
    for (int unsigned cycle = 0; cycle < WATCHDOG_CYCLES; cycle++) begin
      @(posedge clk);
      if ((cycle % 10_000_000) == 0)
        check_active_status(cycle);
      if (dut.i_axi_dma_ctrl.ctrl_fsm_ps == 2'b11) begin
        $display("* TESTCASE FAILED");
        $fatal(1, "AXI_DMA_2GIB: DMA entered ERROR");
      end
      if (dut.i_axi_dma_ctrl.ctrl_fsm_ps == 2'b00 &&
          dut.i_axi_dma_ctrl.bytes_remaining == 0) begin
        check_final_results();
        return;
      end
    end

    // A hung DMA fails with the last remaining-byte count and FSM state.
    $display("* TESTCASE FAILED");
    $fatal(1, "AXI_DMA_2GIB: timeout remaining=0x%08x fsm=0x%0x",
           dut.i_axi_dma_ctrl.bytes_remaining,
           dut.i_axi_dma_ctrl.ctrl_fsm_ps);
  endtask

  // Top-level test scenario.
  initial begin
    reset_dut();
    program_dma();
    wait_for_dma_start();
    monitor_dma_to_completion();
    $display("AXI_DMA_2GIB: PASS");
    $display("* TESTCASE PASSED");
    $finish;
  end

endmodule
