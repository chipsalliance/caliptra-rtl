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
//======================================================================


  //----------------------------------------------------------------
  // sha_acc_intrblk_test()
  // 
  // Tests SHA ACC interrupt registers over AHB and mode-specific AXI access
  //----------------------------------------------------------------

  logic [3:0] sha_acc_error_internal_intr_r;
  logic       sha_acc_notif_internal_intr_r;
  logic [3:0] sha_acc_error_intr_trig_r;
  logic       sha_acc_notif_intr_trig_r;

  assign sha_acc_error_internal_intr_r = {
    dut.i_sha512_acc_top.i_sha512_acc_csr.field_storage.intr_block_rf.error_internal_intr_r.error3_sts.value,
    dut.i_sha512_acc_top.i_sha512_acc_csr.field_storage.intr_block_rf.error_internal_intr_r.error2_sts.value,
    dut.i_sha512_acc_top.i_sha512_acc_csr.field_storage.intr_block_rf.error_internal_intr_r.error1_sts.value,
    dut.i_sha512_acc_top.i_sha512_acc_csr.field_storage.intr_block_rf.error_internal_intr_r.error0_sts.value
  };

  assign sha_acc_notif_internal_intr_r =
    dut.i_sha512_acc_top.i_sha512_acc_csr.field_storage.intr_block_rf.notif_internal_intr_r.notif_cmd_done_sts.value;

  assign sha_acc_error_intr_trig_r = {
    dut.i_sha512_acc_top.i_sha512_acc_csr.field_storage.intr_block_rf.error_intr_trig_r.error3_trig.value,
    dut.i_sha512_acc_top.i_sha512_acc_csr.field_storage.intr_block_rf.error_intr_trig_r.error2_trig.value,
    dut.i_sha512_acc_top.i_sha512_acc_csr.field_storage.intr_block_rf.error_intr_trig_r.error1_trig.value,
    dut.i_sha512_acc_top.i_sha512_acc_csr.field_storage.intr_block_rf.error_intr_trig_r.error0_trig.value
  };

  assign sha_acc_notif_intr_trig_r =
    dut.i_sha512_acc_top.i_sha512_acc_csr.field_storage.intr_block_rf.notif_intr_trig_r.notif_cmd_done_trig.value;

  // Checks that an AXI write never changes protected SHA interrupt state.
  task automatic monitor_sha_acc_axi_reg(input string regname, input dword_t expected_value, input int num_cycles);
    dword_t observed_value;

    begin
      repeat (num_cycles) begin
        case (regname)
          "SHA_ACC_INTR_BRF_ERROR_INTERNAL_INTR_R": observed_value = sha_acc_error_internal_intr_r;
          "SHA_ACC_INTR_BRF_NOTIF_INTERNAL_INTR_R": observed_value = sha_acc_notif_internal_intr_r;
          "SHA_ACC_INTR_BRF_ERROR_INTR_TRIG_R": observed_value = sha_acc_error_intr_trig_r;
          "SHA_ACC_INTR_BRF_NOTIF_INTR_TRIG_R": observed_value = sha_acc_notif_intr_trig_r;
          default: $fatal(1, "Unsupported SHA interrupt register %s", regname);
        endcase

        if (observed_value !== expected_value) begin
          $error("AXI write changed %s: observed 0x%08x, expected 0x%08x", regname, observed_value, expected_value);
          error_ctr += 1;
          break;
        end
        @(posedge clk_tb);
      end
    end
  endtask

  task sha_acc_intrblk_test; 

    automatic word_addr_t addr; 
    automatic int tid = 0;
    automatic strq_t sha_acc_intrblk_regnames;
    automatic string rname;
    automatic dword_t axi_wrdata;
    automatic dword_t axi_rddata;
    automatic dword_t exp_regval;
    automatic exp_txn_sts_e axi_exp_txn_sts;
    automatic WordTransaction wrtrans, rdtrans;

    begin
      $display("Executing task sha_acc_intrblk_test"); 
      $display("---------------------------------\n");

      tc_ctr = tc_ctr + 1;
      wrtrans = new();
      rdtrans = new();

      // Use the register model as the authoritative list and expected-value source.
      sha_acc_intrblk_regnames = get_sha_acc_intrblk_regnames();
      axi_exp_txn_sts = subsystem_mode_tb ? PASS : ERROR_RESP;

      // Complete boot before exercising the Caliptra-internal AHB register path.
      simulate_caliptra_boot();
      repeat (20) @(posedge clk_tb);

      // Clear queued pre-test transactions without resetting expected register values.
      sb.del_all();
      update_CPTRA_FLOW_STATUS(ready_for_fuses, `REG_HIER_BOOT_FSM_PS);

      $display("\nWriting and reading SHA interrupt registers over AHB, then checking mode-specific AXI access");

      foreach (sha_acc_intrblk_regnames[i]) begin
        rname = sha_acc_intrblk_regnames[i];
        addr = socregs.get_addr(rname);

        // Establish each register's legal AHB state with randomized stimulus.
        wrtrans.update(addr, 0, tid);
        if (!wrtrans.randomize())
          $fatal(1, "Failed to randomize SHA interrupt register transaction for %s", rname);

        write_reg_trans(SET_AHB, wrtrans);
        repeat (3) @(posedge clk_tb);

        // Check RW, RO, W1C, and pulse behavior through the register model.
        rdtrans.update(addr, 0, tid);
        read_reg_trans(GET_AHB, rdtrans);
        exp_regval = socregs.get_exp_regval(rname);
        if (rdtrans.data !== exp_regval) begin
          $error("AHB read mismatch for addr 0x%08x (%s): observed 0x%08x, expected 0x%08x", addr, rname, rdtrans.data, exp_regval);
          error_ctr += 1;
        end

        // Preserve the original directed all-ones clear check for W1C status.
        if ((rname == "SHA_ACC_INTR_BRF_ERROR_INTERNAL_INTR_R") ||
            (rname == "SHA_ACC_INTR_BRF_NOTIF_INTERNAL_INTR_R")) begin
          wrtrans.update_data(32'hffff_ffff);
          write_reg_trans(SET_AHB, wrtrans);
          repeat (3) @(posedge clk_tb);

          rdtrans.update(addr, 0, tid);
          read_reg_trans(GET_AHB, rdtrans);
          exp_regval = socregs.get_exp_regval(rname);
          if ((rdtrans.data !== '0) || (rdtrans.data !== exp_regval)) begin
            $error("W1C clear mismatch for addr 0x%08x (%s): observed 0x%08x, expected 0x%08x", addr, rname, rdtrans.data, exp_regval);
            error_ctr += 1;
          end
        end

        // Subsystem mode permits the configured DMA AXI user, but the interrupt
        // registers remain AXI read-only. Passive mode rejects both directions.
        // Low-level helpers keep the AXI write out of the expected-value model.
        axi_wrdata = ~wrtrans.data;
        if ((rname == "SHA_ACC_INTR_BRF_ERROR_INTERNAL_INTR_R") ||
            (rname == "SHA_ACC_INTR_BRF_NOTIF_INTERNAL_INTR_R") ||
            (rname == "SHA_ACC_INTR_BRF_ERROR_INTR_TRIG_R") ||
            (rname == "SHA_ACC_INTR_BRF_NOTIF_INTR_TRIG_R")) begin
          fork
            write_single_word_axi_sub(addr, axi_wrdata, axi_exp_txn_sts);
            monitor_sha_acc_axi_reg(rname, exp_regval, 10);
          join
        end
        else begin
          write_single_word_axi_sub(addr, axi_wrdata, axi_exp_txn_sts);
        end
        read_single_word_axi_sub(addr, axi_rddata, axi_exp_txn_sts);
        repeat (3) @(posedge clk_tb);

        // In subsystem mode, the successful AXI read must return the AHB state.
        if (subsystem_mode_tb && (axi_rddata !== exp_regval)) begin
          $error("AXI read mismatch for addr 0x%08x (%s): observed 0x%08x, expected 0x%08x", addr, rname, axi_rddata, exp_regval);
          error_ctr += 1;
        end

        // Re-read over AHB to prove the AXI write had no side effects in either mode.
        rdtrans.update(addr, 0, tid);
        read_reg_trans(GET_AHB, rdtrans);
        if (rdtrans.data !== exp_regval) begin
          $error("AXI write changed addr 0x%08x (%s): observed 0x%08x, expected 0x%08x", addr, rname, rdtrans.data, exp_regval);
          error_ctr += 1;
        end
      end
    end

  endtask // sha_acc_intrblk_test
