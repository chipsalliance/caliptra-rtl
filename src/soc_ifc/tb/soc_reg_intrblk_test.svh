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

  // Keeping all declarations and assignments of internal signals for possibly future use
  logic [1:0] global_intr_en_r;  
  logic [7:0] error_intr_en_r;   
  logic [5:0] notif_intr_en_r;   
  logic error_global_intr_r;          // *RO* 
  logic notif_global_intr_r;          // *RO* 
  logic [7:0] error_internal_intr_r;  // *WO*
  logic [5:0] notif_internal_intr_r;  // *WO*
  logic [7:0] error_intr_trig_r;      // *WO*
  logic [5:0] notif_intr_trig_r;      // *WO*
  logic error_internal_intr_count_r;  
  logic error_inv_dev_intr_count_r;             
  logic error_cmd_fail_intr_count_r;            
  logic error_bad_fuse_intr_count_r;            
  logic error_iccm_blocked_intr_count_r;        
  logic error_mbox_ecc_unc_intr_count_r;        
  logic error_wdt_timer1_timeout_intr_count_r;  
  logic error_wdt_timer2_timeout_intr_count_r;  
  logic notif_cmd_avail_intr_count_r;           
  logic notif_mbox_ecc_cor_intr_count_r;        
  logic notif_debug_locked_intr_count_r;        
  logic notif_soc_req_lock_intr_count_r;        
  logic notif_gen_in_toggle_intr_count_r;       
  // Following are already covered via other tests and implications; not needed for INTR_BLOCK 
  // logic error_internal_intr_count_incr_r;       dut.i_soc_ifc_reg.field_storage.intr_block_rf.error_internal_intr_count_incr_r.pulse.value;
  // logic error_inv_dev_intr_count_incr_r;        dut.i_soc_ifc_reg.field_storage.intr_block_rf.error_inv_dev_intr_count_incr_r.pulse.value;
  // logic error_cmd_fail_intr_count_incr_r;       dut.i_soc_ifc_reg.field_storage.intr_block_rf.error_cmd_fail_intr_count_incr_r.pulse.value;
  // logic error_bad_fuse_intr_count_incr_r;       dut.i_soc_ifc_reg.field_storage.intr_block_rf.error_bad_fuse_intr_count_incr_r.pulse.value;
  // logic error_iccm_blocked_intr_count_incr_r;   dut.i_soc_ifc_reg.field_storage.intr_block_rf.error_iccm_blocked_intr_count_incr_r.pulse.value;
  // logic error_mbox_ecc_unc_intr_count_incr_r;   dut.i_soc_ifc_reg.field_storage.intr_block_rf.error_mbox_ecc_unc_intr_count_incr_r.pulse.value;
  // logic error_wdt_timer1_timeout_intr_count_incr_r; dut.i_soc_ifc_reg.field_storage.intr_block_rf.error_wdt_timer1_timeout_intr_count_incr_r.pulse.value;
  // logic error_wdt_timer2_timeout_intr_count_incr_r; dut.i_soc_ifc_reg.field_storage.intr_block_rf.error_wdt_timer2_timeout_intr_count_incr_r.pulse.value;
  // logic notif_cmd_avail_intr_count_incr_r;      dut.i_soc_ifc_reg.field_storage.intr_block_rf.notif_cmd_avail_intr_count_incr_r.pulse.value;
  // logic notif_mbox_ecc_cor_intr_count_incr_r;   dut.i_soc_ifc_reg.field_storage.intr_block_rf.notif_mbox_ecc_cor_intr_count_incr_r.pulse.value;
  // logic notif_debug_locked_intr_count_incr_r;   dut.i_soc_ifc_reg.field_storage.intr_block_rf.notif_debug_locked_intr_count_incr_r.pulse.value;
  // logic notif_soc_req_lock_intr_count_incr_r;   dut.i_soc_ifc_reg.field_storage.intr_block_rf.notif_soc_req_lock_intr_count_incr_r.pulse.value;
  // logic notif_gen_in_toggle_intr_count_incr_r;  dut.i_soc_ifc_reg.field_storage.intr_block_rf.notif_gen_in_toggle_intr_count_incr_r.pulse.value;

  assign global_intr_en_r =        {dut.i_soc_ifc_reg.field_storage.intr_block_rf.global_intr_en_r.error_en.value,
                                    dut.i_soc_ifc_reg.field_storage.intr_block_rf.global_intr_en_r.notif_en.value};
  assign error_intr_en_r =         {dut.i_soc_ifc_reg.field_storage.intr_block_rf.error_intr_en_r.error_internal_en.value,
                                    dut.i_soc_ifc_reg.field_storage.intr_block_rf.error_intr_en_r.error_inv_dev_en.value,
                                    dut.i_soc_ifc_reg.field_storage.intr_block_rf.error_intr_en_r.error_cmd_fail_en.value,
                                    dut.i_soc_ifc_reg.field_storage.intr_block_rf.error_intr_en_r.error_bad_fuse_en.value,
                                    dut.i_soc_ifc_reg.field_storage.intr_block_rf.error_intr_en_r.error_iccm_blocked_en.value,
                                    dut.i_soc_ifc_reg.field_storage.intr_block_rf.error_intr_en_r.error_mbox_ecc_unc_en.value,
                                    dut.i_soc_ifc_reg.field_storage.intr_block_rf.error_intr_en_r.error_wdt_timer1_timeout_en.value,
                                    dut.i_soc_ifc_reg.field_storage.intr_block_rf.error_intr_en_r.error_wdt_timer2_timeout_en};
  assign notif_intr_en_r =         {dut.i_soc_ifc_reg.field_storage.intr_block_rf.notif_intr_en_r.notif_cmd_avail_en.value,
                                    dut.i_soc_ifc_reg.field_storage.intr_block_rf.notif_intr_en_r.notif_mbox_ecc_cor_en.value,
                                    dut.i_soc_ifc_reg.field_storage.intr_block_rf.notif_intr_en_r.notif_debug_locked_en.value,
                                    dut.i_soc_ifc_reg.field_storage.intr_block_rf.notif_intr_en_r.notif_scan_mode_en.value,
                                    dut.i_soc_ifc_reg.field_storage.intr_block_rf.notif_intr_en_r.notif_soc_req_lock_en.value,
                                    dut.i_soc_ifc_reg.field_storage.intr_block_rf.notif_intr_en_r.notif_gen_in_toggle_en.value};
  assign error_global_intr_r =      dut.i_soc_ifc_reg.field_storage.intr_block_rf.error_global_intr_r.agg_sts.value; // *RO*
  assign notif_global_intr_r =      dut.i_soc_ifc_reg.field_storage.intr_block_rf.notif_global_intr_r.agg_sts.value; // *RO*
  assign error_internal_intr_r =   {dut.i_soc_ifc_reg.field_storage.intr_block_rf.error_internal_intr_r.error_wdt_timer2_timeout_sts.value,
                                    dut.i_soc_ifc_reg.field_storage.intr_block_rf.error_internal_intr_r.error_wdt_timer1_timeout_sts.value,
                                    dut.i_soc_ifc_reg.field_storage.intr_block_rf.error_internal_intr_r.error_mbox_ecc_unc_sts.value,
                                    dut.i_soc_ifc_reg.field_storage.intr_block_rf.error_internal_intr_r.error_iccm_blocked_sts.value,
                                    dut.i_soc_ifc_reg.field_storage.intr_block_rf.error_internal_intr_r.error_bad_fuse_sts.value,
                                    dut.i_soc_ifc_reg.field_storage.intr_block_rf.error_internal_intr_r.error_cmd_fail_sts.value,
                                    dut.i_soc_ifc_reg.field_storage.intr_block_rf.error_internal_intr_r.error_inv_dev_sts.value,
                                    dut.i_soc_ifc_reg.field_storage.intr_block_rf.error_internal_intr_r.error_internal_sts.value};
  assign notif_internal_intr_r =   {dut.i_soc_ifc_reg.field_storage.intr_block_rf.notif_internal_intr_r.notif_gen_in_toggle_sts.value,
                                    dut.i_soc_ifc_reg.field_storage.intr_block_rf.notif_internal_intr_r.notif_soc_req_lock_sts.value,
                                    dut.i_soc_ifc_reg.field_storage.intr_block_rf.notif_internal_intr_r.notif_scan_mode_sts.value,
                                    dut.i_soc_ifc_reg.field_storage.intr_block_rf.notif_internal_intr_r.notif_debug_locked_sts.value,
                                    dut.i_soc_ifc_reg.field_storage.intr_block_rf.notif_internal_intr_r.notif_mbox_ecc_cor_sts.value,
                                    dut.i_soc_ifc_reg.field_storage.intr_block_rf.notif_internal_intr_r.notif_cmd_avail_sts.value};            
  assign error_intr_trig_r =       {dut.i_soc_ifc_reg.field_storage.intr_block_rf.error_intr_trig_r.error_wdt_timer2_timeout_trig.value,
                                    dut.i_soc_ifc_reg.field_storage.intr_block_rf.error_intr_trig_r.error_wdt_timer1_timeout_trig.value,
                                    dut.i_soc_ifc_reg.field_storage.intr_block_rf.error_intr_trig_r.error_mbox_ecc_unc_trig.value,
                                    dut.i_soc_ifc_reg.field_storage.intr_block_rf.error_intr_trig_r.error_iccm_blocked_trig.value,
                                    dut.i_soc_ifc_reg.field_storage.intr_block_rf.error_intr_trig_r.error_bad_fuse_trig.value,
                                    dut.i_soc_ifc_reg.field_storage.intr_block_rf.error_intr_trig_r.error_cmd_fail_trig.value,
                                    dut.i_soc_ifc_reg.field_storage.intr_block_rf.error_intr_trig_r.error_inv_dev_trig.value,
                                    dut.i_soc_ifc_reg.field_storage.intr_block_rf.error_intr_trig_r.error_internal_trig.value};
    assign notif_intr_trig_r =     {dut.i_soc_ifc_reg.field_storage.intr_block_rf.notif_intr_trig_r.notif_gen_in_toggle_trig.value,
                                    dut.i_soc_ifc_reg.field_storage.intr_block_rf.notif_intr_trig_r.notif_soc_req_lock_trig.value,
                                    dut.i_soc_ifc_reg.field_storage.intr_block_rf.notif_intr_trig_r.notif_scan_mode_trig.value,
                                    dut.i_soc_ifc_reg.field_storage.intr_block_rf.notif_intr_trig_r.notif_debug_locked_trig.value,
                                    dut.i_soc_ifc_reg.field_storage.intr_block_rf.notif_intr_trig_r.notif_mbox_ecc_cor_trig.value,
                                    dut.i_soc_ifc_reg.field_storage.intr_block_rf.notif_intr_trig_r.notif_cmd_avail_trig.value};

  assign error_internal_intr_count_r =            dut.i_soc_ifc_reg.field_storage.intr_block_rf.error_internal_intr_count_r.cnt.value;
  assign error_inv_dev_intr_count_r =             dut.i_soc_ifc_reg.field_storage.intr_block_rf.error_inv_dev_intr_count_r.cnt.value;
  assign error_cmd_fail_intr_count_r =            dut.i_soc_ifc_reg.field_storage.intr_block_rf.error_cmd_fail_intr_count_r.cnt.value;
  assign error_bad_fuse_intr_count_r =            dut.i_soc_ifc_reg.field_storage.intr_block_rf.error_bad_fuse_intr_count_r.cnt.value;
  assign error_iccm_blocked_intr_count_r =        dut.i_soc_ifc_reg.field_storage.intr_block_rf.error_iccm_blocked_intr_count_r.cnt.value;
  assign error_mbox_ecc_unc_intr_count_r =        dut.i_soc_ifc_reg.field_storage.intr_block_rf.error_mbox_ecc_unc_intr_count_r.cnt.value;
  assign error_wdt_timer1_timeout_intr_count_r =  dut.i_soc_ifc_reg.field_storage.intr_block_rf.error_wdt_timer1_timeout_intr_count_r.cnt.value;
  assign error_wdt_timer2_timeout_intr_count_r =  dut.i_soc_ifc_reg.field_storage.intr_block_rf.error_wdt_timer2_timeout_intr_count_r.cnt.value;
  assign notif_cmd_avail_intr_count_r =           dut.i_soc_ifc_reg.field_storage.intr_block_rf.notif_cmd_avail_intr_count_r.cnt.value;
  assign notif_mbox_ecc_cor_intr_count_r =        dut.i_soc_ifc_reg.field_storage.intr_block_rf.notif_mbox_ecc_cor_intr_count_r.cnt.value;
  assign notif_debug_locked_intr_count_r =        dut.i_soc_ifc_reg.field_storage.intr_block_rf.notif_debug_locked_intr_count_r.cnt.value;
  assign notif_soc_req_lock_intr_count_r =        dut.i_soc_ifc_reg.field_storage.intr_block_rf.notif_soc_req_lock_intr_count_r.cnt.value;
  assign notif_gen_in_toggle_intr_count_r =       dut.i_soc_ifc_reg.field_storage.intr_block_rf.notif_gen_in_toggle_intr_count_r.cnt.value;


  //----------------------------------------------------------------
  // soc_reg_intrblk_test()
  // 
  // Test writing & reading of all soc ifc interrupt block registers 
  //----------------------------------------------------------------
  task soc_reg_intrblk_test; 
    // SoC Register Interrupt Block Test excluding *INCR_R which are automatically tested elsewhere

    word_addr_t addr; 
    int tid = 0; // TID is to be updated ONLY if multiple writes to an address 
    strq_t intrblk_regnames;
    string rname, associated_rname;

    WordTransaction wrtrans, rdtrans;
    strq_t ro_regnames, wo_regnames, wo_associated_regnames;

    logic [31:0] nonzero_cyc = '0; 
    dword_t ahb_wrdata; 

    int changeup; 
    int changedn;
    int changeup_cyc = 0;
    int changedn_cyc = 0;
    dword_t nonzero_regval;
    dword_t final_regval; 
    dword_t associated_regval; 


    begin
      $display("Executing task soc_reg_intrblk_test"); 
      $display("-----------------------------------\n");

      // set_security_state_byname("DEBUG_UNLOCKED_PRODCUTION"); 

      tc_ctr = tc_ctr + 1;

      wrtrans = new();
      rdtrans  = new();

      intrblk_regnames = get_intrblk_regnames_minus_incr();

      // These are read-only registers
      update_exp_regval("INTR_BRF_ERROR_GLOBAL_INTR_R", error_global_intr_r, SET_DIRECT); 
      update_exp_regval("INTR_BRF_NOTIF_GLOBAL_INTR_R", error_global_intr_r, SET_DIRECT); 

      // Write-one to clear regs need special handling
      wo_regnames = { "INTR_BRF_ERROR_INTR_TRIG_R", "INTR_BRF_NOTIF_INTR_TRIG_R" };
      wo_associated_regnames  = { "INTR_BRF_ERROR_INTERNAL_INTR_R",  "INTR_BRF_NOTIF_INTERNAL_INTR_R" };

      repeat (5) @(posedge clk_tb);


      // Skip wrting & reading over AHB until post reset sequencing is done 
      // THEN, update scoreboard entry accordingly for a couple of registers which 
      // are written using APB as part of Caliptra boot.  Scoreboard update not 
      // needed for readonly fields which are set directly by wires.
      simulate_caliptra_boot();
      update_CPTRA_FLOW_STATUS(ready_for_fuses, `REG_HIER_BOOT_FSM_PS);

      repeat (20) @(posedge clk_tb);
      sb.del_all();


      // PHASE I. 1a-d Write-Read register back2back 
      // ------------------------------------------------------------

      $display ("\n------------------------------------------------------------------------------");
      $display ("1a. Writing/Reading back to back using AHB/AHB every 3 cycles");
      $display ("------------------------------------------------------------------------------");
      tphase = "1a";
      write_read_regs(SET_AHB, GET_AHB, intrblk_regnames, tid, 3);

      repeat (20) @(posedge clk_tb);
      // sb.del_all(); // Keep scoreboard entries of writes for next phase 1b 


      $display ("\n------------------------------------------------------------------------------");
      $display ("1b. Read over AHB. Then Writing/Reading back to back using APB/APB every 3 cycles");
      $display ("------------------------------------------------------------------------------");
      tphase = "1b";

      // Read out the data over AHB. Ensure APB writes cannot modify the registers 
      // Implicity test neither can AHB reads. 
      foreach (intrblk_regnames[i]) begin
        $display("-- expect no modification over apb writes --");
        rname = intrblk_regnames[i];
        rdtrans.update(socregs.get_addr(rname), 32'hffff_ffff, tid); 
        read_reg_trans(GET_AHB, rdtrans); 
        update_exp_regval(rname, rdtrans.data, SET_DIRECT);  // what has been just read cannot be changed by APB 
        write_regs(SET_APB, {rname}, tid, 3);
      end 
      read_regs(GET_APB, intrblk_regnames, tid, 3);

      repeat (20) @(posedge clk_tb);
      // sb.del_all();   // Keep scoreboard entries of AHB writes from 1a for next phase 1c


      $display ("\n------------------------------------------------------------------------------");
      $display ("1c. Read over APB. Then Writing/Reading back to back using APB/AHB every 3 cycles");
      $display ("------------------------------------------------------------------------------");
      tphase = "1c";

      // Read out the data over APB. Ensure APB writes cannot modify the registers either 
      // Implicity test neither can APB reads. 
      foreach (intrblk_regnames[i]) begin
        $display("-- expect no modification over apb writes --");
        rname = intrblk_regnames[i];
        rname = intrblk_regnames[i];
        rdtrans.update(socregs.get_addr(rname), 32'hffff_ffff, tid); 
        read_reg_trans(GET_APB, rdtrans); 
        update_exp_regval(rname, rdtrans.data, SET_DIRECT);  // what has been read cannot be changed by APB 
        write_regs(SET_APB, {rname}, tid, 3);
      end 
      read_regs(GET_AHB, intrblk_regnames, tid, 3);

      repeat (20) @(posedge clk_tb);
      sb.del_all();   

      // Don't need to test AHB/APB write read anymore; included  in sequences above
      // $display ("1d. Writing/Reading back to back using AHB/APB every 3 cycles");

      $display ("\n------------------------------------------------------------------------------");
      $display ("2a. Handle WO special registers"); 
      $display ("------------------------------------------------------------------------------");
      tphase = "2a";

      // For WO_ASSOCIATED_REGNAMES. 
      // First expect to clear all write-to-clear data (check it too) 
      // Then randomly set bits and ensure only those bits are cleared.
      foreach (wo_associated_regnames[i]) begin
        rname = wo_associated_regnames[i];
        addr = socregs.get_addr(rname);
        $display ("\n-- Handling WO associated register 0x%08x (%s) --", addr, rname);

        $display ("\n  -- First clear register and check --"); 
        wrtrans.update_byname(rname, 32'hffff_ffff, tid); 
        write_reg_trans(SET_AHB, wrtrans);
        repeat (5) @(posedge clk_tb);

        rdtrans.update_byname(rname, 0, tid); 
        read_reg_trans(GET_AHB, rdtrans); 
        if (rdtrans.data != '0)  begin
          $display("TB ERROR. Expected a write ones to clear register for addr 0x%08x (%s). Instead received 0x%08x", 
            addr, rname, rdtrans.data); 
          error_ctr += 1; 
          continue; 
        end
      end

      // Repeat. Longer squence for WO_REGNAMES (Trigger registers).
      // First expect to clear all write-to-clear data (check it too) 
      // Then randomly set bits and ensure only those bits are 1.
      foreach (wo_regnames[i]) begin
        word_addr_t associated_addr; 

        rname = wo_regnames[i];
        associated_rname = rname == "INTR_BRF_ERROR_INTR_TRIG_R" ? "INTR_BRF_ERROR_INTERNAL_INTR_R" :
                           rname == "INTR_BRF_NOTIF_INTR_TRIG_R" ? "INTR_BRF_NOTIF_INTERNAL_INTR_R" : 
                                                                   "UNDEFINED";
        addr = socregs.get_addr(rname);
        associated_addr = socregs.get_addr(associated_rname);

        $display ("\n-- Handling WO register 0x%08x (%s) --", socregs.get_addr(rname), rname);

        // Now randomly set bits after reg is all clear 
        wrtrans.update_byname(rname, 0, tid); 
        wrtrans.randomize() with {wrtrans.data & get_mask(rname) != 0;}; // Require some nonzero value after masking
        ahb_wrdata = wrtrans.data & get_mask(rname);
        // $display ("TB DEBUG. Now randomly set bits to write 0x%08x; w/masking expect to write 0x%08x",
        //   wrtrans.data, ahb_wrdata); 

        $display ("\n  -- Write random trigger data and check for non-zero value, then transition to 0 --"); 


        nonzero_regval = 0;
        fork
          begin : writing_over_ahb
            write_reg_trans(SET_AHB, wrtrans);
            repeat (10) @(posedge clk_tb);
          end

          begin : checking_for_transition 
            monitor_pulsed_reg(rname, 10, nonzero_regval, final_regval, changeup, changedn);
          end
        join

        $display("Inspecting rname %s = addr 0x%08x", rname, addr);
        $display ("TB DEBUG. All said and done; from addr 0x%08x (%s). Directly probed non-zero val = 0x%08x and final val = 0x%08x| expected non-zero = 0x%08x", 
          addr, rname, nonzero_regval, final_regval, ahb_wrdata);

        associated_regval = probe_reg(associated_rname);
        $display ("TB INFO. Checking associated address %s related to trigger %s; associated value = 0x%08x, trigger value %08x", 
          associated_rname, rname, associated_regval, nonzero_regval);
        if (associated_regval != ahb_wrdata)
          $display("TB ERROR value 0x%08x in associated register 0x%08x (%s) does not match trigger value 0x%08x", associated_regval, socregs.get_addr(associated_rname), associated_rname, ahb_wrdata);


        if (changeup && changedn && (nonzero_regval == ahb_wrdata) && (final_regval == '0)) 
          $display ("TB INFO. Both up and down transitions noted correctly; all good with addr 0x%08x (%s)!", addr, rname);
        else begin
          error_ctr += 1; 
          if (!changeup) 
            $display("TB ERROR did not see a transition to non-zero value for addr 0x%08x (%s)", addr, rname); 
          else if (!changedn) 
            $display("TB ERROR did not see a transition back to a zero value for addr 0x%08x (%s) and stayed at 0x%08x", addr, rname, final_regval); 
          if (nonzero_regval != ahb_wrdata)  
            $display("TB ERROR Nonzero value noted for addr 0x%08x (%s) is 0x%08x | expected 0x%08x", addr, rname, nonzero_regval, ahb_wrdata); 
        end

        $display ("\n  -- Finally clear associated register 0x%08x (%s) and check --", associated_addr, associated_rname); 
        wrtrans.update_byname(associated_rname, ahb_wrdata, tid); 
        write_reg_trans(SET_AHB, wrtrans);
        repeat (5) @(posedge clk_tb);

        rdtrans.update_byname(associated_rname, 0, tid); 
        read_reg_trans(GET_AHB, rdtrans); 
        if (rdtrans.data != '0)  begin
          $display("TB ERROR. Expected a write value of 0x%08x to clear register for addr 0x%08x (%s). Instead received 0x%08x", 
            ahb_wrdata, associated_addr, associated_rname, rdtrans.data); 
          error_ctr += 1; 
          continue; 
        end

      end

    end

  endtask // soc_reg_intrblk_test;



  task automatic monitor_pulsed_reg(input string regname, input int num_cycles, 
                                    inout dword_t nonzero_val, inout dword_t final_val, inout up, inout dn);

    dword_t probed_val = 32'hbead_face;
    dword_t latched_val = 32'hbead_face;

    begin

      up = 0;
      dn = 0;

      repeat (num_cycles) begin                    
        probed_val =  probe_reg(regname); 

        if (up && dn) begin
          $display("TB INFO. Saw both up and dn for register %s", regname);
          break;
        end

        up = up | ((probed_val != latched_val)  &&  (latched_val == '0));  // Sticky transition up
        dn = dn | ((probed_val == '0) &&  (latched_val != '0));  // Sticky transition down 
      
        if (probed_val != '0) 
          nonzero_val = probed_val; 

        @(posedge clk_tb);
        latched_val = probed_val;
      end

      final_val = probe_reg(regname); 

      // $display("TB DEBUG. For register %s Checking past initated ahb_write_trans. Probed regval = 0x%08x", rname, probed_val);
    end

  endtask // monitor_pulsed_reg


  function automatic dword_t probe_reg(string regname);

    return (regname == "INTR_BRF_ERROR_INTERNAL_INTR_R") ?  error_internal_intr_r :
           (regname == "INTR_BRF_NOTIF_INTERNAL_INTR_R") ?  notif_internal_intr_r :
           (regname == "INTR_BRF_ERROR_INTR_TRIG_R")     ?  error_intr_trig_r     :
           (regname == "INTR_BRF_NOTIF_INTR_TRIG_R")     ?  notif_intr_trig_r     :  32'hdead_face;

  endfunction


/* 
// Placeholder reference

sequence remain_low__sha_acc_error_internal_intr_r;
  (| ({ dut.i_sha512_acc_top.i_sha512_acc_csr.field_storage.intr_block_rf.error_internal_intr_r.error0_sts.value, 
        dut.i_sha512_acc_top.i_sha512_acc_csr.field_storage.intr_block_rf.error_internal_intr_r.error1_sts.value, 
        dut.i_sha512_acc_top.i_sha512_acc_csr.field_storage.intr_block_rf.error_internal_intr_r.error2_sts.value,
        dut.i_sha512_acc_top.i_sha512_acc_csr.field_storage.intr_block_rf.error_internal_intr_r.error3_sts.value }) == 1'b0); 
endsequence 

property reg_remains_low;
  @(posedge clk_tb)
  disable iff (reg_sva_off) remain_low__sha_acc_error_internal_intr_r;
endproperty

monitor_trans2ones: assert property(reg_remains_low);
*/

