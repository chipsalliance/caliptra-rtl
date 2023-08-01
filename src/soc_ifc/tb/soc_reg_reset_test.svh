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
  // soc_reg_pwron_test()
  // 
  // Test power-on reset values of ALL soc registers 
  //----------------------------------------------------------------
  task soc_reg_pwron_test(input string ss_name="RANDOM");    

    int tid = 0; // TID is to be updated ONLY if multiple writes to an address 
    strq_t soc_regnames;
    int iq [$];

    logic [2:0] random_security_state; 

    WordTransaction rdtrans = new();
    string rname_dyn; 
    dword_t flow_status; 
    dword_t regval; 

    int tmp_i = 1000; // max 1000 cycle wait time

    begin
      print_banner("\nExecuting task soc_reg_pwron_test", "="); 

      set_security_state_byname(ss_name); 
      sim_dut_init();

      tc_ctr = tc_ctr + 1;
      $display("Current security state = 0b%03b", security_state);

      soc_regnames = get_soc_regnames_minus_intr();
      del_from_strq(soc_regnames, "INTERNAL_RV_MTIME_L"); // Exclude CPTRA_RV_MTIME_L


      $display ("0a. Checking Power-on values\n"); 

      print_banner("Phase 1. Inialize soc_regs ON COLD BOOT, then check values");
      // --------------------------------------------------------------------------

      sb.record_reset_values(0, COLD_RESET);
      flow_status = update_CPTRA_FLOW_STATUS(ready_for_fuses, `REG_HIER_BOOT_FSM_PS); 
      @(posedge clk_tb);

      read_regs(GET_APB, soc_regnames, 0, 3);
      _read_special_register(GET_APB, "INTERNAL_RV_MTIME_L", 0); // *** special register ***

      simulate_caliptra_boot();
      flow_status = update_CPTRA_FLOW_STATUS(ready_for_fuses, `REG_HIER_BOOT_FSM_PS); 

      // *** begin - special registers GENERIC_INPUT_WIRES ***
      if (cptra_noncore_rst_b_tb == 1'b0) begin
        fork 
          begin 
            wait (cptra_noncore_rst_b_tb == 1'b1);
            $display("TB. INFO Finished waiting for cptra_noncore_rst_b_tb; current value = 1'b%b", cptra_noncore_rst_b_tb);
          end
          begin
            repeat(tmp_i) @(posedge clk_tb);
            $display("TB. ERROR Timed out while waiting for cptra_noncore_rst_b_tb; current value = 1'b%b", cptra_noncore_rst_b_tb);
          end
        join_any
      end

      _read_special_register(GET_APB, "CPTRA_GENERIC_INPUT_WIRES0", 0);
      _read_special_register(GET_APB, "CPTRA_GENERIC_INPUT_WIRES1", 0);
      // *** end - special registers ***


      repeat (10) @(posedge clk_tb); 
      
      // FUSE_WR_DONE and BOOTFSM_GO are both 'h1
      // no point in checking over ahb; pwron is long done


      print_banner("Phase 2. Repeat COLD BOOT, init explicitly as needed, then check values");
      // ---------------------------------------------------------------------------------------

      reset_dut();

      sb.del_all();

      sb.record_reset_values(0, COLD_RESET);
      reset_generic_input_wires(0, 0); 

      read_regs(GET_APB, soc_regnames, 0, 3);
      _read_special_register(GET_APB, "INTERNAL_RV_MTIME_L", 0); // *** special register ***

      error_ctr = sb.err_count;
    end

  endtask // soc_reg_pwron_test  



  //----------------------------------------------------------------
  // soc_reg_wrmrst_test()
  //
  // Test warm reset warm reset values of ALL soc registers 
  //----------------------------------------------------------------
  task soc_reg_wrmrst_test(input string ss_name="RANDOM");    

    int tid = 0; // TID is to be updated ONLY if multiple writes to an address 
    strq_t soc_regnames, fuse_regnames;

    logic [2:0] random_security_state; 

    dword_t flow_status; 
    dword_t reset_reason; 

    WordTransaction transaction; 

    string rname_dyn; 

    begin
      print_banner("\nExecuting task soc_reg_wrmrst_test", "="); 

      transaction = new(); 

      set_security_state_byname("RANDOM");
      sim_dut_init();

      tc_ctr = tc_ctr + 1;

      fuse_regnames = get_fuse_regnames();
      soc_regnames = get_soc_regnames_minus_fuse_intr();

      foreach (soc_regnames[ix]) begin
        if ((soc_regnames[ix] == "CPTRA_FUSE_WR_DONE") || (soc_regnames[ix] == "CPTRA_TRNG_STATUS") || 
            (soc_regnames[ix] == "CPTRA_TRNG_DATA")) begin 
          soc_regnames.delete(ix);  // can cause problem downstream if fuse_wr_done == True 
          continue; 
        end
      end

      del_from_strq(soc_regnames, "INTERNAL_RV_MTIME_L"); // Exclude CPTRA_RV_MTIME_L


      tphase = "1";
      print_banner("\nPhase 1. Initialize registers after cold boot, overwrite and check");
      // ---------------------------------------------------------------------------------

      write_regs(SET_APB, fuse_regnames, 0, 3);
      read_regs(GET_APB, fuse_regnames, 0, 3); // just so we see what was written

      // Have to wait until after cptra_noncore_rst_b_tb is high
      //  write_regs(SET_APB, soc_regnames, 0, 3);
      //  read_regs(GET_APB, soc_regnames, 0, 3); // just so we see what was written

      simulate_caliptra_boot();
      wait (cptra_noncore_rst_b_tb == 1'b1);

      repeat (5) @(posedge clk_tb); 

      write_regs(SET_APB, soc_regnames, 0, 3);
      read_regs(GET_APB, soc_regnames, 0, 3); // just so we see what was written

      repeat (5) @(posedge clk_tb); 


      tphase = "2a";
      print_banner("\nPhase 2a. Perform a warm reset then just read regs over APB"); 
      // --------------------------------------------------------------------------

      sb.del_all();
      warm_reset_dut(); 

      sb.record_reset_values(0, WARM_RESET);
      wait (ready_for_fuses == 1'b1);

      // Some registers need update for specific fields
      flow_status = update_CPTRA_FLOW_STATUS(ready_for_fuses, `REG_HIER_BOOT_FSM_PS); 
      reset_reason = update_CPTRA_RESET_REASON(1, 0);


      $display("TB DEBUG. -- caliptra flow status updated = 0x%08x --", flow_status);
      sb.del_entries("CPTRA_FLOW_STATUS");
      transaction.update_byname("CPTRA_FLOW_STATUS", flow_status, 0);    
      sb.record_entry(transaction, SET_DIRECT); 

      sb.del_entries("CPTRA_RESET_REASON");
      transaction.update_byname("CPTRA_RESET_REASON", reset_reason, 0);    
      sb.record_entry(transaction, SET_DIRECT); 

      // Treat GENERIC_INPUT_WIRES slightly differently
      del_from_strq(soc_regnames, "CPTRA_GENERIC_INPUT_WIRES0"); 
      del_from_strq(soc_regnames, "CPTRA_GENERIC_INPUT_WIRES1"); 


      // expect old sticky values which are different from power-on values
      read_regs(GET_APB, fuse_regnames, 0, 3);      
      read_regs(GET_APB, soc_regnames, 0, 3);      

      // *** begin - special registers ***
      _read_special_register(GET_APB, "INTERNAL_RV_MTIME_L", 0);
      _read_special_register(GET_APB, "CPTRA_GENERIC_INPUT_WIRES0", 0);
      _read_special_register(GET_APB, "CPTRA_GENERIC_INPUT_WIRES1", 0);
      // *** end - special registers ***


      tphase = "2b";
      print_banner("\nPhase 2b. Simulate boot and read regs over AHB adjusting for boot regs"); 
      // -------------------------------------------------------------------------------------

      simulate_caliptra_boot();

      $display ("WRM_RST_TEST: After caliptra boot, Ready for fuses = %d, Flow status value is %x", ready_for_fuses, flow_status);  // DEBUG

      sb.del_entries("CPTRA_FLOW_STATUS");
      flow_status = update_CPTRA_FLOW_STATUS(ready_for_fuses, `REG_HIER_BOOT_FSM_PS); 
      transaction.update_byname("CPTRA_FLOW_STATUS", flow_status, 0);    
      transaction.display(); // DEBUG
      sb.record_entry(transaction, SET_APB);


      // task above updates bootfsm_go so need to update scoreboard accordingly 
      sb.del_entries("CPTRA_BOOTFSM_GO");
      transaction.update_byname("CPTRA_BOOTFSM_GO", 32'h1, 0);    
      sb.record_entry(transaction, SET_APB);

      read_regs(GET_AHB, fuse_regnames, 0, 3);
      read_regs(GET_AHB, soc_regnames, 0, 3);

      // *** begin - special registers ***
      _read_special_register(GET_AHB, "INTERNAL_RV_MTIME_L", 0);
      _read_special_register(GET_AHB, "CPTRA_GENERIC_INPUT_WIRES0", 0);
      _read_special_register(GET_AHB, "CPTRA_GENERIC_INPUT_WIRES1", 0);
      // *** end - special registers ***
 
      error_ctr = sb.err_count;
    end

  endtask // soc_reg_wrmrst_test;


  //----------------------------------------------------------------
  // _read_special_register()
  // 
  // Registers that have special read outcomes. Uses on global tb-level signals 
  //----------------------------------------------------------------

  task _read_special_register(access_t modifier, string regname, int tid);

    begin
      case (regname)
        "INTERNAL_RV_MTIME_L": read_reg_chk_inrange(modifier, regname, tid, cycle_ctr_since_pwrgood - 'd1 , cycle_ctr_since_pwrgood + 'd20); 

        "CPTRA_GENERIC_INPUT_WIRES0": 
          if (cptra_noncore_rst_b_tb) 
            read_reg_chk_inrange(modifier, regname, tid, generic_input_wires0_q,  generic_input_wires0_q);
          else
            read_reg_chk_inrange(modifier, regname, tid, '0, '0); 

        "CPTRA_GENERIC_INPUT_WIRES1": 
          if (cptra_noncore_rst_b_tb) 
            read_reg_chk_inrange(modifier, regname, tid, generic_input_wires1_q,  generic_input_wires1_q);
          else
            read_reg_chk_inrange(modifier, regname, tid, '0, '0); 

        default: $display( "TB ERROR. Unsupported special register %s", regname);

      endcase

      @(posedge clk_tb);
    end
  endtask 