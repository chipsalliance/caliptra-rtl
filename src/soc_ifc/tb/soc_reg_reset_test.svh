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

    logic [2:0] random_security_state; 


    begin

      $display("\nExecuting task soc_reg_pwron_test"); 
      $display("---------------------------------\n");

      // set_security_state('{device_lifecycle: DEVICE_PRODUCTION, debug_locked: DEBUG_LOCKED});
      if (ss_name == "RANDOM") begin
        random_security_state = $urandom_range(0, 7); 
        set_security_state(security_state_t'(random_security_state)); 
      end else begin
        random_security_state = get_ss_code(ss_name);
        set_security_state(security_state_t'(random_security_state)); 
      end
      sim_dut_init();

      tc_ctr = tc_ctr + 1;

      $display("Current security state = 0b%03b", security_state);

      soc_regnames = get_soc_regnames_minus_intr();

      $display ("0a. Checking Power-on values\n"); 

      // ---------------------------------------------------------------
      // Phase 1. Inialize soc_regs ON COLD BOOT, then check values  
      // ---------------------------------------------------------------
      $display ("1. Init values beyond reset at start of simulation "); 
      sb.record_reset_values(0, COLD_RESET);

      read_regs(GET_APB, soc_regnames, 0, 3);

      simulate_caliptra_boot();

      repeat (10) @(posedge clk_tb); 
      
      // FUSE_WR_DONE and BOOTFSM_GO are both 'h1
      // no point in checking over ahb; pwron is long done

      // ---------------------------------------------------------------
      // Phase 2. Repeat COLD BOOT, then check values  
      // ---------------------------------------------------------------
      $display ("1. Init values after asserting new cold reset"); 
      reset_dut();

      sb.del_all();

      sb.record_reset_values(0, COLD_RESET);

      read_regs(GET_APB, soc_regnames, 0, 3);

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
    strq_t soc_regnames;

    logic [2:0] random_security_state; 

    dword_t flow_status; 
    dword_t reset_reason; 

    WordTransaction transaction; 

    begin
      $display("\nExecuting task soc_reg_wrmrst_test"); 
      $display("----------------------------------\n");

      transaction = new(); 

      // ---------------------------------------------------------------
      // Phase 1. Inialize soc_regs ON COLD BOOT, overwrite w/new values 
      // ---------------------------------------------------------------

      if (ss_name == "RANDOM") begin 
        random_security_state = $urandom_range(0, 7); 
        set_security_state(security_state_t'(random_security_state)); 
      end else begin
        random_security_state = get_ss_code(ss_name);
        set_security_state(security_state_t'(random_security_state)); 
      end

      sim_dut_init();

      tc_ctr = tc_ctr + 1;

      $display ("\n1a. Write to registers after cold boot and check back writes");

      soc_regnames = get_soc_regnames_minus_intr();  

      foreach (soc_regnames[ix]) begin
        if (soc_regnames[ix] == "CPTRA_FUSE_WR_DONE") begin
          soc_regnames.delete(ix);  // can cause problem downstream if fuse_wr_done == True 
          break;
        end
      end

      write_regs(SET_APB, soc_regnames, 0, 3);
      read_regs(GET_APB, soc_regnames, 0, 3); // just so we see what was written

      simulate_caliptra_boot();

      repeat (10) @(posedge clk_tb); 


      // -----------------------------------------------------------------
      // Phase 2. Perform Warm Reset, read values over APB & AHB 
      // -----------------------------------------------------------------
      $display ("\n2a. Perform a warm reset then just read regs"); 

      sb.del_all();
      warm_reset_dut(); 

      sb.record_reset_values(0, WARM_RESET);
      wait (ready_for_fuses == 1'b1);

      // Some registers need update for specific fields
      flow_status = update_CPTRA_FLOW_STATUS(ready_for_fuses); 
      reset_reason = update_CPTRA_RESET_REASON(1, 0);

      sb.del_entries("CPTRA_FLOW_STATUS");
      transaction.update_byname("CPTRA_FLOW_STATUS", flow_status, 0);    
      sb.record_entry(transaction, SET_DIRECT); 

      sb.del_entries("CPTRA_RESET_REASON");
      transaction.update_byname("CPTRA_RESET_REASON", reset_reason, 0);    
      sb.record_entry(transaction, SET_DIRECT); 


      // expect old sticky values which are different from power-on values
      read_regs(GET_APB, soc_regnames, 0, 3);      

      simulate_caliptra_boot();

      $display ("WRM_RST_TEST: After caliptra boot, Ready for fuses = %d, Flow status value is %x", ready_for_fuses, flow_status);  // DEBUG

      sb.del_entries("CPTRA_FLOW_STATUS");
      flow_status = update_CPTRA_FLOW_STATUS(ready_for_fuses); 
      transaction.update_byname("CPTRA_FLOW_STATUS", flow_status, 0);    
      transaction.display(); // DEBUG


      // task above updates bootfsm_go so need to update scoreboard accordingly 
      sb.del_entries("CPTRA_BOOTFSM_GO");
      transaction.update_byname("CPTRA_BOOTFSM_GO", 32'h1, 0);    
      sb.record_entry(transaction, SET_APB);

      read_regs(GET_AHB, soc_regnames, 0, 3);

      error_ctr = sb.err_count;
    end

  endtask // soc_reg_wrmrst_test;
