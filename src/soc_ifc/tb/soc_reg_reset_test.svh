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
  task soc_reg_pwron_test;    

    int tid = 0; // TID is to be updated ONLY if multiple writes to an address 
    strq_t soc_regnames;

    logic [2:0] random_security_state; 

    begin
      $display("\nExecuting task soc_reg_pwron_test"); 
      $display("---------------------------------\n");

      // set_security_state('{device_lifecycle: DEVICE_PRODUCTION, debug_locked: DEBUG_LOCKED});
      random_security_state = $urandom_range(1, 7); 
      set_security_state(security_state_t'(random_security_state)); 
      sim_dut_init();

      tc_ctr = tc_ctr + 1;

      $display("Current security state = 0b%03b", security_state);

      soc_regnames = get_soc_regnames(); 

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
  task soc_reg_wrmrst_test;

    int tid = 0; // TID is to be updated ONLY if multiple writes to an address 
    strq_t soc_regnames;

    logic [2:0] random_security_state; 

    begin
      $display("\nExecuting task soc_reg_wrmrst_test"); 
      $display("----------------------------------\n");

      // ---------------------------------------------------------------
      // Phase 1. Inialize soc_regs ON COLD BOOT, overwrite w/new values 
      // ---------------------------------------------------------------

      random_security_state = $urandom_range(1, 7); 
      set_security_state(security_state_t'(random_security_state)); 
      sim_dut_init();

      tc_ctr = tc_ctr + 1;

      $display ("\n1a. Write to registers after cold boot and check back writes");

      // FIXME. Using get_soc_regnames() doesn't work yet.  Using just 
      // get_fuse_regnames() first.
      soc_regnames = get_fuse_regnames(); // get_soc_regnames();  
      foreach (soc_regnames[ix]) begin
        if (soc_regnames[ix] == "CPTRA_FUSE_WR_DONE") begin
          soc_regnames.delete(ix);  // can cause problem downstream if fuse_wr_done == True 
          break;
        end
      end

      // update_exp_regval("CPTRA_GENERIC_INPUT_WIRES*", ... SET_DIRECT) -- TODO. 
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

      // expect old sticky values which are different from power-on values
      read_regs(GET_APB, soc_regnames, 0, 3);      

      simulate_caliptra_boot();

      read_regs(GET_AHB, soc_regnames, 0, 3);

      error_ctr = sb.err_count;
    end

  endtask // soc_reg_wrmrst_test;
