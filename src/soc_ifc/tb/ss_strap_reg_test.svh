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
// ss_strap_reg_test()
//----------------------------------------------------------------
task ss_strap_reg_test;
    // SS Straps  Register Test 
  
    int tid = 0; // optional to increment UNLESS multiple writes to same address 
    strq_t ss_strap_soc_rw_regnames;
    strq_t ss_strap_soc_ro_regnames;
  
    begin
      $display("\nExecuting task ss_strap_reg_test"); 
      $display("----------------------------\n");
  
      $display("Current security state = 0b%03b", security_state);
      tc_ctr = tc_ctr + 1;
  
      ss_strap_soc_rw_regnames = get_ss_strap_regnames();
  
      foreach (_soc_register_dict[rkey]) begin
        if (str_startswith(rkey, "SS_GENERIC_FW_EXEC_CTRL")) begin 
          add_to_strq(ss_strap_soc_rw_regnames, rkey); // Add to rw queue for appropriate testing
          add_to_strq(ss_strap_soc_ro_regnames, rkey); // Add to ro queue for appropriate testing
        end
      end
      add_to_strq(ss_strap_soc_ro_regnames, "SS_OCP_LOCK_CTRL");
      add_to_strq(ss_strap_soc_ro_regnames, "SS_DEBUG_INTENT");
  
      // I. Write over AXI, read over AXI then read again over AHB
  
      $display ("1a. Writing using AXI 3 cycles apart");
      write_regs(SET_AXI, ss_strap_soc_rw_regnames, tid, 3);
      write_regs(SET_AXI, ss_strap_soc_ro_regnames, tid, 3, FAIL);
  
      repeat (10) @(posedge clk_tb);
  
      $display ("\n1b. Reading over AXI 3 cycles apart"); 
      read_regs(GET_AXI, ss_strap_soc_rw_regnames, tid, 3);
      read_regs(GET_AXI, ss_strap_soc_ro_regnames, tid, 3);
  
      repeat (10) @(posedge clk_tb);
      tid = 1;
  
      $display ("1c. Writing again using AXI 3 cycles apart");
      write_regs(SET_AXI, ss_strap_soc_rw_regnames, tid, 3);
      write_regs(SET_AXI, ss_strap_soc_ro_regnames, tid, 3, FAIL);
  
      repeat (10) @(posedge clk_tb);
  
      $display ("\n1d. Reading again over AXI 3 cycles apart"); 
      read_regs(GET_AXI, ss_strap_soc_rw_regnames, tid, 3);
      read_regs(GET_AXI, ss_strap_soc_ro_regnames, tid, 3);
  
      simulate_caliptra_boot();
  
      $display ("\n1e. Reading over AHB 3 cycles apart");
      read_regs(GET_AHB, ss_strap_soc_rw_regnames, tid, 3);
      read_regs(GET_AHB, ss_strap_soc_ro_regnames, tid, 3);
  
  
      // II. Swap -- Write over AHB, read over AHB then read over AXI
  
      repeat (20) @(posedge clk_tb);
      sb.del_all();
  
      // Massive failures  -- debugging
      $display ("\n2a. Writing over AHB 3 cycles apart");
      write_regs(SET_AHB, ss_strap_soc_rw_regnames, tid, 3, FAIL);
      write_regs(SET_AHB, ss_strap_soc_ro_regnames, tid, 3);
  
      $display ("\n2b. Read over AHB 3 cycles apart");
      read_regs(GET_AHB, ss_strap_soc_rw_regnames, tid, 3);
      read_regs(GET_AHB, ss_strap_soc_ro_regnames, tid, 3);
  
      $display ("\n2c. Read over AXI 3 cycles apart");
      read_regs(GET_AXI, ss_strap_soc_rw_regnames, tid, 3);
      read_regs(GET_AXI, ss_strap_soc_ro_regnames, tid, 3);
  
  
      // III. Repeat "I". Attempt to write over AXI, read over AHB and AXI     
  
      repeat (20) @(posedge clk_tb);
      sb.del_all();
  
      $display ("3a. Writing using AXI 3 cycles apart");
      write_regs(SET_AXI, ss_strap_soc_rw_regnames, tid, 3, FAIL);
      write_regs(SET_AXI, ss_strap_soc_ro_regnames, tid, 3, FAIL);
  
      repeat (10) @(posedge clk_tb);
  
      $display ("\n3b. Reading over AHB 3 cycles apart");
      read_regs(GET_AHB, ss_strap_soc_rw_regnames, tid, 3);
      read_regs(GET_AHB, ss_strap_soc_ro_regnames, tid, 3);
  
      repeat (10) @(posedge clk_tb);
  
      $display ("\n3c. Reading over AXI 3 cycles apart"); 
      read_regs(GET_AXI, ss_strap_soc_rw_regnames, tid, 3);
      read_regs(GET_AXI, ss_strap_soc_ro_regnames, tid, 3);
  
      error_ctr = sb.err_count;
  
    end
  endtask // ss_strap_reg_test
  
  
  
  
  
  
