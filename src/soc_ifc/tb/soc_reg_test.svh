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
  // soc_reg_test()
  // 
  // Test writing & reading of all non-fuse soc registers 
  //----------------------------------------------------------------
  task soc_reg_test;    
    // SoC Register Test excluding FUSE*, TRNG_DATA* and TRNG_STATUS registers 

    int tid = 0; // TID is to be updated ONLY if multiple writes to an address 
    strq_t soc_regnames;
    int iq [$]; 

    begin
      $display("Executing task soc_reg_test"); 
      $display("---------------------------\n");

      // TODO. Randomize 
      set_security_state('{device_lifecycle: DEVICE_PRODUCTION, debug_locked: DEBUG_UNLOCKED});

      tc_ctr = tc_ctr + 1;

      soc_regnames = get_soc_regnames_minus_fuse_intr();

      // Exclude registers that are covered in separate tasks - fuse and intrblk regs
      // -- Exclude CPTRA_TRNG_STATUS, INTERNAL_RV_MTIME_L/H
      del_from_strq(soc_regnames, "INTERNAL_RV_MTIME_L");
      del_from_strq(soc_regnames, "INTERNAL_RV_MTIME_H");
      del_from_strq(soc_regnames, "CPTRA_TRNG_STATUS");

      // -- Exclude CPTRA_TRNG_DATA*
      delm_from_strq(soc_regnames, "CPTRA_TRNG_DATA");

      repeat (5) @(posedge clk_tb);

      // Skip wrting & reading over AHB until post reset sequencing is done 
      // THEN, update scoreboard entry accordingly for a couple of registers which 
      // are written using APB as part of Caliptra boot.  Scoreboard update not 
      // needed for readonly fields which are set directly by wires.
      simulate_caliptra_boot();

      // PHASE I. 1a-d Write-Read register back2back 
      // ------------------------------------------------------------

      repeat (20) @(posedge clk_tb);
      sb.del_all();
      error_ctr = 0;

      update_CPTRA_FLOW_STATUS(ready_for_fuses, `REG_HIER_BOOT_FSM_PS); 


      $display ("\n-------------------------------------------------------------");
      $display ("1a. Writing/Reading back to back using AHB/AHB every 3 cycles");
      $display ("-------------------------------------------------------------");

      write_read_regs(SET_AHB, GET_AHB, soc_regnames, tid, 3);

      //FIXME. Need to add test for delayed cross modification of INTERNAL_ICCM_LOCK  
      //        if ((addr_name == "INTERNAL_FW_UPDATE_RESET") &  (indata[0] == 1'b1)) begin

      repeat (20) @(posedge clk_tb);
      sb.del_all();

      $display ("\n-------------------------------------------------------------");
      $display ("1b. Writing/Reading back to back using APB/APB every 3 cycles");
      $display ("-------------------------------------------------------------");

      write_read_regs(SET_APB, GET_APB, soc_regnames, tid, 3);

      repeat (20) @(posedge clk_tb);
      sb.del_all();


      $display ("\n-------------------------------------------------------------");
      $display ("1c. Writing/Reading back to back using APB/AHB every 3 cycles");
      $display ("-------------------------------------------------------------");

      write_read_regs(SET_APB, GET_AHB, soc_regnames, tid, 3);

      repeat (20) @(posedge clk_tb);
      sb.del_all();

      $display ("\n-------------------------------------------------------------");
      $display ("1d. Writing/Reading back to back using AHB/APB every 3 cycles");
      $display ("-------------------------------------------------------------");

      write_read_regs(SET_AHB, GET_APB, soc_regnames, tid, 3);
      
      //FIXME. Need to add test for delayed cross modification of INTERNAL_ICCM_LOCK  
      //        if ((addr_name == "INTERNAL_FW_UPDATE_RESET") &  (indata[0] == 1'b1)) begin

      error_ctr += sb.err_count;

    end
  endtask // soc_reg_test

