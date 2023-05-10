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

    word_addr_t addr; 
    int tid = 0; // TID is to be updated ONLY if multiple writes to an address 
    strq_t soc_regnames;
    string rname;
    logic [31:0] tmpdata;
    int iq [$]; 

    transaction_t entry;
    transq_t entries; 
    WordTransaction wrtrans, tmptrans; 
    
    dword_t tmpval; 

    begin
      $display("Executing task soc_reg_test"); 
      $display("---------------------------\n");

      // TODO. Randomize 
      set_security_state('{device_lifecycle: DEVICE_PRODUCTION, debug_locked: DEBUG_UNLOCKED});

      // $display("Current security state = 0b%03b", security_state);


      tc_ctr = tc_ctr + 1;

      soc_regnames = get_soc_regnames_minus_fuse_intr();

      // Exclude CPTRA_TRNG_STATUS
      iq = soc_regnames.find_index with (item == "CPTRA_TRNG_STATUS");
      if (iq.size() == 1)
        soc_regnames.delete(iq[0]);

      // Exclude CPTRA_TRNG_DATA*
      soc_regnames.find_index with (str_startswith(item, "CPTRA_TRNG_DATA"));
      foreach(iq[i]) 
        soc_regnames.delete(iq[i]);


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

      update_CPTRA_FLOW_STATUS(ready_for_fuses); 

      $display ("\n1a. Writing/Reading back to back using AHB/AHB every 3 cycles");
      write_read_regs(SET_AHB, GET_AHB, soc_regnames, tid, 3);


      repeat (20) @(posedge clk_tb);
      sb.del_all();

      $display ("\n1b. Writing/Reading back to back using APB/APB every 3 cycles");
      write_read_regs(SET_APB, GET_APB, soc_regnames, tid, 3);


      repeat (20) @(posedge clk_tb);
      sb.del_all();

      $display ("\n1c. Writing/Reading back to back using APB/AHB every 3 cycles");
      write_read_regs(SET_APB, GET_AHB, soc_regnames, tid, 3);


      repeat (20) @(posedge clk_tb);
      sb.del_all();

      $display ("\n1d. Writing/Reading back to back using AHB/APB every 3 cycles");
      write_read_regs(SET_AHB, GET_APB, soc_regnames, tid, 3);

      error_ctr = sb.err_count;
    end
  endtask // soc_reg_test

