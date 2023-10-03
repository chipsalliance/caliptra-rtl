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
  // rvtime_reg_test()
  // 
  // Test writing & reading of RV_MTIME LOW/HIGH Registers 
  //----------------------------------------------------------------
  task rvtime_reg_test;
    // Check RVTIME_L update operations, then effect on RVTIME_H
    // These registers are treated differently from the scoreboard based checks
    // since they are self-updated without a need for an external event  

    string      rvtime_l = "INTERNAL_RV_MTIME_L";        
    string      rvtime_h = "INTERNAL_RV_MTIME_H";        

    word_addr_t rvtime_haddr, rvtime_laddr;
    dword_t     rvtime_hval, rvtime_lval; // most recent value during a fetch or update

    logic [31:0] update_ctr = 'h0; 
    logic [31:0] fetch_ctr = 'h0; 

    dword_t flow_status; 
    dword_t reset_reason; 

    int tid = 0; // TID is to be updated ONLY if multiple writes to an address 

    WordTransaction wrtrans;


    begin
      $display();
      $display("Executing task rvtime_reg_test"); 
      $display("------------------------------\n");

      // TODO. Randomize 
      set_security_state('{device_lifecycle: DEVICE_PRODUCTION, debug_locked: DEBUG_UNLOCKED});

      tc_ctr = tc_ctr + 1;

      wrtrans = new();

      rvtime_haddr = socregs.get_addr(rvtime_h);  
      rvtime_laddr = socregs.get_addr(rvtime_l);  

      // Skip wrting & reading over AHB until post reset sequencing is done 
      // THEN, update scoreboard entry accordingly for a couple of registers which 
      // are written using APB as part of Caliptra boot.  Scoreboard update not 
      // needed for readonly fields which are set directly by wires.
      simulate_caliptra_boot();

      repeat (20) @(posedge clk_tb);
      sb.del_all();
      error_ctr = 0;

      update_CPTRA_FLOW_STATUS(ready_for_fuses, `REG_HIER_BOOT_FSM_PS);


      $display ("\n-------------------------------------------------------------");
      $display ("1a. Writing/Reading using AHB/AHB");
      $display ("-------------------------------------------------------------");

      // ** Write & check RV_MTIME_H not close to overflow **
      wrtrans.update(rvtime_haddr, 0, tid); 
      wrtrans.randomize();
      wrtrans.update_data(wrtrans.data & 32'h7fff_ffff); 

      write_reg_trans(SET_AHB, wrtrans);  
      read_regs(GET_AHB, {rvtime_h}, tid, 3);

      // ** Write to RV_MTIME_L & check val not close to overflow **
      wrtrans.update(rvtime_laddr, 0, tid); 
      wrtrans.randomize();
      wrtrans.update_data(wrtrans.data & 32'h7fff_ffff); 

      rvtime_lval = wrtrans.data;
      write_reg_trans(SET_AHB, wrtrans);  
      update_ctr = cycle_ctr_since_pwrgood;  

      repeat (3) @(posedge clk_tb);
      read_reg_chk_inrange(GET_AHB, rvtime_l, tid, rvtime_lval + 'd3 , rvtime_lval + 'd23); 

      // ** Write to RV_MTIME_L & check for overflow + update of both RV_MTIME_L + RV_MTIME_H **
      rvtime_lval = 32'hffff_fff0;  // 16 cycles from wraparound 
      wrtrans.update(rvtime_laddr, rvtime_lval, tid);  
      update_ctr = cycle_ctr_since_pwrgood;  
      write_reg_trans(SET_AHB, wrtrans);  

      repeat (3) @(posedge clk_tb);
      wrtrans.update(rvtime_haddr, 32'hffff_fffe, tid);  // < 16 cycles from increment 
      write_reg_trans(SET_AHB, wrtrans);  

      repeat (13) @(posedge clk_tb);
      read_reg_chk_inrange(GET_AHB, rvtime_l, tid, 'h1, 'h14); 

      repeat (3) @(posedge clk_tb);
      read_reg_chk_inrange(GET_AHB, rvtime_h, tid, 32'hffff_ffff, 32'hffff_ffff);

      @(posedge clk_tb);
      rvtime_lval = 32'hffff_fff0 + (cycle_ctr_since_pwrgood - update_ctr);  
      rvtime_hval = 32'hffff_ffff;

      $display ("\n-------------------------------------------------------------");
      $display ("1b. Writing/Reading using APB/APB + AHB"); 
      $display ("-------------------------------------------------------------");

      // ** Write & check RV_MTIME_H ** 
      wrtrans.update(rvtime_haddr, 0, tid); 
      wrtrans.randomize();

      write_reg_trans(SET_APB, wrtrans);  
      read_regs(GET_APB, {rvtime_h}, tid, 3); 

      // ** Write to RV_MTIME_L & check val ** 
      wrtrans.update(rvtime_laddr, 0, tid); 
      wrtrans.randomize();

      write_reg_trans(SET_APB, wrtrans);  

      repeat (3) @(posedge clk_tb);
      rvtime_lval = 32'hffff_fff0 + (cycle_ctr_since_pwrgood - update_ctr); 

      read_reg_chk_inrange(GET_AHB, rvtime_l, tid, rvtime_lval - 'd5,  rvtime_lval + 'd15); 
      @(posedge clk_tb);


      // ** Repeat reads over AHB ** 
      repeat (3) @(posedge clk_tb);
      rvtime_lval = 32'hffff_fff0 + (cycle_ctr_since_pwrgood - update_ctr); 

      read_reg_chk_inrange(GET_AHB, rvtime_l, tid, rvtime_lval - 'd5,  rvtime_lval + 'd15); 
      @(posedge clk_tb);

      read_reg_chk_inrange(GET_AHB, rvtime_h, tid, rvtime_hval, rvtime_hval); 
      @(posedge clk_tb);

      // There's no overflow of eiter MTIME register with APB writes since MTIME_L just 
      // rolled passed 0. -- no check needed  


      $display ("\n-------------------------------------------------------------");
      $display ("1c. Writing/Reading using AHB/APB"); 
      $display ("-------------------------------------------------------------");

      // ** Write & check RV_MTIME_H this time preparing for rolloever ** 
      wrtrans.update(rvtime_haddr, 32'hffff_ffff, tid); 
      write_reg_trans(SET_AHB, wrtrans);  
      repeat (3) @(posedge clk_tb);

      // ** Write to RV_MTIME_L & check val ** 
      wrtrans.update(rvtime_laddr, 32'hffff_ffff, tid); 
      write_reg_trans(SET_AHB, wrtrans);  


      repeat (3) @(posedge clk_tb);
      read_reg_chk_inrange(GET_APB, rvtime_h, tid, 'h0, 'h0); 
      repeat (3) @(posedge clk_tb);
      read_reg_chk_inrange(GET_APB, rvtime_l, tid, 'h1, 'h20); 

      // ** Write random values to RV_TIME_H/L preparing for warm reset **  
      wrtrans.update(rvtime_haddr, 0, tid);
      wrtrans.randomize();
      write_reg_trans(SET_AHB, wrtrans);  
      rvtime_hval = wrtrans.data;
      repeat (3) @(posedge clk_tb);

      wrtrans.update(rvtime_laddr, 0, tid);
      wrtrans.randomize();
      wrtrans.update_data(wrtrans.data & 32'h7fff_ffff);
      write_reg_trans(SET_AHB, wrtrans);  
      rvtime_lval = wrtrans.data;
      update_ctr = cycle_ctr_since_pwrgood;
      repeat (3) @(posedge clk_tb);

      // There's no overflow of eiter MTIME register -- no check needed  


      // -----------------------------------------------------------------
      // Phase 2. Perform Warm Reset, read values over APB 
      // -----------------------------------------------------------------
      $display ("\n-------------------------------------------------------------");
      $display ("2a. Perform a warm reset then just read regs"); 
      $display ("-------------------------------------------------------------");

      sb.del_all();
      warm_reset_dut(); 

      sb.record_reset_values(0, WARM_RESET);
      wait (ready_for_fuses == 1'b1);

      // Some registers need update for specific fields
      flow_status = update_CPTRA_FLOW_STATUS(ready_for_fuses, `REG_HIER_BOOT_FSM_PS); 
      reset_reason = update_CPTRA_RESET_REASON(1, 0);

      // expect old sticky values which are different from power-on values
      read_reg_chk_inrange(GET_APB, {rvtime_h}, tid, rvtime_hval, rvtime_hval);
      @(posedge clk_tb);

      rvtime_lval = rvtime_lval + (cycle_ctr_since_pwrgood - update_ctr);  
      read_reg_chk_inrange(GET_APB, {rvtime_l}, tid, rvtime_lval - 'd5, rvtime_lval + 'd15); 
      @(posedge clk_tb);

      // -----------------------------------------------------------------
      // Phase 3. Perform Cold Reset, read values over APB 
      // -----------------------------------------------------------------
      $display ("\n-------------------------------------------------------------");
      $display ("3a. Perform a cold reset then just read regs"); 
      $display ("-------------------------------------------------------------");

      reset_dut();
      sb.del_all();

      sb.record_reset_values(0, COLD_RESET);
      wait (ready_for_fuses == 1'b1);

      // Some registers need update for specific fields
      flow_status =  update_CPTRA_FLOW_STATUS(ready_for_fuses, `REG_HIER_BOOT_FSM_PS);
      reset_reason = update_CPTRA_RESET_REASON(1, 0);

      // expect old sticky values which are different from power-on values
      read_reg_chk_inrange(GET_APB, {rvtime_h}, tid, 0, 0); 
      @(posedge clk_tb);
      read_reg_chk_inrange(GET_APB, {rvtime_l}, tid, 'd1, 'd20);
      @(posedge clk_tb);

      error_ctr += sb.err_count;

    end

  endtask // check_rvtime_regs
