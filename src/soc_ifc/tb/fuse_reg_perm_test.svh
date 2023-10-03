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
// fuse_reg_perm_test()
// 
// Checks fuse permission tests depending on lock status from FUSE_WR_DONE
//----------------------------------------------------------------
task fuse_reg_perm_test;
  // Fuse Register Test 

  word_addr_t addr; 
  int tid = 0; // optional to increment UNLESS multiple writes to same address 
  strq_t fuse_regnames; 

  WordTransaction wrtrans, rdtrans;
  dword_t exp_data; 
  string rname;

  begin
    $display("Executing task fuse_reg_perm_test"); 
    $display("--------------------------------\n");

    $display("Current security state = 0b%03b", security_state);
    tc_ctr = tc_ctr + 1;

    wrtrans = new();
    rdtrans = new();

    fuse_regnames = get_fuse_regnames(); 


/* Writes to fuse registers are completed. After the done bit is set, 
any subsequent writes to a fuse register will be dropped unless 
  a. there is a power cycle or 
  b. a warm reset or 
  c. caliptra FW allows a write (negotiated through a mailbox command).  */

    init_sim();
    reset_dut();
    wait(ready_for_fuses);

    // -----------------------------------------------------------------
    // PHASE 1. Normal sequence 
    // -----------------------------------------------------------------
    $display ("1a. APB write twice to registers, lock fuses and attempt to modify\n");
    tphase = "1a";

    write_regs(SET_APB, fuse_regnames, 0, 3);  // effect changes
    repeat (5) @(posedge clk_tb);

    write_regs(SET_APB, fuse_regnames, 1, 3);  // effect changes

    simulate_caliptra_boot(); 

    write_regs(SET_APB, fuse_regnames, 2, 3);  // ineffectual 

    // expect everything from TID=1 
    read_regs(GET_APB, fuse_regnames, 1, 3);   
    read_regs(GET_AHB, fuse_regnames, 1, 3); 

    repeat (5) @(posedge clk_tb);

    $display ("\n1b. Following writes should have no effect on locked state -- which is still set!\n");
    tphase = "1b";

    sb.del_all();

    write_single_word_apb(socregs.get_addr("CPTRA_FUSE_WR_DONE"), 32'h0); 

    write_regs(SET_APB, fuse_regnames, 3, 3);
    read_regs(GET_APB, fuse_regnames, 1, 3);
    read_regs(GET_AHB, fuse_regnames, 1, 3);

    repeat (10) @(posedge clk_tb);

    // -----------------------------------------------------------------
    // PHASE 2. Perform Cold Reset and Repeat APB Write & Read from 1a  
    // -----------------------------------------------------------------
    $display ("\n2a. Write to registers after cold boot and check back writes");
    tphase = "2a";

    reset_dut(); // expect to be clearing CPTRA_FUSE_WR_DONE effect 
    reset_exp_data();
    sb.del_all();
    wait(ready_for_fuses);
    @(posedge clk_tb);

    write_regs(SET_APB, fuse_regnames, 0, 3);
    read_regs(GET_APB, fuse_regnames, 0, 3);

    simulate_caliptra_boot();

    read_regs(GET_AHB, fuse_regnames, 0, 3);

    repeat (10) @(posedge clk_tb);

    // -----------------------------------------------------------------
    // PHASE 3. Perform Warm Reset, read values & Repeat APB Write & Read from 1a  
    // -----------------------------------------------------------------
    $display ("\n3a. Perform a warm reset then repeat steps 1a (just APB)"); 
    tphase = "3a";

    warm_reset_dut(); 
    warm_reset_exp_data();
    wait(ready_for_fuses);
    @(posedge clk_tb);

    read_regs(GET_APB, fuse_regnames, 0, 3);      // should be old sticky values
    sb.del_all();

    // These writes should fail to write again  
    write_regs(SET_APB, fuse_regnames, 0, 3);
    read_regs(GET_APB, fuse_regnames, 0, 3);

    simulate_caliptra_boot();

    read_regs(GET_AHB, fuse_regnames, 0, 3);

    error_ctr = sb.err_count;

  end

endtask // fuse_reg_perm_test





