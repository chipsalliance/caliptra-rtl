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

    // PHASE 1. Normal sequence 
    $display ("1a. APB write to registers, lock fuses and attempt to modify\n");

    write_regs(SET_APB, fuse_regnames, 0, 3); 

    simulate_caliptra_boot();
    socregs.lock_fuses(); // fuses locked "latched" internally regardless of reg status

    repeat (5) @(posedge clk_tb);

    write_regs(SET_APB, fuse_regnames, 1, 3);
    read_regs(GET_APB, fuse_regnames, 1, 3);
    read_regs(GET_AHB, fuse_regnames, 1, 3);

    sb.del_all();

    $display ("\n1b. Following writes should have no effect on locked state -- which is still set!\n");

    write_single_word_apb(socregs.get_addr("CPTRA_FUSE_WR_DONE"), 32'h0); 

    write_regs(SET_APB, fuse_regnames, 0, 3);
    read_regs(GET_APB, fuse_regnames, 0, 3);
    read_regs(GET_AHB, fuse_regnames, 0, 3);

/* Commenting out until TB has correct checks 
    // PHASE 2. Perform Cold Reset and Repeat APB Write & Read from 1a  
    reset_dut(); // expect to be clearing CPTRA_FUSE_WR_DONE effect 
    socregs.unlock_fuses();

    sb.del_all();

    $display ("\n2a. Write to registers after cold boot and check back writes");

    write_regs(SET_APB, fuse_regnames, 0, 3);
    read_regs(GET_AHB, fuse_regnames, 0, 3);

    write_single_word_apb(socregs.get_addr("CPTRA_FUSE_WR_DONE"), 32'h1); 
    // no point in recording TB fuse_locked state since it will be cleared anyway

    $display ("\n3a. Perform a warm reset then repeat steps 1a (just APB)"); 

    warm_reset_dut(); // expect to be clearing CPTRA_FUSE_WR_DONE effect 
    socregs.unlock_fuses();
    sb.del_all();

    write_regs(SET_APB, fuse_regnames, 0, 3);
    read_regs(GET_AHB, fuse_regnames, 0, 3);
*/

    error_ctr = sb.err_count;

  end
endtask // fuse_reg_perm_test





