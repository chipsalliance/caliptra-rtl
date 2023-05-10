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
// fuse_reg_test()
//----------------------------------------------------------------
task fuse_reg_test;
  // Fuse Register Test 

  word_addr_t addr; 
  int tid = 0; // optional to increment UNLESS multiple writes to same address 
  strq_t fuse_regnames; 

  WordTransaction wrtrans, rdtrans;
  dword_t exp_data; 
  string rname;

  begin
    $display("\nExecuting task fuse_reg_test"); 
    $display("----------------------------\n");

    $display("Current security state = 0b%03b", security_state);
    tc_ctr = tc_ctr + 1;

    wrtrans = new();
    rdtrans = new();

    fuse_regnames = get_fuse_regnames(); 

    // I. Write over APB, read over APB then read again over AHB

    $display ("1a. Writing using APB 3 cycles apart");
    write_regs(SET_APB, fuse_regnames, tid, 3);

    repeat (10) @(posedge clk_tb);

    $display ("\n1b. Reading over APB 3 cycles apart"); 
    read_regs(GET_APB, fuse_regnames, tid, 3);

    repeat (10) @(posedge clk_tb);
    tid = 1;

    $display ("1c. Writing again using APB 3 cycles apart");
    write_regs(SET_APB, fuse_regnames, tid, 3);

    repeat (10) @(posedge clk_tb);

    $display ("\n1d. Reading again over APB 3 cycles apart"); 
    read_regs(GET_APB, fuse_regnames, tid, 3);

    simulate_caliptra_boot();

    $display ("\n1e. Reading over AHB 3 cycles apart");
    read_regs(GET_AHB, fuse_regnames, tid, 3);


    // II. Swap -- Write over AHB, read over AHB then read over APB

    repeat (20) @(posedge clk_tb);
    sb.del_all();

    // Massive failures  -- debugging
    $display ("\n2a. Writing over AHB 3 cycles apart");
    write_regs(SET_AHB, fuse_regnames, tid, 3);

    $display ("\n2b. Read over AHB 3 cycles apart");
    read_regs(GET_AHB, fuse_regnames, tid, 3);

    $display ("\n2c. Read over APB 3 cycles apart");
    read_regs(GET_APB, fuse_regnames, tid, 3);


    // III. Repeat "I". Attempt to write over APB, read over AHB and APB     

    repeat (20) @(posedge clk_tb);
    sb.del_all();

    $display ("3a. Writing using APB 3 cycles apart");
    write_regs(SET_APB, fuse_regnames, tid, 3);

    repeat (10) @(posedge clk_tb);

    $display ("\n3b. Reading over AHB 3 cycles apart");
    read_regs(GET_AHB, fuse_regnames, tid, 3);

    repeat (10) @(posedge clk_tb);

    $display ("\n3c. Reading over APB 3 cycles apart"); 
    read_regs(GET_APB, fuse_regnames, tid, 3);

    error_ctr = sb.err_count;

  end
endtask // fuse_reg_test





