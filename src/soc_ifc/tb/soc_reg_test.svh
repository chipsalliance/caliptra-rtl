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
    // SoC Register Test excluding FUSE* registers 

    word_addr_t addr; 
    int tid = 0; // TID is to be updated ONLY if multiple writes to an address 
    strq_t soc_regnames;
    string rname;

    // WordTransaction wrtrans, rdtrans;
    
    begin
      $display("Executing task soc_reg_test"); 
      $display("---------------------------\n");

      // $display("Current security state = 0b%03b", security_state);
      tc_ctr = tc_ctr + 1;

      soc_regnames = get_soc_regnames_minus_fuse();

      // 1a-c. Write over APB, read over APB then AHB

      $display ("1a. Writing using APB 3 cycles apart");
      write_regs(SET_APB, soc_regnames, tid, 3);

      repeat (10) @(posedge clk_tb);

      $display ("\n1b. Reading over APB 3 cycles apart");
      read_regs(GET_APB, soc_regnames, tid, 3);

      repeat (10) @(posedge clk_tb);

      // Skip wrting & reading over AHB until post reset sequencing is done 
      simulate_caliptra_boot();

      $display ("\n1b. Reading over AHB 3 cycles apart");
      read_regs(GET_APB, soc_regnames, tid, 3);



      error_ctr = sb.err_count;
    end
  endtask // soc_reg_test
