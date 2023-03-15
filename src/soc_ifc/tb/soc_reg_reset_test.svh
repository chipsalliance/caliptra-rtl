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

    word_addr_t addr; 
    int tid = 0; // TID is to be updated ONLY if multiple writes to an address 
    strq_t soc_regnames;

    WordTransaction wrtrans, rdtrans;
    dword_t exp_data; 
    
    begin
      $display("Executing task soc_reg_pwron_test"); 
      $display("---------------------------------\n");

      $display("Current security state = 0b%03b", security_state);
      tc_ctr = tc_ctr + 1;

      wrtrans = new();
      rdtrans = new();

      soc_regnames = get_soc_regnames(); 

      $display ("0a. Checking Power-on values\n"); 

      // Inialize soc_regs ON COLD BOOT  
      reset_exp_data(); 
      sb.record_reset_values(0, COLD_RESET);

      // Check Init values for COLD BOOT 
      foreach (soc_regnames[rname]) begin 
        addr = socregs.get_addr(rname);
        read_single_word_apb(addr); 
        $display("Read over APB:  addr = %30s (0x%08x), data = 0x%08x", rname, addr, prdata_o_tb);
        rdtrans.update(addr, prdata_o_tb, tid); 
        sb.check_entry(rdtrans);

        read_single_word_ahb(addr); 
        $display("Read over AHB:  addr = %30s (0x%08x), data = 0x%08x", rname, addr, hrdata_o_tb);
        rdtrans.update(addr, hrdata_o_tb, tid); 
        sb.check_entry(rdtrans);
        repeat (3) @(posedge clk_tb);
      end 


      error_ctr = sb.err_count;
    end

  endtask // soc_reg_pwron_test  



  //----------------------------------------------------------------
  // soc_reg_wrmrst_test()
  //
  // Test warm reset warm reset values of ALL soc registers 
  //----------------------------------------------------------------
  task soc_reg_wrmrst_test;

    begin
      $display("Executing task soc_reg_wrmrst_test"); 
      $display("----------------------------------\n");
    end
  endtask // soc_reg_wrmrst_test;




