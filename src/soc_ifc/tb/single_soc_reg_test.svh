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
  // single_socreg_test(...)
  //
  // Tests out write/read single soc register test using same bus protocol 
  //----------------------------------------------------------------
  task single_socreg_test(input string meth_name);

    access_t access;
    string meth, rname;
    word_addr_t addr; 
    int tid = 0; 

    WordTransaction wrtrans, rdtrans;
 
    begin
      $display("Executing single_socreg_test: %s", meth_name);
      $display("----------------------------%s\n", {meth_name.len(){"-"}});

      tc_ctr = tc_ctr + 1;

      wrtrans = new();
      rdtrans = new();

      rname = meth_name.substr(4, meth_name.len()-1);
      addr = socregs.get_addr(rname); 
 
      // Write over a method & read over same method 

      wrtrans.update(addr, 0, tid); 
      wrtrans.randomize();

      if (str_startswith(meth_name, "APB.")) begin
        write_single_word_apb(addr, wrtrans.data); 
        sb.record_entry(wrtrans, SET_APB);

        repeat (10) @(posedge clk_tb);
        read_single_word_apb(addr); 
        $display("Read over APB:  addr = %30s (0x%08x), data = 0x%08x", rname, addr, prdata_o_tb);

        rdtrans.update(addr, prdata_o_tb, tid); 
        sb.check_entry(rdtrans);

      end  else if (str_startswith(meth_name, "AHB.")) begin
        write_single_word_ahb(addr, wrtrans.data);
        sb.record_entry(wrtrans, SET_AHB);

        repeat (10) @(posedge clk_tb);
        read_single_word_apb(addr); 
        $display("Read over AHB:  addr = %30s (0x%08x), data = 0x%08x", rname, addr, prdata_o_tb);

        rdtrans.update(addr, hrdata_o_tb, tid); 
        sb.check_entry(rdtrans);
      end 
         
      error_ctr = sb.err_count;
    end

  endtask // single_socreg_test


