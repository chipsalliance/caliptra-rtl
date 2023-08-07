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
  task single_socreg_test(input string meth_name, int wrcount);
    // Example 
    //   meth_name: AHB.CPTRA_TIMER_CONFIG -- for back2back AHB write+read
    //   wrcount:   20 --  number of times to perform write-read pairs 

    access_t access;
    string meth, rname;
    word_addr_t addr; 
    int tid = 0; 

    strq_t reglist;
    WordTransaction wrtrans, rdtrans;
 
    begin

      $display("Executing single_socreg_test: %s", meth_name);
      $display("----------------------------%s\n", {meth_name.len(){"-"}});

      tc_ctr = tc_ctr + 1;

      wrtrans = new();
      rdtrans = new();

      meth = meth_name.substr(0, 2);
      rname = meth_name.substr(4, meth_name.len()-1);
      addr = socregs.get_addr(rname); 

      reglist.push_back(rname);

      if (wrcount < 1) begin
        error_ctr = 1; 
        $display("ERROR performing %s operations on register %s %d times -- wrcount MUST be > 0", meth, rname, wrcount);
      end else begin
        $display("-- Performing %s operations on register %s %d times --", meth, rname, wrcount);
      end


      if (meth == "AHB") begin // Perform Caliptra boot  

        simulate_caliptra_boot();
        repeat (20) @(posedge clk_tb);
        sb.del_all();
        update_CPTRA_FLOW_STATUS(ready_for_fuses, `REG_HIER_BOOT_FSM_PS);


      end 

      update_INTR_BRF_NOTIF_INTERNAL_INTR_R(gen_input_wire_toggle, security_state.debug_locked); 

      // Write over a method & read over same method 

      for (int i = 0; i < wrcount; i++) begin

        wrtrans.update(addr, 0, tid); 
        wrtrans.randomize();

        if (str_startswith(meth_name, "APB.")) 
          write_read_regs(SET_APB, GET_APB, reglist, tid, 1);
        else if (str_startswith(meth_name, "AHB.")) 
          write_read_regs(SET_AHB, GET_AHB, reglist, tid, 1);

      end 

    error_ctr = sb.err_count;

    end

  endtask // single_socreg_test


