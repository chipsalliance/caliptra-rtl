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
  // ss_soc_dbg_unlock_level_test()
  // 
  // Test ss soc debug unlock level 
  //----------------------------------------------------------------
  task ss_soc_dbg_unlock_level_test;

    dword_t read_data;
    automatic int tid = 0;
    
    dword_t ss_debug_intent_exp; 
    
    strq_t ss_soc_dbg_unlock_level_regnames;
    strq_t ss_strap_soc_rw_regnames = get_ss_strap_regnames();
    

    begin
        $display();
        $display("Executing debug unlock level test");
        $display("-----------------------------------------\n");

        tc_ctr = tc_ctr + 1;

        ss_strap_soc_rw_regnames = get_ss_strap_regnames();

        foreach (ss_strap_soc_rw_regnames[ix]) begin
          if (str_startswith(ss_strap_soc_rw_regnames[ix], "SS_SOC_DBG_UNLOCK_LEVEL")) begin 
            add_to_strq(ss_soc_dbg_unlock_level_regnames, ss_strap_soc_rw_regnames[ix]); // Add to queue for appropriate testing
            continue; 
          end
        end

        if (subsystem_mode_tb == 1)
          ss_debug_intent_exp = 32'h00000001;
        else
          ss_debug_intent_exp = 32'h0;

        update_exp_regval("SS_DEBUG_INTENT", ss_debug_intent_exp, SET_DIRECT);

        $display("subsystem_mode_tb = 0x%0x", subsystem_mode_tb) ;
        $display("ss_debug_intent_exp = 0x%0x", ss_debug_intent_exp) ;

        // Read SS_DEBUG_INTENT register over AHB
        read_single_word_ahb(_soc_register_dict["SS_DEBUG_INTENT"]);
        read_data = _soc_register_dict["SS_DEBUG_INTENT"][2] ? hrdata_o_tb[`AHB64_HI] : hrdata_o_tb[`AHB64_LO];
        $display("SS_DEBUG_INTENT = 0x%08x", read_data);
        assert(read_data == ss_debug_intent_exp) else begin
          $display("TB ERROR. Failed to set SS_DEBUG_INTENT");
          error_ctr += 1;
        end

        print_banner("1. Write to SS_DEBUG_UNLOCK_LEVEL[]  and verify write is successful via AHB, fails via AXI."); 

        //Caliptra Write SS_SOC_DBG_UNLOCK_LEVEL[]
        $display ("\n1a. AHB Write To SoC Debug Unlock Level[0] register  ");
        write_regs(SET_AHB, ss_soc_dbg_unlock_level_regnames, 0, 3); // Writable by Caliptra
        
        repeat (10) @(posedge clk_tb);

        // Caliptra read SS_SOC_DBG_UNLOCK_LEVEL[] 
        $display("\n1b. Reading over AHB");
        read_regs(GET_AHB, ss_soc_dbg_unlock_level_regnames, 0, 3);

        repeat (10) @(posedge clk_tb);

        $display("\n1c. Reading over AXI");
        read_regs(GET_AXI, ss_soc_dbg_unlock_level_regnames, 0, 3);
        repeat (10) @(posedge clk_tb);

        //SOC Write SS_SOC_DBG_UNLOCK_LEVEL[], should fail
        $display ("\n1d. AXI Write To SS_DEBUG_UNLOCK_LEVEL[] and verify it fails  ");
        write_regs(SET_AXI, ss_soc_dbg_unlock_level_regnames, 0, 3, FAIL);
        
        repeat (10) @(posedge clk_tb);

        // Read over AXI 
        $display("\n1e. Reading over AXI");
        read_regs(GET_AXI, ss_soc_dbg_unlock_level_regnames, 0, 3);

        repeat (10) @(posedge clk_tb);

        
        error_ctr += sb.err_count;
    end

  endtask
