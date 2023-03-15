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
  // fuse_reg_lifecycle_test(...)
  //
  // Runs fuse programming & access test in one or all security states 
  //----------------------------------------------------------------
  task fuse_reg_lifecycle_test(input string ss_name); 

    int ss_code;
    // security_state_t = ss;

    begin 
      if (ss_name == "ALL") begin 

        for (int i=0; i < 8; i++) begin
          set_security_state(security_state_t'(i));
          init_sim();
          reset_dut();

          wait (ready_for_fuses == 1'b1);
          update_exp_regval(socregs.get_addr("CPTRA_FLOW_STATUS"), 32'h4000_0000, SET_DIRECT);     

          repeat (5) @(posedge clk_tb);
          fuse_reg_test();
          repeat (5) @(posedge clk_tb);
        end 

      end else begin

        ss_code = get_ss_code(ss_name);
        if (ss_code < 0) 
          $error("Invalid security state; must be:\n  ALL or <DEBUG_LOCKED|DEBUG_UNLOCKED>_<UNPROVISIONED|MANUFACTURING|PRODUCTION");
        else begin  

          set_security_state(security_state_t'(ss_code));
          init_sim();
          reset_dut();

          wait (ready_for_fuses == 1'b1);
          update_exp_regval(socregs.get_addr("CPTRA_FLOW_STATUS"), 32'h4000_0000, SET_DIRECT);     

          repeat (5) @(posedge clk_tb);
          fuse_reg_test();
          repeat (5) @(posedge clk_tb);
        end 

      end 

    end 

  endtask // fuse_reg_lifecycle_test
