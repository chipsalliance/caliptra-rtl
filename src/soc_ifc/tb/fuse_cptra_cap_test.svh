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
// fuse_cptra_cap_test()
//----------------------------------------------------------------
task fuse_cptra_cap_reg_test;
  // Fuse Caliptra Capabilities Register Test 

  word_addr_t addr; 
  int tid = 0; // optional to increment UNLESS multiple writes to same address 
  strq_t cptra_cap_regnames;
  string cptra_cap_lock_reg = "CPTRA_CAP_LOCK";

  WordTransaction wrtrans, rdtrans;
  dword_t exp_data; 
  string rname;
  dword_t read_data;

  //parameter CPTRA_CAP_LOCK = _soc_register_dict["CPTRA_CAP_LOCK"];  //0x130

  begin
    $display("\nExecuting task fuse_cptra_cap_reg_test"); 
    $display("----------------------------------\n");

    $display("Current security state = 0b%03b", security_state);
    tc_ctr = tc_ctr + 1;

    wrtrans = new();
    rdtrans = new();

    add_to_strq(cptra_cap_regnames, "CPTRA_FW_CAPABILITIES");
    add_to_strq(cptra_cap_regnames, "CPTRA_HW_CAPABILITIES");

    tphase = "1";
    print_banner("\nPhase 1. Write and check capabilities registers after cold boot");

    // I. Write over AHB, read over AHB then read again over AXI

    $display ("1a. Writing using AHB 3 cycles apart");
    write_regs(SET_AHB, cptra_cap_regnames, tid, 3);

    repeat (10) @(posedge clk_tb);

    $display ("\n1b. Reading over AHB 3 cycles apart"); 
    read_regs(GET_AHB, cptra_cap_regnames, tid, 3);

    repeat (10) @(posedge clk_tb);
    
    $display ("\n1c. Reading over AXI 3 cycles apart"); 
    read_regs(GET_AXI, cptra_cap_regnames, tid, 3);

    repeat (10) @(posedge clk_tb);
    tid = 1;

    $display ("1d. Writing using AHB 3 cycles apart");
    write_regs(SET_AHB, cptra_cap_regnames, tid, 3);

    repeat (10) @(posedge clk_tb);

    $display ("\n1e. Reading over AHB 3 cycles apart"); 
    read_regs(GET_AHB, cptra_cap_regnames, tid, 3);

    repeat (10) @(posedge clk_tb);
    
    $display ("\n1f. Reading over AXI 3 cycles apart"); 
    read_regs(GET_AXI, cptra_cap_regnames, tid, 3);

    repeat (10) @(posedge clk_tb);

    $display ("1g. Writing using AHB 3 cycles apart");
    write_regs(SET_AXI, cptra_cap_regnames, tid, 3, FAIL);

    repeat (10) @(posedge clk_tb);

    $display ("\n1h. Reading over AHB 3 cycles apart"); 
    read_regs(GET_AHB, cptra_cap_regnames, tid, 3);

    repeat (10) @(posedge clk_tb);
    
    $display ("\n1i. Reading over AXI 3 cycles apart"); 
    read_regs(GET_AXI, cptra_cap_regnames, tid, 3);

    repeat (10) @(posedge clk_tb);

    tphase = "2";
    print_banner("\nPhase 2. Write CPTRA_CAP_LOCK register to lock HW/FW capabilities");

    $display("\n2a. Writing 0x1 to CPTRA_CAP_LOCK register");
    write_single_word_ahb(_soc_register_dict["CPTRA_CAP_LOCK"], 32'h00000001);
    update_exp_regval("CPTRA_CAP_LOCK", 32'h00000001, SET_AHB);

    repeat (10) @(posedge clk_tb);

    $display("\n2b. Reading CPTRA_CAP_LOCK register");
    read_single_word_ahb(_soc_register_dict["CPTRA_CAP_LOCK"]);
    read_data =  _soc_register_dict["CPTRA_CAP_LOCK"][2] ? hrdata_o_tb[`AHB64_HI] :hrdata_o_tb[`AHB64_LO];
    $display("Read over AHB: addr =  %-40s (0x%08x), data = 0x%08x", cptra_cap_lock_reg, _soc_register_dict["CPTRA_CAP_LOCK"], read_data);

    $display ("2c. Writing using AHB 3 cycles apart");
    write_regs(SET_AHB, cptra_cap_regnames, tid, 3, FAIL);

    repeat (10) @(posedge clk_tb);

    $display ("\n2d. Reading over AHB 3 cycles apart"); 
    read_regs(GET_AHB, cptra_cap_regnames, tid, 3);

    repeat (10) @(posedge clk_tb);
    
    $display ("\n2e. Reading over AXI 3 cycles apart"); 
    read_regs(GET_AXI, cptra_cap_regnames, tid, 3);

    repeat (10) @(posedge clk_tb);

    tphase = "3";
    print_banner("\nPhase 3. Perform a warm reset and repeat 2b - 2e");

    sb.del_all();
    warm_reset_dut(); 

    sb.record_reset_values(0, WARM_RESET);
    wait (ready_for_fuses == 1'b1);

    $display("\n3a. Reading CPTRA_CAP_LOCK register");
    read_single_word_ahb(_soc_register_dict["CPTRA_CAP_LOCK"]);
    read_data =  _soc_register_dict["CPTRA_CAP_LOCK"][2] ? hrdata_o_tb[`AHB64_HI] :hrdata_o_tb[`AHB64_LO];
    $display("Read over AHB: addr =  %-40s (0x%08x), data = 0x%08x", cptra_cap_lock_reg, _soc_register_dict["CPTRA_CAP_LOCK"], read_data);

    $display ("3b. Writing using AHB 3 cycles apart");
    write_regs(SET_AHB, cptra_cap_regnames, tid, 3);

    repeat (10) @(posedge clk_tb);

    $display ("\n3c. Reading over AHB 3 cycles apart"); 
    read_regs(GET_AHB, cptra_cap_regnames, tid, 3);

    repeat (10) @(posedge clk_tb);
    
    $display ("\n3d. Reading over AXI 3 cycles apart"); 
    read_regs(GET_AXI, cptra_cap_regnames, tid, 3);

    repeat (10) @(posedge clk_tb);

    error_ctr = sb.err_count;

  end
endtask // fuse_reg_test





