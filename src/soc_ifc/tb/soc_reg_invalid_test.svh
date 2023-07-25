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
  // soc_reg_invalid_test()
  // 
  // Test writing & reading of absent and unaligned registers 
  //----------------------------------------------------------------
  task soc_reg_invalid_test;    
    // SoC Register Test to undefined and unaligned locations -- except for INTR registers


    word_addr_t addr; 
    word_addr_t undef_addr; 
    word_addr_t unaligned_addr; 

    string rname;

    dword_t wdata; 

    strq_t soc_regnames;
    word_addrq_t undef_regs; 

    automatic dword_t valid_hrdata; 

    begin
      $display("Executing task soc_reg_invalid_test"); 
      $display("-----------------------------------\n");

      $display("Current security state = 0b%03b", security_state);

      tc_ctr = tc_ctr + 1;

      // Let the soc regs initialization happen
      repeat (1) @(posedge clk_tb); 

      soc_regnames = get_soc_regnames();
      undef_regs = get_undef_regs();


      $display( "\n** PHASE Ia. Testing undefined address locations over APB -- Expect writes to be dropped and reads to be 0's**\n" ); 

      foreach (undef_regs[i]) begin

        undef_addr = undef_regs[i];
        wdata = $urandom(); 
        write_single_word_apb(undef_addr, wdata);
        read_single_word_apb(undef_addr);

        $display("Write & read over APB : undefined addr = 0x%08x, wdata = 0x%08x, rdata = 0x%x", undef_addr, wdata, prdata_o_tb); 

        if (prdata_o_tb != 0) begin 
          $display("ERROR. undefined addr = 0x%08x, returns non-zero value 0x%08x over APB!", undef_addr, prdata_o_tb); 
          error_ctr += 1;
        end
      end

      repeat (5) @(posedge clk_tb);


      $display( "\n** PHASE Ib. Testing unaligned address locations over APB -- Expect writes to be dropped and reads to be 0's**\n" ); 

      foreach (soc_regnames[i]) begin
  
        rname = soc_regnames[i];

        addr = socregs.get_addr(rname); 
        unaligned_addr = addr + 'd1 + ($urandom() % 3);

        wdata = $urandom(); 
        write_single_word_apb(unaligned_addr, wdata);
        read_single_word_apb(unaligned_addr);

        $display("Write & read over APB : unaligned addr = 0x%08x, wdata = 0x%08x, rdata = 0x%x", unaligned_addr, wdata, prdata_o_tb); 

        if (prdata_o_tb != 0) begin 
          $display("ERROR. undefined addr = 0x%08x, returns non-zero value 0x%08x over APB!", unaligned_addr, prdata_o_tb); 
          error_ctr += 1;
        end
      end

      repeat (5) @(posedge clk_tb);


      // Skip wrting & reading over AHB until post reset sequencing is done 
      // THEN, update scoreboard entry accordingly for a couple of registers which 
      // are written using APB as part of Caliptra boot.  
      simulate_caliptra_boot();


      $display( "\n** PHASE IIa. Testing undefined address locations over AHB -- Expect writes to be dropped and reads to be 0's**\n" ); 

      // Purely a control test -- don't expect 0's to be returned
      wdata = $urandom(); 
      addr = socregs.get_addr("CPTRA_GENERIC_OUTPUT_WIRES0");  
      write_single_word_ahb(addr, wdata);
      read_single_word_ahb(addr);

      valid_hrdata =  addr[2] ?  hrdata_o_tb[`AHB64_HI] : hrdata_o_tb[`AHB64_LO]; 
      $display("Control condtion; test over AHB to aligned address (expect read to mirro write value) : addr = 0x%08x, wdata = 0x%08x, rdata = 0x%x", 
        addr, wdata, valid_hrdata); 


      foreach (undef_regs[i]) begin

        undef_addr = undef_regs[i];
        wdata = $urandom(); 
        write_single_word_ahb(undef_addr, wdata);
        read_single_word_ahb(undef_addr);

        valid_hrdata =  addr[2] ?  hrdata_o_tb[`AHB64_HI] : hrdata_o_tb[`AHB64_LO]; 
        $display("Write & read over AHB : undefined addr = 0x%08x, wdata = 0x%08x, rdata = 0x%x", undef_addr, wdata, valid_hrdata); 

        if (valid_hrdata != 0) begin 
          $display("ERROR. undefined addr = 0x%08x, returns non-zero value 0x%08x over AHB!", undef_addr, valid_hrdata); 
          error_ctr += 1;
        end
      end

      repeat (5) @(posedge clk_tb);

      $display( "\n** PHASE IIb. Testing unaligned address locations over AHB -- Expect writes to be dropped and reads to be 0's**\n" ); 

      foreach (soc_regnames[i]) begin
  
        rname = soc_regnames[i];
    
        addr = socregs.get_addr(rname); 
        unaligned_addr = addr + 'd1 + ($urandom() % 3);

        wdata = $urandom(); 
        write_single_word_ahb(unaligned_addr, wdata);
        read_single_word_ahb(unaligned_addr);

        valid_hrdata =  addr[2] ?  hrdata_o_tb[`AHB64_HI] : hrdata_o_tb[`AHB64_LO]; 
        $display("Write & read over AHB : unaligned addr = 0x%08x, wdata = 0x%08x, rdata = %x", unaligned_addr, wdata, valid_hrdata); 

        if (valid_hrdata != 0) begin 
          $display("ERROR. unaligned addr = 0x%08x, returns non-zero value 0x%08x over AHB!", unaligned_addr, valid_hrdata); 
          error_ctr += 1;
        end

      end

      repeat (5) @(posedge clk_tb);

    end
  endtask // soc_reg_invalid_test

