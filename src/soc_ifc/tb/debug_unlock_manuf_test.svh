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
  // debug_unlock_manuf_test()
  // 
  // Test debug manufacturing flow 
  //----------------------------------------------------------------
  task debug_unlock_manuf_test;

    dword_t read_data;
    automatic int tid = 0;
    string rname;
    //word_addr_t ss_dbg_manuf_req_addr;
    //word_addr_t ss_dbg_manuf_rsp_addr;
    automatic WordTransaction wrtrans_req_reg, rdtrans_req_reg;
    automatic WordTransaction wrtrans_rsp_reg, rdtrans_rsp_reg;

    strq_t   ss_dbg_manuf_req_regname;
    strq_t   ss_dbg_manuf_rsp_regname;

    dword_t prod_debug_unlock_data = 32'h00000002;
    dword_t manuf_debug_unlock_data = 32'h00000001;
    dword_t ss_debug_rsp_data;
    dword_t ss_debug_intent_exp; // = 32'h00000001;
    

    begin
        $display();
        $display("Executing debug unlock manufacturing test");
        $display("-----------------------------------------\n");

        set_security_state('{device_lifecycle: DEVICE_MANUFACTURING, debug_locked: DEBUG_LOCKED});

        wrtrans_req_reg = new();
        rdtrans_req_reg = new();
      
        wrtrans_rsp_reg = new();
        rdtrans_rsp_reg = new();

        tc_ctr = tc_ctr + 1;

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

        print_banner("1. Write to SS_DEBUG_MANUF_SERVICE_REG_REQ - MANUFACTURING DEBUG UNLOCK REQUEST and verify write is successful."); 

        //SOC Write SS_DEBUG_MANUF_SERVICE_REG_REQ.MANUF_DBG_UNLOCK_REQ = 1
        $display ("\n1a. AXI Write To Debug Manuf Service Request register bit 0: manufacturing debug unlock request  ");
        wrtrans_req_reg.update_byname("SS_DBG_SERVICE_REG_REQ", manuf_debug_unlock_data, tid);
        write_reg_trans(SET_AXI, wrtrans_req_reg);
        
        repeat (10) @(posedge clk_tb);

        // Read SS_DEBUG_MANUF_SERVICE_REG_REQ.MANUF_DBG_UNLOCK_REQ = 0 
        $display("\n1b. Reading over AXI");
        rdtrans_req_reg.update_byname("SS_DBG_SERVICE_REG_REQ", 0, tid);
        read_reg_trans(GET_AXI, rdtrans_req_reg);
        if (subsystem_mode_tb) begin
          assert(rdtrans_req_reg.data == manuf_debug_unlock_data) else begin
            $display("TB ERROR. SS_DBG_SERVICE_REG_REQ.MANUF_DBG_UNLOCK_REQ failed");
            error_ctr += 1;
          end
        end
        else begin
          assert(rdtrans_req_reg.data == '0) else begin
            $display("TB ERROR. SS_DBG_SERVICE_REG_REQ.MANUF_DBG_UNLOCK_REQ should be disabled in passive mode");
            error_ctr += 1;
          end
        end

        repeat (10) @(posedge clk_tb);

        $display("\n1c. Reading over AHB");
        read_reg_trans(GET_AHB, rdtrans_req_reg);
        if (subsystem_mode_tb) begin
          assert(rdtrans_req_reg.data == manuf_debug_unlock_data) else begin
            $display("TB ERROR. SS_DBG_SERVICE_REG_REQ.MANUF_DBG_UNLOCK_REQ failed");
            error_ctr += 1;
          end
        end
        else begin
          assert(rdtrans_req_reg.data == '0) else begin
            $display("TB ERROR. SS_DBG_SERVICE_REG_REQ.MANUF_DBG_UNLOCK_REQ should be disabled in passive mode");
            error_ctr += 1;
          end
        end
        repeat (10) @(posedge clk_tb);

        //SOC Write SS_DEBUG_MANUF_SERVICE_REG_REQ.MANUF_DBG_UNLOCK_REQ = 0
        $display ("\n1d. AXI Write To Debug Manuf Service Request register bit 0: manufacturing debug unlock request = 0  ");
        wrtrans_req_reg.update_byname("SS_DBG_SERVICE_REG_REQ", 0, tid);
        write_reg_trans(SET_AXI, wrtrans_req_reg);
        
        repeat (10) @(posedge clk_tb);

        // Read SS_DEBUG_MANUF_SERVICE_REG_REQ.MANUF_DBG_UNLOCK_REQ = 0 
        $display("\n1e. Reading over AXI");
        rdtrans_req_reg.update_byname("SS_DBG_SERVICE_REG_REQ", 0, tid);
        read_reg_trans(GET_AXI, rdtrans_req_reg);
        if (subsystem_mode_tb) begin
          assert(rdtrans_req_reg.data != manuf_debug_unlock_data) else begin
            $display("TB ERROR. SS_DBG_SERVICE_REG_REQ.MANUF_DBG_UNLOCK_REQ failed");
            error_ctr += 1;
          end
        end 
        else begin
          assert(rdtrans_req_reg.data == '0) else begin
            $display("TB ERROR. SS_DBG_SERVICE_REG_REQ.MANUF_DBG_UNLOCK_REQ should be disabled in passive mode");
            error_ctr += 1;
          end
        end

        repeat (10) @(posedge clk_tb);

        $display("\n1f. Reading over AHB");
        read_reg_trans(GET_AHB, rdtrans_req_reg);
        if (subsystem_mode_tb) begin
          assert(rdtrans_req_reg.data != manuf_debug_unlock_data) else begin
            $display("TB ERROR. SS_DBG_SERVICE_REG_REQ.MANUF_DBG_UNLOCK_REQ failed");
            error_ctr += 1;
          end
        end
        else begin
          assert(rdtrans_req_reg.data == '0) else begin
            $display("TB ERROR. SS_DBG_SERVICE_REG_REQ.MANUF_DBG_UNLOCK_REQ should be disabled in passive mode");
            error_ctr += 1;
          end
        end
        repeat (10) @(posedge clk_tb);

        //SOC Write SS_DEBUG_MANUF_SERVICE_REG_REQ.MANUF_DBG_UNLOCK_REQ = 1
        $display ("\n1g. AHB Write To Debug Manuf Service Request register bit 0: manufacturing debug unlock request  ");
        wrtrans_req_reg.update_byname("SS_DBG_SERVICE_REG_REQ", manuf_debug_unlock_data, tid);
        write_reg_trans(SET_AHB, wrtrans_req_reg);
        
        repeat (10) @(posedge clk_tb);

        // Read SS_DEBUG_MANUF_SERVICE_REG_REQ.MANUF_DBG_UNLOCK_REQ = 0 
        $display("\n1h. Reading over AXI");
        rdtrans_req_reg.update_byname("SS_DBG_SERVICE_REG_REQ", 0, tid);
        read_reg_trans(GET_AXI, rdtrans_req_reg);
        if (subsystem_mode_tb) begin
          assert(rdtrans_req_reg.data == manuf_debug_unlock_data) else begin
            $display("TB ERROR. SS_DBG_SERVICE_REG_REQ.PROD_DBG_UNLOCK_REQ failed");
            error_ctr += 1;
          end
        end
        else begin
          assert(rdtrans_req_reg.data == '0) else begin
            $display("TB ERROR. SS_DBG_SERVICE_REG_REQ.MANUF_DBG_UNLOCK_REQ should be disabled in passive mode");
            error_ctr += 1;
          end
        end

        repeat (10) @(posedge clk_tb);

        $display("\n1i. Reading over AHB");
        read_reg_trans(GET_AHB, rdtrans_req_reg);
        if (subsystem_mode_tb) begin
          assert(rdtrans_req_reg.data == manuf_debug_unlock_data) else begin
            $display("TB ERROR. SS_DBG_SERVICE_REG_REQ.MANUF_DBG_UNLOCK_REQ failed");
            error_ctr += 1;
          end
        end
        else begin
          assert(rdtrans_req_reg.data == '0) else begin
            $display("TB ERROR. SS_DBG_SERVICE_REG_REQ.MANUF_DBG_UNLOCK_REQ should be disabled in passive mode");
            error_ctr += 1;
          end
        end
        repeat (10) @(posedge clk_tb);

        print_banner("2. Write to SS_DEBUG_MANUF_SERVICE_REG_REQ - PRODUCTION DEBUG UNLOCK REQUEST and verify write fails"); // Success only when device_lifecycle = DEVICE_PRODUCTION

        //SOC Write SS_DEBUG_MANUF_SERVICE_REG_REQ.PROD_DBG_UNLOCK_REQ = 1
        $display ("\n2a. AXI Write To Debug Manuf Service Request register bit 1: production debug unlock request  ");
        wrtrans_req_reg.update_byname("SS_DBG_SERVICE_REG_REQ", prod_debug_unlock_data, tid);
        write_reg_trans(SET_AXI, wrtrans_req_reg, FAIL);
        
        repeat (10) @(posedge clk_tb);

        // Read SS_DEBUG_MANUF_SERVICE_REG_REQ.PROD_DBG_UNLOCK_REQ = 1
        $display("\n2b. Reading over AXI");
        rdtrans_req_reg.update_byname("SS_DBG_SERVICE_REG_REQ", 0, tid);
        read_reg_trans(GET_AXI, rdtrans_req_reg);
        if (subsystem_mode_tb) begin
          assert(rdtrans_req_reg.data != prod_debug_unlock_data) else begin
            $display("TB ERROR. SS_DBG_SERVICE_REG_REQ.PROD_DBG_UNLOCK_REQ failed");
            error_ctr += 1;
          end
        end
        else begin
          assert(rdtrans_req_reg.data == '0) else begin
            $display("TB ERROR. SS_DBG_SERVICE_REG_REQ.PROD_DBG_UNLOCK_REQ should be disabled in passive mode");
            error_ctr += 1;
          end
        end

        repeat (10) @(posedge clk_tb);

        $display("\n2c. Reading over AHB");
        read_reg_trans(GET_AHB, rdtrans_req_reg);
        if (subsystem_mode_tb) begin
          assert(rdtrans_req_reg.data != prod_debug_unlock_data) else begin
            $display("TB ERROR. SS_DBG_SERVICE_REG_REQ.PROD_DBG_UNLOCK_REQ failed");
            error_ctr += 1;
          end
        end
        else begin
          assert(rdtrans_req_reg.data == '0) else begin
            $display("TB ERROR. SS_DBG_SERVICE_REG_REQ.PROD_DBG_UNLOCK_REQ should be disabled in passive mode");
            error_ctr += 1;
          end
        end
        repeat (10) @(posedge clk_tb);

        //Caliptra Write SS_DEBUG_MANUF_SERVICE_REG_REQ.PROD_DBG_UNLOCK_REQ = 1
        $display ("\n2d. AHB Write To Debug Manuf Service Request register bit 1: production debug unlock request  ");
        wrtrans_req_reg.update_byname("SS_DBG_SERVICE_REG_REQ", prod_debug_unlock_data, tid);
        write_reg_trans(SET_AHB, wrtrans_req_reg);
        
        repeat (10) @(posedge clk_tb);

        // Read SS_DEBUG_MANUF_SERVICE_REG_REQ.PROD_DBG_UNLOCK_REQ = 1
        $display("\n2e. Reading over AXI");
        rdtrans_req_reg.update_byname("SS_DBG_SERVICE_REG_REQ", 0, tid);
        read_reg_trans(GET_AXI, rdtrans_req_reg);
        if (subsystem_mode_tb) begin
          assert(rdtrans_req_reg.data != prod_debug_unlock_data) else begin
            $display("TB ERROR. SS_DBG_SERVICE_REG_REQ.PROD_DBG_UNLOCK_REQ failed");
            error_ctr += 1;
          end
        end
        else begin
          assert(rdtrans_req_reg.data == '0) else begin
            $display("TB ERROR. SS_DBG_SERVICE_REG_REQ.PROD_DBG_UNLOCK_REQ should be disabled in passive mode");
            error_ctr += 1;
          end
        end

        repeat (10) @(posedge clk_tb);

        $display("\n2f. Reading over AHB");
        read_reg_trans(GET_AHB, rdtrans_req_reg);
        if (subsystem_mode_tb) begin
          assert(rdtrans_req_reg.data != prod_debug_unlock_data) else begin
            $display("TB ERROR. SS_DBG_SERVICE_REG_REQ.PROD_DBG_UNLOCK_REQ failed");
            error_ctr += 1;
          end
        end
        else begin
          assert(rdtrans_req_reg.data == '0) else begin
            $display("TB ERROR. SS_DBG_SERVICE_REG_REQ.PROD_DBG_UNLOCK_REQ should be disabled in passive mode");
            error_ctr += 1;
          end
        end
        repeat (10) @(posedge clk_tb);

        print_banner("3. AHB Write to SS_DEBUG_MANUF_SERVICE_REG_RSP - MANUFACTURING DEBUG UNLOCK RESPONSE and verify write successful.");

        // Caliptra write to SS_DEBUG_MANUF_SERVICE_REG_RSP register
        $display("\n3a. Write to SS_DBG_MANUF_SERVICE_REG_RSP over AHB");
        wrtrans_rsp_reg.update_byname("SS_DBG_MANUF_SERVICE_REG_RSP", 0, tid);
        wrtrans_rsp_reg.randomize();
        //$display("Write data no mask = 0x%0x", wrtrans_rsp_reg.data);
        //$display("mask = 0x%0x", get_mask("SS_DBG_MANUF_SERVICE_REG_RSP_MANUF_UNLOCK"));
        ss_debug_rsp_data = wrtrans_rsp_reg.data & get_mask("SS_DBG_MANUF_SERVICE_REG_RSP_MANUF_UNLOCK");
        //$display("Write data with mask = 0x%0x", ss_debug_rsp_data);
        write_reg_trans(SET_AHB, wrtrans_rsp_reg, .pfx("_MANUF_UNLOCK"));

        repeat (10) @(posedge clk_tb);

        //Caliptra read SS_DEBUG_MANUF_SERVICE_REG_RSP register
        $display("\n3b. Read SS_DBG_MANUF_SERVICE_REG_RSP over AHB");
        rdtrans_rsp_reg.update_byname("SS_DBG_MANUF_SERVICE_REG_RSP", 0, tid);
        read_reg_trans(GET_AHB, rdtrans_rsp_reg);
        if (subsystem_mode_tb) begin
          assert(rdtrans_rsp_reg.data == ss_debug_rsp_data) else begin
            $display("TB ERROR. SS_DBG_MANUF_SERVICE_REG_RSP read failed");
            error_ctr += 1;
          end
        end
        else begin
          assert(rdtrans_req_reg.data == '0) else begin
            $display("TB ERROR. SS_DBG_MANUF_SERVICE_REG_RSP should be disabled in passive mode");
            error_ctr += 1;
          end
        end

        repeat (10) @(posedge clk_tb);

        //SOC read SS_DEBUG_MANUF_SERVICE_REG_RSP register
        $display("\n3c. Read SS_DBG_MANUF_SERVICE_REG_RSP over AXI");
        read_reg_trans(GET_AXI, rdtrans_rsp_reg);
        if (subsystem_mode_tb) begin
          assert(rdtrans_rsp_reg.data == ss_debug_rsp_data) else begin
            $display("TB ERROR. SS_DBG_MANUF_SERVICE_REG_RSP read failed");
            error_ctr += 1;
          end
        end
        else begin
          assert(rdtrans_req_reg.data == '0) else begin
            $display("TB ERROR. SS_DBG_MANUF_SERVICE_REG_RSP should be disabled in passive mode");
            error_ctr += 1;
          end
        end

        print_banner("4. AXI Write to SS_DEBUG_MANUF_SERVICE_REG_RSP - MANUFACTURING DEBUG UNLOCK RESPONSE and verify write fails.");

        // SoC write to SS_DEBUG_MANUF_SERVICE_REG_RSP register
        $display("\n4a. Write to SS_DBG_MANUF_SERVICE_REG_RSP over AXI");
        wrtrans_rsp_reg.update_byname("SS_DBG_MANUF_SERVICE_REG_RSP", 0, tid);
        wrtrans_rsp_reg.randomize();
        //$display("Write data no mask = 0x%0x", wrtrans_rsp_reg.data);
        //$display("mask = 0x%0x", get_mask("SS_DBG_MANUF_SERVICE_REG_RSP_MANUF_UNLOCK"));
        //ss_debug_rsp_data = wrtrans_rsp_reg.data & get_mask("SS_DBG_MANUF_SERVICE_REG_RSP_MANUF_UNLOCK");
        ////$display("Write data with mask = 0x%0x", ss_debug_rsp_data);
        write_reg_trans(SET_AXI, wrtrans_rsp_reg, .pfx("_MANUF_UNLOCK"), .exp_sts(FAIL));

        repeat (10) @(posedge clk_tb);

        //Caliptra read SS_DEBUG_MANUF_SERVICE_REG_RSP register
        $display("\n4b. Read SS_DBG_MANUF_SERVICE_REG_RSP over AHB");
        rdtrans_rsp_reg.update_byname("SS_DBG_MANUF_SERVICE_REG_RSP", 0, tid);
        read_reg_trans(GET_AHB, rdtrans_rsp_reg);
        //Read data should match AHB write data from #3 above. 
        if (subsystem_mode_tb) begin
          assert(rdtrans_rsp_reg.data == ss_debug_rsp_data) else begin
            $display("TB ERROR. SS_DBG_MANUF_SERVICE_REG_RSP read failed");
            error_ctr += 1;
          end
        end
        else begin
          assert(rdtrans_req_reg.data == '0) else begin
            $display("TB ERROR. SS_DBG_MANUF_SERVICE_REG_RSP should be disabled in passive mode");
            error_ctr += 1;
          end
        end

        repeat (10) @(posedge clk_tb);

        //SOC read SS_DEBUG_MANUF_SERVICE_REG_RSP register
        $display("\n4c. Read SS_DBG_MANUF_SERVICE_REG_RSP over AXI");
        read_reg_trans(GET_AXI, rdtrans_rsp_reg);
        //Read data should match AHB write data from #3 above. 
        if (subsystem_mode_tb) begin
          assert(rdtrans_rsp_reg.data == ss_debug_rsp_data) else begin
            $display("TB ERROR. SS_DBG_MANUF_SERVICE_REG_RSP read failed");
            error_ctr += 1;
          end
        end
        else begin
          assert(rdtrans_req_reg.data == '0) else begin
            $display("TB ERROR. SS_DBG_MANUF_SERVICE_REG_RSP should be disabled in passive mode");
            error_ctr += 1;
          end
        end

        print_banner("5. AXI/AHB Write to SS_DEBUG_MANUF_SERVICE_REG_RSP - PRODUCTION DEBUG UNLOCK RESPONSE and verify write fails."); // Success only when device_lifecycle = PRODUCTION

        // SOC (AXI) write to SS_DEBUG_MANUF_SERVICE_REG_RSP register
        $display("\n5a. Write to SS_DBG_MANUF_SERVICE_REG_RSP over AXI");
        wrtrans_rsp_reg.update_byname("SS_DBG_MANUF_SERVICE_REG_RSP", 0, tid);
        wrtrans_rsp_reg.randomize();
        //$display("Write data no mask = 0x%0x", wrtrans_rsp_reg.data);
        //$display("mask = 0x%0x", get_mask("SS_DBG_MANUF_SERVICE_REG_RSP_PROD_UNLOCK"));
        ss_debug_rsp_data = wrtrans_rsp_reg.data & get_mask("SS_DBG_MANUF_SERVICE_REG_RSP_PROD_UNLOCK");
        //$display("Write data with mask = 0x%0x", ss_debug_rsp_data);
        write_reg_trans(SET_AXI, wrtrans_rsp_reg, .pfx("_PROD_UNLOCK"), .exp_sts(FAIL));

        repeat (10) @(posedge clk_tb);

        //Caliptra read SS_DEBUG_MANUF_SERVICE_REG_RSP register
        $display("\n5b. Read SS_DBG_MANUF_SERVICE_REG_RSP over AHB");
        rdtrans_rsp_reg.update_byname("SS_DBG_MANUF_SERVICE_REG_RSP", 0, tid);
        read_reg_trans(GET_AHB, rdtrans_rsp_reg);
        if (subsystem_mode_tb) begin
          assert(rdtrans_rsp_reg.data != ss_debug_rsp_data) else begin
            $display("TB ERROR. SS_DBG_MANUF_SERVICE_REG_RSP read failed");
            error_ctr += 1;
          end
        end
        else begin
          assert(rdtrans_req_reg.data == '0) else begin
            $display("TB ERROR. SS_DBG_MANUF_SERVICE_REG_RSP should be disabled in passive mode");
            error_ctr += 1;
          end
        end

        repeat (10) @(posedge clk_tb);

        //SOC read SS_DEBUG_MANUF_SERVICE_REG_RSP register
        $display("\n5c. Read SS_DBG_MANUF_SERVICE_REG_RSP over AXI");
        read_reg_trans(GET_AXI, rdtrans_rsp_reg);
        if (subsystem_mode_tb) begin
          assert(rdtrans_rsp_reg.data != ss_debug_rsp_data) else begin
            $display("TB ERROR. SS_DBG_MANUF_SERVICE_REG_RSP read failed");
            error_ctr += 1;
          end
        end
        else begin
          assert(rdtrans_req_reg.data == '0) else begin
            $display("TB ERROR. SS_DBG_MANUF_SERVICE_REG_RSP should be disabled in passive mode");
            error_ctr += 1;
          end
        end

        // Caliptra (AHB) write to SS_DEBUG_MANUF_SERVICE_REG_RSP register
        $display("\n5d. Write to SS_DBG_MANUF_SERVICE_REG_RSP over AHB");
        wrtrans_rsp_reg.update_byname("SS_DBG_MANUF_SERVICE_REG_RSP", 0, tid);
        wrtrans_rsp_reg.randomize();
        //$display("Write data no mask = 0x%0x", wrtrans_rsp_reg.data);
        //$display("mask = 0x%0x", get_mask("SS_DBG_MANUF_SERVICE_REG_RSP_PROD_UNLOCK"));
        ss_debug_rsp_data = wrtrans_rsp_reg.data & get_mask("SS_DBG_MANUF_SERVICE_REG_RSP_PROD_UNLOCK");
        //$display("Write data with mask = 0x%0x", ss_debug_rsp_data);
        write_reg_trans(SET_AXI, wrtrans_rsp_reg, .pfx("_PROD_UNLOCK"), .exp_sts(FAIL));

        repeat (10) @(posedge clk_tb);

        //Caliptra read SS_DEBUG_MANUF_SERVICE_REG_RSP register
        $display("\n5e. Read SS_DBG_MANUF_SERVICE_REG_RSP over AHB");
        rdtrans_rsp_reg.update_byname("SS_DBG_MANUF_SERVICE_REG_RSP", 0, tid);
        read_reg_trans(GET_AHB, rdtrans_rsp_reg);
        if (subsystem_mode_tb) begin
          assert(rdtrans_rsp_reg.data != ss_debug_rsp_data) else begin
            $display("TB ERROR. SS_DBG_MANUF_SERVICE_REG_RSP read failed");
            error_ctr += 1;
          end
        end
        else begin
          assert(rdtrans_req_reg.data == '0) else begin
            $display("TB ERROR. SS_DBG_MANUF_SERVICE_REG_RSP should be disabled in passive mode");
            error_ctr += 1;
          end
        end

        repeat (10) @(posedge clk_tb);

        //SOC read SS_DEBUG_MANUF_SERVICE_REG_RSP register
        $display("\n5f. Read SS_DBG_MANUF_SERVICE_REG_RSP over AXI");
        read_reg_trans(GET_AXI, rdtrans_rsp_reg);
        if (subsystem_mode_tb) begin
          assert(rdtrans_rsp_reg.data != ss_debug_rsp_data) else begin
            $display("TB ERROR. SS_DBG_MANUF_SERVICE_REG_RSP read failed");
            error_ctr += 1;
          end
        end
        else begin
          assert(rdtrans_req_reg.data == '0) else begin
            $display("TB ERROR. SS_DBG_MANUF_SERVICE_REG_RSP should be disabled in passive mode");
            error_ctr += 1;
          end
        end

        error_ctr += sb.err_count;
    end

  endtask
