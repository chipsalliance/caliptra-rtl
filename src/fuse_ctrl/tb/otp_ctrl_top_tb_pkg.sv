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

`ifndef OTP_CTRL_TOP_TB_PKG
`define OTP_CTRL_TOP_TB_PKG

package otp_ctrl_top_tb_pkg;
    
    localparam int CoreAw = 13;

    localparam CSR_BASE = 0;

    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_INTR_STATE_OFFSET = 13'h 0;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_INTR_ENABLE_OFFSET = 13'h 4;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_INTR_TEST_OFFSET = 13'h 8;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_ALERT_TEST_OFFSET = 13'h c;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_STATUS_OFFSET = 13'h 10;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_ERR_CODE_0_OFFSET = 13'h 14;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_ERR_CODE_1_OFFSET = 13'h 18;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_ERR_CODE_2_OFFSET = 13'h 1c;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_ERR_CODE_3_OFFSET = 13'h 20;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_ERR_CODE_4_OFFSET = 13'h 24;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_ERR_CODE_5_OFFSET = 13'h 28;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_ERR_CODE_6_OFFSET = 13'h 2c;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_ERR_CODE_7_OFFSET = 13'h 30;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_ERR_CODE_8_OFFSET = 13'h 34;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_DIRECT_ACCESS_REGWEN_OFFSET = 13'h 38;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_DIRECT_ACCESS_CMD_OFFSET = 13'h 3c;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_DIRECT_ACCESS_ADDRESS_OFFSET = 13'h 40;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_DIRECT_ACCESS_WDATA_0_OFFSET = 13'h 44;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_DIRECT_ACCESS_WDATA_1_OFFSET = 13'h 48;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_DIRECT_ACCESS_RDATA_0_OFFSET = 13'h 4c;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_DIRECT_ACCESS_RDATA_1_OFFSET = 13'h 50;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_CHECK_TRIGGER_REGWEN_OFFSET = 13'h 54;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_CHECK_TRIGGER_OFFSET = 13'h 58;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_CHECK_REGWEN_OFFSET = 13'h 5c;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_CHECK_TIMEOUT_OFFSET = 13'h 60;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_INTEGRITY_CHECK_PERIOD_OFFSET = 13'h 64;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_CONSISTENCY_CHECK_PERIOD_OFFSET = 13'h 68;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_VENDOR_TEST_READ_LOCK_OFFSET = 13'h 6c;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_NON_SECRET_FUSES_READ_LOCK_OFFSET = 13'h 70;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_VENDOR_TEST_DIGEST_0_OFFSET = 13'h 74;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_VENDOR_TEST_DIGEST_1_OFFSET = 13'h 78;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_NON_SECRET_FUSES_DIGEST_0_OFFSET = 13'h 7c;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_NON_SECRET_FUSES_DIGEST_1_OFFSET = 13'h 80;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_SECRET0_DIGEST_0_OFFSET = 13'h 84;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_SECRET0_DIGEST_1_OFFSET = 13'h 88;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_SECRET1_DIGEST_0_OFFSET = 13'h 8c;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_SECRET1_DIGEST_1_OFFSET = 13'h 90;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_SECRET2_DIGEST_0_OFFSET = 13'h 94;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_SECRET2_DIGEST_1_OFFSET = 13'h 98;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_SECRET3_DIGEST_0_OFFSET = 13'h 9c;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_SECRET3_DIGEST_1_OFFSET = 13'h a0;

    typedef logic [CoreAw-1:0] word_addr_t;

    typedef string strq_t [$];

    strq_t csr_registers = '{
        "CALIPTRA_OTP_CTRL_INTR_STATE_OFFSET",
        "CALIPTRA_OTP_CTRL_INTR_ENABLE_OFFSET",
        "CALIPTRA_OTP_CTRL_INTR_TEST_OFFSET",
        "CALIPTRA_OTP_CTRL_ALERT_TEST_OFFSET",
        "CALIPTRA_OTP_CTRL_STATUS_OFFSET",
        "CALIPTRA_OTP_CTRL_ERR_CODE_0_OFFSET",
        "CALIPTRA_OTP_CTRL_ERR_CODE_1_OFFSET",
        "CALIPTRA_OTP_CTRL_ERR_CODE_2_OFFSET",
        "CALIPTRA_OTP_CTRL_ERR_CODE_3_OFFSET",
        "CALIPTRA_OTP_CTRL_ERR_CODE_4_OFFSET",
        "CALIPTRA_OTP_CTRL_ERR_CODE_5_OFFSET",
        "CALIPTRA_OTP_CTRL_ERR_CODE_6_OFFSET",
        "CALIPTRA_OTP_CTRL_ERR_CODE_7_OFFSET",
        "CALIPTRA_OTP_CTRL_ERR_CODE_8_OFFSET",
        "CALIPTRA_OTP_CTRL_DIRECT_ACCESS_REGWEN_OFFSET",
        "CALIPTRA_OTP_CTRL_DIRECT_ACCESS_CMD_OFFSET",
        "CALIPTRA_OTP_CTRL_DIRECT_ACCESS_ADDRESS_OFFSET",
        "CALIPTRA_OTP_CTRL_DIRECT_ACCESS_WDATA_0_OFFSET",
        "CALIPTRA_OTP_CTRL_DIRECT_ACCESS_WDATA_1_OFFSET",
        "CALIPTRA_OTP_CTRL_DIRECT_ACCESS_RDATA_0_OFFSET",
        "CALIPTRA_OTP_CTRL_DIRECT_ACCESS_RDATA_1_OFFSET",
        "CALIPTRA_OTP_CTRL_CHECK_TRIGGER_REGWEN_OFFSET",
        "CALIPTRA_OTP_CTRL_CHECK_TRIGGER_OFFSET",
        "CALIPTRA_OTP_CTRL_CHECK_REGWEN_OFFSET",
        "CALIPTRA_OTP_CTRL_CHECK_TIMEOUT_OFFSET",
        "CALIPTRA_OTP_CTRL_INTEGRITY_CHECK_PERIOD_OFFSET",
        "CALIPTRA_OTP_CTRL_CONSISTENCY_CHECK_PERIOD_OFFSET",
        "CALIPTRA_OTP_CTRL_VENDOR_TEST_READ_LOCK_OFFSET",
        "CALIPTRA_OTP_CTRL_NON_SECRET_FUSES_READ_LOCK_OFFSET",
        "CALIPTRA_OTP_CTRL_VENDOR_TEST_DIGEST_0_OFFSET",
        "CALIPTRA_OTP_CTRL_VENDOR_TEST_DIGEST_1_OFFSET",
        "CALIPTRA_OTP_CTRL_NON_SECRET_FUSES_DIGEST_0_OFFSET",
        "CALIPTRA_OTP_CTRL_NON_SECRET_FUSES_DIGEST_1_OFFSET",
        "CALIPTRA_OTP_CTRL_SECRET0_DIGEST_0_OFFSET",
        "CALIPTRA_OTP_CTRL_SECRET0_DIGEST_1_OFFSET",
        "CALIPTRA_OTP_CTRL_SECRET1_DIGEST_0_OFFSET",
        "CALIPTRA_OTP_CTRL_SECRET1_DIGEST_1_OFFSET",
        "CALIPTRA_OTP_CTRL_SECRET2_DIGEST_0_OFFSET",
        "CALIPTRA_OTP_CTRL_SECRET2_DIGEST_1_OFFSET",
        "CALIPTRA_OTP_CTRL_SECRET3_DIGEST_0_OFFSET",
        "CALIPTRA_OTP_CTRL_SECRET3_DIGEST_1_OFFSET"
    };

    word_addr_t _csr_register_dict [string] = { 
        "CALIPTRA_OTP_CTRL_INTR_STATE_OFFSET"		            : CSR_BASE + CALIPTRA_OTP_CTRL_INTR_STATE_OFFSET, 		            // 0x00     Interrupt State
        "CALIPTRA_OTP_CTRL_INTR_ENABLE_OFFSET"		            : CSR_BASE + CALIPTRA_OTP_CTRL_INTR_ENABLE_OFFSET, 		            // 0x04     Interrupt Enable
        "CALIPTRA_OTP_CTRL_INTR_TEST_OFFSET"		            : CSR_BASE + CALIPTRA_OTP_CTRL_INTR_TEST_OFFSET, 		            // 0x08     Interrupt Test
        "CALIPTRA_OTP_CTRL_ALERT_TEST_OFFSET"		            : CSR_BASE + CALIPTRA_OTP_CTRL_ALERT_TEST_OFFSET, 		            // 0x0C     Alert Test
        "CALIPTRA_OTP_CTRL_STATUS_OFFSET"		                : CSR_BASE + CALIPTRA_OTP_CTRL_STATUS_OFFSET, 		                // 0x10     Status
        "CALIPTRA_OTP_CTRL_ERR_CODE_0_OFFSET"		            : CSR_BASE + CALIPTRA_OTP_CTRL_ERR_CODE_0_OFFSET, 		            // 0x14     Error Code 0
        "CALIPTRA_OTP_CTRL_ERR_CODE_1_OFFSET"		            : CSR_BASE + CALIPTRA_OTP_CTRL_ERR_CODE_1_OFFSET, 		            // 0x18     Error Code 1
        "CALIPTRA_OTP_CTRL_ERR_CODE_2_OFFSET"		            : CSR_BASE + CALIPTRA_OTP_CTRL_ERR_CODE_2_OFFSET, 		            // 0x1C     Error Code 2
        "CALIPTRA_OTP_CTRL_ERR_CODE_3_OFFSET"		            : CSR_BASE + CALIPTRA_OTP_CTRL_ERR_CODE_3_OFFSET, 		            // 0x20     Error Code 3
        "CALIPTRA_OTP_CTRL_ERR_CODE_4_OFFSET"		            : CSR_BASE + CALIPTRA_OTP_CTRL_ERR_CODE_4_OFFSET, 		            // 0x24     Error Code 4
        "CALIPTRA_OTP_CTRL_ERR_CODE_5_OFFSET"		            : CSR_BASE + CALIPTRA_OTP_CTRL_ERR_CODE_5_OFFSET, 		            // 0x28     Error Code 5
        "CALIPTRA_OTP_CTRL_ERR_CODE_6_OFFSET"		            : CSR_BASE + CALIPTRA_OTP_CTRL_ERR_CODE_6_OFFSET, 		            // 0x2C     Error Code 6
        "CALIPTRA_OTP_CTRL_ERR_CODE_7_OFFSET"		            : CSR_BASE + CALIPTRA_OTP_CTRL_ERR_CODE_7_OFFSET, 		            // 0x30     Error Code 7
        "CALIPTRA_OTP_CTRL_ERR_CODE_8_OFFSET"		            : CSR_BASE + CALIPTRA_OTP_CTRL_ERR_CODE_8_OFFSET, 		            // 0x34     Error Code 8
        "CALIPTRA_OTP_CTRL_DIRECT_ACCESS_REGWEN_OFFSET"		    : CSR_BASE + CALIPTRA_OTP_CTRL_DIRECT_ACCESS_REGWEN_OFFSET, 		// 0x38     Direct Access Register Write Enable
        "CALIPTRA_OTP_CTRL_DIRECT_ACCESS_CMD_OFFSET"		    : CSR_BASE + CALIPTRA_OTP_CTRL_DIRECT_ACCESS_CMD_OFFSET, 		    // 0x3C     Direct Access Command
        "CALIPTRA_OTP_CTRL_DIRECT_ACCESS_ADDRESS_OFFSET"	    : CSR_BASE + CALIPTRA_OTP_CTRL_DIRECT_ACCESS_ADDRESS_OFFSET, 		// 040x     Direct Access Address
        "CALIPTRA_OTP_CTRL_DIRECT_ACCESS_WDATA_0_OFFSET"	    : CSR_BASE + CALIPTRA_OTP_CTRL_DIRECT_ACCESS_WDATA_0_OFFSET, 		// 0x44     Direct Access Write Data 0
        "CALIPTRA_OTP_CTRL_DIRECT_ACCESS_WDATA_1_OFFSET"	    : CSR_BASE + CALIPTRA_OTP_CTRL_DIRECT_ACCESS_WDATA_1_OFFSET, 		// 0x48     Direct Access Write Data 1
        "CALIPTRA_OTP_CTRL_DIRECT_ACCESS_RDATA_0_OFFSET"	    : CSR_BASE + CALIPTRA_OTP_CTRL_DIRECT_ACCESS_RDATA_0_OFFSET, 		// 0x4C     Direct Access Read Data 0
        "CALIPTRA_OTP_CTRL_DIRECT_ACCESS_RDATA_1_OFFSET"	    : CSR_BASE + CALIPTRA_OTP_CTRL_DIRECT_ACCESS_RDATA_1_OFFSET, 		// 0x50     Direct Access Read Data 1
        "CALIPTRA_OTP_CTRL_CHECK_TRIGGER_REGWEN_OFFSET"		    : CSR_BASE + CALIPTRA_OTP_CTRL_CHECK_TRIGGER_REGWEN_OFFSET, 		// 0x54     Check Trigger Register Write Enable
        "CALIPTRA_OTP_CTRL_CHECK_TRIGGER_OFFSET"		        : CSR_BASE + CALIPTRA_OTP_CTRL_CHECK_TRIGGER_OFFSET, 		        // 0x58     Check Trigger
        "CALIPTRA_OTP_CTRL_CHECK_REGWEN_OFFSET"		            : CSR_BASE + CALIPTRA_OTP_CTRL_CHECK_REGWEN_OFFSET, 		        // 0x5C     Check Register Write Enable
        "CALIPTRA_OTP_CTRL_CHECK_TIMEOUT_OFFSET"		        : CSR_BASE + CALIPTRA_OTP_CTRL_CHECK_TIMEOUT_OFFSET, 		        // 0x60     Check Timeout
        "CALIPTRA_OTP_CTRL_INTEGRITY_CHECK_PERIOD_OFFSET"	    : CSR_BASE + CALIPTRA_OTP_CTRL_INTEGRITY_CHECK_PERIOD_OFFSET, 		// 0x64     Integrity Check Period
        "CALIPTRA_OTP_CTRL_CONSISTENCY_CHECK_PERIOD_OFFSET"	    : CSR_BASE + CALIPTRA_OTP_CTRL_CONSISTENCY_CHECK_PERIOD_OFFSET, 	// 0x68     Consistency Check Period
        "CALIPTRA_OTP_CTRL_VENDOR_TEST_READ_LOCK_OFFSET"	    : CSR_BASE + CALIPTRA_OTP_CTRL_VENDOR_TEST_READ_LOCK_OFFSET, 		// 0x6C     Vendor Test Read Lock   
        "CALIPTRA_OTP_CTRL_NON_SECRET_FUSES_READ_LOCK_OFFSET"	: CSR_BASE + CALIPTRA_OTP_CTRL_NON_SECRET_FUSES_READ_LOCK_OFFSET, 	// 0x70     Non Secret Fuses Read Lock
        "CALIPTRA_OTP_CTRL_VENDOR_TEST_DIGEST_0_OFFSET"	        : CSR_BASE + CALIPTRA_OTP_CTRL_VENDOR_TEST_DIGEST_0_OFFSET, 		// 0x74     Vendor Test Digest 0
        "CALIPTRA_OTP_CTRL_VENDOR_TEST_DIGEST_1_OFFSET"		    : CSR_BASE + CALIPTRA_OTP_CTRL_VENDOR_TEST_DIGEST_1_OFFSET, 		// 0x78     Vendor Test Digest 1
        "CALIPTRA_OTP_CTRL_NON_SECRET_FUSES_DIGEST_0_OFFSET"	: CSR_BASE + CALIPTRA_OTP_CTRL_NON_SECRET_FUSES_DIGEST_0_OFFSET, 	// 0x7C     Non Secret Fuses Digest 0
        "CALIPTRA_OTP_CTRL_NON_SECRET_FUSES_DIGEST_1_OFFSET"	: CSR_BASE + CALIPTRA_OTP_CTRL_NON_SECRET_FUSES_DIGEST_1_OFFSET, 	// 0x80     Non Secret Fuses Digest 1
        "CALIPTRA_OTP_CTRL_SECRET0_DIGEST_0_OFFSET"		        : CSR_BASE + CALIPTRA_OTP_CTRL_SECRET0_DIGEST_0_OFFSET, 		    // 0x84     Secret 0 Digest 0
        "CALIPTRA_OTP_CTRL_SECRET0_DIGEST_1_OFFSET"		        : CSR_BASE + CALIPTRA_OTP_CTRL_SECRET0_DIGEST_1_OFFSET, 		    // 0x88     Secret 0 Digest 1
        "CALIPTRA_OTP_CTRL_SECRET1_DIGEST_0_OFFSET"		        : CSR_BASE + CALIPTRA_OTP_CTRL_SECRET1_DIGEST_0_OFFSET, 		    // 0x8C     Secret 1 Digest 0
        "CALIPTRA_OTP_CTRL_SECRET1_DIGEST_1_OFFSET"		        : CSR_BASE + CALIPTRA_OTP_CTRL_SECRET1_DIGEST_1_OFFSET, 		    // 0x90     Secret 1 Digest 1
        "CALIPTRA_OTP_CTRL_SECRET2_DIGEST_0_OFFSET"		        : CSR_BASE + CALIPTRA_OTP_CTRL_SECRET2_DIGEST_0_OFFSET, 		    // 0x94     Secret 2 Digest 0
        "CALIPTRA_OTP_CTRL_SECRET2_DIGEST_1_OFFSET"		        : CSR_BASE + CALIPTRA_OTP_CTRL_SECRET2_DIGEST_1_OFFSET, 		    // 0x98     Secret 2 Digest 1
        "CALIPTRA_OTP_CTRL_SECRET3_DIGEST_0_OFFSET"		        : CSR_BASE + CALIPTRA_OTP_CTRL_SECRET3_DIGEST_0_OFFSET, 		    // 0x9C     Secret 3 Digest 0
        "CALIPTRA_OTP_CTRL_SECRET3_DIGEST_1_OFFSET"             : CSR_BASE + CALIPTRA_OTP_CTRL_SECRET3_DIGEST_1_OFFSET              // 0xA0     Secret 3 Digest 1
    };

    function word_addr_t get_addr(string name);
        if (_csr_register_dict.exists(name))
            return _csr_register_dict[name];
        else begin
            $display("TB WARNING. Address %s is not found in csr reg name -> address map. Returning 0", name);
            return 0;
        end
    endfunction // get_addr

    function strq_t get_dai_regnames();
        strq_t dai_regs;
        string csr_reg_name;

        foreach (csr_registers[i]) begin
            csr_reg_name = csr_registers[i];
            if (csr_reg_name.substr(18, 23) == "DIRECT") 
                dai_regs.push_back(csr_reg_name);
        end

        return dai_regs;
    endfunction

    function bit str_find (string reg_name, string substr);
        int i;
        bit found;
        for (i = 0; i <= reg_name.len() - substr.len(); i++) begin
            $display(reg_name, i);
            //$display(reg_name[i], reg_name[i+1], reg_name[i+2], reg_name[i+3], reg_name[i+4], reg_name[i+5]);
            $display(reg_name.substr(i, substr.len()-1));
            if (reg_name.substr(i, (i + substr.len()-1)) == substr) begin
                //$display("Substring '%s' found at index %0d", substr, i);
                found = 1;
                break;
            end
        end
        if (!found) begin
            $display("Substring '%s' not found", substr);
        end
        return found;
    endfunction

        


endpackage

`endif