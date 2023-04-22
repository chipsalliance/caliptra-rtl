//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
//----------------------------------------------------------------------
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

//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
// DESCRIPTION: Extended from mbox_base sequence to test the SHA512
//              Accelerator mailbox functionality
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_env_mbox_sha_accel_sequence extends soc_ifc_env_mbox_sequence_base;

    `uvm_object_utils( soc_ifc_env_mbox_sha_accel_sequence )
        
    rand sha_accel_op_s sha_accel_op_rand;
    rand int test_case;
    rand reg [31:0] start_addr;
    reg [31:0] dlen;

    //for reading known answer tests from file
    reg [3199:0][31:0] sha_block_data;
    reg [31:0] block_len;
    reg [15:0][31:0] sha_digest;
    reg [1:0] byte_shift;

    int cnt_tmp;
    int line_skip;

    int fd_r;

    string line_read;
    string tmp_str1;
    string tmp_str2;
    string file_name;

    extern virtual task mbox_setup();
    extern virtual task mbox_push_datain();
    extern virtual task mbox_read_resp_data();

    constraint sha_accel_op_c { sha_accel_op_rand.mailbox_mode == 1'b1; }
    constraint mbox_cmd_c { sha_accel_op_rand.sha512_mode == 1'b0 -> mbox_op_rand.cmd.cmd_e == MBOX_CMD_SHA384_REQ;
                            sha_accel_op_rand.sha512_mode == 1'b1 -> mbox_op_rand.cmd.cmd_e == MBOX_CMD_SHA512_REQ; 
                            solve sha_accel_op_rand before mbox_op_rand; }
    constraint mbox_resp_dlen_c {sha_accel_op_rand.sha512_mode == 1'b0 -> mbox_resp_expected_dlen == 32'd48;
                                 sha_accel_op_rand.sha512_mode == 1'b1 -> mbox_resp_expected_dlen == 32'd64; 
                                 solve sha_accel_op_rand before mbox_resp_expected_dlen; }
    constraint test_case_c {test_case inside { [0:255] }; }
    //Start address can be anywhere from entry 0 to the final mailbox address
    //Must be aligned to dword
    constraint start_addr_c {start_addr inside { [0:131068] }; 
                             start_addr[1:0] == '0; }

endclass

task soc_ifc_env_mbox_sha_accel_sequence::mbox_setup();
    super.mbox_setup();

    //open appropriate file for test vectors
    if (this.sha_accel_op_rand.sha512_mode) begin
        case(this.test_case) inside
        [0:127]: begin
            file_name = "./SHA512ShortMsg.rsp";
            line_skip = this.test_case * 4 + 7;
        end
        [128:255]: begin
            file_name = "./SHA512LongMsg.rsp";
            line_skip = (this.test_case - 128) * 4 + 7;
        end
        endcase
    end
    else begin
        case(this.test_case) inside
        [0:127]: begin
            file_name = "./SHA384ShortMsg.rsp";
            line_skip = this.test_case * 4 + 7;
        end
        [128:255]: begin
            file_name = "./SHA384LongMsg.rsp";
            line_skip = (this.test_case - 128) * 4 + 7;
        end
        endcase
    end

    `uvm_info("SHA_ACCEL_SEQ", $sformatf("Test Case: %d", this.test_case), UVM_DEBUG)
    `uvm_info("SHA_ACCEL_SEQ", $sformatf("SHA512 Mode: %x", this.sha_accel_op_rand.sha512_mode), UVM_DEBUG)
    `uvm_info("SHA_ACCEL_SEQ", $sformatf("File Name: %s", file_name), UVM_DEBUG)

    fd_r = $fopen(file_name,"r");

    while (cnt_tmp <= line_skip) begin
        cnt_tmp = cnt_tmp + 1;
        $fgets(line_read,fd_r);
    end

    // get the block and its length
    $sscanf( line_read, "%s %s %d", tmp_str1, tmp_str2, block_len);
    $fgets(line_read,fd_r);
    $sscanf( line_read, "%s %s %h", tmp_str1, tmp_str2, sha_block_data);
    $fgets(line_read,fd_r);
    $sscanf( line_read, "%s %s %h", tmp_str1, tmp_str2, sha_digest);
    
    $fclose(fd_r);

    `uvm_info("SHA_ACCEL_SEQ", $sformatf("Pre Shift sha_block_data: %x", sha_block_data), UVM_LOW)
    `uvm_info("SHA_ACCEL_SEQ", $sformatf("Block Len: %x", block_len), UVM_LOW)

    //dlen is in bytes
    this.dlen = block_len >> 3;

    byte_shift = 'd4 - this.dlen[1:0];
    sha_block_data = sha_block_data << (byte_shift * 8);

    `uvm_info("SHA_ACCEL_SEQ", $sformatf("sha_block_data: %x", sha_block_data), UVM_LOW)

    // Restrict the start addr so that we don't overflow the mailbox
    if ( (this.start_addr + this.dlen) > 'h20000 ) begin
        //if we would have overflowed, just lower start address so the data fits in the mailbox at the end
        this.start_addr = 'h20000 - (this.dlen);
    end
    // Override dlen to reflect the size of the SHA data
    this.mbox_op_rand.dlen = this.start_addr + this.dlen;
endtask

// This should be overridden with real data to write
task soc_ifc_env_mbox_sha_accel_sequence::mbox_push_datain();
    int ii;
    reg [31:0] data;
    int most_sig_dword;
    int sha_block_start_dw;

    //write 0's until the start address
    sha_block_start_dw = this.start_addr >> 2;

    for (ii=0; ii < sha_block_start_dw; ii++) begin
        reg_model.mbox_csr_rm.mbox_datain.write(reg_sts, uvm_reg_data_t'('0), UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(get_rand_user(PAUSER_PROB_DATAIN)));
        report_reg_sts(reg_sts, "mbox_datain");
    end

    //write the sha block
    most_sig_dword = (this.dlen[1:0] == 2'b00) ? (this.dlen >> 2) - 1 : (this.dlen >> 2);

    if (this.dlen != 0) begin
        for (ii=most_sig_dword; ii >= 0 ; ii--) begin
            data = sha_block_data[ii];
            `uvm_info("SHA_ACCEL_SEQ", $sformatf("[Iteration: %0d] Sending datain: 0x%x", ii, data), UVM_DEBUG)
            reg_model.mbox_csr_rm.mbox_datain.write(reg_sts, uvm_reg_data_t'(data), UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(get_rand_user(PAUSER_PROB_DATAIN)));
            report_reg_sts(reg_sts, "mbox_datain");
        end
    end


endtask

task soc_ifc_env_mbox_sha_accel_sequence::mbox_read_resp_data();
    uvm_reg_data_t data;
    int ii;
    int digest_dwords = this.sha_accel_op_rand.sha512_mode ? 16 : 12;

    for (ii=0; ii < digest_dwords; ii++) begin
        reg_model.mbox_csr_rm.mbox_dataout.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(get_rand_user(PAUSER_PROB_DATAOUT)));
        report_reg_sts(reg_sts, "mbox_dataout");
        if (!pauser_used_is_valid() && retry_failed_reg_axs) begin
            `uvm_info("SHA_ACCEL_SEQ", "Re-do dataout read with valid PAUSER", UVM_HIGH)
            reg_model.mbox_csr_rm.mbox_dataout.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(get_rand_user(FORCE_VALID_PAUSER)));
            report_reg_sts(reg_sts, "mbox_dataout");
        end
        if (data != sha_digest[digest_dwords-1-ii]) begin
            `uvm_error("SHA_ACCEL_SEQ",$sformatf("SHA512 Digest Mismatch - Digest[%x] Expected: %x Actual: %x", ii, sha_digest[digest_dwords-1-ii], data))
        end
    end
endtask