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
// DESCRIPTION: Base sequence to perform a SHA Accelerator commands within the
//              soc_ifc environment.
//              Extended to provide additional functionality.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_env_sha_accel_sequence extends soc_ifc_env_sequence_base #(.CONFIG_T(soc_ifc_env_configuration_t));

  `uvm_object_utils( soc_ifc_env_sha_accel_sequence )

  caliptra_apb_user apb_user_obj;
  rand sha_accel_op_s sha_accel_op_rand;
  rand int test_case;
  reg [31:0] dlen;
  int sts_rsp_count;
  uvm_status_e reg_sts;

  extern virtual task sha_accel_setup();
  extern virtual task sha_accel_acquire_lock(output op_sts_e op_sts);
  extern virtual task sha_accel_set_cmd(input sha_accel_op_s op);
  extern virtual task sha_accel_push_datain(input reg [3199:0][31:0] sha_block_data);
  extern virtual task sha_accel_execute();
  extern virtual task sha_accel_poll_status();
  extern virtual task sha_accel_read_result(input reg [15:0][31:0] sha_digest);
  extern virtual task sha_accel_clr_lock();
  extern virtual task sha_accel_teardown();

  extern virtual function void report_reg_sts(uvm_status_e reg_sts, string name);

  constraint sha_accel_mailbox_mode_c { sha_accel_op_rand.mailbox_mode == 1'b0; }
  constraint test_case_c {test_case inside { [0:255] }; }

  virtual function void do_kill();
    // FIXME gracefully terminate any APB requests pending?
    reg_model.soc_ifc_APB_map.get_sequencer().stop_sequences(); // Kill any pending APB transfers
  endfunction

  virtual task pre_body();
    super.pre_body();
    reg_model = configuration.soc_ifc_rm;

    if (soc_ifc_status_agent_rsp_seq == null)
        `uvm_fatal("SHA_ACCEL_SEQ", "SHA Accelerator Sequence expected a handle to the soc_ifc status agent responder sequence (from bench-level sequence) but got null!")

  endtask

  virtual task body();

    op_sts_e op_sts;

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

    sts_rsp_count = 0;

    fork
        forever begin
            @(soc_ifc_status_agent_rsp_seq.new_rsp) sts_rsp_count++;
        end
    join_none

    //`uvm_info("SHA_ACCEL_SEQ", $sformatf("Initiating command sequence to mailbox with cmd: [%p] dlen: [%p] resp_dlen: [%p]", sha_accel_op_rand.cmd.cmd_e, sha_accel_op_rand.dlen, sha_accel_resp_expected_dlen), UVM_MEDIUM)
    apb_user_obj = new();
    apb_user_obj.randomize();

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

    //dlen is in bytes
    this.dlen = block_len >> 3;


    byte_shift = 'd4 - this.dlen[1:0];
    sha_block_data = sha_block_data << (byte_shift * 8);

    `uvm_info("SHA_ACCEL_SEQ", $sformatf("Block Data: %x", sha_block_data), UVM_LOW)
    `uvm_info("SHA_ACCEL_SEQ", $sformatf("Block Len: %x", block_len), UVM_LOW)

    sha_accel_setup();
    sha_accel_acquire_lock(op_sts);
    sha_accel_set_cmd(sha_accel_op_rand);
    sha_accel_push_datain(sha_block_data);
    sha_accel_execute();
    sha_accel_poll_status();
    sha_accel_read_result(sha_digest);
    sha_accel_clr_lock();
    sha_accel_teardown();

  endtask

endclass

task soc_ifc_env_sha_accel_sequence::sha_accel_setup();
    `uvm_info("SHA_ACCEL_SEQ", $sformatf("Start of SHA Accelerator sequence"), UVM_MEDIUM)
endtask

task soc_ifc_env_sha_accel_sequence::sha_accel_acquire_lock(output op_sts_e op_sts);
    uvm_reg_data_t data;

    op_sts = CPTRA_TIMEOUT;
    reg_model.sha512_acc_csr_rm.LOCK.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(apb_user_obj));
    report_reg_sts(reg_sts, "LOCK");
    // Wait for read data to return with '0', indicating no other agent has lock
    while (data[reg_model.sha512_acc_csr_rm.LOCK.LOCK.get_lsb_pos()]) begin
        configuration.soc_ifc_ctrl_agent_config.wait_for_num_clocks(200); // FIXME add more randomization on delay
        reg_model.sha512_acc_csr_rm.LOCK.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(apb_user_obj));
        report_reg_sts(reg_sts, "LOCK");
    end
    op_sts = CPTRA_SUCCESS;
endtask

task soc_ifc_env_sha_accel_sequence::sha_accel_set_cmd(input sha_accel_op_s op);
    uvm_reg_data_t data;
    
    data = '0;
    data[0] = op.sha512_mode;
    data[1] = op.mailbox_mode;

    reg_model.sha512_acc_csr_rm.MODE.write(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(apb_user_obj));
    report_reg_sts(reg_sts, "MODE");
    data[31:0] = this.dlen;

    reg_model.sha512_acc_csr_rm.DLEN.write(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(apb_user_obj));
    report_reg_sts(reg_sts, "DLEN");
endtask

task soc_ifc_env_sha_accel_sequence::sha_accel_push_datain(reg [3199:0][31:0] sha_block_data);
    int ii;
    reg [31:0] data;
    int most_sig_dword;
    //Divide the number of bytes by 4 to get the number of dwords.
    //If the data is evenly divisible, the most significant dword is N-1. If it includes a partial dword it's already rounded down
    most_sig_dword = (this.dlen[1:0] == 2'b00) ? (this.dlen >> 2) - 1 : (this.dlen >> 2);

    if (this.dlen != 0) begin
        for (ii=most_sig_dword; ii >= 0 ; ii--) begin
            data = sha_block_data[ii];
            `uvm_info("SHA_ACCEL_SEQ", $sformatf("[Iteration: %0d] Sending datain: 0x%x", ii, data), UVM_DEBUG)
            reg_model.sha512_acc_csr_rm.DATAIN.write(reg_sts, uvm_reg_data_t'(data), UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(apb_user_obj));
            report_reg_sts(reg_sts, "DATAIN");
        end
    end
endtask

task soc_ifc_env_sha_accel_sequence::sha_accel_execute();
    uvm_reg_data_t data = uvm_reg_data_t'(1) << reg_model.sha512_acc_csr_rm.EXECUTE.EXECUTE.get_lsb_pos();
    reg_model.sha512_acc_csr_rm.EXECUTE.write(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(apb_user_obj));
    report_reg_sts(reg_sts, "EXECUTE");
endtask

task soc_ifc_env_sha_accel_sequence::sha_accel_poll_status();
    uvm_reg_data_t data;
    reg_model.sha512_acc_csr_rm.STATUS.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(apb_user_obj));
    report_reg_sts(reg_sts, "STATUS");

    // Wait for read data to return with '0', indicating no other agent has lock
    while (!data[reg_model.sha512_acc_csr_rm.STATUS.VALID.get_lsb_pos()]) begin
        configuration.soc_ifc_ctrl_agent_config.wait_for_num_clocks(200); // FIXME add more randomization on delay
        reg_model.sha512_acc_csr_rm.STATUS.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(apb_user_obj));
        report_reg_sts(reg_sts, "STATUS");
    end
endtask

task soc_ifc_env_sha_accel_sequence::sha_accel_read_result(reg [15:0][31:0] sha_digest);
    uvm_reg_data_t data;
    int ii;
    int digest_dwords = this.sha_accel_op_rand.sha512_mode ? 16 : 12;
    for (ii=0; ii < digest_dwords; ii++) begin
        reg_model.sha512_acc_csr_rm.DIGEST[ii].read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(apb_user_obj));
        report_reg_sts(reg_sts, "DIGEST");
        if (data != sha_digest[digest_dwords-1-ii]) begin
            `uvm_error("SHA_ACCEL_SEQ",$sformatf("SHA512 Digest Mismatch - Digest[%x] Expected: %x Actual: %x", ii, sha_digest[digest_dwords-1-ii], data))
        end
    end
endtask

task soc_ifc_env_sha_accel_sequence::sha_accel_clr_lock();
    uvm_reg_data_t data = 0;
    data[reg_model.sha512_acc_csr_rm.LOCK.LOCK.get_lsb_pos()] = 1'b1;
    //write one to clear lock
    reg_model.sha512_acc_csr_rm.LOCK.write(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(apb_user_obj));
    report_reg_sts(reg_sts, "LOCK");
endtask

task soc_ifc_env_sha_accel_sequence::sha_accel_teardown();
    // Summary at sequence end
    `uvm_info("SHA_ACCEL_SEQ", $sformatf("End of SHA Accelerator sequence"), UVM_MEDIUM)
endtask

function void soc_ifc_env_sha_accel_sequence::report_reg_sts(uvm_status_e reg_sts, string name);
    if (reg_sts != UVM_IS_OK)
        `uvm_error("SHA_ACCEL_SEQ",$sformatf("Register access failed unexpectedly (%s)", name))
endfunction
