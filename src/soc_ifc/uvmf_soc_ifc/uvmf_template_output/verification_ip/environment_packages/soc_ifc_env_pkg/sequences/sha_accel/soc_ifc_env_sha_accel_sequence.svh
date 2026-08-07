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
// DESCRIPTION: Mode-aware SoC-AXI SHA Accelerator access-control sequence.
//
//   This sequence exercises the SoC-AXI path to the SHA512 accelerator and
//   proves the per-mode access-control policy defined in the Caliptra
//   Integration Specification:
//     * Subsystem mode: only the requester whose AxUSER matches
//       SS_CALIPTRA_DMA_AXI_USER may operate the accelerator; every other
//       requester is rejected (SLVERR, no state change).
//     * Passive mode: the SoC-AXI SHA route is unavailable, so EVERY requester
//       (including one presenting the strap value) is rejected.
//
//   SHA requester AxUSER values are randomized 50% toward the randomized
//   strap_ss_caliptra_dma_axi_user value and 50% toward other values, in both
//   modes. Response and read data are checked through the RAL frontdoor,
//   predictor and AXI scoreboard; the soc_ifc_sha_acc_state_sva assertion module
//   (bound into soc_ifc_top) additionally proves that a rejected SoC-AXI access
//   is never granted the SHA route and so cannot change the SHA lock/state.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_env_sha_accel_sequence extends soc_ifc_env_sequence_base #(.CONFIG_T(soc_ifc_env_configuration_t));

  `uvm_object_utils( soc_ifc_env_sha_accel_sequence )

  caliptra_axi_user axi_user_obj;
  bit valid_user;
  rand sha_accel_op_s sha_accel_op_rand;
  rand int test_case;

  // Number of SoC-AXI SHA requester sessions to run. Constrained even so the
  // strap/other split can be exactly 50/50.
  rand int num_sessions;

  reg [31:0] dlen;
  uvm_status_e reg_sts;

  // Serializes individual RAL frontdoor bus accesses issued from run_legal_flow,
  // where the authorized owner thread and the continuous hijack thread both drive
  // the SHA CSR range through the SAME soc_ifc_AXI_map/adapter. The AVERY AXI reg
  // adapter is stateful and is not re-entrant, so exactly one bus transaction may
  // be in flight at a time. Hijack attempts still interleave with the owner
  // between accesses (during the randomized inter-poll delays).
  semaphore ral_bus_sem;

  // Loaded SHA test vector state (used for the subsystem-mode legal flow).
  reg [3199:0][31:0] vec_block_data;
  reg [15:0][31:0]   vec_digest;
  reg [31:0]         vec_block_len;

  extern virtual task load_vector();
  extern virtual function caliptra_axi_user make_user(bit want_strap);

  // Semaphore-guarded atomic RAL frontdoor accesses to the SHA CSR range. All SHA
  // register reads/writes in this sequence go through these so the owner and the
  // parallel hijack thread never re-enter the (stateful) AXI reg adapter at once.
  extern virtual task ral_read (uvm_reg rg, output uvm_status_e sts, output uvm_reg_data_t data, input caliptra_axi_user user);
  extern virtual task ral_write(uvm_reg rg, output uvm_status_e sts, input  uvm_reg_data_t data, input caliptra_axi_user user);

  extern virtual task sha_accel_setup();
  extern virtual task sha_accel_acquire_lock(output op_sts_e op_sts);
  extern virtual task sha_accel_set_cmd(input sha_accel_op_s op);
  extern virtual task sha_accel_push_datain(input reg [3199:0][31:0] sha_block_data, input reg endian_toggle);
  extern virtual task sha_accel_execute();
  extern virtual task sha_accel_poll_status();
  extern virtual task sha_accel_read_result(input reg [15:0][31:0] sha_digest);
  extern virtual task sha_accel_clr_lock();
  extern virtual task sha_accel_teardown();

  extern virtual task run_rejected_battery(input caliptra_axi_user user);
  extern virtual task run_legal_flow(input caliptra_axi_user owner, input caliptra_axi_user interferer);

  extern virtual function void report_reg_sts(uvm_status_e reg_sts, string name);
  extern virtual function void report_reg_sts_u(uvm_status_e reg_sts, string name, bit expect_valid, caliptra_axi_user user);

  constraint sha_accel_mailbox_mode_c { sha_accel_op_rand.mailbox_mode == 1'b0; }
  //don't run the "empty" test case
  constraint test_case_c {test_case inside { [1:255] }; }
  // Even number of requester sessions in a reasonable range
  constraint num_sessions_c { num_sessions inside {[4:12]}; num_sessions % 2 == 0; }

  // Bounds (in core clocks) for the randomized delay between successive LOCK/
  // STATUS polls, so polling is not lock-stepped to a fixed cadence.
  static const int unsigned SHA_POLL_DELAY_MIN = 20;
  static const int unsigned SHA_POLL_DELAY_MAX = 200;

  function new(string name = "soc_ifc_env_sha_accel_sequence");
    super.new(name);
    ral_bus_sem = new(1);
  endfunction

  // Return a fresh randomized inter-poll delay within [MIN:MAX] core clocks.
  virtual function int unsigned rand_poll_delay();
    return $urandom_range(SHA_POLL_DELAY_MIN, SHA_POLL_DELAY_MAX);
  endfunction

  virtual function void do_kill();
    // do_kill() runs before UVM terminates this sequence's process. Replace the
    // semaphore so a killed frontdoor operation cannot strand its only key if
    // this sequence object is subsequently reused.
    ral_bus_sem = new(1);
    reg_model.soc_ifc_AXI_map.get_sequencer().stop_sequences(); // Kill any pending AXI transfers
  endfunction

  virtual task pre_body();
    super.pre_body();
    reg_model = configuration.soc_ifc_rm;

    if (soc_ifc_status_agent_rsp_seq == null)
        `uvm_fatal("SHA_ACCEL_SEQ", "SHA Accelerator Sequence expected a handle to the soc_ifc status agent responder sequence (from bench-level sequence) but got null!")

  endtask

  virtual task body();

    caliptra_axi_user owner_user;
    caliptra_axi_user interferer_user;
    bit want_strap_q[$];
    int ii;

    // Global environment facts (integration mode + effective SoC-DMA AxUSER) are
    // captured once by the bringup sequence into the environment configuration.
    if (!configuration.global_straps_captured)
        `uvm_fatal("SHA_ACCEL_SEQ", "Global straps were not captured by the bringup sequence before this sequence ran!")
    if (configuration.subsystem_mode && !configuration.enable_sha_iccm_unlock)
        `uvm_fatal("SHA_ACCEL_SEQ", "Subsystem SHA sequence requires enable_sha_iccm_unlock before bringup")

    // Load a SHA test vector (used for the subsystem-mode legal flow).
    load_vector();

    // Build an exact 50/50 strap-vs-other requester-category list, shuffled.
    for (ii = 0; ii < num_sessions/2; ii++) want_strap_q.push_back(1'b1);
    for (ii = 0; ii < num_sessions/2; ii++) want_strap_q.push_back(1'b0);
    want_strap_q.shuffle();

    `uvm_info("SHA_ACCEL_SEQ", $sformatf("Running %0d SoC-AXI SHA sessions in %s mode (strap AxUSER = 0x%08x)",
                                         num_sessions, configuration.subsystem_mode ? "SUBSYSTEM" : "PASSIVE", configuration.ss_dma_axi_user), UVM_LOW)

    foreach (want_strap_q[ii]) begin
        if (configuration.subsystem_mode && want_strap_q[ii]) begin
            // Subsystem mode, matching strap requester: run the full legal flow,
            // with a non-matching requester continuously attempting to hijack the
            // accelerator in parallel for the whole session.
            owner_user      = make_user(1'b1);
            interferer_user = make_user(1'b0);
            run_legal_flow(owner_user, interferer_user);
        end
        else begin
            // Every other case is expected to be rejected:
            //  - passive mode: all requesters (strap or other)
            //  - subsystem mode: non-strap requesters
            run_rejected_battery(make_user(want_strap_q[ii]));
        end
    end

  endtask

endclass

//----------------------------------------------------------------------
// Construct a caliptra_axi_user. When want_strap is set the AxUSER equals the
// synchronized strap value; otherwise it is randomized to any other value.
//----------------------------------------------------------------------
function caliptra_axi_user soc_ifc_env_sha_accel_sequence::make_user(bit want_strap);
    caliptra_axi_user user;
    bit [31:0] strap;
    strap = configuration.ss_dma_axi_user;
    user = caliptra_axi_user::type_id::create("sha_axi_user");
    if (want_strap) begin
        user.set_addr_user(strap);
    end
    else begin
        if (!user.randomize() with { addr_user != strap; })
            `uvm_fatal("SHA_ACCEL_SEQ", "Failed to randomize a non-strap caliptra_axi_user")
    end
    return user;
endfunction

//----------------------------------------------------------------------
// Load a SHA test vector from the reference response files.
//----------------------------------------------------------------------
task soc_ifc_env_sha_accel_sequence::load_vector();
    reg [1:0] byte_shift;
    int cnt_tmp;
    int line_skip;
    int fd_r;
    string line_read;
    string tmp_str1;
    string tmp_str2;
    string extra_str;
    string file_name;
    int line_num;
    int parse_count;

    cnt_tmp = 0;
    line_num = 0;

    if (this.sha_accel_op_rand.sha512_mode) begin
        case(this.test_case) inside
        [0:127]:   begin file_name = "./SHA512ShortMsg.rsp"; line_skip = this.test_case * 4 + 7; end
        [128:255]: begin file_name = "./SHA512LongMsg.rsp";  line_skip = (this.test_case - 128) * 4 + 7; end
        endcase
    end
    else begin
        case(this.test_case) inside
        [0:127]:   begin file_name = "./SHA384ShortMsg.rsp"; line_skip = this.test_case * 4 + 7; end
        [128:255]: begin file_name = "./SHA384LongMsg.rsp";  line_skip = (this.test_case - 128) * 4 + 7; end
        endcase
    end

    fd_r = $fopen(file_name,"r");
    if (fd_r == 0)
        `uvm_fatal("SHA_ACCEL_VEC", $sformatf("Unable to open SHA vector file '%s' for test_case %0d", file_name, test_case))

    while (cnt_tmp <= line_skip) begin
        cnt_tmp = cnt_tmp + 1;
        line_num++;
        if ($fgets(line_read,fd_r) == 0) begin
            $fclose(fd_r);
            `uvm_fatal("SHA_ACCEL_VEC", $sformatf("Premature EOF in '%s' while seeking length record for test_case %0d (line %0d)", file_name, test_case, line_num))
        end
    end

    parse_count = $sscanf(line_read, "%s %s %d %s", tmp_str1, tmp_str2, vec_block_len, extra_str);
    if ((parse_count != 3) || (tmp_str1 != "Len") || (tmp_str2 != "=")) begin
        $fclose(fd_r);
        `uvm_fatal("SHA_ACCEL_VEC", $sformatf("Malformed length record in '%s' for test_case %0d at line %0d: '%s'", file_name, test_case, line_num, line_read))
    end

    line_num++;
    if ($fgets(line_read,fd_r) == 0) begin
        $fclose(fd_r);
        `uvm_fatal("SHA_ACCEL_VEC", $sformatf("Premature EOF in '%s' before data record for test_case %0d (line %0d)", file_name, test_case, line_num))
    end
    parse_count = $sscanf(line_read, "%s %s %h %s", tmp_str1, tmp_str2, vec_block_data, extra_str);
    if ((parse_count != 3) || (tmp_str1 != "Msg") || (tmp_str2 != "=")) begin
        $fclose(fd_r);
        `uvm_fatal("SHA_ACCEL_VEC", $sformatf("Malformed data record in '%s' for test_case %0d at line %0d: '%s'", file_name, test_case, line_num, line_read))
    end

    line_num++;
    if ($fgets(line_read,fd_r) == 0) begin
        $fclose(fd_r);
        `uvm_fatal("SHA_ACCEL_VEC", $sformatf("Premature EOF in '%s' before digest record for test_case %0d (line %0d)", file_name, test_case, line_num))
    end
    parse_count = $sscanf(line_read, "%s %s %h %s", tmp_str1, tmp_str2, vec_digest, extra_str);
    if ((parse_count != 3) || (tmp_str1 != "MD") || (tmp_str2 != "=")) begin
        $fclose(fd_r);
        `uvm_fatal("SHA_ACCEL_VEC", $sformatf("Malformed digest record in '%s' for test_case %0d at line %0d: '%s'", file_name, test_case, line_num, line_read))
    end

    $fclose(fd_r);

    // dlen is in bytes
    this.dlen  = vec_block_len >> 3;
    byte_shift = 'd4 - this.dlen[1:0];
    vec_block_data = vec_block_data << (byte_shift * 8);

    `uvm_info("SHA_ACCEL_SEQ", $sformatf("Loaded vector [%s] test_case %0d: block_len=%0d dlen=%0d", file_name, test_case, vec_block_len, dlen), UVM_MEDIUM)
endtask

task soc_ifc_env_sha_accel_sequence::ral_read(uvm_reg rg, output uvm_status_e sts, output uvm_reg_data_t data, input caliptra_axi_user user);
    ral_bus_sem.get(1);
    rg.read(sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(user));
    ral_bus_sem.put(1);
endtask

task soc_ifc_env_sha_accel_sequence::ral_write(uvm_reg rg, output uvm_status_e sts, input uvm_reg_data_t data, input caliptra_axi_user user);
    ral_bus_sem.get(1);
    rg.write(sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(user));
    ral_bus_sem.put(1);
endtask

task soc_ifc_env_sha_accel_sequence::sha_accel_setup();
    `uvm_info("SHA_ACCEL_SEQ", $sformatf("Start of SHA Accelerator legal flow"), UVM_MEDIUM)
    `uvm_info("SHA_ACCEL_SEQ", $sformatf("Using AXI USER 0x%x (valid: %x)", axi_user_obj.get_addr_user(), valid_user), UVM_HIGH)
endtask

task soc_ifc_env_sha_accel_sequence::sha_accel_acquire_lock(output op_sts_e op_sts);
    uvm_reg_data_t data;
    int unsigned attempts;

    op_sts = CPTRA_TIMEOUT;
    attempts = 0;
    do begin
        // Wait for read data to return with '0', indicating no other agent has lock
        configuration.soc_ifc_ctrl_agent_config.wait_for_num_clocks(rand_poll_delay());
        ral_read(reg_model.sha512_acc_csr_rm.LOCK, reg_sts, data, axi_user_obj);
        report_reg_sts(reg_sts, "LOCK");
        attempts++;
        if (attempts > 8) begin
            // Could not acquire a free lock. The authorized user's access was not
            // rejected (checked by report_reg_sts above); the lock is simply held.
            `uvm_info("SHA_ACCEL_SEQ", "Authorized user could not acquire a free SHA lock (lock held)", UVM_MEDIUM)
            return;
        end
    end
    while (data[reg_model.sha512_acc_csr_rm.LOCK.LOCK.get_lsb_pos()]);
    //Read the lock again to test predictor
    configuration.soc_ifc_ctrl_agent_config.wait_for_num_clocks(rand_poll_delay());
    ral_read(reg_model.sha512_acc_csr_rm.LOCK, reg_sts, data, axi_user_obj);
    report_reg_sts(reg_sts, "LOCK");
    op_sts = CPTRA_SUCCESS;
endtask

task soc_ifc_env_sha_accel_sequence::sha_accel_set_cmd(input sha_accel_op_s op);
    uvm_reg_data_t data;

    data = '0;
    data[0] = op.sha512_mode;
    data[1] = op.mailbox_mode;
    data[2] = op.endian_toggle;

    ral_write(reg_model.sha512_acc_csr_rm.MODE, reg_sts, data, axi_user_obj);
    report_reg_sts(reg_sts, "MODE");
    data[31:0] = this.dlen;

    ral_write(reg_model.sha512_acc_csr_rm.DLEN, reg_sts, data, axi_user_obj);
    report_reg_sts(reg_sts, "DLEN");

    //read back some fields to test predictor
    ral_read(reg_model.sha512_acc_csr_rm.USER, reg_sts, data, axi_user_obj);
    report_reg_sts(reg_sts, "USER");
    ral_read(reg_model.sha512_acc_csr_rm.MODE, reg_sts, data, axi_user_obj);
    report_reg_sts(reg_sts, "MODE");
    ral_read(reg_model.sha512_acc_csr_rm.DLEN, reg_sts, data, axi_user_obj);
    report_reg_sts(reg_sts, "DLEN");
endtask

task soc_ifc_env_sha_accel_sequence::sha_accel_push_datain(input reg [3199:0][31:0] sha_block_data, input reg endian_toggle);
    int ii;
    reg [31:0] data;
    int most_sig_dword;
    most_sig_dword = (this.dlen[1:0] == 2'b00) ? (this.dlen >> 2) - 1 : (this.dlen >> 2);

    if (this.dlen != 0) begin
        for (ii=most_sig_dword; ii >= 0 ; ii--) begin
            data = endian_toggle ? sha_block_data[ii] : {sha_block_data[ii][7:0],sha_block_data[ii][15:8],sha_block_data[ii][23:16],sha_block_data[ii][31:24]};
            `uvm_info("SHA_ACCEL_SEQ", $sformatf("[Iteration: %0d] sha_block_data: 0x%x. Sending datain: 0x%x", ii, sha_block_data[ii], data), UVM_DEBUG)
            ral_write(reg_model.sha512_acc_csr_rm.DATAIN, reg_sts, uvm_reg_data_t'(data), axi_user_obj);
            report_reg_sts(reg_sts, "DATAIN");
        end
    end
endtask

task soc_ifc_env_sha_accel_sequence::sha_accel_execute();
    uvm_reg_data_t data = uvm_reg_data_t'(1) << reg_model.sha512_acc_csr_rm.EXECUTE.EXECUTE.get_lsb_pos();
    ral_write(reg_model.sha512_acc_csr_rm.EXECUTE, reg_sts, data, axi_user_obj);
    report_reg_sts(reg_sts, "EXECUTE");
endtask

task soc_ifc_env_sha_accel_sequence::sha_accel_poll_status();
    uvm_reg_data_t data;
    int unsigned attempts;

    attempts = 0;
    // Wait for read data to return with 'VALID == 1', indicating operation is successful
    do begin
        configuration.soc_ifc_ctrl_agent_config.wait_for_num_clocks(rand_poll_delay());
        ral_read(reg_model.sha512_acc_csr_rm.STATUS, reg_sts, data, axi_user_obj);
        report_reg_sts(reg_sts, "STATUS");
        if (!valid_user) break;
        attempts++;
        if (attempts > 50) begin
            `uvm_error("SHA_ACCEL_SEQ", "Timed out waiting for SHA STATUS.VALID")
            break;
        end
    end
    while (!data[reg_model.sha512_acc_csr_rm.STATUS.VALID.get_lsb_pos()]);
endtask

task soc_ifc_env_sha_accel_sequence::sha_accel_read_result(reg [15:0][31:0] sha_digest);
    uvm_reg_data_t data;
    int ii;
    int digest_dwords = this.sha_accel_op_rand.sha512_mode ? 16 : 12;
    for (ii=0; ii < digest_dwords; ii++) begin
        ral_read(reg_model.sha512_acc_csr_rm.DIGEST[ii], reg_sts, data, axi_user_obj);
        report_reg_sts(reg_sts, "DIGEST");
        if (valid_user && (data != sha_digest[digest_dwords-1-ii])) begin
            `uvm_error("SHA_ACCEL_SEQ",$sformatf("SHA512 Digest Mismatch - Digest[%x] Expected: %x Actual: %x", ii, sha_digest[digest_dwords-1-ii], data))
        end
        else if (!valid_user && (data == sha_digest[digest_dwords-1-ii])) begin
            `uvm_error("SHA_ACCEL_SEQ",$sformatf("SHA512 Digest Matches, but SHA Accelerator was not accessed with valid user! - Digest[%x] Expected: %x Actual: %x", ii, sha_digest[digest_dwords-1-ii], data))
        end
    end
endtask

task soc_ifc_env_sha_accel_sequence::sha_accel_clr_lock();
    uvm_reg_data_t data = 0;
    data[reg_model.sha512_acc_csr_rm.LOCK.LOCK.get_lsb_pos()] = 1'b1;
    //write one to clear lock
    ral_write(reg_model.sha512_acc_csr_rm.LOCK, reg_sts, data, axi_user_obj);
    report_reg_sts(reg_sts, "LOCK");
endtask

task soc_ifc_env_sha_accel_sequence::sha_accel_teardown();
    `uvm_info("SHA_ACCEL_SEQ", $sformatf("End of SHA Accelerator legal flow"), UVM_MEDIUM)
endtask

//----------------------------------------------------------------------
// Subsystem-mode legal flow: the authorized (strap) requester runs its full SHA
// session (acquire -> configure -> push -> execute -> poll -> read -> clear)
// while a non-matching interferer CONTINUOUSLY attempts to hijack the
// accelerator in parallel. Every hijack attempt must be rejected, and none may
// disturb the owner - proven by the owner still acquiring the lock and its final
// digest still matching the expected vector.
//----------------------------------------------------------------------
task soc_ifc_env_sha_accel_sequence::run_legal_flow(input caliptra_axi_user owner, input caliptra_axi_user interferer);
    op_sts_e op_sts;
    bit      owner_done;

    axi_user_obj = owner;
    valid_user   = 1'b1;
    owner_done   = 1'b0;

    sha_accel_setup();

    // Run the authorized owner's ENTIRE SHA session (acquire -> configure -> push
    // -> execute -> poll -> read -> clear) while a non-matching requester
    // CONTINUOUSLY tries to hijack the accelerator in parallel. Every hijack
    // attempt must be rejected (checked in run_rejected_battery) AND must not
    // disturb the owner: the owner must still acquire the lock, its final digest
    // must match the expected vector (checked in sha_accel_read_result), and no
    // hijack access may steal or clear the lock. The interferer thread uses only
    // its own AxUSER and local status, so it shares no mutable state with the
    // owner thread (which owns axi_user_obj / valid_user / reg_sts / dlen).
    `uvm_info("SHA_ACCEL_SEQ", $sformatf("Owner 0x%08x running full SHA session while non-strap AxUSER 0x%08x continuously attempts hijack (acquire..clear)", owner.get_addr_user(), interferer.get_addr_user()), UVM_MEDIUM)
    fork
        begin : owner_thread
            sha_accel_acquire_lock(op_sts);
            if (op_sts != CPTRA_SUCCESS) begin
                // The authorized (strap) user must be able to acquire the SHA lock
                // in subsystem mode. The bringup/reset flow releases the SHA
                // accelerator boot lock via the requested HW ICCM-content-hash
                // flow. Failing to acquire it is a hard error.
                `uvm_error("SHA_ACCEL_SEQ", "Authorized user failed to acquire the SHA lock after the requested ICCM-content-hash release.")
            end
            else begin
                sha_accel_set_cmd(sha_accel_op_rand);
                sha_accel_push_datain(vec_block_data, sha_accel_op_rand.endian_toggle);
                sha_accel_execute();
                sha_accel_poll_status();
                sha_accel_read_result(vec_digest);
                sha_accel_clr_lock();
            end
            owner_done = 1'b1; // signal the hijack thread to stop (all exit paths)
        end
        begin : hijack_thread
            int unsigned guard = 0;
            while (!owner_done && (guard < 1000)) begin
                run_rejected_battery(interferer);
                guard++;
            end
        end
    join

    sha_accel_teardown();
endtask

//----------------------------------------------------------------------
// Rejected-access battery: exercise reads and writes across the SHA CSR map,
// including CSRs with distinct internal RDL policy, and prove every access is
// rejected by the route policy for the given requester. Used
// for all passive-mode requesters, all non-strap subsystem-mode requesters, and
// as the continuous parallel hijack thread in run_legal_flow. Uses only local
// state so it is safe to run concurrently with the authorized owner.
//----------------------------------------------------------------------
task soc_ifc_env_sha_accel_sequence::run_rejected_battery(input caliptra_axi_user user);
    uvm_reg_data_t data;
    // Local status (not the shared class member reg_sts) so this task is safe to
    // run concurrently with the authorized owner's flow in run_legal_flow.
    uvm_status_e   lsts;

    `uvm_info("SHA_ACCEL_SEQ", $sformatf("Rejected-access battery with AxUSER 0x%08x (%s mode)", user.get_addr_user(), configuration.subsystem_mode ? "SUBSYSTEM" : "PASSIVE"), UVM_MEDIUM)

    // Attempt to acquire the lock (read LOCK). Must be rejected.
    ral_read(reg_model.sha512_acc_csr_rm.LOCK, lsts, data, user);
    report_reg_sts_u(lsts, "LOCK", 1'b0, user);

    // Read USER. Must be rejected.
    ral_read(reg_model.sha512_acc_csr_rm.USER, lsts, data, user);
    report_reg_sts_u(lsts, "USER", 1'b0, user);

    // Attempt configuration writes (MODE, DLEN) and read them back. Must be rejected.
    ral_write(reg_model.sha512_acc_csr_rm.MODE, lsts, uvm_reg_data_t'(1), user);
    report_reg_sts_u(lsts, "MODE", 1'b0, user);
    ral_read(reg_model.sha512_acc_csr_rm.MODE, lsts, data, user);
    report_reg_sts_u(lsts, "MODE", 1'b0, user);

    ral_write(reg_model.sha512_acc_csr_rm.DLEN, lsts, uvm_reg_data_t'(32'h40), user);
    report_reg_sts_u(lsts, "DLEN", 1'b0, user);
    ral_read(reg_model.sha512_acc_csr_rm.DLEN, lsts, data, user);
    report_reg_sts_u(lsts, "DLEN", 1'b0, user);

    // Attempt a data push. Must be rejected.
    ral_write(reg_model.sha512_acc_csr_rm.DATAIN, lsts, uvm_reg_data_t'(32'hDEAD_BEEF), user);
    report_reg_sts_u(lsts, "DATAIN", 1'b0, user);

    // Attempt to trigger execution. Must be rejected.
    data = uvm_reg_data_t'(1) << reg_model.sha512_acc_csr_rm.EXECUTE.EXECUTE.get_lsb_pos();
    ral_write(reg_model.sha512_acc_csr_rm.EXECUTE, lsts, data, user);
    report_reg_sts_u(lsts, "EXECUTE", 1'b0, user);

    // Read STATUS and a DIGEST word. Must be rejected.
    ral_read(reg_model.sha512_acc_csr_rm.STATUS, lsts, data, user);
    report_reg_sts_u(lsts, "STATUS", 1'b0, user);
    ral_read(reg_model.sha512_acc_csr_rm.DIGEST[0], lsts, data, user);
    report_reg_sts_u(lsts, "DIGEST", 1'b0, user);

    // Attempt to clear the lock. An unauthorized requester must not affect the owner.
    data = uvm_reg_data_t'(1) << reg_model.sha512_acc_csr_rm.LOCK.LOCK.get_lsb_pos();
    ral_write(reg_model.sha512_acc_csr_rm.LOCK, lsts, data, user);
    report_reg_sts_u(lsts, "LOCK", 1'b0, user);

    // CONTROL has a distinct internal RDL policy, but the route policy must
    // still reject this requester. Writing zero avoids requesting zeroization.
    ral_write(reg_model.sha512_acc_csr_rm.CONTROL, lsts, '0, user);
    report_reg_sts_u(lsts, "CONTROL", 1'b0, user);
    ral_read(reg_model.sha512_acc_csr_rm.CONTROL, lsts, data, user);
    report_reg_sts_u(lsts, "CONTROL", 1'b0, user);

    // SHA interrupt CSRs also have distinct internal RDL policy, but remain
    // unreachable when the route rejects this requester.
    ral_read(reg_model.sha512_acc_csr_rm.intr_block_rf_ext.global_intr_en_r,
             lsts, data, user);
    report_reg_sts_u(lsts, "global_intr_en_r", 1'b0, user);
endtask

function void soc_ifc_env_sha_accel_sequence::report_reg_sts(uvm_status_e reg_sts, string name);
    report_reg_sts_u(reg_sts, name, valid_user, axi_user_obj);
endfunction

function void soc_ifc_env_sha_accel_sequence::report_reg_sts_u(uvm_status_e reg_sts, string name, bit expect_valid, caliptra_axi_user user);
    if ( expect_valid && (reg_sts != UVM_IS_OK))
        `uvm_error("SHA_ACCEL_SEQ",$sformatf("Register access failed unexpectedly (%s) when using valid SHA user 0x%x", name, user.get_addr_user()))
    if (!expect_valid && (reg_sts == UVM_IS_OK))
        `uvm_error("SHA_ACCEL_SEQ",$sformatf("Register access succeeded unexpectedly (%s) when using invalid SHA user 0x%x", name, user.get_addr_user()))
endfunction
