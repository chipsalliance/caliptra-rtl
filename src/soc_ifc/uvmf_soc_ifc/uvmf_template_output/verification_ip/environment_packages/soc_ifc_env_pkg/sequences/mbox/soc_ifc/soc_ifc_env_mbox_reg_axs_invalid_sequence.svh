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
// DESCRIPTION: Extended from mbox_base sequence to provide additional
//              functionality in a test that sends mailbox commands
//              of a size that exceeds mailbox capacity.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_env_mbox_reg_axs_invalid_sequence extends soc_ifc_env_mbox_sequence_base;

  `uvm_object_utils( soc_ifc_env_mbox_reg_axs_invalid_sequence )

  // Constrain command to undefined opcode
  constraint mbox_cmd_undef_c { !(mbox_op_rand.cmd.cmd_s inside {defined_cmds}); }

  extern virtual task                    mbox_do_random_reg_write(process mainline);
  extern virtual function uvm_reg_data_t get_rand_wr_data(uvm_reg axs_reg);

  function new(string name = "" );
    super.new(name);
  endfunction

  //==========================================
  // Task:        body
  // Description: Implement main functionality for
  //              SOC-side transmission of mailbox request.
  //              Override default body to inject random
  //              (deliberately erroneous) register accesses
  //              throughout a normal test flow.
  //==========================================
  virtual task body();

    op_sts_e op_sts;
    process mbox_flow_proc;

    sts_rsp_count = 0;

    fork
        forever begin
            @(soc_ifc_status_agent_rsp_seq.new_rsp) sts_rsp_count++;
        end
    join_none

    `uvm_info("MBOX_SEQ", $sformatf("Initiating command sequence to mailbox with cmd: [%p] dlen: [%p] resp_dlen: [%p]", mbox_op_rand.cmd.cmd_e, mbox_op_rand.dlen, mbox_resp_expected_dlen), UVM_MEDIUM)

    fork
        begin: MBOX_FLOW
            mbox_flow_proc = process::self();
            mbox_setup();               if (rand_delay_en) do_rand_delay(1, step_delay);
            mbox_acquire_lock(op_sts);  if (rand_delay_en) do_rand_delay(1, step_delay);
            mbox_set_cmd(mbox_op_rand); if (rand_delay_en) do_rand_delay(1, step_delay);
            mbox_push_datain();         if (rand_delay_en) do_rand_delay(1, step_delay);
            mbox_execute();             if (rand_delay_en) do_rand_delay(1, step_delay);
            mbox_poll_status();         if (rand_delay_en) do_rand_delay(1, step_delay);
        end
        begin: ERR_INJECT_FLOW
            wait(mbox_flow_proc != null);
            mbox_do_random_reg_write(mbox_flow_proc);
        end
    join
    mbox_clr_execute();         if (rand_delay_en) do_rand_delay(1, step_delay);
    mbox_teardown();

  endtask

endclass

//==========================================
// Task:        mbox_do_random_reg_write
// Description: Do some random reg write that will
//              (most likely) be invalid and trigger
//              the protocol error violation.
//==========================================
task soc_ifc_env_mbox_reg_axs_invalid_sequence::mbox_do_random_reg_write(process mainline);
    uvm_reg mbox_regs[$];
    int unsigned rand_idx;
    uvm_reg_data_t rand_wr_data;
    caliptra_apb_user local_apb_user_obj;
    uvm_status_e local_reg_sts;

    mbox_regs.push_back(reg_model.mbox_csr_rm.mbox_cmd    );
    mbox_regs.push_back(reg_model.mbox_csr_rm.mbox_dlen   );
    mbox_regs.push_back(reg_model.mbox_csr_rm.mbox_datain );
    mbox_regs.push_back(reg_model.mbox_csr_rm.mbox_dataout);
    mbox_regs.push_back(reg_model.mbox_csr_rm.mbox_execute);
    mbox_regs.push_back(reg_model.mbox_csr_rm.mbox_status );

    if (!std::randomize(rand_idx) with {rand_idx < mbox_regs.size(); })
        `uvm_fatal("MBOX_SEQ", "Failed to randomize reg idx")

    // Wait and do the reg write at some random point in the sequence
    do_rand_delay(1, DLY_CUSTOM);
    // Data used depends on which reg is being accessed to force invalid contents
    rand_wr_data = get_rand_wr_data(mbox_regs[rand_idx]);
    // Get a randomized PAUSER for this transaction - 50% chance of being valid
    local_apb_user_obj = new();
    if (!local_apb_user_obj.randomize() with {if (pauser_locked.locked)
                                                       (addr_user == pauser_locked.pauser) dist
                                                       {1 :/ 1,
                                                        0 :/ 1};
                                                   else
                                                       (addr_user inside {mbox_valid_users}) dist
                                                       {1 :/ 1,
                                                        0 :/ 1}; })
        `uvm_error("MBOX_SEQ", "Failed to randomize APB PAUSER override value")
    else
        `uvm_info("MBOX_SEQ", $sformatf("Randomized APB PAUSER override value to 0x%x", local_apb_user_obj.addr_user), UVM_HIGH)
    // Pause the main mailbox flow to prevent race conditions (on accesses to the same register, triggering is_busy UVM_WARNING)
    if (mainline.status() inside {process::RUNNING,process::WAITING}) begin
        in_report_reg_sts.wait_on();
        `uvm_info("MBOX_SEQ", $sformatf("Pausing main mailbox flow to allow random reg access injection"), UVM_HIGH)
        mainline.suspend();
        in_report_reg_sts.reset();
    end
    else begin
        `uvm_info("MBOX_SEQ", $sformatf("Main mailbox flow is in state [%s], so it will not be suspended for random reg access injection", mainline.status().name()), UVM_HIGH)
    end
    `uvm_info("MBOX_SEQ", {"Performing random register access to ", mbox_regs[rand_idx].get_name()}, UVM_LOW)
    if (mbox_regs[rand_idx].get_name() == "mbox_dataout") begin
        mbox_regs[rand_idx].read(local_reg_sts, rand_wr_data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(local_apb_user_obj));
        report_reg_sts(local_reg_sts, mbox_regs[rand_idx].get_name(), local_apb_user_obj);
    end
    else if (mbox_regs[rand_idx].get_name() == "mbox_datain") begin
        wait(reg_model.mbox_csr_rm.mbox_fn_state_sigs.uc_receive_stage == 1'b0);
        mbox_regs[rand_idx].write(local_reg_sts, rand_wr_data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(local_apb_user_obj));
        report_reg_sts(local_reg_sts, mbox_regs[rand_idx].get_name(), local_apb_user_obj);
    end
    else begin
        mbox_regs[rand_idx].write(local_reg_sts, rand_wr_data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(local_apb_user_obj));
        report_reg_sts(local_reg_sts, mbox_regs[rand_idx].get_name(), local_apb_user_obj);
    end
    if (mainline.status() == process::SUSPENDED) begin
        `uvm_info("MBOX_SEQ", $sformatf("Resuming main mailbox flow after random reg access injection"), UVM_HIGH)
        mainline.resume();
    end
endtask

//==========================================
// Task:        get_rand_wr_data
// Description: Generate random data according
//              to a set of rules related to which register
//              is being accessed, with intent to cause
//              a protocol violation.
//==========================================
function uvm_reg_data_t soc_ifc_env_mbox_reg_axs_invalid_sequence::get_rand_wr_data(uvm_reg axs_reg);
    uvm_reg_data_t tmp_data;
    case (axs_reg.get_name()) inside
        "mbox_cmd": begin
            tmp_data = mbox_op_rand.cmd;
        end
        "mbox_dlen": begin
            tmp_data = mbox_op_rand.dlen; 
        end
        "mbox_datain",
        "mbox_dataout": begin
            std::randomize(tmp_data);
        end
        "mbox_execute": begin
            uvm_reg_data_t msk;
            msk = ~(uvm_reg_data_t'(1) << reg_model.mbox_csr_rm.mbox_execute.execute.get_lsb_pos());
            std::randomize(tmp_data) with {(tmp_data & msk) == 0;};
        end
        "mbox_status": begin
            uvm_reg_data_t msk;
            msk = ((uvm_reg_data_t'(1) << reg_model.mbox_csr_rm.mbox_status.status.get_n_bits()) - 1) << reg_model.mbox_csr_rm.mbox_status.status.get_lsb_pos();
            msk = ~msk;
            std::randomize(tmp_data) with {(tmp_data & msk) == 0;};
        end
        default: begin
            `uvm_fatal("MBOX_SEQ", "Bad reg")
        end
    endcase
    return tmp_data;
endfunction
