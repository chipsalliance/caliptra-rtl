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

// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
// DESCRIPTION: Sequence to wait for Mailbox commands (from uC) and
//              respond/handle the command.
//              This sequence also injects protocol errors into the mailbox
//              by performing out-of-order register accesses.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_env_soc_mbox_reg_axs_invalid_handler_sequence extends soc_ifc_env_soc_mbox_handler_sequence;


  `uvm_object_utils( soc_ifc_env_soc_mbox_reg_axs_invalid_handler_sequence )

  extern virtual task                    mbox_do_random_reg_write(process mainline);
  extern virtual function uvm_reg_data_t get_rand_wr_data(uvm_reg axs_reg);

  //==========================================
  // Task:        body
  // Description: Implement main functionality for
  //              Caliptra-side handling of received
  //              mailbox request.
  //==========================================
  virtual task body();

    op_sts_e op_sts;
    bit do_fsm_chk = 1;
    process mbox_flow_proc;
    reg_model = configuration.soc_ifc_rm;

    if (soc_ifc_status_agent_rsp_seq == null)
        `uvm_fatal("SOC_MBOX_HANDLER", "SOC_IFC ENV SOC mailbox handler sequence expected a handle to the soc_ifc status agent responder sequence (from bench-level sequence) but got null!")
    fork
        forever begin
            @(soc_ifc_status_agent_rsp_seq.new_rsp) sts_rsp_count++;
        end
    join_none

    // Setup
    mbox_setup();

    fork
        begin: HANDLER_FLOW
            mbox_flow_proc = process::self();
            // Wait for a mailbox command to be received
            mbox_wait_for_command(op_sts);
            if (op_sts != CPTRA_SUCCESS) begin
                `uvm_error("SOC_MBOX_HANDLER", "Unsuccessful return code from wait_for_command_avail()")
            end

            // Get COMMAND
            mbox_get_command();
            mbox_pop_dataout();

            // Return control to uC
            if (sts_rsp_count && !soc_ifc_status_agent_rsp_seq.rsp.mailbox_data_avail) begin
                // Our random_reg_write may write to mbox_status and cause us to exit EXECUTE_SOC early...
                do_fsm_chk = 0;
            end
            mbox_set_status();
            configuration.soc_ifc_ctrl_agent_config.wait_for_num_clocks(2); // Takes a few cycles for FSM update to propagate into register
            if (do_fsm_chk)
                mbox_check_fsm();
        end
        begin: ERR_INJECT_FLOW
            wait(mbox_flow_proc != null);
            mbox_do_random_reg_write(mbox_flow_proc);
        end
    join
    mbox_wait_done();

    // End of Sequence
    mbox_teardown();

  endtask

endclass

//==========================================
// Task:        mbox_do_random_reg_write
// Description: Do some random reg write that will
//              (most likely) be invalid and trigger
//              the protocol error violation.
//==========================================
task soc_ifc_env_soc_mbox_reg_axs_invalid_handler_sequence::mbox_do_random_reg_write(process mainline);
    uvm_reg mbox_regs[$];
    int unsigned rand_idx;
    int unsigned rand_delay;
    uvm_reg_data_t rand_wr_data;
    caliptra_apb_user local_apb_user_obj;

    mbox_regs.push_back(reg_model.mbox_csr_rm.mbox_cmd    );
    mbox_regs.push_back(reg_model.mbox_csr_rm.mbox_dlen   );
    mbox_regs.push_back(reg_model.mbox_csr_rm.mbox_datain );
    mbox_regs.push_back(reg_model.mbox_csr_rm.mbox_dataout);
    mbox_regs.push_back(reg_model.mbox_csr_rm.mbox_execute);
    mbox_regs.push_back(reg_model.mbox_csr_rm.mbox_status );

    if (!std::randomize(rand_idx) with {rand_idx < mbox_regs.size(); })
        `uvm_fatal("SOC_MBOX_HANDLER", "Failed to randomize reg idx")

    // Wait to do the reg write at some random point in the sequence, or do it
    // very soon after the normal operation ends
    std::randomize(rand_delay) with {rand_delay dist {[1:255] :/ 5, [256:1023] :/ 3, [1024:65535] :/ 1};};
    fork
        automatic int unsigned dly = rand_delay;
        begin
            configuration.soc_ifc_ctrl_agent_config.wait_for_num_clocks(dly);
        end
        begin
            mainline.await();
            configuration.soc_ifc_ctrl_agent_config.wait_for_num_clocks(dly % 25);
        end
    join_any
 
    // Data used depends on which reg is being accessed to force invalid contents
    rand_wr_data = get_rand_wr_data(mbox_regs[rand_idx]);

    // Get a randomized PAUSER for this transaction - 50% chance of being valid
    local_apb_user_obj = new();
    if (!local_apb_user_obj.randomize() with {(addr_user inside {mbox_valid_users}) dist
                                              {1 :/ 1,
                                               0 :/ 1}; })
        `uvm_error("SOC_MBOX_HANDLER", "Failed to randomize APB PAUSER override value")
    else
        `uvm_info("SOC_MBOX_HANDLER", $sformatf("Randomized APB PAUSER override value to 0x%x", local_apb_user_obj.addr_user), UVM_HIGH)

    // Pause the main mailbox responder flow to prevent race conditions (on accesses to the same register, triggering is_busy UVM_WARNING)
    if (mainline.status() inside {process::RUNNING,process::WAITING}) begin
        in_report_reg_sts.wait_on();
        `uvm_info("SOC_MBOX_HANDLER", $sformatf("Pausing main mailbox flow to allow random reg access injection"), UVM_HIGH)
        mainline.suspend();
        in_report_reg_sts.reset();
    end
    else begin
        `uvm_info("SOC_MBOX_HANDLER", $sformatf("Main mailbox flow is in state [%s], so it will not be suspended for random reg access injection", mainline.status().name()), UVM_HIGH)
    end

    // Do the access
    `uvm_info("SOC_MBOX_HANDLER", {"Performing random register access to ", mbox_regs[rand_idx].get_name()}, UVM_LOW)
    if (mbox_regs[rand_idx].get_name() == "mbox_dataout") begin
        mbox_regs[rand_idx].read(reg_sts, rand_wr_data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(local_apb_user_obj));
        report_reg_sts(reg_sts, mbox_regs[rand_idx].get_name(), local_apb_user_obj);
    end
    else if (mbox_regs[rand_idx].get_name() == "mbox_datain") begin
        wait(reg_model.mbox_csr_rm.mbox_fn_state_sigs.uc_receive_stage == 1'b0);
        mbox_regs[rand_idx].write(reg_sts, rand_wr_data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(local_apb_user_obj));
        report_reg_sts(reg_sts, mbox_regs[rand_idx].get_name(), local_apb_user_obj);
    end
    else begin
        mbox_regs[rand_idx].write(reg_sts, rand_wr_data, UVM_FRONTDOOR, reg_model.soc_ifc_APB_map, this, .extension(local_apb_user_obj));
        report_reg_sts(reg_sts, mbox_regs[rand_idx].get_name(), local_apb_user_obj);
    end
    if (mainline.status() == process::SUSPENDED) begin
        `uvm_info("SOC_MBOX_HANDLER", $sformatf("Resuming main mailbox flow after random reg access injection"), UVM_HIGH)
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
function uvm_reg_data_t soc_ifc_env_soc_mbox_reg_axs_invalid_handler_sequence::get_rand_wr_data(uvm_reg axs_reg);
    uvm_reg_data_t tmp_data;
    case (axs_reg.get_name()) inside
        "mbox_cmd": begin
            tmp_data = op.cmd;
        end
        "mbox_dlen": begin
            tmp_data = op.dlen; 
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
            msk = (uvm_reg_data_t'(1) << reg_model.mbox_csr_rm.mbox_status.status.get_n_bits()) - 1;
            msk = ~msk;
            std::randomize(tmp_data) with {(tmp_data & msk) == 0;};
        end
        default: begin
            `uvm_fatal("SOC_MBOX_HANDLER", "Bad reg")
        end
    endcase
    return tmp_data;
endfunction
