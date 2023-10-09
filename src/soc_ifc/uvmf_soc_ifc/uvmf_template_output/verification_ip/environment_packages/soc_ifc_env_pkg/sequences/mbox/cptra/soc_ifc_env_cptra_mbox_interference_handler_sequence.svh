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
// DESCRIPTION: Sequence to wait for Mailbox commands (from SoC) and
//              respond/handle the command
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_env_cptra_mbox_interference_handler_sequence extends soc_ifc_env_cptra_mbox_handler_sequence;


  `uvm_object_utils( soc_ifc_env_cptra_mbox_interference_handler_sequence )

  extern virtual task mbox_wait_for_command(output op_sts_e op_sts);
  extern virtual task mbox_wait_and_force_unlock();
  extern virtual task burst_random_reg_accesses(uvm_event stop, ref process this_proc);

  rand uvm_reg_data_t data;
  rand uvm_reg_addr_t mem_offset;
  rand ahb_rnw_e RnW;
  rand byte unsigned xfers;
  rand byte unsigned cycles;

endclass

//==========================================
// Task:        mbox_wait_for_command
// Description: Poll for availability of new
//              mailbox request, indicated by:
//                - mbox_execute = 1
//                - intr status = 1
//==========================================
task soc_ifc_env_cptra_mbox_interference_handler_sequence::mbox_wait_for_command(output op_sts_e op_sts);
    byte ii;

    uvm_reg_data_t data;
    op_sts = CPTRA_TIMEOUT;
    op_active = 1;
    // Wait for notification interrupt indicating command is available
    while (ntf_rsp_count == 0) begin
        uvm_reg_data_t dlen;
        byte unsigned  mem_n_bytes;

        dlen = reg_model.mbox_csr_rm.mbox_dlen.length.get_mirrored_value();
        mem_n_bytes = reg_model.mbox_mem_rm.get_n_bytes();

        if(!this.randomize(xfers) with {xfers inside {[1:20]}; }) begin
            `uvm_error("CPTRA_MBOX_HANDLER", "Failed to randomize memory AHB transfer count in mbox_wait_for_command")
        end
        else begin
            for (ii=0; ii<xfers; ii++) begin: XFER_LOOP
                // Do random access to mailbox memory to trigger arb logic as soc APB actor writes command data
                // NOTE that RnW is forced to AHB_READ when the address falls inside the range of DLEN current value, so that
                // data from the mailbox command is not corrupted.
                // TODO also mix in some reg accesses?
                if(!this.randomize(RnW, mem_offset, data, cycles) with {mem_offset inside {[0:reg_model.mbox_mem_rm.get_size()-1]};
                                                                        cycles inside {[1:200]};
                                                                        if(mem_offset * mem_n_bytes < dlen) RnW == AHB_READ; }) begin
                    `uvm_error("CPTRA_MBOX_HANDLER", "Failed to randomize memory AHB transfer in mbox_wait_for_command")
                end
                else begin
                    if (RnW == AHB_READ) begin
                        reg_model.mbox_mem_rm.read (reg_sts, mem_offset, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
                        report_reg_sts(reg_sts, $sformatf("mbox_mem_rm, offset 0x%x", mem_offset));
                    end
                    else begin
                        reg_model.mbox_mem_rm.write(reg_sts, mem_offset, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
                        report_reg_sts(reg_sts, $sformatf("mbox_mem_rm, offset 0x%x", mem_offset));
                    end
                end
            end
        end
        configuration.soc_ifc_ctrl_agent_config.wait_for_num_clocks(cycles);
        if (ntf_rsp_count != 0 && !cptra_status_agent_rsp_seq.rsp.soc_ifc_notif_intr_pending) begin
            ntf_rsp_count = 0;
        end
    end
    ntf_rsp_count = 0;
    // Clear interrupt
    reg_model.soc_ifc_reg_rm.intr_block_rf_ext.notif_internal_intr_r.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    report_reg_sts(reg_sts, "notif_internal_intr_r");
    if (!data[reg_model.soc_ifc_reg_rm.intr_block_rf_ext.notif_internal_intr_r.notif_cmd_avail_sts.get_lsb_pos()]) begin
        `uvm_error("CPTRA_MBOX_HANDLER", "After receiving notification interrupt, notif_cmd_avail_sts is not set!")
    end
    data &= uvm_reg_data_t'(1) << reg_model.soc_ifc_reg_rm.intr_block_rf_ext.notif_internal_intr_r.notif_cmd_avail_sts.get_lsb_pos();
    reg_model.soc_ifc_reg_rm.intr_block_rf_ext.notif_internal_intr_r.write(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    report_reg_sts(reg_sts, "notif_internal_intr_r");
    op_sts = CPTRA_SUCCESS;
endtask

//==========================================
// Task:        mbox_wait_and_force_unlock
// Description: If enabled, wait for some random amount of time and
//              then do a write to mbox_unlock to forcibly end
//              the current mailbox flow.
//              In the interference sequence, use this routine to
//              inject random reads (to non-mailbox registers)
//              throughout the entire duration of the scenario.
//==========================================
task soc_ifc_env_cptra_mbox_interference_handler_sequence::mbox_wait_and_force_unlock();
    uvm_reg_data_t data;
    mbox_fsm_state_e state;
    process rand_reg_axs_proc;
    uvm_event halt_rand_reg_accesses = new("halt_rand_reg_accesses");

    // Start the unlock proc prior to burst accesses so that the parent
    // sequence knows to wait for AHB traffic to complete before ending the
    // sequence
    unlock_proc_active = 1'b1;
    `uvm_info("CPTRA_MBOX_HANDLER", $sformatf("Starting mbox_wait_and_force_unlock with inject_force_unlock [%d] force_unlock_delay_cycles [%0d]", inject_force_unlock, force_unlock_delay_cycles), UVM_MEDIUM)

    // Wait...
    // If force unlock is disabled, this task will only exit upon detecting
    // an ERROR that requires servicing, whereupon force_unlock will still
    // be set to recover. In either case, only an event resulting in force
    // unlock causes this routine to break
    halt_rand_reg_accesses.reset();
    fork
        begin
            wait(rand_reg_axs_proc != null);
            if (inject_force_unlock) begin
                configuration.soc_ifc_ctrl_agent_config.wait_for_num_clocks(force_unlock_delay_cycles);
                halt_rand_reg_accesses.trigger();
                while(rand_reg_axs_proc.status() != process::WAITING)
                    configuration.soc_ifc_ctrl_agent_config.wait_for_num_clocks(1);
            end
            else begin
                `uvm_info("CPTRA_MBOX_HANDLER", "Not injecting force unlock - burst random reg accesses until any err interrupt is observed", UVM_HIGH)
                forever begin
                    if (err_rsp_count > 0 && cptra_status_agent_rsp_seq.rsp.soc_ifc_err_intr_pending) begin
                        `uvm_info("CPTRA_MBOX_HANDLER", "Received soc_ifc_err_intr, clearing and (if needed) proceeding to mbox_unlock", UVM_MEDIUM)
                        // Pause rand reg accesses while servicing interrupt
                        halt_rand_reg_accesses.trigger();
                        while(rand_reg_axs_proc.status() != process::WAITING)
                            configuration.soc_ifc_ctrl_agent_config.wait_for_num_clocks(1);
                        // Read and clear any error interrupts
                        reg_model.soc_ifc_reg_rm.intr_block_rf_ext.error_internal_intr_r.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
                        report_reg_sts(reg_sts, "error_internal_intr_r");
                        configuration.soc_ifc_ctrl_agent_config.wait_for_num_clocks(10/*TODO rand delays*/);
                        reg_model.soc_ifc_reg_rm.intr_block_rf_ext.error_internal_intr_r.write(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
                        report_reg_sts(reg_sts, "error_internal_intr_r");
                        err_rsp_count = 0;
                        // Next, check if we need to proceed to mbox_unlock step
                        if (!data[reg_model.soc_ifc_reg_rm.intr_block_rf_ext.error_internal_intr_r.error_cmd_fail_sts.get_lsb_pos()]) begin
                            halt_rand_reg_accesses.reset();
                            continue;
                        end
                        reg_model.mbox_csr_rm.mbox_status.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
                        report_reg_sts(reg_sts, "mbox_status");
                        state = mbox_fsm_state_e'(data >> reg_model.mbox_csr_rm.mbox_status.mbox_fsm_ps.get_lsb_pos());
                        // If we're in the error state, the only recovery is by mbox_unlock - proceed to that step
                        if (state == MBOX_ERROR) begin
                            `uvm_info("CPTRA_MBOX_HANDLER", "After servicing soc_ifc_err_intr, proceeding with mbox_unlock", UVM_MEDIUM)
                            break;
                        end
                    end
                    else begin
                        configuration.soc_ifc_ctrl_agent_config.wait_for_num_clocks(10/*TODO rand delays*/);
                    end
                end
            end
            rand_reg_axs_proc.kill();
        end
        burst_random_reg_accesses(halt_rand_reg_accesses, rand_reg_axs_proc);
    join

    // After waiting the requisite number of cycles, check mbox_status.
    // If SOC doesn't currently have the lock, doing a force-unlock has no
    // effect. Poll until soc_has_lock is set.
    // NOTE: Making this check the reg-model mirror instead of actual polling
    //       might be beneficial?
    reg_model.mbox_csr_rm.mbox_status.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    report_reg_sts(reg_sts, "mbox_status");
    while (!data[reg_model.mbox_csr_rm.mbox_status.soc_has_lock.get_lsb_pos()]) begin
        configuration.soc_ifc_ctrl_agent_config.wait_for_num_clocks(50); /* short 500ns between reads */
        reg_model.mbox_csr_rm.mbox_status.read(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
        report_reg_sts(reg_sts, "mbox_status");
    end

    // Write unlock reg
    `uvm_info("CPTRA_MBOX_HANDLER","Executing force unlock of mailbox. CPTRA mbox flow handler will exit after unlock.", UVM_MEDIUM)
    reg_model.mbox_csr_rm.mbox_unlock.write(reg_sts, uvm_reg_data_t'(1) << reg_model.mbox_csr_rm.mbox_unlock.unlock.get_lsb_pos(), UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    report_reg_sts(reg_sts, "mbox_unlock");

    // Clear any interrupts as well, if they weren't cleared before unlock
    data = uvm_reg_data_t'(1) << reg_model.soc_ifc_reg_rm.intr_block_rf_ext.notif_internal_intr_r.notif_cmd_avail_sts.get_lsb_pos();
    `uvm_info("CPTRA_MBOX_HANDLER", "Doing clear notif intr", UVM_LOW)
    reg_model.soc_ifc_reg_rm.intr_block_rf_ext.notif_internal_intr_r.write(reg_sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    report_reg_sts(reg_sts, "notif_internal_intr_r");
    in_report_reg_sts.reset(); /* Clear the trigger from report_reg_sts so that DO_FORCE_UNLOCK can catch the end of a reg-write from ALL_TIME_CONSUMING_TASKS */

    // End
    unlock_proc_active = 1'b0;
    seq_done = 1'b1;
    `uvm_info("CPTRA_MBOX_HANDLER", "Done clearing notif intr", UVM_LOW)
endtask

//==========================================
// Task:        burst_random_reg_accesses
// Description: Continuously issue bursts (of random length)
//              of bus reads to randomly selected SOC_IFC registers,
//              intermixed with random delays, until the input event
//              is triggered.
//==========================================
task soc_ifc_env_cptra_mbox_interference_handler_sequence::burst_random_reg_accesses(uvm_event stop, ref process this_proc);
    int unsigned burst_length;
    int unsigned delay_cycles;

    uvm_reg regs[$];
    uvm_reg blocklist[];
    int     del_idx[$];

    byte unsigned  ii;
    int            reg_select;
    ahb_rnw_e      rand_RnW;
    uvm_reg_data_t rand_data;
    uvm_status_e   rand_sts;

    this_proc = process::self();
    reg_model.soc_ifc_AHB_map.get_registers(regs, UVM_HIER);

    // Registers we won't randomly access due to side-effects
    // Don't include any mailbox registers
    blocklist = '{reg_model.mbox_csr_rm.mbox_lock,
                  reg_model.mbox_csr_rm.mbox_user,
                  reg_model.mbox_csr_rm.mbox_cmd,
                  reg_model.mbox_csr_rm.mbox_dlen,
                  reg_model.mbox_csr_rm.mbox_datain,
                  reg_model.mbox_csr_rm.mbox_dataout,
                  reg_model.mbox_csr_rm.mbox_execute,
                  reg_model.mbox_csr_rm.mbox_status,
                  reg_model.mbox_csr_rm.mbox_unlock,
                  reg_model.sha512_acc_csr_rm.LOCK};
    foreach (blocklist[idx]) begin
        del_idx = regs.find_first_index(found_reg) with (found_reg == blocklist[idx]);
        regs.delete(del_idx.pop_front());
    end

    forever begin
        if (!std::randomize(burst_length, delay_cycles) with {burst_length inside {[1:100]};
                                                              delay_cycles inside {[1:500]};})
            `uvm_error("CPTRA_MBOX_HANDLER", "Failed to randomize burst_length and delay_cycles")
        else begin
            `uvm_info("CPTRA_MBOX_HANDLER", $sformatf("Beginning random AHB burst with delay_cycles [%d] burst_length [%d]", delay_cycles, burst_length), UVM_HIGH)
            for (ii=0; ii<burst_length; ii++) begin: XFER_LOOP
                // Do random access to soc_ifc to trigger arb logic as cptra sequence processes
                // incoming mailbox command
                // TODO also mix in some reg writes?
                if(!std::randomize(rand_RnW, reg_select, rand_data) with {rand_RnW == AHB_READ;
                                                                          reg_select < regs.size(); }) begin
                    `uvm_error("CPTRA_MBOX_HANDLER", "Failed to randomize reg AHB transfer in burst_random_reg_accesses")
                end
                else begin
                    `uvm_info("CPTRA_MBOX_HANDLER", $sformatf("Doing random AHB access of type %p to %s, which has is_busy(): %d", rand_RnW, regs[reg_select].get_name(), regs[reg_select].is_busy()), UVM_DEBUG)
                    if (rand_RnW == AHB_READ) regs[reg_select].read (rand_sts, rand_data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
                    else                      regs[reg_select].write(rand_sts, rand_data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
                    report_reg_sts(rand_sts, regs[reg_select].get_name());
                end
                if (stop.is_on()) stop.wait_off();
            end
        end
        for (ii=delay_cycles; ii > 0; ii--) begin
            configuration.soc_ifc_ctrl_agent_config.wait_for_num_clocks(1);
            if (stop.is_on()) stop.wait_off();
        end
    end
endtask
