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
// DESCRIPTION: Extended from mbox sequence base to exercise double-bit flips
//              on the mailbox SRAM.
//              Desired result is to observe the internal error interrupt and
//              assertion of the cptra_error_non_fatal pin.
//              After responding to the error by clearing the interrupts, the
//              mailbox flow will be terminated.
// NOTES:
//   - SOC may respond with any of:
//     1. Wait for uC to clear the internal interrupt / reset the mbox
//        FSM (or proceed with the cmd as normal), then proceed to
//        clear the cptra_error_non_fatal pin
//     2. Clear the cptra_error_non_fatal pin immediately, issue a new command
//        (still requires waiting for LOCK)
//     3. Reset Caliptra
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_env_mbox_sram_double_bit_flip_sequence extends soc_ifc_env_mbox_sequence_base;

  `uvm_object_utils( soc_ifc_env_mbox_sram_double_bit_flip_sequence )

  // Constrain command to undefined opcode
  constraint mbox_cmd_undef_c { !(mbox_op_rand.cmd.cmd_s inside {defined_cmds}); }

  function new(string name = "" );
    super.new(name);
    this.mbox_sts_exp_error = 1;
  endfunction

  //==========================================
  // Task:        body
  // Description: Implement main functionality for
  //              SOC-side transmission of mailbox request.
  //              Override default body to inject double
  //              bit flips into the Mailbox SRAM at random
  //              throughout a normal test flow.
  //==========================================
  virtual task body();

    op_sts_e op_sts;
    process mbox_flow_proc;
    process err_proc;

    sts_rsp_count = 0;

    fork
        forever begin
            @(soc_ifc_status_agent_rsp_seq.new_rsp) sts_rsp_count++;
        end
    join_none

    `uvm_info("MBOX_SEQ", $sformatf("Initiating command sequence to mailbox with cmd: [%p] dlen: [%p] resp_dlen: [%p]", mbox_op_rand.cmd.cmd_e, mbox_op_rand.dlen, mbox_resp_expected_dlen), UVM_MEDIUM)

    fork
        begin: MBOX_FLOW
            mbox_setup();               if (rand_delay_en) do_rand_delay(1, step_delay);
            mbox_acquire_lock(op_sts);  if (rand_delay_en) do_rand_delay(1, step_delay);
            mbox_flow_proc = process::self();
            mbox_set_cmd(mbox_op_rand); if (rand_delay_en) do_rand_delay(1, step_delay);
            mbox_push_datain();         if (rand_delay_en) do_rand_delay(1, step_delay);
            mbox_execute();             if (rand_delay_en) do_rand_delay(1, step_delay);
            mbox_poll_status();         if (rand_delay_en) do_rand_delay(1, step_delay);
            if (err_proc.status() == process::WAITING) begin
                `uvm_info("MBOX_SEQ", "Ending SRAM bit flip injection thread before it has completed!", UVM_LOW)
                disable ERR_INJECT_FLOW;
            end
            else if (err_proc.status() != process::FINISHED) begin
                `uvm_error("MBOX_SEQ", $sformatf("Error process is in unexpected state %s!", err_proc.status().name()))
            end
        end
        begin: ERR_INJECT_FLOW
            err_proc = process::self();
            wait(mbox_flow_proc != null);
            // Wait and do the SRAM error injection at some random point in the sequence
            do_rand_delay(1, DLY_CUSTOM);
            `uvm_info("MBOX_SEQ", "Triggering Mailbox SRAM double-bit flip injection", UVM_LOW)
            set_mbox_sram_ecc_double_error_injection();
        end
    join
    mbox_clr_execute();         if (rand_delay_en) do_rand_delay(1, step_delay);
    mbox_teardown();

  endtask

endclass
