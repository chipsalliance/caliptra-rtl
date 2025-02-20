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
// DESCRIPTION: Extended from mbox sequence base to exercise AXI_USER filtering.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_env_mbox_rand_axi_user_sequence extends soc_ifc_env_mbox_sequence_base;

  `uvm_object_utils( soc_ifc_env_mbox_rand_axi_user_sequence )

  extern virtual function void              set_axi_user_prob_vals();

  // Force the lock check when deliberately testing AXI accesses with invalid AXI_USER values
  constraint axi_reg_check_c {do_axi_lock_check == 1;}
  constraint retry_failed_reg_c {retry_failed_reg_axs == 1'b1;}

  // Constrain command to undefined opcode
  constraint mbox_cmd_undef_c { !(mbox_op_rand.cmd.cmd_s inside {defined_cmds}); }

  function new(string name = "" );
    super.new(name);
    this.mbox_sts_exp_error = 1;
    this.mbox_sts_exp_error_type = EXP_ERR_PROT;
  endfunction

endclass

function void soc_ifc_env_mbox_rand_axi_user_sequence::set_axi_user_prob_vals();
  // ============ OVERRIDES for rand probability members ============
  // Make it slightly more likely to randomly generate a valid AXI_USER override
  // for earlier calls, so the first occurrence of invalid AXI_USER is later
  // on (or, very rarely, never happens).
  // We want to stimulate the bad-actor scenario, but at varying points
  // throughout the sequence.
  // It is occasionally interesting to let invalid AXI_USER be generated on the
  // first attempt though.
  this.AXI_USER_PROB_LOCK    = 350;
  this.AXI_USER_PROB_CMD     = AXI_USER_PROB_LOCK;
  // Wildly more likely to generate a valid AXI_USER, since we do so many accesses
  // against datain it is almost certain at _some_ point to be invalid
  this.AXI_USER_PROB_DATAIN  = 25;
  this.AXI_USER_PROB_EXECUTE = AXI_USER_PROB_LOCK;
  // More likely to generate a valid AXI_USER, since we do so many accesses
  // against mbox_status while polling
  this.AXI_USER_PROB_STATUS  = 150;
  // Wildly more likely to generate a valid AXI_USER, since we do so many accesses
  // against dataout it is almost certain at _some_ point to be invalid
  this.AXI_USER_PROB_DATAOUT = AXI_USER_PROB_DATAIN;
endfunction
