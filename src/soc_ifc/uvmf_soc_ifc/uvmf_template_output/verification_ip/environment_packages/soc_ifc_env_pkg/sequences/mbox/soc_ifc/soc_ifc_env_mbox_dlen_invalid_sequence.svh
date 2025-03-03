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
class soc_ifc_env_mbox_dlen_invalid_sequence extends soc_ifc_env_mbox_sequence_base;

  `uvm_object_utils( soc_ifc_env_mbox_dlen_invalid_sequence )

  // Constrain command to undefined opcode
  constraint mbox_cmd_undef_c { !(mbox_op_rand.cmd.cmd_s inside {defined_cmds}); }

  // Constrain size to greater than 128KiB to test a command with invalid
  // size (larger than mailbox).
  // But keep a reasonable-ish size so the test can run to completion
  constraint mbox_dlen_max_c { mbox_op_rand.dlen <= 4*CPTRA_MBOX_SIZE_BYTES; }
  constraint mbox_dlen_min_c { mbox_op_rand.dlen >    CPTRA_MBOX_SIZE_BYTES; }
  // Response data is only non-zero if a response is requested, and also must
  // be large enough to exceed the mailbox capacity
  constraint mbox_resp_dlen_c {                                      mbox_resp_expected_dlen <= 4*CPTRA_MBOX_SIZE_BYTES;
                                !mbox_op_rand.cmd.cmd_s.resp_reqd -> mbox_resp_expected_dlen == 0;
                                 mbox_op_rand.cmd.cmd_s.resp_reqd -> mbox_resp_expected_dlen >    CPTRA_MBOX_SIZE_BYTES; }

  function new(string name = "" );
    super.new(name);
    this.mbox_sts_exp_error = 1;
    this.mbox_sts_exp_error_type = EXP_ERR_RSP_DLEN;
  endfunction

endclass
