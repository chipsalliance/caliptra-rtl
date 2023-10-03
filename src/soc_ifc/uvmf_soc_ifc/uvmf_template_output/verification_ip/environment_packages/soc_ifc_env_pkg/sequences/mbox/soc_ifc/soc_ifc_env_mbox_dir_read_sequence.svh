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
class soc_ifc_env_mbox_dir_read_sequence extends soc_ifc_env_mbox_sequence_base;

  `uvm_object_utils( soc_ifc_env_mbox_dir_read_sequence )

  // Constrain command to undefined opcode
  constraint mbox_cmd_dir_read_c { (mbox_op_rand.cmd.cmd_e == MBOX_CMD_DIR_RD); }

  // Constrain size to something reasonable
  constraint mbox_dlen_max_c { mbox_op_rand.dlen <= 2000; }

  function new(string name = "" );
    super.new(name);
  endfunction

endclass
