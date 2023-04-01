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
// DESCRIPTION: Extended from mbox sequence base to exercise PAUSER filtering.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_env_mbox_rand_pauser_sequence extends soc_ifc_env_mbox_sequence_base;

  `uvm_object_utils( soc_ifc_env_mbox_rand_pauser_sequence )

  extern virtual function void              set_pauser_prob_vals();

  // Force the lock check when deliberately testing APB accesses with invalid PAUSER values
  constraint apb_reg_check_c {do_apb_lock_check == 1;}
  constraint retry_failed_reg_c {retry_failed_reg_axs == 1'b1;}

  function new(string name = "" );
    super.new(name);
  endfunction

endclass

function void soc_ifc_env_mbox_rand_pauser_sequence::set_pauser_prob_vals();
  // ============ OVERRIDES for rand probability members ============
  // Slightly more likely to randomly generate a valid PAUSER override
  // for earlier calls, so the first occurrence of invalid PAUSER is later
  // on (or, very rarely, never happens).
  // We want to stimulate the bad-actor scenario, but at varying points
  // throughout the sequence.
  // It is occasionally interesting to let invalid PAUSER be generated on the
  // first attempt though.
  this.PAUSER_PROB_LOCK    = 250;
  this.PAUSER_PROB_CMD     = PAUSER_PROB_LOCK;
  // Wildly more likely to generate a valid PAUSER, since we do so many accesses
  // against datain it is almost certain at _some_ point to be invalid
  this.PAUSER_PROB_DATAIN  = 5;
  this.PAUSER_PROB_EXECUTE = PAUSER_PROB_LOCK;
  // More likely to generate a valid PAUSER, since we do so many accesses
  // against mbox_status while polling
  this.PAUSER_PROB_STATUS  = 150;
  // Wildly more likely to generate a valid PAUSER, since we do so many accesses
  // against dataout it is almost certain at _some_ point to be invalid
  this.PAUSER_PROB_DATAOUT = PAUSER_PROB_DATAIN;
endfunction
