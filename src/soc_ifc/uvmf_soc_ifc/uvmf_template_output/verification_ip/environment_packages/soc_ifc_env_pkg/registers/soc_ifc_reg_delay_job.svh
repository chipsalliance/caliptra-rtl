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
// Description:
//   A delay job is a prediction task that should not be executed
//   immediately. In order to accurately model the expected DUT
//   behavior, some prediction tasks should not run until some amount
//   of time has transpired. I.e., register write side-effects
//   may not be latched to flip-flop until after some time.
//   This job object defines what those tasks are, and allows them to
//   be executed from soc_ifc_predictor after waiting.
//----------------------------------------------------------------------

class soc_ifc_reg_delay_job extends uvm_object;

    `uvm_object_utils( soc_ifc_reg_delay_job )

    int unsigned delay_cycles = 0;

    virtual function void set_delay_cycles(int unsigned value);
        this.delay_cycles = value;
    endfunction

    virtual function int unsigned get_delay_cycles();
        return this.delay_cycles;
    endfunction

    virtual task do_job();
        `uvm_error("SOC_IFC_REG_DELAY_JOB", "FIXME: Extend soc_ifc_reg_delay_job and define job functionality before invoking!")
    endtask

endclass
