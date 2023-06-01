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

`ifndef PV_REG_COVERGROUPS
    `define PV_REG_COVERGROUPS
    
    /*----------------------- PV_REG__PVCTRL COVERGROUPS -----------------------*/
    covergroup pv_reg__pvCtrl_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup pv_reg__pvCtrl_fld_cg with function sample(
    input bit [1-1:0] lock,
    input bit [1-1:0] clear,
    input bit [1-1:0] rsvd0,
    input bit [5-1:0] rsvd1
    );
        option.per_instance = 1;
        lock_cp : coverpoint lock;
        clear_cp : coverpoint clear;
        rsvd0_cp : coverpoint rsvd0;
        rsvd1_cp : coverpoint rsvd1;

    endgroup

    /*----------------------- PV_REG__PCRREG COVERGROUPS -----------------------*/
    covergroup pv_reg__pcrReg_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup pv_reg__pcrReg_fld_cg with function sample(
    input bit [32-1:0] data
    );
        option.per_instance = 1;
        data_cp : coverpoint data;

    endgroup

`endif