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

`ifndef KV_REG_COVERGROUPS
    `define KV_REG_COVERGROUPS
    
    /*----------------------- KV_REG__KVCTRL COVERGROUPS -----------------------*/
    covergroup kv_reg__kvCtrl_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup kv_reg__kvCtrl_fld_cg with function sample(
    input bit [1-1:0] lock_wr,
    input bit [1-1:0] lock_use,
    input bit [1-1:0] clear,
    input bit [1-1:0] rsvd0,
    input bit [5-1:0] rsvd1,
    input bit [8-1:0] dest_valid,
    input bit [4-1:0] last_dword
    );
        option.per_instance = 1;
        lock_wr_cp : coverpoint lock_wr;
        lock_use_cp : coverpoint lock_use;
        clear_cp : coverpoint clear;
        rsvd0_cp : coverpoint rsvd0;
        rsvd1_cp : coverpoint rsvd1;
        dest_valid_cp : coverpoint dest_valid;
        last_dword_cp : coverpoint last_dword;

    endgroup

    /*----------------------- KV_REG__KEYREG COVERGROUPS -----------------------*/
    covergroup kv_reg__keyReg_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup kv_reg__keyReg_fld_cg with function sample(
    input bit [32-1:0] data
    );
        option.per_instance = 1;
        data_cp : coverpoint data;

    endgroup

    /*----------------------- KV_REG__CLEAR_SECRETS COVERGROUPS -----------------------*/
    covergroup kv_reg__CLEAR_SECRETS_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup kv_reg__CLEAR_SECRETS_fld_cg with function sample(
    input bit [1-1:0] wr_debug_values,
    input bit [1-1:0] sel_debug_value
    );
        option.per_instance = 1;
        wr_debug_values_cp : coverpoint wr_debug_values;
        sel_debug_value_cp : coverpoint sel_debug_value;

    endgroup

`endif