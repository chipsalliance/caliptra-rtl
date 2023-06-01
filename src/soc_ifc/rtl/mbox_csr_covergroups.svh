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

`ifndef MBOX_CSR_COVERGROUPS
    `define MBOX_CSR_COVERGROUPS
    
    /*----------------------- MBOX_CSR__MBOX_LOCK COVERGROUPS -----------------------*/
    covergroup mbox_csr__mbox_lock_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup mbox_csr__mbox_lock_fld_cg with function sample(
    input bit [1-1:0] lock
    );
        option.per_instance = 1;
        lock_cp : coverpoint lock;

    endgroup

    /*----------------------- MBOX_CSR__MBOX_USER COVERGROUPS -----------------------*/
    covergroup mbox_csr__mbox_user_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup mbox_csr__mbox_user_fld_cg with function sample(
    input bit [32-1:0] user
    );
        option.per_instance = 1;
        user_cp : coverpoint user;

    endgroup

    /*----------------------- MBOX_CSR__MBOX_CMD COVERGROUPS -----------------------*/
    covergroup mbox_csr__mbox_cmd_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup mbox_csr__mbox_cmd_fld_cg with function sample(
    input bit [32-1:0] command
    );
        option.per_instance = 1;
        command_cp : coverpoint command;

    endgroup

    /*----------------------- MBOX_CSR__MBOX_DLEN COVERGROUPS -----------------------*/
    covergroup mbox_csr__mbox_dlen_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup mbox_csr__mbox_dlen_fld_cg with function sample(
    input bit [32-1:0] length
    );
        option.per_instance = 1;
        length_cp : coverpoint length;

    endgroup

    /*----------------------- MBOX_CSR__MBOX_DATAIN COVERGROUPS -----------------------*/
    covergroup mbox_csr__mbox_datain_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup mbox_csr__mbox_datain_fld_cg with function sample(
    input bit [32-1:0] datain
    );
        option.per_instance = 1;
        datain_cp : coverpoint datain;

    endgroup

    /*----------------------- MBOX_CSR__MBOX_DATAOUT COVERGROUPS -----------------------*/
    covergroup mbox_csr__mbox_dataout_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup mbox_csr__mbox_dataout_fld_cg with function sample(
    input bit [32-1:0] dataout
    );
        option.per_instance = 1;
        dataout_cp : coverpoint dataout;

    endgroup

    /*----------------------- MBOX_CSR__MBOX_EXECUTE COVERGROUPS -----------------------*/
    covergroup mbox_csr__mbox_execute_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup mbox_csr__mbox_execute_fld_cg with function sample(
    input bit [1-1:0] execute
    );
        option.per_instance = 1;
        execute_cp : coverpoint execute;

    endgroup

    /*----------------------- MBOX_CSR__MBOX_STATUS_ECC_DOUBLE_ERROR_38CEC4B0_ECC_SINGLE_ERROR_9C62B760 COVERGROUPS -----------------------*/
    covergroup mbox_csr__mbox_status_ecc_double_error_38cec4b0_ecc_single_error_9c62b760_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup mbox_csr__mbox_status_ecc_double_error_38cec4b0_ecc_single_error_9c62b760_fld_cg with function sample(
    input bit [4-1:0] status,
    input bit [1-1:0] ecc_single_error,
    input bit [1-1:0] ecc_double_error,
    input bit [3-1:0] mbox_fsm_ps,
    input bit [1-1:0] soc_has_lock
    );
        option.per_instance = 1;
        status_cp : coverpoint status;
        ecc_single_error_cp : coverpoint ecc_single_error;
        ecc_double_error_cp : coverpoint ecc_double_error;
        mbox_fsm_ps_cp : coverpoint mbox_fsm_ps;
        soc_has_lock_cp : coverpoint soc_has_lock;

    endgroup

    /*----------------------- MBOX_CSR__MBOX_UNLOCK COVERGROUPS -----------------------*/
    covergroup mbox_csr__mbox_unlock_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup mbox_csr__mbox_unlock_fld_cg with function sample(
    input bit [1-1:0] unlock
    );
        option.per_instance = 1;
        unlock_cp : coverpoint unlock;

    endgroup

`endif