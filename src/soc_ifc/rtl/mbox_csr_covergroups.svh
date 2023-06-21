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

    import soc_ifc_pkg::*;
    
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
        lock_edge_cp : coverpoint lock {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

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
        user_cp : coverpoint user {
            bins zero_val = {32'h0};
            bins rand_val[64] = {[1:32'hFFFF_FFFE]};
            bins ones_val = {{32{1'b1}}};
            wildcard bins set = (0 => 32'h????_????);
            wildcard bins clr = (32'h????_???? => 0);
        }

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
        command_cp : coverpoint command {
            bins zero_val = {32'h0};
            bins rand_val[64] = {[1:32'hFFFF_FFFE]};
            bins ones_val = {{32{1'b1}}};
            wildcard bins set = (0 => 32'h????_????);
            wildcard bins clr = (32'h????_???? => 0);
        }

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
        // TODO These need a cross with lock/execute/fsm state to properly get coverage...
        length_cp : coverpoint length {
            bins zero_val = {32'h0};
            bins tiny_val = {[1:3]};
            bins small_val = {[4:15]};
            bins medium_val = {[16:4095]};
            bins large_val = {[4096:32768]};
            bins legal_word_aligned_val  = {[1:32'h8000]} with (~|item[0]);
            bins legal_dword_aligned_val = {[1:32'h8000]} with (~|item[1:0]);
            bins legal_qword_aligned_val = {[1:32'h8000]} with (~|item[2:0]);
            bins legal_oword_aligned_val = {[1:32'h8000]} with (~|item[3:0]);
            bins oversize_val = {[32769:32'hFFFF_FFFE]}; /* Value larger than mailbox size */
            bins ones_val = {{32{1'b1}}};
            wildcard bins set = (0 => 32'h????_????);
            wildcard bins clr = (32'h????_???? => 0);
        }

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
        datain_cp : coverpoint datain {
            bins zero_val = {32'h0};
            bins rand_val[64] = {[1:32'hFFFF_FFFE]};
            bins ones_val = {{32{1'b1}}};
            wildcard bins set = (0 => 32'h????_????);
            wildcard bins clr = (32'h????_???? => 0);
        }

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
        dataout_cp : coverpoint dataout {
            bins zero_val = {32'h0};
            bins rand_val[64] = {[1:32'hFFFF_FFFE]};
            bins ones_val = {{32{1'b1}}};
            wildcard bins set = (0 => 32'h????_????);
            wildcard bins clr = (32'h????_???? => 0);
        }

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
        execute_edge_cp : coverpoint execute {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

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
        mbox_fsm_ps_cp : coverpoint mbox_fsm_ps {
            bins MBOX_IDLE                                    = {mbox_fsm_state_e'(MBOX_IDLE        )};
            bins MBOX_RDY_FOR_CMD                             = {mbox_fsm_state_e'(MBOX_RDY_FOR_CMD )};
            bins MBOX_RDY_FOR_DLEN                            = {mbox_fsm_state_e'(MBOX_RDY_FOR_DLEN)};
            bins MBOX_RDY_FOR_DATA                            = {mbox_fsm_state_e'(MBOX_RDY_FOR_DATA)};
            bins MBOX_EXECUTE_UC                              = {mbox_fsm_state_e'(MBOX_EXECUTE_UC  )};
            bins MBOX_EXECUTE_SOC                             = {mbox_fsm_state_e'(MBOX_EXECUTE_SOC )};
            bins MBOX_ERROR                                   = {mbox_fsm_state_e'(MBOX_ERROR       )};
        }
        mbox_fsm_ps_edge_cp : coverpoint mbox_fsm_ps {
            bins TRANSITION_IDLE_RDY_FOR_CMD                  = (mbox_fsm_state_e'(MBOX_IDLE)         => mbox_fsm_state_e'(MBOX_RDY_FOR_CMD));
            bins TRANSITION_RDY_FOR_CMD_RDY_FOR_DLEN          = (mbox_fsm_state_e'(MBOX_RDY_FOR_CMD)  => mbox_fsm_state_e'(MBOX_RDY_FOR_DLEN));
            bins TRANSITION_RDY_FOR_DLEN_RDY_FOR_DATA         = (mbox_fsm_state_e'(MBOX_RDY_FOR_DLEN) => mbox_fsm_state_e'(MBOX_RDY_FOR_DATA));
            bins TRANSITION_RDY_FOR_DATA_EXECUTE_UC           = (mbox_fsm_state_e'(MBOX_RDY_FOR_DATA) => mbox_fsm_state_e'(MBOX_EXECUTE_UC));
            bins TRANSITION_RDY_FOR_DATA_EXECUTE_SOC          = (mbox_fsm_state_e'(MBOX_RDY_FOR_DATA) => mbox_fsm_state_e'(MBOX_EXECUTE_SOC));
            bins TRANSITION_EXECUTE_UC_EXECUTE_SOC            = (mbox_fsm_state_e'(MBOX_EXECUTE_UC)   => mbox_fsm_state_e'(MBOX_EXECUTE_SOC));
            bins TRANSITION_EXECUTE_SOC_EXECUTE_UC            = (mbox_fsm_state_e'(MBOX_EXECUTE_SOC)  => mbox_fsm_state_e'(MBOX_EXECUTE_UC));
            bins TRANSITION_EXECUTE_UC_IDLE                   = (mbox_fsm_state_e'(MBOX_EXECUTE_UC)   => mbox_fsm_state_e'(MBOX_IDLE));
            bins TRANSITION_EXECUTE_SOC_IDLE                  = (mbox_fsm_state_e'(MBOX_EXECUTE_SOC)  => mbox_fsm_state_e'(MBOX_IDLE));
            bins TRANSITION_RDY_FOR_CMD_ERROR                 = (mbox_fsm_state_e'(MBOX_RDY_FOR_CMD)  => mbox_fsm_state_e'(MBOX_ERROR));
            bins TRANSITION_RDY_FOR_DLEN_ERROR                = (mbox_fsm_state_e'(MBOX_RDY_FOR_DLEN) => mbox_fsm_state_e'(MBOX_ERROR));
            bins TRANSITION_RDY_FOR_DATA_ERROR                = (mbox_fsm_state_e'(MBOX_RDY_FOR_DATA) => mbox_fsm_state_e'(MBOX_ERROR));
            bins TRANSITION_EXECUTE_UC_ERROR                  = (mbox_fsm_state_e'(MBOX_EXECUTE_UC)   => mbox_fsm_state_e'(MBOX_ERROR));
            bins TRANSITION_EXECUTE_SOC_ERROR                 = (mbox_fsm_state_e'(MBOX_EXECUTE_SOC)  => mbox_fsm_state_e'(MBOX_ERROR));
            bins TRANSITION_ERROR_IDLE                        = (mbox_fsm_state_e'(MBOX_ERROR)        => mbox_fsm_state_e'(MBOX_IDLE));
//            illegal_bins TRANSITION_IDLE_ERROR                = (mbox_fsm_state_e'(MBOX_IDLE)         => mbox_fsm_state_e'(MBOX_ERROR));
//            illegal_bins TRANSITION_IDLE_RDY_FOR_DLEN         = (mbox_fsm_state_e'(MBOX_IDLE)         => mbox_fsm_state_e'(MBOX_RDY_FOR_DLEN));
//            illegal_bins TRANSITION_IDLE_RDY_FOR_DATA         = (mbox_fsm_state_e'(MBOX_IDLE)         => mbox_fsm_state_e'(MBOX_RDY_FOR_DATA));
//            illegal_bins TRANSITION_IDLE_EXECUTE_UC           = (mbox_fsm_state_e'(MBOX_IDLE)         => mbox_fsm_state_e'(MBOX_EXECUTE_UC));
//            illegal_bins TRANSITION_IDLE_EXECUTE_SOC          = (mbox_fsm_state_e'(MBOX_IDLE)         => mbox_fsm_state_e'(MBOX_EXECUTE_SOC));
//            illegal_bins TRANSITION_RDY_FOR_CMD_RDY_FOR_DATA  = (mbox_fsm_state_e'(MBOX_RDY_FOR_CMD)  => mbox_fsm_state_e'(MBOX_RDY_FOR_DATA));
//            illegal_bins TRANSITION_RDY_FOR_CMD_EXECUTE_UC    = (mbox_fsm_state_e'(MBOX_RDY_FOR_CMD)  => mbox_fsm_state_e'(MBOX_EXECUTE_UC));
//            illegal_bins TRANSITION_RDY_FOR_CMD_EXECUTE_SOC   = (mbox_fsm_state_e'(MBOX_RDY_FOR_CMD)  => mbox_fsm_state_e'(MBOX_EXECUTE_SOC));
//            illegal_bins TRANSITION_RDY_FOR_DLEN_RDY_FOR_CMD  = (mbox_fsm_state_e'(MBOX_RDY_FOR_DLEN) => mbox_fsm_state_e'(MBOX_RDY_FOR_CMD));
//            illegal_bins TRANSITION_RDY_FOR_DLEN_EXECUTE_UC   = (mbox_fsm_state_e'(MBOX_RDY_FOR_DLEN) => mbox_fsm_state_e'(MBOX_EXECUTE_UC));
//            illegal_bins TRANSITION_RDY_FOR_DLEN_EXECUTE_SOC  = (mbox_fsm_state_e'(MBOX_RDY_FOR_DLEN) => mbox_fsm_state_e'(MBOX_EXECUTE_SOC));
//            illegal_bins TRANSITION_RDY_FOR_DATA_RDY_FOR_CMD  = (mbox_fsm_state_e'(MBOX_RDY_FOR_DATA) => mbox_fsm_state_e'(MBOX_RDY_FOR_CMD));
//            illegal_bins TRANSITION_RDY_FOR_DATA_RDY_FOR_DLEN = (mbox_fsm_state_e'(MBOX_RDY_FOR_DATA) => mbox_fsm_state_e'(MBOX_RDY_FOR_DLEN));
//            illegal_bins TRANSITION_EXECUTE_UC_RDY_FOR_CMD    = (mbox_fsm_state_e'(MBOX_EXECUTE_UC)   => mbox_fsm_state_e'(MBOX_RDY_FOR_CMD));
//            illegal_bins TRANSITION_EXECUTE_UC_RDY_FOR_DLEN   = (mbox_fsm_state_e'(MBOX_EXECUTE_UC)   => mbox_fsm_state_e'(MBOX_RDY_FOR_DLEN));
//            illegal_bins TRANSITION_EXECUTE_UC_RDY_FOR_DATA   = (mbox_fsm_state_e'(MBOX_EXECUTE_UC)   => mbox_fsm_state_e'(MBOX_RDY_FOR_DATA));
//            illegal_bins TRANSITION_EXECUTE_SOC_RDY_FOR_CMD   = (mbox_fsm_state_e'(MBOX_EXECUTE_SOC)  => mbox_fsm_state_e'(MBOX_RDY_FOR_CMD));
//            illegal_bins TRANSITION_EXECUTE_SOC_RDY_FOR_DLEN  = (mbox_fsm_state_e'(MBOX_EXECUTE_SOC)  => mbox_fsm_state_e'(MBOX_RDY_FOR_DLEN));
//            illegal_bins TRANSITION_EXECUTE_SOC_RDY_FOR_DATA  = (mbox_fsm_state_e'(MBOX_EXECUTE_SOC)  => mbox_fsm_state_e'(MBOX_RDY_FOR_DATA));
//            illegal_bins TRANSITION_ERROR_RDY_FOR_CMD         = (mbox_fsm_state_e'(MBOX_ERROR)        => mbox_fsm_state_e'(MBOX_RDY_FOR_CMD));
//            illegal_bins TRANSITION_ERROR_RDY_FOR_DLEN        = (mbox_fsm_state_e'(MBOX_ERROR)        => mbox_fsm_state_e'(MBOX_RDY_FOR_DLEN));
//            illegal_bins TRANSITION_ERROR_RDY_FOR_DATA        = (mbox_fsm_state_e'(MBOX_ERROR)        => mbox_fsm_state_e'(MBOX_RDY_FOR_DATA));
//            illegal_bins TRANSITION_ERROR_EXECUTE_UC          = (mbox_fsm_state_e'(MBOX_ERROR)        => mbox_fsm_state_e'(MBOX_EXECUTE_UC));
//            illegal_bins TRANSITION_ERROR_EXECUTE_SOC         = (mbox_fsm_state_e'(MBOX_ERROR)        => mbox_fsm_state_e'(MBOX_EXECUTE_SOC));
        }
        soc_has_lock_cp : coverpoint soc_has_lock;
        status_edge_cp : coverpoint status {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }
        ecc_single_error_edge_cp : coverpoint ecc_single_error {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }
        ecc_double_error_edge_cp : coverpoint ecc_double_error {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }
        soc_has_lock_edge_cp : coverpoint soc_has_lock {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

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
        unlock_edge_cp : coverpoint unlock {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup

`endif
