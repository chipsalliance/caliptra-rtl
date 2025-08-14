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
//
`ifndef CALIPTRA_TOP_REG_FIELD_DEFINES_HEADER
`define CALIPTRA_TOP_REG_FIELD_DEFINES_HEADER


`ifndef MBOX_CSR_MBOX_LOCK
`define MBOX_CSR_MBOX_LOCK                                                                          (32'h0)
`define MBOX_CSR_MBOX_LOCK_LOCK_LOW                                                                 (0)
`define MBOX_CSR_MBOX_LOCK_LOCK_MASK                                                                (32'h1)
`endif
`ifndef MBOX_CSR_MBOX_USER
`define MBOX_CSR_MBOX_USER                                                                          (32'h4)
`endif
`ifndef MBOX_CSR_MBOX_CMD
`define MBOX_CSR_MBOX_CMD                                                                           (32'h8)
`endif
`ifndef MBOX_CSR_MBOX_DLEN
`define MBOX_CSR_MBOX_DLEN                                                                          (32'hc)
`endif
`ifndef MBOX_CSR_MBOX_DATAIN
`define MBOX_CSR_MBOX_DATAIN                                                                        (32'h10)
`endif
`ifndef MBOX_CSR_MBOX_DATAOUT
`define MBOX_CSR_MBOX_DATAOUT                                                                       (32'h14)
`endif
`ifndef MBOX_CSR_MBOX_EXECUTE
`define MBOX_CSR_MBOX_EXECUTE                                                                       (32'h18)
`define MBOX_CSR_MBOX_EXECUTE_EXECUTE_LOW                                                           (0)
`define MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK                                                          (32'h1)
`endif
`ifndef MBOX_CSR_MBOX_STATUS
`define MBOX_CSR_MBOX_STATUS                                                                        (32'h1c)
`define MBOX_CSR_MBOX_STATUS_STATUS_LOW                                                             (0)
`define MBOX_CSR_MBOX_STATUS_STATUS_MASK                                                            (32'hf)
`define MBOX_CSR_MBOX_STATUS_ECC_SINGLE_ERROR_LOW                                                   (4)
`define MBOX_CSR_MBOX_STATUS_ECC_SINGLE_ERROR_MASK                                                  (32'h10)
`define MBOX_CSR_MBOX_STATUS_ECC_DOUBLE_ERROR_LOW                                                   (5)
`define MBOX_CSR_MBOX_STATUS_ECC_DOUBLE_ERROR_MASK                                                  (32'h20)
`define MBOX_CSR_MBOX_STATUS_MBOX_FSM_PS_LOW                                                        (6)
`define MBOX_CSR_MBOX_STATUS_MBOX_FSM_PS_MASK                                                       (32'h1c0)
`define MBOX_CSR_MBOX_STATUS_SOC_HAS_LOCK_LOW                                                       (9)
`define MBOX_CSR_MBOX_STATUS_SOC_HAS_LOCK_MASK                                                      (32'h200)
`define MBOX_CSR_MBOX_STATUS_MBOX_RDPTR_LOW                                                         (10)
`define MBOX_CSR_MBOX_STATUS_MBOX_RDPTR_MASK                                                        (32'h3fffc00)
`define MBOX_CSR_MBOX_STATUS_TAP_HAS_LOCK_LOW                                                       (26)
`define MBOX_CSR_MBOX_STATUS_TAP_HAS_LOCK_MASK                                                      (32'h4000000)
`endif
`ifndef MBOX_CSR_MBOX_UNLOCK
`define MBOX_CSR_MBOX_UNLOCK                                                                        (32'h20)
`define MBOX_CSR_MBOX_UNLOCK_UNLOCK_LOW                                                             (0)
`define MBOX_CSR_MBOX_UNLOCK_UNLOCK_MASK                                                            (32'h1)
`endif
`ifndef MBOX_CSR_TAP_MODE
`define MBOX_CSR_TAP_MODE                                                                           (32'h24)
`define MBOX_CSR_TAP_MODE_ENABLED_LOW                                                               (0)
`define MBOX_CSR_TAP_MODE_ENABLED_MASK                                                              (32'h1)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_FATAL
`define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_FATAL                                                   (32'h0)
`define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_FATAL_ICCM_ECC_UNC_LOW                                  (0)
`define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_FATAL_ICCM_ECC_UNC_MASK                                 (32'h1)
`define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_FATAL_DCCM_ECC_UNC_LOW                                  (1)
`define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_FATAL_DCCM_ECC_UNC_MASK                                 (32'h2)
`define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_FATAL_NMI_PIN_LOW                                       (2)
`define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_FATAL_NMI_PIN_MASK                                      (32'h4)
`define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_FATAL_CRYPTO_ERR_LOW                                    (3)
`define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_FATAL_CRYPTO_ERR_MASK                                   (32'h8)
`define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_FATAL_RSVD_LOW                                          (4)
`define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_FATAL_RSVD_MASK                                         (32'hfffffff0)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_NON_FATAL
`define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_NON_FATAL                                               (32'h4)
`define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_NON_FATAL_MBOX_PROT_NO_LOCK_LOW                         (0)
`define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_NON_FATAL_MBOX_PROT_NO_LOCK_MASK                        (32'h1)
`define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_NON_FATAL_MBOX_PROT_OOO_LOW                             (1)
`define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_NON_FATAL_MBOX_PROT_OOO_MASK                            (32'h2)
`define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_NON_FATAL_MBOX_ECC_UNC_LOW                              (2)
`define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_NON_FATAL_MBOX_ECC_UNC_MASK                             (32'h4)
`define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_NON_FATAL_RSVD_LOW                                      (3)
`define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_NON_FATAL_RSVD_MASK                                     (32'hfffffff8)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_FW_ERROR_FATAL
`define GENERIC_AND_FUSE_REG_CPTRA_FW_ERROR_FATAL                                                   (32'h8)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_FW_ERROR_NON_FATAL
`define GENERIC_AND_FUSE_REG_CPTRA_FW_ERROR_NON_FATAL                                               (32'hc)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_ENC
`define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_ENC                                                     (32'h10)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_FW_ERROR_ENC
`define GENERIC_AND_FUSE_REG_CPTRA_FW_ERROR_ENC                                                     (32'h14)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_FW_EXTENDED_ERROR_INFO_0
`define GENERIC_AND_FUSE_REG_CPTRA_FW_EXTENDED_ERROR_INFO_0                                         (32'h18)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_FW_EXTENDED_ERROR_INFO_1
`define GENERIC_AND_FUSE_REG_CPTRA_FW_EXTENDED_ERROR_INFO_1                                         (32'h1c)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_FW_EXTENDED_ERROR_INFO_2
`define GENERIC_AND_FUSE_REG_CPTRA_FW_EXTENDED_ERROR_INFO_2                                         (32'h20)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_FW_EXTENDED_ERROR_INFO_3
`define GENERIC_AND_FUSE_REG_CPTRA_FW_EXTENDED_ERROR_INFO_3                                         (32'h24)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_FW_EXTENDED_ERROR_INFO_4
`define GENERIC_AND_FUSE_REG_CPTRA_FW_EXTENDED_ERROR_INFO_4                                         (32'h28)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_FW_EXTENDED_ERROR_INFO_5
`define GENERIC_AND_FUSE_REG_CPTRA_FW_EXTENDED_ERROR_INFO_5                                         (32'h2c)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_FW_EXTENDED_ERROR_INFO_6
`define GENERIC_AND_FUSE_REG_CPTRA_FW_EXTENDED_ERROR_INFO_6                                         (32'h30)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_FW_EXTENDED_ERROR_INFO_7
`define GENERIC_AND_FUSE_REG_CPTRA_FW_EXTENDED_ERROR_INFO_7                                         (32'h34)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_BOOT_STATUS
`define GENERIC_AND_FUSE_REG_CPTRA_BOOT_STATUS                                                      (32'h38)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_FLOW_STATUS
`define GENERIC_AND_FUSE_REG_CPTRA_FLOW_STATUS                                                      (32'h3c)
`define GENERIC_AND_FUSE_REG_CPTRA_FLOW_STATUS_STATUS_LOW                                           (0)
`define GENERIC_AND_FUSE_REG_CPTRA_FLOW_STATUS_STATUS_MASK                                          (32'hffffff)
`define GENERIC_AND_FUSE_REG_CPTRA_FLOW_STATUS_IDEVID_CSR_READY_LOW                                 (24)
`define GENERIC_AND_FUSE_REG_CPTRA_FLOW_STATUS_IDEVID_CSR_READY_MASK                                (32'h1000000)
`define GENERIC_AND_FUSE_REG_CPTRA_FLOW_STATUS_BOOT_FSM_PS_LOW                                      (25)
`define GENERIC_AND_FUSE_REG_CPTRA_FLOW_STATUS_BOOT_FSM_PS_MASK                                     (32'he000000)
`define GENERIC_AND_FUSE_REG_CPTRA_FLOW_STATUS_READY_FOR_MB_PROCESSING_LOW                          (28)
`define GENERIC_AND_FUSE_REG_CPTRA_FLOW_STATUS_READY_FOR_MB_PROCESSING_MASK                         (32'h10000000)
`define GENERIC_AND_FUSE_REG_CPTRA_FLOW_STATUS_READY_FOR_RUNTIME_LOW                                (29)
`define GENERIC_AND_FUSE_REG_CPTRA_FLOW_STATUS_READY_FOR_RUNTIME_MASK                               (32'h20000000)
`define GENERIC_AND_FUSE_REG_CPTRA_FLOW_STATUS_READY_FOR_FUSES_LOW                                  (30)
`define GENERIC_AND_FUSE_REG_CPTRA_FLOW_STATUS_READY_FOR_FUSES_MASK                                 (32'h40000000)
`define GENERIC_AND_FUSE_REG_CPTRA_FLOW_STATUS_MAILBOX_FLOW_DONE_LOW                                (31)
`define GENERIC_AND_FUSE_REG_CPTRA_FLOW_STATUS_MAILBOX_FLOW_DONE_MASK                               (32'h80000000)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_RESET_REASON
`define GENERIC_AND_FUSE_REG_CPTRA_RESET_REASON                                                     (32'h40)
`define GENERIC_AND_FUSE_REG_CPTRA_RESET_REASON_FW_UPD_RESET_LOW                                    (0)
`define GENERIC_AND_FUSE_REG_CPTRA_RESET_REASON_FW_UPD_RESET_MASK                                   (32'h1)
`define GENERIC_AND_FUSE_REG_CPTRA_RESET_REASON_WARM_RESET_LOW                                      (1)
`define GENERIC_AND_FUSE_REG_CPTRA_RESET_REASON_WARM_RESET_MASK                                     (32'h2)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_SECURITY_STATE
`define GENERIC_AND_FUSE_REG_CPTRA_SECURITY_STATE                                                   (32'h44)
`define GENERIC_AND_FUSE_REG_CPTRA_SECURITY_STATE_DEVICE_LIFECYCLE_LOW                              (0)
`define GENERIC_AND_FUSE_REG_CPTRA_SECURITY_STATE_DEVICE_LIFECYCLE_MASK                             (32'h3)
`define GENERIC_AND_FUSE_REG_CPTRA_SECURITY_STATE_DEBUG_LOCKED_LOW                                  (2)
`define GENERIC_AND_FUSE_REG_CPTRA_SECURITY_STATE_DEBUG_LOCKED_MASK                                 (32'h4)
`define GENERIC_AND_FUSE_REG_CPTRA_SECURITY_STATE_SCAN_MODE_LOW                                     (3)
`define GENERIC_AND_FUSE_REG_CPTRA_SECURITY_STATE_SCAN_MODE_MASK                                    (32'h8)
`define GENERIC_AND_FUSE_REG_CPTRA_SECURITY_STATE_RSVD_LOW                                          (4)
`define GENERIC_AND_FUSE_REG_CPTRA_SECURITY_STATE_RSVD_MASK                                         (32'hfffffff0)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_MBOX_VALID_AXI_USER_0
`define GENERIC_AND_FUSE_REG_CPTRA_MBOX_VALID_AXI_USER_0                                            (32'h48)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_MBOX_VALID_AXI_USER_1
`define GENERIC_AND_FUSE_REG_CPTRA_MBOX_VALID_AXI_USER_1                                            (32'h4c)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_MBOX_VALID_AXI_USER_2
`define GENERIC_AND_FUSE_REG_CPTRA_MBOX_VALID_AXI_USER_2                                            (32'h50)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_MBOX_VALID_AXI_USER_3
`define GENERIC_AND_FUSE_REG_CPTRA_MBOX_VALID_AXI_USER_3                                            (32'h54)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_MBOX_VALID_AXI_USER_4
`define GENERIC_AND_FUSE_REG_CPTRA_MBOX_VALID_AXI_USER_4                                            (32'h58)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_MBOX_AXI_USER_LOCK_0
`define GENERIC_AND_FUSE_REG_CPTRA_MBOX_AXI_USER_LOCK_0                                             (32'h5c)
`define GENERIC_AND_FUSE_REG_CPTRA_MBOX_AXI_USER_LOCK_0_LOCK_LOW                                    (0)
`define GENERIC_AND_FUSE_REG_CPTRA_MBOX_AXI_USER_LOCK_0_LOCK_MASK                                   (32'h1)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_MBOX_AXI_USER_LOCK_1
`define GENERIC_AND_FUSE_REG_CPTRA_MBOX_AXI_USER_LOCK_1                                             (32'h60)
`define GENERIC_AND_FUSE_REG_CPTRA_MBOX_AXI_USER_LOCK_1_LOCK_LOW                                    (0)
`define GENERIC_AND_FUSE_REG_CPTRA_MBOX_AXI_USER_LOCK_1_LOCK_MASK                                   (32'h1)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_MBOX_AXI_USER_LOCK_2
`define GENERIC_AND_FUSE_REG_CPTRA_MBOX_AXI_USER_LOCK_2                                             (32'h64)
`define GENERIC_AND_FUSE_REG_CPTRA_MBOX_AXI_USER_LOCK_2_LOCK_LOW                                    (0)
`define GENERIC_AND_FUSE_REG_CPTRA_MBOX_AXI_USER_LOCK_2_LOCK_MASK                                   (32'h1)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_MBOX_AXI_USER_LOCK_3
`define GENERIC_AND_FUSE_REG_CPTRA_MBOX_AXI_USER_LOCK_3                                             (32'h68)
`define GENERIC_AND_FUSE_REG_CPTRA_MBOX_AXI_USER_LOCK_3_LOCK_LOW                                    (0)
`define GENERIC_AND_FUSE_REG_CPTRA_MBOX_AXI_USER_LOCK_3_LOCK_MASK                                   (32'h1)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_MBOX_AXI_USER_LOCK_4
`define GENERIC_AND_FUSE_REG_CPTRA_MBOX_AXI_USER_LOCK_4                                             (32'h6c)
`define GENERIC_AND_FUSE_REG_CPTRA_MBOX_AXI_USER_LOCK_4_LOCK_LOW                                    (0)
`define GENERIC_AND_FUSE_REG_CPTRA_MBOX_AXI_USER_LOCK_4_LOCK_MASK                                   (32'h1)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_TRNG_VALID_AXI_USER
`define GENERIC_AND_FUSE_REG_CPTRA_TRNG_VALID_AXI_USER                                              (32'h70)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_TRNG_AXI_USER_LOCK
`define GENERIC_AND_FUSE_REG_CPTRA_TRNG_AXI_USER_LOCK                                               (32'h74)
`define GENERIC_AND_FUSE_REG_CPTRA_TRNG_AXI_USER_LOCK_LOCK_LOW                                      (0)
`define GENERIC_AND_FUSE_REG_CPTRA_TRNG_AXI_USER_LOCK_LOCK_MASK                                     (32'h1)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_0
`define GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_0                                                      (32'h78)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_1
`define GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_1                                                      (32'h7c)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_2
`define GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_2                                                      (32'h80)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_3
`define GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_3                                                      (32'h84)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_4
`define GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_4                                                      (32'h88)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_5
`define GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_5                                                      (32'h8c)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_6
`define GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_6                                                      (32'h90)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_7
`define GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_7                                                      (32'h94)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_8
`define GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_8                                                      (32'h98)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_9
`define GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_9                                                      (32'h9c)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_10
`define GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_10                                                     (32'ha0)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_11
`define GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_11                                                     (32'ha4)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_TRNG_CTRL
`define GENERIC_AND_FUSE_REG_CPTRA_TRNG_CTRL                                                        (32'ha8)
`define GENERIC_AND_FUSE_REG_CPTRA_TRNG_CTRL_CLEAR_LOW                                              (0)
`define GENERIC_AND_FUSE_REG_CPTRA_TRNG_CTRL_CLEAR_MASK                                             (32'h1)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_TRNG_STATUS
`define GENERIC_AND_FUSE_REG_CPTRA_TRNG_STATUS                                                      (32'hac)
`define GENERIC_AND_FUSE_REG_CPTRA_TRNG_STATUS_DATA_REQ_LOW                                         (0)
`define GENERIC_AND_FUSE_REG_CPTRA_TRNG_STATUS_DATA_REQ_MASK                                        (32'h1)
`define GENERIC_AND_FUSE_REG_CPTRA_TRNG_STATUS_DATA_WR_DONE_LOW                                     (1)
`define GENERIC_AND_FUSE_REG_CPTRA_TRNG_STATUS_DATA_WR_DONE_MASK                                    (32'h2)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_FUSE_WR_DONE
`define GENERIC_AND_FUSE_REG_CPTRA_FUSE_WR_DONE                                                     (32'hb0)
`define GENERIC_AND_FUSE_REG_CPTRA_FUSE_WR_DONE_DONE_LOW                                            (0)
`define GENERIC_AND_FUSE_REG_CPTRA_FUSE_WR_DONE_DONE_MASK                                           (32'h1)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_TIMER_CONFIG
`define GENERIC_AND_FUSE_REG_CPTRA_TIMER_CONFIG                                                     (32'hb4)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_BOOTFSM_GO
`define GENERIC_AND_FUSE_REG_CPTRA_BOOTFSM_GO                                                       (32'hb8)
`define GENERIC_AND_FUSE_REG_CPTRA_BOOTFSM_GO_GO_LOW                                                (0)
`define GENERIC_AND_FUSE_REG_CPTRA_BOOTFSM_GO_GO_MASK                                               (32'h1)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_DBG_MANUF_SERVICE_REG
`define GENERIC_AND_FUSE_REG_CPTRA_DBG_MANUF_SERVICE_REG                                            (32'hbc)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_CLK_GATING_EN
`define GENERIC_AND_FUSE_REG_CPTRA_CLK_GATING_EN                                                    (32'hc0)
`define GENERIC_AND_FUSE_REG_CPTRA_CLK_GATING_EN_CLK_GATING_EN_LOW                                  (0)
`define GENERIC_AND_FUSE_REG_CPTRA_CLK_GATING_EN_CLK_GATING_EN_MASK                                 (32'h1)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_GENERIC_INPUT_WIRES_0
`define GENERIC_AND_FUSE_REG_CPTRA_GENERIC_INPUT_WIRES_0                                            (32'hc4)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_GENERIC_INPUT_WIRES_1
`define GENERIC_AND_FUSE_REG_CPTRA_GENERIC_INPUT_WIRES_1                                            (32'hc8)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_GENERIC_OUTPUT_WIRES_0
`define GENERIC_AND_FUSE_REG_CPTRA_GENERIC_OUTPUT_WIRES_0                                           (32'hcc)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_GENERIC_OUTPUT_WIRES_1
`define GENERIC_AND_FUSE_REG_CPTRA_GENERIC_OUTPUT_WIRES_1                                           (32'hd0)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_HW_REV_ID
`define GENERIC_AND_FUSE_REG_CPTRA_HW_REV_ID                                                        (32'hd4)
`define GENERIC_AND_FUSE_REG_CPTRA_HW_REV_ID_CPTRA_GENERATION_LOW                                   (0)
`define GENERIC_AND_FUSE_REG_CPTRA_HW_REV_ID_CPTRA_GENERATION_MASK                                  (32'hffff)
`define GENERIC_AND_FUSE_REG_CPTRA_HW_REV_ID_SOC_STEPPING_ID_LOW                                    (16)
`define GENERIC_AND_FUSE_REG_CPTRA_HW_REV_ID_SOC_STEPPING_ID_MASK                                   (32'hffff0000)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_FW_REV_ID_0
`define GENERIC_AND_FUSE_REG_CPTRA_FW_REV_ID_0                                                      (32'hd8)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_FW_REV_ID_1
`define GENERIC_AND_FUSE_REG_CPTRA_FW_REV_ID_1                                                      (32'hdc)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_HW_CONFIG
`define GENERIC_AND_FUSE_REG_CPTRA_HW_CONFIG                                                        (32'he0)
`define GENERIC_AND_FUSE_REG_CPTRA_HW_CONFIG_ITRNG_EN_LOW                                           (0)
`define GENERIC_AND_FUSE_REG_CPTRA_HW_CONFIG_ITRNG_EN_MASK                                          (32'h1)
`define GENERIC_AND_FUSE_REG_CPTRA_HW_CONFIG_FUSE_GRANULARITY_LOW                                   (1)
`define GENERIC_AND_FUSE_REG_CPTRA_HW_CONFIG_FUSE_GRANULARITY_MASK                                  (32'h2)
`define GENERIC_AND_FUSE_REG_CPTRA_HW_CONFIG_RSVD_EN_LOW                                            (2)
`define GENERIC_AND_FUSE_REG_CPTRA_HW_CONFIG_RSVD_EN_MASK                                           (32'hc)
`define GENERIC_AND_FUSE_REG_CPTRA_HW_CONFIG_LMS_ACC_EN_LOW                                         (4)
`define GENERIC_AND_FUSE_REG_CPTRA_HW_CONFIG_LMS_ACC_EN_MASK                                        (32'h10)
`define GENERIC_AND_FUSE_REG_CPTRA_HW_CONFIG_SUBSYSTEM_MODE_EN_LOW                                  (5)
`define GENERIC_AND_FUSE_REG_CPTRA_HW_CONFIG_SUBSYSTEM_MODE_EN_MASK                                 (32'h20)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_WDT_TIMER1_EN
`define GENERIC_AND_FUSE_REG_CPTRA_WDT_TIMER1_EN                                                    (32'he4)
`define GENERIC_AND_FUSE_REG_CPTRA_WDT_TIMER1_EN_TIMER1_EN_LOW                                      (0)
`define GENERIC_AND_FUSE_REG_CPTRA_WDT_TIMER1_EN_TIMER1_EN_MASK                                     (32'h1)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_WDT_TIMER1_CTRL
`define GENERIC_AND_FUSE_REG_CPTRA_WDT_TIMER1_CTRL                                                  (32'he8)
`define GENERIC_AND_FUSE_REG_CPTRA_WDT_TIMER1_CTRL_TIMER1_RESTART_LOW                               (0)
`define GENERIC_AND_FUSE_REG_CPTRA_WDT_TIMER1_CTRL_TIMER1_RESTART_MASK                              (32'h1)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD_0
`define GENERIC_AND_FUSE_REG_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD_0                                      (32'hec)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD_1
`define GENERIC_AND_FUSE_REG_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD_1                                      (32'hf0)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_WDT_TIMER2_EN
`define GENERIC_AND_FUSE_REG_CPTRA_WDT_TIMER2_EN                                                    (32'hf4)
`define GENERIC_AND_FUSE_REG_CPTRA_WDT_TIMER2_EN_TIMER2_EN_LOW                                      (0)
`define GENERIC_AND_FUSE_REG_CPTRA_WDT_TIMER2_EN_TIMER2_EN_MASK                                     (32'h1)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_WDT_TIMER2_CTRL
`define GENERIC_AND_FUSE_REG_CPTRA_WDT_TIMER2_CTRL                                                  (32'hf8)
`define GENERIC_AND_FUSE_REG_CPTRA_WDT_TIMER2_CTRL_TIMER2_RESTART_LOW                               (0)
`define GENERIC_AND_FUSE_REG_CPTRA_WDT_TIMER2_CTRL_TIMER2_RESTART_MASK                              (32'h1)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD_0
`define GENERIC_AND_FUSE_REG_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD_0                                      (32'hfc)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD_1
`define GENERIC_AND_FUSE_REG_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD_1                                      (32'h100)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_WDT_STATUS
`define GENERIC_AND_FUSE_REG_CPTRA_WDT_STATUS                                                       (32'h104)
`define GENERIC_AND_FUSE_REG_CPTRA_WDT_STATUS_T1_TIMEOUT_LOW                                        (0)
`define GENERIC_AND_FUSE_REG_CPTRA_WDT_STATUS_T1_TIMEOUT_MASK                                       (32'h1)
`define GENERIC_AND_FUSE_REG_CPTRA_WDT_STATUS_T2_TIMEOUT_LOW                                        (1)
`define GENERIC_AND_FUSE_REG_CPTRA_WDT_STATUS_T2_TIMEOUT_MASK                                       (32'h2)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_FUSE_VALID_AXI_USER
`define GENERIC_AND_FUSE_REG_CPTRA_FUSE_VALID_AXI_USER                                              (32'h108)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_FUSE_AXI_USER_LOCK
`define GENERIC_AND_FUSE_REG_CPTRA_FUSE_AXI_USER_LOCK                                               (32'h10c)
`define GENERIC_AND_FUSE_REG_CPTRA_FUSE_AXI_USER_LOCK_LOCK_LOW                                      (0)
`define GENERIC_AND_FUSE_REG_CPTRA_FUSE_AXI_USER_LOCK_LOCK_MASK                                     (32'h1)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_WDT_CFG_0
`define GENERIC_AND_FUSE_REG_CPTRA_WDT_CFG_0                                                        (32'h110)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_WDT_CFG_1
`define GENERIC_AND_FUSE_REG_CPTRA_WDT_CFG_1                                                        (32'h114)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_ITRNG_ENTROPY_CONFIG_0
`define GENERIC_AND_FUSE_REG_CPTRA_ITRNG_ENTROPY_CONFIG_0                                           (32'h118)
`define GENERIC_AND_FUSE_REG_CPTRA_ITRNG_ENTROPY_CONFIG_0_LOW_THRESHOLD_LOW                         (0)
`define GENERIC_AND_FUSE_REG_CPTRA_ITRNG_ENTROPY_CONFIG_0_LOW_THRESHOLD_MASK                        (32'hffff)
`define GENERIC_AND_FUSE_REG_CPTRA_ITRNG_ENTROPY_CONFIG_0_HIGH_THRESHOLD_LOW                        (16)
`define GENERIC_AND_FUSE_REG_CPTRA_ITRNG_ENTROPY_CONFIG_0_HIGH_THRESHOLD_MASK                       (32'hffff0000)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_ITRNG_ENTROPY_CONFIG_1
`define GENERIC_AND_FUSE_REG_CPTRA_ITRNG_ENTROPY_CONFIG_1                                           (32'h11c)
`define GENERIC_AND_FUSE_REG_CPTRA_ITRNG_ENTROPY_CONFIG_1_REPETITION_COUNT_LOW                      (0)
`define GENERIC_AND_FUSE_REG_CPTRA_ITRNG_ENTROPY_CONFIG_1_REPETITION_COUNT_MASK                     (32'hffff)
`define GENERIC_AND_FUSE_REG_CPTRA_ITRNG_ENTROPY_CONFIG_1_RSVD_LOW                                  (16)
`define GENERIC_AND_FUSE_REG_CPTRA_ITRNG_ENTROPY_CONFIG_1_RSVD_MASK                                 (32'hffff0000)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_RSVD_REG_0
`define GENERIC_AND_FUSE_REG_CPTRA_RSVD_REG_0                                                       (32'h120)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_RSVD_REG_1
`define GENERIC_AND_FUSE_REG_CPTRA_RSVD_REG_1                                                       (32'h124)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_HW_CAPABILITIES
`define GENERIC_AND_FUSE_REG_CPTRA_HW_CAPABILITIES                                                  (32'h128)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_FW_CAPABILITIES
`define GENERIC_AND_FUSE_REG_CPTRA_FW_CAPABILITIES                                                  (32'h12c)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_CAP_LOCK
`define GENERIC_AND_FUSE_REG_CPTRA_CAP_LOCK                                                         (32'h130)
`define GENERIC_AND_FUSE_REG_CPTRA_CAP_LOCK_LOCK_LOW                                                (0)
`define GENERIC_AND_FUSE_REG_CPTRA_CAP_LOCK_LOCK_MASK                                               (32'h1)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_0
`define GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_0                                                  (32'h140)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_1
`define GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_1                                                  (32'h144)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_2
`define GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_2                                                  (32'h148)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_3
`define GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_3                                                  (32'h14c)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_4
`define GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_4                                                  (32'h150)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_5
`define GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_5                                                  (32'h154)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_6
`define GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_6                                                  (32'h158)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_7
`define GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_7                                                  (32'h15c)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_8
`define GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_8                                                  (32'h160)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_9
`define GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_9                                                  (32'h164)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_10
`define GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_10                                                 (32'h168)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_11
`define GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_11                                                 (32'h16c)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_LOCK
`define GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_LOCK                                               (32'h170)
`define GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_LOCK_LOCK_LOW                                      (0)
`define GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_LOCK_LOCK_MASK                                     (32'h1)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_0
`define GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_0                                                        (32'h200)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_1
`define GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_1                                                        (32'h204)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_2
`define GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_2                                                        (32'h208)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_3
`define GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_3                                                        (32'h20c)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_4
`define GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_4                                                        (32'h210)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_5
`define GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_5                                                        (32'h214)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_6
`define GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_6                                                        (32'h218)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_7
`define GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_7                                                        (32'h21c)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_8
`define GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_8                                                        (32'h220)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_9
`define GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_9                                                        (32'h224)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_10
`define GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_10                                                       (32'h228)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_11
`define GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_11                                                       (32'h22c)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_12
`define GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_12                                                       (32'h230)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_13
`define GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_13                                                       (32'h234)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_14
`define GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_14                                                       (32'h238)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_15
`define GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_15                                                       (32'h23c)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_FIELD_ENTROPY_0
`define GENERIC_AND_FUSE_REG_FUSE_FIELD_ENTROPY_0                                                   (32'h240)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_FIELD_ENTROPY_1
`define GENERIC_AND_FUSE_REG_FUSE_FIELD_ENTROPY_1                                                   (32'h244)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_FIELD_ENTROPY_2
`define GENERIC_AND_FUSE_REG_FUSE_FIELD_ENTROPY_2                                                   (32'h248)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_FIELD_ENTROPY_3
`define GENERIC_AND_FUSE_REG_FUSE_FIELD_ENTROPY_3                                                   (32'h24c)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_FIELD_ENTROPY_4
`define GENERIC_AND_FUSE_REG_FUSE_FIELD_ENTROPY_4                                                   (32'h250)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_FIELD_ENTROPY_5
`define GENERIC_AND_FUSE_REG_FUSE_FIELD_ENTROPY_5                                                   (32'h254)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_FIELD_ENTROPY_6
`define GENERIC_AND_FUSE_REG_FUSE_FIELD_ENTROPY_6                                                   (32'h258)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_FIELD_ENTROPY_7
`define GENERIC_AND_FUSE_REG_FUSE_FIELD_ENTROPY_7                                                   (32'h25c)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_0
`define GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_0                                                  (32'h260)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_1
`define GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_1                                                  (32'h264)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_2
`define GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_2                                                  (32'h268)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_3
`define GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_3                                                  (32'h26c)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_4
`define GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_4                                                  (32'h270)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_5
`define GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_5                                                  (32'h274)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_6
`define GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_6                                                  (32'h278)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_7
`define GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_7                                                  (32'h27c)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_8
`define GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_8                                                  (32'h280)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_9
`define GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_9                                                  (32'h284)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_10
`define GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_10                                                 (32'h288)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_11
`define GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_11                                                 (32'h28c)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_ECC_REVOCATION
`define GENERIC_AND_FUSE_REG_FUSE_ECC_REVOCATION                                                    (32'h290)
`define GENERIC_AND_FUSE_REG_FUSE_ECC_REVOCATION_ECC_REVOCATION_LOW                                 (0)
`define GENERIC_AND_FUSE_REG_FUSE_ECC_REVOCATION_ECC_REVOCATION_MASK                                (32'hf)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_FMC_KEY_MANIFEST_SVN
`define GENERIC_AND_FUSE_REG_FUSE_FMC_KEY_MANIFEST_SVN                                              (32'h2b4)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_RUNTIME_SVN_0
`define GENERIC_AND_FUSE_REG_FUSE_RUNTIME_SVN_0                                                     (32'h2b8)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_RUNTIME_SVN_1
`define GENERIC_AND_FUSE_REG_FUSE_RUNTIME_SVN_1                                                     (32'h2bc)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_RUNTIME_SVN_2
`define GENERIC_AND_FUSE_REG_FUSE_RUNTIME_SVN_2                                                     (32'h2c0)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_RUNTIME_SVN_3
`define GENERIC_AND_FUSE_REG_FUSE_RUNTIME_SVN_3                                                     (32'h2c4)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_ANTI_ROLLBACK_DISABLE
`define GENERIC_AND_FUSE_REG_FUSE_ANTI_ROLLBACK_DISABLE                                             (32'h2c8)
`define GENERIC_AND_FUSE_REG_FUSE_ANTI_ROLLBACK_DISABLE_DIS_LOW                                     (0)
`define GENERIC_AND_FUSE_REG_FUSE_ANTI_ROLLBACK_DISABLE_DIS_MASK                                    (32'h1)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_0
`define GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_0                                                (32'h2cc)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_1
`define GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_1                                                (32'h2d0)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_2
`define GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_2                                                (32'h2d4)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_3
`define GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_3                                                (32'h2d8)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_4
`define GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_4                                                (32'h2dc)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_5
`define GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_5                                                (32'h2e0)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_6
`define GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_6                                                (32'h2e4)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_7
`define GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_7                                                (32'h2e8)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_8
`define GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_8                                                (32'h2ec)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_9
`define GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_9                                                (32'h2f0)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_10
`define GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_10                                               (32'h2f4)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_11
`define GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_11                                               (32'h2f8)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_12
`define GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_12                                               (32'h2fc)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_13
`define GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_13                                               (32'h300)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_14
`define GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_14                                               (32'h304)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_15
`define GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_15                                               (32'h308)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_16
`define GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_16                                               (32'h30c)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_17
`define GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_17                                               (32'h310)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_18
`define GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_18                                               (32'h314)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_19
`define GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_19                                               (32'h318)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_20
`define GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_20                                               (32'h31c)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_21
`define GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_21                                               (32'h320)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_22
`define GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_22                                               (32'h324)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_23
`define GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_23                                               (32'h328)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_IDEVID_MANUF_HSM_ID_0
`define GENERIC_AND_FUSE_REG_FUSE_IDEVID_MANUF_HSM_ID_0                                             (32'h32c)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_IDEVID_MANUF_HSM_ID_1
`define GENERIC_AND_FUSE_REG_FUSE_IDEVID_MANUF_HSM_ID_1                                             (32'h330)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_IDEVID_MANUF_HSM_ID_2
`define GENERIC_AND_FUSE_REG_FUSE_IDEVID_MANUF_HSM_ID_2                                             (32'h334)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_IDEVID_MANUF_HSM_ID_3
`define GENERIC_AND_FUSE_REG_FUSE_IDEVID_MANUF_HSM_ID_3                                             (32'h338)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_LMS_REVOCATION
`define GENERIC_AND_FUSE_REG_FUSE_LMS_REVOCATION                                                    (32'h340)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_MLDSA_REVOCATION
`define GENERIC_AND_FUSE_REG_FUSE_MLDSA_REVOCATION                                                  (32'h344)
`define GENERIC_AND_FUSE_REG_FUSE_MLDSA_REVOCATION_MLDSA_REVOCATION_LOW                             (0)
`define GENERIC_AND_FUSE_REG_FUSE_MLDSA_REVOCATION_MLDSA_REVOCATION_MASK                            (32'hf)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_SOC_STEPPING_ID
`define GENERIC_AND_FUSE_REG_FUSE_SOC_STEPPING_ID                                                   (32'h348)
`define GENERIC_AND_FUSE_REG_FUSE_SOC_STEPPING_ID_SOC_STEPPING_ID_LOW                               (0)
`define GENERIC_AND_FUSE_REG_FUSE_SOC_STEPPING_ID_SOC_STEPPING_ID_MASK                              (32'hffff)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_0
`define GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_0                                          (32'h34c)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_1
`define GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_1                                          (32'h350)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_2
`define GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_2                                          (32'h354)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_3
`define GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_3                                          (32'h358)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_4
`define GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_4                                          (32'h35c)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_5
`define GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_5                                          (32'h360)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_6
`define GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_6                                          (32'h364)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_7
`define GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_7                                          (32'h368)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_8
`define GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_8                                          (32'h36c)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_9
`define GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_9                                          (32'h370)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_10
`define GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_10                                         (32'h374)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_11
`define GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_11                                         (32'h378)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_12
`define GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_12                                         (32'h37c)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_13
`define GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_13                                         (32'h380)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_14
`define GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_14                                         (32'h384)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_15
`define GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_15                                         (32'h388)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_PQC_KEY_TYPE
`define GENERIC_AND_FUSE_REG_FUSE_PQC_KEY_TYPE                                                      (32'h38c)
`define GENERIC_AND_FUSE_REG_FUSE_PQC_KEY_TYPE_KEY_TYPE_LOW                                         (0)
`define GENERIC_AND_FUSE_REG_FUSE_PQC_KEY_TYPE_KEY_TYPE_MASK                                        (32'h3)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_SOC_MANIFEST_SVN_0
`define GENERIC_AND_FUSE_REG_FUSE_SOC_MANIFEST_SVN_0                                                (32'h390)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_SOC_MANIFEST_SVN_1
`define GENERIC_AND_FUSE_REG_FUSE_SOC_MANIFEST_SVN_1                                                (32'h394)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_SOC_MANIFEST_SVN_2
`define GENERIC_AND_FUSE_REG_FUSE_SOC_MANIFEST_SVN_2                                                (32'h398)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_SOC_MANIFEST_SVN_3
`define GENERIC_AND_FUSE_REG_FUSE_SOC_MANIFEST_SVN_3                                                (32'h39c)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_SOC_MANIFEST_MAX_SVN
`define GENERIC_AND_FUSE_REG_FUSE_SOC_MANIFEST_MAX_SVN                                              (32'h3a0)
`define GENERIC_AND_FUSE_REG_FUSE_SOC_MANIFEST_MAX_SVN_SVN_LOW                                      (0)
`define GENERIC_AND_FUSE_REG_FUSE_SOC_MANIFEST_MAX_SVN_SVN_MASK                                     (32'hff)
`endif
`ifndef GENERIC_AND_FUSE_REG_SS_CALIPTRA_BASE_ADDR_L
`define GENERIC_AND_FUSE_REG_SS_CALIPTRA_BASE_ADDR_L                                                (32'h500)
`endif
`ifndef GENERIC_AND_FUSE_REG_SS_CALIPTRA_BASE_ADDR_H
`define GENERIC_AND_FUSE_REG_SS_CALIPTRA_BASE_ADDR_H                                                (32'h504)
`endif
`ifndef GENERIC_AND_FUSE_REG_SS_MCI_BASE_ADDR_L
`define GENERIC_AND_FUSE_REG_SS_MCI_BASE_ADDR_L                                                     (32'h508)
`endif
`ifndef GENERIC_AND_FUSE_REG_SS_MCI_BASE_ADDR_H
`define GENERIC_AND_FUSE_REG_SS_MCI_BASE_ADDR_H                                                     (32'h50c)
`endif
`ifndef GENERIC_AND_FUSE_REG_SS_RECOVERY_IFC_BASE_ADDR_L
`define GENERIC_AND_FUSE_REG_SS_RECOVERY_IFC_BASE_ADDR_L                                            (32'h510)
`endif
`ifndef GENERIC_AND_FUSE_REG_SS_RECOVERY_IFC_BASE_ADDR_H
`define GENERIC_AND_FUSE_REG_SS_RECOVERY_IFC_BASE_ADDR_H                                            (32'h514)
`endif
`ifndef GENERIC_AND_FUSE_REG_SS_OTP_FC_BASE_ADDR_L
`define GENERIC_AND_FUSE_REG_SS_OTP_FC_BASE_ADDR_L                                                  (32'h518)
`endif
`ifndef GENERIC_AND_FUSE_REG_SS_OTP_FC_BASE_ADDR_H
`define GENERIC_AND_FUSE_REG_SS_OTP_FC_BASE_ADDR_H                                                  (32'h51c)
`endif
`ifndef GENERIC_AND_FUSE_REG_SS_UDS_SEED_BASE_ADDR_L
`define GENERIC_AND_FUSE_REG_SS_UDS_SEED_BASE_ADDR_L                                                (32'h520)
`endif
`ifndef GENERIC_AND_FUSE_REG_SS_UDS_SEED_BASE_ADDR_H
`define GENERIC_AND_FUSE_REG_SS_UDS_SEED_BASE_ADDR_H                                                (32'h524)
`endif
`ifndef GENERIC_AND_FUSE_REG_SS_PROD_DEBUG_UNLOCK_AUTH_PK_HASH_REG_BANK_OFFSET
`define GENERIC_AND_FUSE_REG_SS_PROD_DEBUG_UNLOCK_AUTH_PK_HASH_REG_BANK_OFFSET                      (32'h528)
`endif
`ifndef GENERIC_AND_FUSE_REG_SS_NUM_OF_PROD_DEBUG_UNLOCK_AUTH_PK_HASHES
`define GENERIC_AND_FUSE_REG_SS_NUM_OF_PROD_DEBUG_UNLOCK_AUTH_PK_HASHES                             (32'h52c)
`endif
`ifndef GENERIC_AND_FUSE_REG_SS_DEBUG_INTENT
`define GENERIC_AND_FUSE_REG_SS_DEBUG_INTENT                                                        (32'h530)
`define GENERIC_AND_FUSE_REG_SS_DEBUG_INTENT_DEBUG_INTENT_LOW                                       (0)
`define GENERIC_AND_FUSE_REG_SS_DEBUG_INTENT_DEBUG_INTENT_MASK                                      (32'h1)
`endif
`ifndef GENERIC_AND_FUSE_REG_SS_CALIPTRA_DMA_AXI_USER
`define GENERIC_AND_FUSE_REG_SS_CALIPTRA_DMA_AXI_USER                                               (32'h534)
`endif
`ifndef GENERIC_AND_FUSE_REG_SS_EXTERNAL_STAGING_AREA_BASE_ADDR_L
`define GENERIC_AND_FUSE_REG_SS_EXTERNAL_STAGING_AREA_BASE_ADDR_L                                   (32'h538)
`endif
`ifndef GENERIC_AND_FUSE_REG_SS_EXTERNAL_STAGING_AREA_BASE_ADDR_H
`define GENERIC_AND_FUSE_REG_SS_EXTERNAL_STAGING_AREA_BASE_ADDR_H                                   (32'h53c)
`endif
`ifndef GENERIC_AND_FUSE_REG_SS_STRAP_GENERIC_0
`define GENERIC_AND_FUSE_REG_SS_STRAP_GENERIC_0                                                     (32'h5a0)
`endif
`ifndef GENERIC_AND_FUSE_REG_SS_STRAP_GENERIC_1
`define GENERIC_AND_FUSE_REG_SS_STRAP_GENERIC_1                                                     (32'h5a4)
`endif
`ifndef GENERIC_AND_FUSE_REG_SS_STRAP_GENERIC_2
`define GENERIC_AND_FUSE_REG_SS_STRAP_GENERIC_2                                                     (32'h5a8)
`endif
`ifndef GENERIC_AND_FUSE_REG_SS_STRAP_GENERIC_3
`define GENERIC_AND_FUSE_REG_SS_STRAP_GENERIC_3                                                     (32'h5ac)
`endif
`ifndef GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_REQ
`define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_REQ                                                 (32'h5c0)
`define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_REQ_MANUF_DBG_UNLOCK_REQ_LOW                        (0)
`define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_REQ_MANUF_DBG_UNLOCK_REQ_MASK                       (32'h1)
`define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_REQ_PROD_DBG_UNLOCK_REQ_LOW                         (1)
`define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_REQ_PROD_DBG_UNLOCK_REQ_MASK                        (32'h2)
`define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_REQ_UDS_PROGRAM_REQ_LOW                             (2)
`define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_REQ_UDS_PROGRAM_REQ_MASK                            (32'h4)
`define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_REQ_RSVD_LOW                                        (3)
`define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_REQ_RSVD_MASK                                       (32'hfffffff8)
`endif
`ifndef GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_RSP
`define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_RSP                                                 (32'h5c4)
`define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_RSP_MANUF_DBG_UNLOCK_SUCCESS_LOW                    (0)
`define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_RSP_MANUF_DBG_UNLOCK_SUCCESS_MASK                   (32'h1)
`define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_RSP_MANUF_DBG_UNLOCK_FAIL_LOW                       (1)
`define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_RSP_MANUF_DBG_UNLOCK_FAIL_MASK                      (32'h2)
`define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_RSP_MANUF_DBG_UNLOCK_IN_PROGRESS_LOW                (2)
`define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_RSP_MANUF_DBG_UNLOCK_IN_PROGRESS_MASK               (32'h4)
`define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_RSP_PROD_DBG_UNLOCK_SUCCESS_LOW                     (3)
`define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_RSP_PROD_DBG_UNLOCK_SUCCESS_MASK                    (32'h8)
`define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_RSP_PROD_DBG_UNLOCK_FAIL_LOW                        (4)
`define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_RSP_PROD_DBG_UNLOCK_FAIL_MASK                       (32'h10)
`define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_RSP_PROD_DBG_UNLOCK_IN_PROGRESS_LOW                 (5)
`define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_RSP_PROD_DBG_UNLOCK_IN_PROGRESS_MASK                (32'h20)
`define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_RSP_UDS_PROGRAM_SUCCESS_LOW                         (6)
`define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_RSP_UDS_PROGRAM_SUCCESS_MASK                        (32'h40)
`define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_RSP_UDS_PROGRAM_FAIL_LOW                            (7)
`define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_RSP_UDS_PROGRAM_FAIL_MASK                           (32'h80)
`define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_RSP_UDS_PROGRAM_IN_PROGRESS_LOW                     (8)
`define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_RSP_UDS_PROGRAM_IN_PROGRESS_MASK                    (32'h100)
`define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_RSP_TAP_MAILBOX_AVAILABLE_LOW                       (9)
`define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_RSP_TAP_MAILBOX_AVAILABLE_MASK                      (32'h200)
`define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_RSP_RSVD_LOW                                        (10)
`define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_RSP_RSVD_MASK                                       (32'hfffffc00)
`endif
`ifndef GENERIC_AND_FUSE_REG_SS_SOC_DBG_UNLOCK_LEVEL_0
`define GENERIC_AND_FUSE_REG_SS_SOC_DBG_UNLOCK_LEVEL_0                                              (32'h5c8)
`endif
`ifndef GENERIC_AND_FUSE_REG_SS_SOC_DBG_UNLOCK_LEVEL_1
`define GENERIC_AND_FUSE_REG_SS_SOC_DBG_UNLOCK_LEVEL_1                                              (32'h5cc)
`endif
`ifndef GENERIC_AND_FUSE_REG_SS_GENERIC_FW_EXEC_CTRL_0
`define GENERIC_AND_FUSE_REG_SS_GENERIC_FW_EXEC_CTRL_0                                              (32'h5d0)
`endif
`ifndef GENERIC_AND_FUSE_REG_SS_GENERIC_FW_EXEC_CTRL_1
`define GENERIC_AND_FUSE_REG_SS_GENERIC_FW_EXEC_CTRL_1                                              (32'h5d4)
`endif
`ifndef GENERIC_AND_FUSE_REG_SS_GENERIC_FW_EXEC_CTRL_2
`define GENERIC_AND_FUSE_REG_SS_GENERIC_FW_EXEC_CTRL_2                                              (32'h5d8)
`endif
`ifndef GENERIC_AND_FUSE_REG_SS_GENERIC_FW_EXEC_CTRL_3
`define GENERIC_AND_FUSE_REG_SS_GENERIC_FW_EXEC_CTRL_3                                              (32'h5dc)
`endif


`endif