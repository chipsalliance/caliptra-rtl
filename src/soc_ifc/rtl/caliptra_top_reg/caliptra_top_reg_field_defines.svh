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
`define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_FATAL_KV_ERROR_LOW                                      (4)
`define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_FATAL_KV_ERROR_MASK                                     (32'h10)
`define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_FATAL_SHADOW_STORAGE_ERR_LOW                            (5)
`define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_FATAL_SHADOW_STORAGE_ERR_MASK                           (32'h20)
`define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_FATAL_RSVD_LOW                                          (6)
`define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_FATAL_RSVD_MASK                                         (32'hffffffc0)
`endif
`ifndef GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_NON_FATAL
`define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_NON_FATAL                                               (32'h4)
`define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_NON_FATAL_MBOX_PROT_NO_LOCK_LOW                         (0)
`define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_NON_FATAL_MBOX_PROT_NO_LOCK_MASK                        (32'h1)
`define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_NON_FATAL_MBOX_PROT_OOO_LOW                             (1)
`define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_NON_FATAL_MBOX_PROT_OOO_MASK                            (32'h2)
`define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_NON_FATAL_MBOX_ECC_UNC_LOW                              (2)
`define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_NON_FATAL_MBOX_ECC_UNC_MASK                             (32'h4)
`define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_NON_FATAL_SHADOW_UPDATE_ERR_LOW                         (3)
`define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_NON_FATAL_SHADOW_UPDATE_ERR_MASK                        (32'h8)
`define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_NON_FATAL_RSVD_LOW                                      (4)
`define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_NON_FATAL_RSVD_MASK                                     (32'hfffffff0)
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
`define GENERIC_AND_FUSE_REG_CPTRA_HW_CONFIG_OCP_LOCK_MODE_EN_LOW                                   (6)
`define GENERIC_AND_FUSE_REG_CPTRA_HW_CONFIG_OCP_LOCK_MODE_EN_MASK                                  (32'h40)
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
`ifndef GENERIC_AND_FUSE_REG_FUSE_HEK_SEED_0
`define GENERIC_AND_FUSE_REG_FUSE_HEK_SEED_0                                                        (32'h3c0)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_HEK_SEED_1
`define GENERIC_AND_FUSE_REG_FUSE_HEK_SEED_1                                                        (32'h3c4)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_HEK_SEED_2
`define GENERIC_AND_FUSE_REG_FUSE_HEK_SEED_2                                                        (32'h3c8)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_HEK_SEED_3
`define GENERIC_AND_FUSE_REG_FUSE_HEK_SEED_3                                                        (32'h3cc)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_HEK_SEED_4
`define GENERIC_AND_FUSE_REG_FUSE_HEK_SEED_4                                                        (32'h3d0)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_HEK_SEED_5
`define GENERIC_AND_FUSE_REG_FUSE_HEK_SEED_5                                                        (32'h3d4)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_HEK_SEED_6
`define GENERIC_AND_FUSE_REG_FUSE_HEK_SEED_6                                                        (32'h3d8)
`endif
`ifndef GENERIC_AND_FUSE_REG_FUSE_HEK_SEED_7
`define GENERIC_AND_FUSE_REG_FUSE_HEK_SEED_7                                                        (32'h3dc)
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
`ifndef GENERIC_AND_FUSE_REG_SS_KEY_RELEASE_BASE_ADDR_L
`define GENERIC_AND_FUSE_REG_SS_KEY_RELEASE_BASE_ADDR_L                                             (32'h540)
`endif
`ifndef GENERIC_AND_FUSE_REG_SS_KEY_RELEASE_BASE_ADDR_H
`define GENERIC_AND_FUSE_REG_SS_KEY_RELEASE_BASE_ADDR_H                                             (32'h544)
`endif
`ifndef GENERIC_AND_FUSE_REG_SS_KEY_RELEASE_SIZE
`define GENERIC_AND_FUSE_REG_SS_KEY_RELEASE_SIZE                                                    (32'h548)
`define GENERIC_AND_FUSE_REG_SS_KEY_RELEASE_SIZE_SIZE_LOW                                           (0)
`define GENERIC_AND_FUSE_REG_SS_KEY_RELEASE_SIZE_SIZE_MASK                                          (32'hffff)
`endif
`ifndef GENERIC_AND_FUSE_REG_SS_OCP_LOCK_CTRL
`define GENERIC_AND_FUSE_REG_SS_OCP_LOCK_CTRL                                                       (32'h54c)
`define GENERIC_AND_FUSE_REG_SS_OCP_LOCK_CTRL_LOCK_IN_PROGRESS_LOW                                  (0)
`define GENERIC_AND_FUSE_REG_SS_OCP_LOCK_CTRL_LOCK_IN_PROGRESS_MASK                                 (32'h1)
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
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_0
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_0                                                 (32'hc00)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_1
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_1                                                 (32'hc04)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_2
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_2                                                 (32'hc08)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_3
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_3                                                 (32'hc0c)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_4
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_4                                                 (32'hc10)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_5
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_5                                                 (32'hc14)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_6
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_6                                                 (32'hc18)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_7
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_7                                                 (32'hc1c)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_8
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_8                                                 (32'hc20)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_9
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_9                                                 (32'hc24)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_10
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_10                                                (32'hc28)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_11
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_11                                                (32'hc2c)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_12
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_12                                                (32'hc30)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_13
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_13                                                (32'hc34)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_14
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_14                                                (32'hc38)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_15
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_15                                                (32'hc3c)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_16
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_16                                                (32'hc40)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_17
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_17                                                (32'hc44)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_18
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_18                                                (32'hc48)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_19
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_19                                                (32'hc4c)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_20
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_20                                                (32'hc50)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_21
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_21                                                (32'hc54)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_22
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_22                                                (32'hc58)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_23
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_23                                                (32'hc5c)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_24
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_24                                                (32'hc60)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_25
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_25                                                (32'hc64)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_26
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_26                                                (32'hc68)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_27
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_27                                                (32'hc6c)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_28
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_28                                                (32'hc70)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_29
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_29                                                (32'hc74)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_30
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_30                                                (32'hc78)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_31
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_31                                                (32'hc7c)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_32
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_32                                                (32'hc80)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_33
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_33                                                (32'hc84)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_34
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_34                                                (32'hc88)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_35
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_35                                                (32'hc8c)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_36
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_36                                                (32'hc90)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_37
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_37                                                (32'hc94)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_38
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_38                                                (32'hc98)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_39
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_39                                                (32'hc9c)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_40
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_40                                                (32'hca0)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_41
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_41                                                (32'hca4)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_42
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_42                                                (32'hca8)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_43
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_43                                                (32'hcac)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_44
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_44                                                (32'hcb0)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_45
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_45                                                (32'hcb4)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_46
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_46                                                (32'hcb8)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_47
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_47                                                (32'hcbc)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_48
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_48                                                (32'hcc0)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_49
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_49                                                (32'hcc4)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_50
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_50                                                (32'hcc8)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_51
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_51                                                (32'hccc)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_52
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_52                                                (32'hcd0)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_53
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_53                                                (32'hcd4)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_54
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_54                                                (32'hcd8)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_55
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_55                                                (32'hcdc)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_56
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_56                                                (32'hce0)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_57
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_57                                                (32'hce4)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_58
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_58                                                (32'hce8)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_59
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_59                                                (32'hcec)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_60
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_60                                                (32'hcf0)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_61
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_61                                                (32'hcf4)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_62
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_62                                                (32'hcf8)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_63
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_63                                                (32'hcfc)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_64
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_64                                                (32'hd00)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_65
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_65                                                (32'hd04)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_66
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_66                                                (32'hd08)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_67
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_67                                                (32'hd0c)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_68
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_68                                                (32'hd10)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_69
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_69                                                (32'hd14)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_70
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_70                                                (32'hd18)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_71
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_71                                                (32'hd1c)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_72
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_72                                                (32'hd20)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_73
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_73                                                (32'hd24)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_74
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_74                                                (32'hd28)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_75
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_75                                                (32'hd2c)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_76
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_76                                                (32'hd30)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_77
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_77                                                (32'hd34)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_78
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_78                                                (32'hd38)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_79
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_79                                                (32'hd3c)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_80
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_80                                                (32'hd40)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_81
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_81                                                (32'hd44)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_82
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_82                                                (32'hd48)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_83
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_83                                                (32'hd4c)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_84
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_84                                                (32'hd50)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_85
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_85                                                (32'hd54)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_86
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_86                                                (32'hd58)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_87
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_87                                                (32'hd5c)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_88
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_88                                                (32'hd60)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_89
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_89                                                (32'hd64)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_90
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_90                                                (32'hd68)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_91
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_91                                                (32'hd6c)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_92
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_92                                                (32'hd70)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_93
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_93                                                (32'hd74)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_94
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_94                                                (32'hd78)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_95
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_95                                                (32'hd7c)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_96
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_96                                                (32'hd80)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_97
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_97                                                (32'hd84)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_98
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_98                                                (32'hd88)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_99
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_99                                                (32'hd8c)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_100
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_100                                               (32'hd90)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_101
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_101                                               (32'hd94)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_102
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_102                                               (32'hd98)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_103
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_103                                               (32'hd9c)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_104
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_104                                               (32'hda0)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_105
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_105                                               (32'hda4)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_106
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_106                                               (32'hda8)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_107
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_107                                               (32'hdac)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_108
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_108                                               (32'hdb0)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_109
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_109                                               (32'hdb4)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_110
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_110                                               (32'hdb8)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_111
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_111                                               (32'hdbc)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_112
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_112                                               (32'hdc0)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_113
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_113                                               (32'hdc4)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_114
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_114                                               (32'hdc8)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_115
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_115                                               (32'hdcc)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_116
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_116                                               (32'hdd0)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_117
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_117                                               (32'hdd4)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_118
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_118                                               (32'hdd8)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_119
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_119                                               (32'hddc)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_120
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_120                                               (32'hde0)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_121
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_121                                               (32'hde4)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_122
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_122                                               (32'hde8)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_123
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_123                                               (32'hdec)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_124
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_124                                               (32'hdf0)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_125
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_125                                               (32'hdf4)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_126
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_126                                               (32'hdf8)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_127
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_127                                               (32'hdfc)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_128
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_128                                               (32'he00)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_129
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_129                                               (32'he04)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_130
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_130                                               (32'he08)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_131
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_131                                               (32'he0c)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_132
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_132                                               (32'he10)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_133
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_133                                               (32'he14)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_134
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_134                                               (32'he18)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_135
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_135                                               (32'he1c)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_136
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_136                                               (32'he20)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_137
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_137                                               (32'he24)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_138
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_138                                               (32'he28)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_139
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_139                                               (32'he2c)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_140
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_140                                               (32'he30)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_141
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_141                                               (32'he34)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_142
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_142                                               (32'he38)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_143
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_143                                               (32'he3c)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_144
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_144                                               (32'he40)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_145
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_145                                               (32'he44)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_146
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_146                                               (32'he48)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_147
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_147                                               (32'he4c)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_148
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_148                                               (32'he50)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_149
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_149                                               (32'he54)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_150
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_150                                               (32'he58)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_151
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_151                                               (32'he5c)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_152
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_152                                               (32'he60)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_153
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_153                                               (32'he64)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_154
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_154                                               (32'he68)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_155
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_155                                               (32'he6c)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_156
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_156                                               (32'he70)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_157
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_157                                               (32'he74)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_158
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_158                                               (32'he78)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_159
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_159                                               (32'he7c)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_160
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_160                                               (32'he80)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_161
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_161                                               (32'he84)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_162
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_162                                               (32'he88)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_163
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_163                                               (32'he8c)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_164
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_164                                               (32'he90)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_165
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_165                                               (32'he94)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_166
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_166                                               (32'he98)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_167
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_167                                               (32'he9c)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_168
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_168                                               (32'hea0)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_169
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_169                                               (32'hea4)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_170
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_170                                               (32'hea8)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_171
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_171                                               (32'heac)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_172
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_172                                               (32'heb0)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_173
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_173                                               (32'heb4)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_174
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_174                                               (32'heb8)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_175
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_175                                               (32'hebc)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_176
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_176                                               (32'hec0)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_177
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_177                                               (32'hec4)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_178
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_178                                               (32'hec8)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_179
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_179                                               (32'hecc)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_180
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_180                                               (32'hed0)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_181
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_181                                               (32'hed4)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_182
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_182                                               (32'hed8)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_183
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_183                                               (32'hedc)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_184
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_184                                               (32'hee0)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_185
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_185                                               (32'hee4)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_186
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_186                                               (32'hee8)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_187
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_187                                               (32'heec)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_188
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_188                                               (32'hef0)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_189
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_189                                               (32'hef4)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_190
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_190                                               (32'hef8)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_191
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_191                                               (32'hefc)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_192
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_192                                               (32'hf00)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_193
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_193                                               (32'hf04)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_194
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_194                                               (32'hf08)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_195
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_195                                               (32'hf0c)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_196
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_196                                               (32'hf10)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_197
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_197                                               (32'hf14)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_198
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_198                                               (32'hf18)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_199
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_199                                               (32'hf1c)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_200
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_200                                               (32'hf20)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_201
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_201                                               (32'hf24)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_202
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_202                                               (32'hf28)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_203
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_203                                               (32'hf2c)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_204
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_204                                               (32'hf30)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_205
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_205                                               (32'hf34)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_206
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_206                                               (32'hf38)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_207
`define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_207                                               (32'hf3c)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SOC_LOCK
`define GENERIC_AND_FUSE_REG_STASH_BANK_SOC_LOCK                                                    (32'hf40)
`define GENERIC_AND_FUSE_REG_STASH_BANK_SOC_LOCK_LOCK_LOW                                           (0)
`define GENERIC_AND_FUSE_REG_STASH_BANK_SOC_LOCK_LOCK_MASK                                          (32'hff)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_END_STASH
`define GENERIC_AND_FUSE_REG_STASH_END_STASH                                                        (32'hf44)
`define GENERIC_AND_FUSE_REG_STASH_END_STASH_END_STASH_LOW                                          (0)
`define GENERIC_AND_FUSE_REG_STASH_END_STASH_END_STASH_MASK                                         (32'h1)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_CPTRA_LOCK
`define GENERIC_AND_FUSE_REG_STASH_BANK_CPTRA_LOCK                                                  (32'hf48)
`define GENERIC_AND_FUSE_REG_STASH_BANK_CPTRA_LOCK_CPTRA_LOCK_LOW                                   (0)
`define GENERIC_AND_FUSE_REG_STASH_BANK_CPTRA_LOCK_CPTRA_LOCK_MASK                                  (32'h1)
`endif
`ifndef GENERIC_AND_FUSE_REG_STASH_BANK_STATUS
`define GENERIC_AND_FUSE_REG_STASH_BANK_STATUS                                                      (32'hf4c)
`define GENERIC_AND_FUSE_REG_STASH_BANK_STATUS_SLOT_LOCKED_LOW                                      (0)
`define GENERIC_AND_FUSE_REG_STASH_BANK_STATUS_SLOT_LOCKED_MASK                                     (32'hff)
`define GENERIC_AND_FUSE_REG_STASH_BANK_STATUS_END_STASH_LOW                                        (8)
`define GENERIC_AND_FUSE_REG_STASH_BANK_STATUS_END_STASH_MASK                                       (32'h100)
`define GENERIC_AND_FUSE_REG_STASH_BANK_STATUS_CPTRA_LOCK_LOW                                       (9)
`define GENERIC_AND_FUSE_REG_STASH_BANK_STATUS_CPTRA_LOCK_MASK                                      (32'h200)
`endif


`endif