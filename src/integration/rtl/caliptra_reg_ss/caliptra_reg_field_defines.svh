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
`ifndef CALIPTRA_REG_FIELD_DEFINES_HEADER
`define CALIPTRA_REG_FIELD_DEFINES_HEADER


`ifndef DOE_REG_DOE_IV_0
`define DOE_REG_DOE_IV_0                                                                            (32'h0)
`endif
`ifndef DOE_REG_DOE_IV_1
`define DOE_REG_DOE_IV_1                                                                            (32'h4)
`endif
`ifndef DOE_REG_DOE_IV_2
`define DOE_REG_DOE_IV_2                                                                            (32'h8)
`endif
`ifndef DOE_REG_DOE_IV_3
`define DOE_REG_DOE_IV_3                                                                            (32'hc)
`endif
`ifndef DOE_REG_DOE_CTRL
`define DOE_REG_DOE_CTRL                                                                            (32'h10)
`define DOE_REG_DOE_CTRL_CMD_LOW                                                                    (0)
`define DOE_REG_DOE_CTRL_CMD_MASK                                                                   (32'h3)
`define DOE_REG_DOE_CTRL_DEST_LOW                                                                   (2)
`define DOE_REG_DOE_CTRL_DEST_MASK                                                                  (32'h7c)
`define DOE_REG_DOE_CTRL_CMD_EXT_LOW                                                                (7)
`define DOE_REG_DOE_CTRL_CMD_EXT_MASK                                                               (32'h180)
`endif
`ifndef DOE_REG_DOE_STATUS
`define DOE_REG_DOE_STATUS                                                                          (32'h14)
`define DOE_REG_DOE_STATUS_READY_LOW                                                                (0)
`define DOE_REG_DOE_STATUS_READY_MASK                                                               (32'h1)
`define DOE_REG_DOE_STATUS_VALID_LOW                                                                (1)
`define DOE_REG_DOE_STATUS_VALID_MASK                                                               (32'h2)
`define DOE_REG_DOE_STATUS_UDS_FLOW_DONE_LOW                                                        (2)
`define DOE_REG_DOE_STATUS_UDS_FLOW_DONE_MASK                                                       (32'h4)
`define DOE_REG_DOE_STATUS_FE_FLOW_DONE_LOW                                                         (3)
`define DOE_REG_DOE_STATUS_FE_FLOW_DONE_MASK                                                        (32'h8)
`define DOE_REG_DOE_STATUS_DEOBF_SECRETS_CLEARED_LOW                                                (4)
`define DOE_REG_DOE_STATUS_DEOBF_SECRETS_CLEARED_MASK                                               (32'h10)
`define DOE_REG_DOE_STATUS_HEK_FLOW_DONE_LOW                                                        (5)
`define DOE_REG_DOE_STATUS_HEK_FLOW_DONE_MASK                                                       (32'h20)
`define DOE_REG_DOE_STATUS_ERROR_LOW                                                                (8)
`define DOE_REG_DOE_STATUS_ERROR_MASK                                                               (32'h100)
`endif
`ifndef DOE_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R
`define DOE_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R                                                      (32'h800)
`define DOE_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_LOW                                         (0)
`define DOE_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_MASK                                        (32'h1)
`define DOE_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_LOW                                         (1)
`define DOE_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_MASK                                        (32'h2)
`endif
`ifndef DOE_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R
`define DOE_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R                                                       (32'h804)
`define DOE_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR0_EN_LOW                                         (0)
`define DOE_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR0_EN_MASK                                        (32'h1)
`define DOE_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR1_EN_LOW                                         (1)
`define DOE_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR1_EN_MASK                                        (32'h2)
`define DOE_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR2_EN_LOW                                         (2)
`define DOE_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR2_EN_MASK                                        (32'h4)
`define DOE_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR3_EN_LOW                                         (3)
`define DOE_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR3_EN_MASK                                        (32'h8)
`endif
`ifndef DOE_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R
`define DOE_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R                                                       (32'h808)
`define DOE_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_CMD_DONE_EN_LOW                                 (0)
`define DOE_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_CMD_DONE_EN_MASK                                (32'h1)
`endif
`ifndef DOE_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R
`define DOE_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R                                                   (32'h80c)
`define DOE_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS_LOW                                       (0)
`define DOE_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS_MASK                                      (32'h1)
`endif
`ifndef DOE_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R
`define DOE_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R                                                   (32'h810)
`define DOE_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS_LOW                                       (0)
`define DOE_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS_MASK                                      (32'h1)
`endif
`ifndef DOE_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R
`define DOE_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R                                                 (32'h814)
`define DOE_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR0_STS_LOW                                  (0)
`define DOE_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR0_STS_MASK                                 (32'h1)
`define DOE_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR1_STS_LOW                                  (1)
`define DOE_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR1_STS_MASK                                 (32'h2)
`define DOE_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR2_STS_LOW                                  (2)
`define DOE_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR2_STS_MASK                                 (32'h4)
`define DOE_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR3_STS_LOW                                  (3)
`define DOE_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR3_STS_MASK                                 (32'h8)
`endif
`ifndef DOE_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R
`define DOE_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R                                                 (32'h818)
`define DOE_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_LOW                          (0)
`define DOE_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK                         (32'h1)
`endif
`ifndef DOE_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R
`define DOE_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R                                                     (32'h81c)
`define DOE_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR0_TRIG_LOW                                     (0)
`define DOE_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR0_TRIG_MASK                                    (32'h1)
`define DOE_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR1_TRIG_LOW                                     (1)
`define DOE_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR1_TRIG_MASK                                    (32'h2)
`define DOE_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR2_TRIG_LOW                                     (2)
`define DOE_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR2_TRIG_MASK                                    (32'h4)
`define DOE_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR3_TRIG_LOW                                     (3)
`define DOE_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR3_TRIG_MASK                                    (32'h8)
`endif
`ifndef DOE_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R
`define DOE_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R                                                     (32'h820)
`define DOE_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_DONE_TRIG_LOW                             (0)
`define DOE_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_DONE_TRIG_MASK                            (32'h1)
`endif
`ifndef DOE_REG_INTR_BLOCK_RF_ERROR0_INTR_COUNT_R
`define DOE_REG_INTR_BLOCK_RF_ERROR0_INTR_COUNT_R                                                   (32'h900)
`endif
`ifndef DOE_REG_INTR_BLOCK_RF_ERROR1_INTR_COUNT_R
`define DOE_REG_INTR_BLOCK_RF_ERROR1_INTR_COUNT_R                                                   (32'h904)
`endif
`ifndef DOE_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_R
`define DOE_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_R                                                   (32'h908)
`endif
`ifndef DOE_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_R
`define DOE_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_R                                                   (32'h90c)
`endif
`ifndef DOE_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R
`define DOE_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R                                           (32'h980)
`endif
`ifndef DOE_REG_INTR_BLOCK_RF_ERROR0_INTR_COUNT_INCR_R
`define DOE_REG_INTR_BLOCK_RF_ERROR0_INTR_COUNT_INCR_R                                              (32'ha00)
`define DOE_REG_INTR_BLOCK_RF_ERROR0_INTR_COUNT_INCR_R_PULSE_LOW                                    (0)
`define DOE_REG_INTR_BLOCK_RF_ERROR0_INTR_COUNT_INCR_R_PULSE_MASK                                   (32'h1)
`endif
`ifndef DOE_REG_INTR_BLOCK_RF_ERROR1_INTR_COUNT_INCR_R
`define DOE_REG_INTR_BLOCK_RF_ERROR1_INTR_COUNT_INCR_R                                              (32'ha04)
`define DOE_REG_INTR_BLOCK_RF_ERROR1_INTR_COUNT_INCR_R_PULSE_LOW                                    (0)
`define DOE_REG_INTR_BLOCK_RF_ERROR1_INTR_COUNT_INCR_R_PULSE_MASK                                   (32'h1)
`endif
`ifndef DOE_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R
`define DOE_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R                                              (32'ha08)
`define DOE_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R_PULSE_LOW                                    (0)
`define DOE_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R_PULSE_MASK                                   (32'h1)
`endif
`ifndef DOE_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R
`define DOE_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R                                              (32'ha0c)
`define DOE_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R_PULSE_LOW                                    (0)
`define DOE_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R_PULSE_MASK                                   (32'h1)
`endif
`ifndef DOE_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R
`define DOE_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R                                      (32'ha10)
`define DOE_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R_PULSE_LOW                            (0)
`define DOE_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R_PULSE_MASK                           (32'h1)
`endif
`ifndef ECC_REG_ECC_NAME_0
`define ECC_REG_ECC_NAME_0                                                                          (32'h0)
`endif
`ifndef ECC_REG_ECC_NAME_1
`define ECC_REG_ECC_NAME_1                                                                          (32'h4)
`endif
`ifndef ECC_REG_ECC_VERSION_0
`define ECC_REG_ECC_VERSION_0                                                                       (32'h8)
`endif
`ifndef ECC_REG_ECC_VERSION_1
`define ECC_REG_ECC_VERSION_1                                                                       (32'hc)
`endif
`ifndef ECC_REG_ECC_CTRL
`define ECC_REG_ECC_CTRL                                                                            (32'h10)
`define ECC_REG_ECC_CTRL_CTRL_LOW                                                                   (0)
`define ECC_REG_ECC_CTRL_CTRL_MASK                                                                  (32'h3)
`define ECC_REG_ECC_CTRL_ZEROIZE_LOW                                                                (2)
`define ECC_REG_ECC_CTRL_ZEROIZE_MASK                                                               (32'h4)
`define ECC_REG_ECC_CTRL_PCR_SIGN_LOW                                                               (3)
`define ECC_REG_ECC_CTRL_PCR_SIGN_MASK                                                              (32'h8)
`define ECC_REG_ECC_CTRL_DH_SHAREDKEY_LOW                                                           (4)
`define ECC_REG_ECC_CTRL_DH_SHAREDKEY_MASK                                                          (32'h10)
`endif
`ifndef ECC_REG_ECC_STATUS
`define ECC_REG_ECC_STATUS                                                                          (32'h18)
`define ECC_REG_ECC_STATUS_READY_LOW                                                                (0)
`define ECC_REG_ECC_STATUS_READY_MASK                                                               (32'h1)
`define ECC_REG_ECC_STATUS_VALID_LOW                                                                (1)
`define ECC_REG_ECC_STATUS_VALID_MASK                                                               (32'h2)
`endif
`ifndef ECC_REG_ECC_SEED_0
`define ECC_REG_ECC_SEED_0                                                                          (32'h80)
`endif
`ifndef ECC_REG_ECC_SEED_1
`define ECC_REG_ECC_SEED_1                                                                          (32'h84)
`endif
`ifndef ECC_REG_ECC_SEED_2
`define ECC_REG_ECC_SEED_2                                                                          (32'h88)
`endif
`ifndef ECC_REG_ECC_SEED_3
`define ECC_REG_ECC_SEED_3                                                                          (32'h8c)
`endif
`ifndef ECC_REG_ECC_SEED_4
`define ECC_REG_ECC_SEED_4                                                                          (32'h90)
`endif
`ifndef ECC_REG_ECC_SEED_5
`define ECC_REG_ECC_SEED_5                                                                          (32'h94)
`endif
`ifndef ECC_REG_ECC_SEED_6
`define ECC_REG_ECC_SEED_6                                                                          (32'h98)
`endif
`ifndef ECC_REG_ECC_SEED_7
`define ECC_REG_ECC_SEED_7                                                                          (32'h9c)
`endif
`ifndef ECC_REG_ECC_SEED_8
`define ECC_REG_ECC_SEED_8                                                                          (32'ha0)
`endif
`ifndef ECC_REG_ECC_SEED_9
`define ECC_REG_ECC_SEED_9                                                                          (32'ha4)
`endif
`ifndef ECC_REG_ECC_SEED_10
`define ECC_REG_ECC_SEED_10                                                                         (32'ha8)
`endif
`ifndef ECC_REG_ECC_SEED_11
`define ECC_REG_ECC_SEED_11                                                                         (32'hac)
`endif
`ifndef ECC_REG_ECC_MSG_0
`define ECC_REG_ECC_MSG_0                                                                           (32'h100)
`endif
`ifndef ECC_REG_ECC_MSG_1
`define ECC_REG_ECC_MSG_1                                                                           (32'h104)
`endif
`ifndef ECC_REG_ECC_MSG_2
`define ECC_REG_ECC_MSG_2                                                                           (32'h108)
`endif
`ifndef ECC_REG_ECC_MSG_3
`define ECC_REG_ECC_MSG_3                                                                           (32'h10c)
`endif
`ifndef ECC_REG_ECC_MSG_4
`define ECC_REG_ECC_MSG_4                                                                           (32'h110)
`endif
`ifndef ECC_REG_ECC_MSG_5
`define ECC_REG_ECC_MSG_5                                                                           (32'h114)
`endif
`ifndef ECC_REG_ECC_MSG_6
`define ECC_REG_ECC_MSG_6                                                                           (32'h118)
`endif
`ifndef ECC_REG_ECC_MSG_7
`define ECC_REG_ECC_MSG_7                                                                           (32'h11c)
`endif
`ifndef ECC_REG_ECC_MSG_8
`define ECC_REG_ECC_MSG_8                                                                           (32'h120)
`endif
`ifndef ECC_REG_ECC_MSG_9
`define ECC_REG_ECC_MSG_9                                                                           (32'h124)
`endif
`ifndef ECC_REG_ECC_MSG_10
`define ECC_REG_ECC_MSG_10                                                                          (32'h128)
`endif
`ifndef ECC_REG_ECC_MSG_11
`define ECC_REG_ECC_MSG_11                                                                          (32'h12c)
`endif
`ifndef ECC_REG_ECC_PRIVKEY_OUT_0
`define ECC_REG_ECC_PRIVKEY_OUT_0                                                                   (32'h180)
`endif
`ifndef ECC_REG_ECC_PRIVKEY_OUT_1
`define ECC_REG_ECC_PRIVKEY_OUT_1                                                                   (32'h184)
`endif
`ifndef ECC_REG_ECC_PRIVKEY_OUT_2
`define ECC_REG_ECC_PRIVKEY_OUT_2                                                                   (32'h188)
`endif
`ifndef ECC_REG_ECC_PRIVKEY_OUT_3
`define ECC_REG_ECC_PRIVKEY_OUT_3                                                                   (32'h18c)
`endif
`ifndef ECC_REG_ECC_PRIVKEY_OUT_4
`define ECC_REG_ECC_PRIVKEY_OUT_4                                                                   (32'h190)
`endif
`ifndef ECC_REG_ECC_PRIVKEY_OUT_5
`define ECC_REG_ECC_PRIVKEY_OUT_5                                                                   (32'h194)
`endif
`ifndef ECC_REG_ECC_PRIVKEY_OUT_6
`define ECC_REG_ECC_PRIVKEY_OUT_6                                                                   (32'h198)
`endif
`ifndef ECC_REG_ECC_PRIVKEY_OUT_7
`define ECC_REG_ECC_PRIVKEY_OUT_7                                                                   (32'h19c)
`endif
`ifndef ECC_REG_ECC_PRIVKEY_OUT_8
`define ECC_REG_ECC_PRIVKEY_OUT_8                                                                   (32'h1a0)
`endif
`ifndef ECC_REG_ECC_PRIVKEY_OUT_9
`define ECC_REG_ECC_PRIVKEY_OUT_9                                                                   (32'h1a4)
`endif
`ifndef ECC_REG_ECC_PRIVKEY_OUT_10
`define ECC_REG_ECC_PRIVKEY_OUT_10                                                                  (32'h1a8)
`endif
`ifndef ECC_REG_ECC_PRIVKEY_OUT_11
`define ECC_REG_ECC_PRIVKEY_OUT_11                                                                  (32'h1ac)
`endif
`ifndef ECC_REG_ECC_PUBKEY_X_0
`define ECC_REG_ECC_PUBKEY_X_0                                                                      (32'h200)
`endif
`ifndef ECC_REG_ECC_PUBKEY_X_1
`define ECC_REG_ECC_PUBKEY_X_1                                                                      (32'h204)
`endif
`ifndef ECC_REG_ECC_PUBKEY_X_2
`define ECC_REG_ECC_PUBKEY_X_2                                                                      (32'h208)
`endif
`ifndef ECC_REG_ECC_PUBKEY_X_3
`define ECC_REG_ECC_PUBKEY_X_3                                                                      (32'h20c)
`endif
`ifndef ECC_REG_ECC_PUBKEY_X_4
`define ECC_REG_ECC_PUBKEY_X_4                                                                      (32'h210)
`endif
`ifndef ECC_REG_ECC_PUBKEY_X_5
`define ECC_REG_ECC_PUBKEY_X_5                                                                      (32'h214)
`endif
`ifndef ECC_REG_ECC_PUBKEY_X_6
`define ECC_REG_ECC_PUBKEY_X_6                                                                      (32'h218)
`endif
`ifndef ECC_REG_ECC_PUBKEY_X_7
`define ECC_REG_ECC_PUBKEY_X_7                                                                      (32'h21c)
`endif
`ifndef ECC_REG_ECC_PUBKEY_X_8
`define ECC_REG_ECC_PUBKEY_X_8                                                                      (32'h220)
`endif
`ifndef ECC_REG_ECC_PUBKEY_X_9
`define ECC_REG_ECC_PUBKEY_X_9                                                                      (32'h224)
`endif
`ifndef ECC_REG_ECC_PUBKEY_X_10
`define ECC_REG_ECC_PUBKEY_X_10                                                                     (32'h228)
`endif
`ifndef ECC_REG_ECC_PUBKEY_X_11
`define ECC_REG_ECC_PUBKEY_X_11                                                                     (32'h22c)
`endif
`ifndef ECC_REG_ECC_PUBKEY_Y_0
`define ECC_REG_ECC_PUBKEY_Y_0                                                                      (32'h280)
`endif
`ifndef ECC_REG_ECC_PUBKEY_Y_1
`define ECC_REG_ECC_PUBKEY_Y_1                                                                      (32'h284)
`endif
`ifndef ECC_REG_ECC_PUBKEY_Y_2
`define ECC_REG_ECC_PUBKEY_Y_2                                                                      (32'h288)
`endif
`ifndef ECC_REG_ECC_PUBKEY_Y_3
`define ECC_REG_ECC_PUBKEY_Y_3                                                                      (32'h28c)
`endif
`ifndef ECC_REG_ECC_PUBKEY_Y_4
`define ECC_REG_ECC_PUBKEY_Y_4                                                                      (32'h290)
`endif
`ifndef ECC_REG_ECC_PUBKEY_Y_5
`define ECC_REG_ECC_PUBKEY_Y_5                                                                      (32'h294)
`endif
`ifndef ECC_REG_ECC_PUBKEY_Y_6
`define ECC_REG_ECC_PUBKEY_Y_6                                                                      (32'h298)
`endif
`ifndef ECC_REG_ECC_PUBKEY_Y_7
`define ECC_REG_ECC_PUBKEY_Y_7                                                                      (32'h29c)
`endif
`ifndef ECC_REG_ECC_PUBKEY_Y_8
`define ECC_REG_ECC_PUBKEY_Y_8                                                                      (32'h2a0)
`endif
`ifndef ECC_REG_ECC_PUBKEY_Y_9
`define ECC_REG_ECC_PUBKEY_Y_9                                                                      (32'h2a4)
`endif
`ifndef ECC_REG_ECC_PUBKEY_Y_10
`define ECC_REG_ECC_PUBKEY_Y_10                                                                     (32'h2a8)
`endif
`ifndef ECC_REG_ECC_PUBKEY_Y_11
`define ECC_REG_ECC_PUBKEY_Y_11                                                                     (32'h2ac)
`endif
`ifndef ECC_REG_ECC_SIGN_R_0
`define ECC_REG_ECC_SIGN_R_0                                                                        (32'h300)
`endif
`ifndef ECC_REG_ECC_SIGN_R_1
`define ECC_REG_ECC_SIGN_R_1                                                                        (32'h304)
`endif
`ifndef ECC_REG_ECC_SIGN_R_2
`define ECC_REG_ECC_SIGN_R_2                                                                        (32'h308)
`endif
`ifndef ECC_REG_ECC_SIGN_R_3
`define ECC_REG_ECC_SIGN_R_3                                                                        (32'h30c)
`endif
`ifndef ECC_REG_ECC_SIGN_R_4
`define ECC_REG_ECC_SIGN_R_4                                                                        (32'h310)
`endif
`ifndef ECC_REG_ECC_SIGN_R_5
`define ECC_REG_ECC_SIGN_R_5                                                                        (32'h314)
`endif
`ifndef ECC_REG_ECC_SIGN_R_6
`define ECC_REG_ECC_SIGN_R_6                                                                        (32'h318)
`endif
`ifndef ECC_REG_ECC_SIGN_R_7
`define ECC_REG_ECC_SIGN_R_7                                                                        (32'h31c)
`endif
`ifndef ECC_REG_ECC_SIGN_R_8
`define ECC_REG_ECC_SIGN_R_8                                                                        (32'h320)
`endif
`ifndef ECC_REG_ECC_SIGN_R_9
`define ECC_REG_ECC_SIGN_R_9                                                                        (32'h324)
`endif
`ifndef ECC_REG_ECC_SIGN_R_10
`define ECC_REG_ECC_SIGN_R_10                                                                       (32'h328)
`endif
`ifndef ECC_REG_ECC_SIGN_R_11
`define ECC_REG_ECC_SIGN_R_11                                                                       (32'h32c)
`endif
`ifndef ECC_REG_ECC_SIGN_S_0
`define ECC_REG_ECC_SIGN_S_0                                                                        (32'h380)
`endif
`ifndef ECC_REG_ECC_SIGN_S_1
`define ECC_REG_ECC_SIGN_S_1                                                                        (32'h384)
`endif
`ifndef ECC_REG_ECC_SIGN_S_2
`define ECC_REG_ECC_SIGN_S_2                                                                        (32'h388)
`endif
`ifndef ECC_REG_ECC_SIGN_S_3
`define ECC_REG_ECC_SIGN_S_3                                                                        (32'h38c)
`endif
`ifndef ECC_REG_ECC_SIGN_S_4
`define ECC_REG_ECC_SIGN_S_4                                                                        (32'h390)
`endif
`ifndef ECC_REG_ECC_SIGN_S_5
`define ECC_REG_ECC_SIGN_S_5                                                                        (32'h394)
`endif
`ifndef ECC_REG_ECC_SIGN_S_6
`define ECC_REG_ECC_SIGN_S_6                                                                        (32'h398)
`endif
`ifndef ECC_REG_ECC_SIGN_S_7
`define ECC_REG_ECC_SIGN_S_7                                                                        (32'h39c)
`endif
`ifndef ECC_REG_ECC_SIGN_S_8
`define ECC_REG_ECC_SIGN_S_8                                                                        (32'h3a0)
`endif
`ifndef ECC_REG_ECC_SIGN_S_9
`define ECC_REG_ECC_SIGN_S_9                                                                        (32'h3a4)
`endif
`ifndef ECC_REG_ECC_SIGN_S_10
`define ECC_REG_ECC_SIGN_S_10                                                                       (32'h3a8)
`endif
`ifndef ECC_REG_ECC_SIGN_S_11
`define ECC_REG_ECC_SIGN_S_11                                                                       (32'h3ac)
`endif
`ifndef ECC_REG_ECC_VERIFY_R_0
`define ECC_REG_ECC_VERIFY_R_0                                                                      (32'h400)
`endif
`ifndef ECC_REG_ECC_VERIFY_R_1
`define ECC_REG_ECC_VERIFY_R_1                                                                      (32'h404)
`endif
`ifndef ECC_REG_ECC_VERIFY_R_2
`define ECC_REG_ECC_VERIFY_R_2                                                                      (32'h408)
`endif
`ifndef ECC_REG_ECC_VERIFY_R_3
`define ECC_REG_ECC_VERIFY_R_3                                                                      (32'h40c)
`endif
`ifndef ECC_REG_ECC_VERIFY_R_4
`define ECC_REG_ECC_VERIFY_R_4                                                                      (32'h410)
`endif
`ifndef ECC_REG_ECC_VERIFY_R_5
`define ECC_REG_ECC_VERIFY_R_5                                                                      (32'h414)
`endif
`ifndef ECC_REG_ECC_VERIFY_R_6
`define ECC_REG_ECC_VERIFY_R_6                                                                      (32'h418)
`endif
`ifndef ECC_REG_ECC_VERIFY_R_7
`define ECC_REG_ECC_VERIFY_R_7                                                                      (32'h41c)
`endif
`ifndef ECC_REG_ECC_VERIFY_R_8
`define ECC_REG_ECC_VERIFY_R_8                                                                      (32'h420)
`endif
`ifndef ECC_REG_ECC_VERIFY_R_9
`define ECC_REG_ECC_VERIFY_R_9                                                                      (32'h424)
`endif
`ifndef ECC_REG_ECC_VERIFY_R_10
`define ECC_REG_ECC_VERIFY_R_10                                                                     (32'h428)
`endif
`ifndef ECC_REG_ECC_VERIFY_R_11
`define ECC_REG_ECC_VERIFY_R_11                                                                     (32'h42c)
`endif
`ifndef ECC_REG_ECC_IV_0
`define ECC_REG_ECC_IV_0                                                                            (32'h480)
`endif
`ifndef ECC_REG_ECC_IV_1
`define ECC_REG_ECC_IV_1                                                                            (32'h484)
`endif
`ifndef ECC_REG_ECC_IV_2
`define ECC_REG_ECC_IV_2                                                                            (32'h488)
`endif
`ifndef ECC_REG_ECC_IV_3
`define ECC_REG_ECC_IV_3                                                                            (32'h48c)
`endif
`ifndef ECC_REG_ECC_IV_4
`define ECC_REG_ECC_IV_4                                                                            (32'h490)
`endif
`ifndef ECC_REG_ECC_IV_5
`define ECC_REG_ECC_IV_5                                                                            (32'h494)
`endif
`ifndef ECC_REG_ECC_IV_6
`define ECC_REG_ECC_IV_6                                                                            (32'h498)
`endif
`ifndef ECC_REG_ECC_IV_7
`define ECC_REG_ECC_IV_7                                                                            (32'h49c)
`endif
`ifndef ECC_REG_ECC_IV_8
`define ECC_REG_ECC_IV_8                                                                            (32'h4a0)
`endif
`ifndef ECC_REG_ECC_IV_9
`define ECC_REG_ECC_IV_9                                                                            (32'h4a4)
`endif
`ifndef ECC_REG_ECC_IV_10
`define ECC_REG_ECC_IV_10                                                                           (32'h4a8)
`endif
`ifndef ECC_REG_ECC_IV_11
`define ECC_REG_ECC_IV_11                                                                           (32'h4ac)
`endif
`ifndef ECC_REG_ECC_NONCE_0
`define ECC_REG_ECC_NONCE_0                                                                         (32'h500)
`endif
`ifndef ECC_REG_ECC_NONCE_1
`define ECC_REG_ECC_NONCE_1                                                                         (32'h504)
`endif
`ifndef ECC_REG_ECC_NONCE_2
`define ECC_REG_ECC_NONCE_2                                                                         (32'h508)
`endif
`ifndef ECC_REG_ECC_NONCE_3
`define ECC_REG_ECC_NONCE_3                                                                         (32'h50c)
`endif
`ifndef ECC_REG_ECC_NONCE_4
`define ECC_REG_ECC_NONCE_4                                                                         (32'h510)
`endif
`ifndef ECC_REG_ECC_NONCE_5
`define ECC_REG_ECC_NONCE_5                                                                         (32'h514)
`endif
`ifndef ECC_REG_ECC_NONCE_6
`define ECC_REG_ECC_NONCE_6                                                                         (32'h518)
`endif
`ifndef ECC_REG_ECC_NONCE_7
`define ECC_REG_ECC_NONCE_7                                                                         (32'h51c)
`endif
`ifndef ECC_REG_ECC_NONCE_8
`define ECC_REG_ECC_NONCE_8                                                                         (32'h520)
`endif
`ifndef ECC_REG_ECC_NONCE_9
`define ECC_REG_ECC_NONCE_9                                                                         (32'h524)
`endif
`ifndef ECC_REG_ECC_NONCE_10
`define ECC_REG_ECC_NONCE_10                                                                        (32'h528)
`endif
`ifndef ECC_REG_ECC_NONCE_11
`define ECC_REG_ECC_NONCE_11                                                                        (32'h52c)
`endif
`ifndef ECC_REG_ECC_PRIVKEY_IN_0
`define ECC_REG_ECC_PRIVKEY_IN_0                                                                    (32'h580)
`endif
`ifndef ECC_REG_ECC_PRIVKEY_IN_1
`define ECC_REG_ECC_PRIVKEY_IN_1                                                                    (32'h584)
`endif
`ifndef ECC_REG_ECC_PRIVKEY_IN_2
`define ECC_REG_ECC_PRIVKEY_IN_2                                                                    (32'h588)
`endif
`ifndef ECC_REG_ECC_PRIVKEY_IN_3
`define ECC_REG_ECC_PRIVKEY_IN_3                                                                    (32'h58c)
`endif
`ifndef ECC_REG_ECC_PRIVKEY_IN_4
`define ECC_REG_ECC_PRIVKEY_IN_4                                                                    (32'h590)
`endif
`ifndef ECC_REG_ECC_PRIVKEY_IN_5
`define ECC_REG_ECC_PRIVKEY_IN_5                                                                    (32'h594)
`endif
`ifndef ECC_REG_ECC_PRIVKEY_IN_6
`define ECC_REG_ECC_PRIVKEY_IN_6                                                                    (32'h598)
`endif
`ifndef ECC_REG_ECC_PRIVKEY_IN_7
`define ECC_REG_ECC_PRIVKEY_IN_7                                                                    (32'h59c)
`endif
`ifndef ECC_REG_ECC_PRIVKEY_IN_8
`define ECC_REG_ECC_PRIVKEY_IN_8                                                                    (32'h5a0)
`endif
`ifndef ECC_REG_ECC_PRIVKEY_IN_9
`define ECC_REG_ECC_PRIVKEY_IN_9                                                                    (32'h5a4)
`endif
`ifndef ECC_REG_ECC_PRIVKEY_IN_10
`define ECC_REG_ECC_PRIVKEY_IN_10                                                                   (32'h5a8)
`endif
`ifndef ECC_REG_ECC_PRIVKEY_IN_11
`define ECC_REG_ECC_PRIVKEY_IN_11                                                                   (32'h5ac)
`endif
`ifndef ECC_REG_ECC_DH_SHARED_KEY_0
`define ECC_REG_ECC_DH_SHARED_KEY_0                                                                 (32'h5c0)
`endif
`ifndef ECC_REG_ECC_DH_SHARED_KEY_1
`define ECC_REG_ECC_DH_SHARED_KEY_1                                                                 (32'h5c4)
`endif
`ifndef ECC_REG_ECC_DH_SHARED_KEY_2
`define ECC_REG_ECC_DH_SHARED_KEY_2                                                                 (32'h5c8)
`endif
`ifndef ECC_REG_ECC_DH_SHARED_KEY_3
`define ECC_REG_ECC_DH_SHARED_KEY_3                                                                 (32'h5cc)
`endif
`ifndef ECC_REG_ECC_DH_SHARED_KEY_4
`define ECC_REG_ECC_DH_SHARED_KEY_4                                                                 (32'h5d0)
`endif
`ifndef ECC_REG_ECC_DH_SHARED_KEY_5
`define ECC_REG_ECC_DH_SHARED_KEY_5                                                                 (32'h5d4)
`endif
`ifndef ECC_REG_ECC_DH_SHARED_KEY_6
`define ECC_REG_ECC_DH_SHARED_KEY_6                                                                 (32'h5d8)
`endif
`ifndef ECC_REG_ECC_DH_SHARED_KEY_7
`define ECC_REG_ECC_DH_SHARED_KEY_7                                                                 (32'h5dc)
`endif
`ifndef ECC_REG_ECC_DH_SHARED_KEY_8
`define ECC_REG_ECC_DH_SHARED_KEY_8                                                                 (32'h5e0)
`endif
`ifndef ECC_REG_ECC_DH_SHARED_KEY_9
`define ECC_REG_ECC_DH_SHARED_KEY_9                                                                 (32'h5e4)
`endif
`ifndef ECC_REG_ECC_DH_SHARED_KEY_10
`define ECC_REG_ECC_DH_SHARED_KEY_10                                                                (32'h5e8)
`endif
`ifndef ECC_REG_ECC_DH_SHARED_KEY_11
`define ECC_REG_ECC_DH_SHARED_KEY_11                                                                (32'h5ec)
`endif
`ifndef ECC_REG_ECC_KV_RD_PKEY_CTRL
`define ECC_REG_ECC_KV_RD_PKEY_CTRL                                                                 (32'h600)
`define ECC_REG_ECC_KV_RD_PKEY_CTRL_READ_EN_LOW                                                     (0)
`define ECC_REG_ECC_KV_RD_PKEY_CTRL_READ_EN_MASK                                                    (32'h1)
`define ECC_REG_ECC_KV_RD_PKEY_CTRL_READ_ENTRY_LOW                                                  (1)
`define ECC_REG_ECC_KV_RD_PKEY_CTRL_READ_ENTRY_MASK                                                 (32'h3e)
`define ECC_REG_ECC_KV_RD_PKEY_CTRL_PCR_HASH_EXTEND_LOW                                             (6)
`define ECC_REG_ECC_KV_RD_PKEY_CTRL_PCR_HASH_EXTEND_MASK                                            (32'h40)
`define ECC_REG_ECC_KV_RD_PKEY_CTRL_RSVD_LOW                                                        (7)
`define ECC_REG_ECC_KV_RD_PKEY_CTRL_RSVD_MASK                                                       (32'hffffff80)
`endif
`ifndef ECC_REG_ECC_KV_RD_PKEY_STATUS
`define ECC_REG_ECC_KV_RD_PKEY_STATUS                                                               (32'h604)
`define ECC_REG_ECC_KV_RD_PKEY_STATUS_READY_LOW                                                     (0)
`define ECC_REG_ECC_KV_RD_PKEY_STATUS_READY_MASK                                                    (32'h1)
`define ECC_REG_ECC_KV_RD_PKEY_STATUS_VALID_LOW                                                     (1)
`define ECC_REG_ECC_KV_RD_PKEY_STATUS_VALID_MASK                                                    (32'h2)
`define ECC_REG_ECC_KV_RD_PKEY_STATUS_ERROR_LOW                                                     (2)
`define ECC_REG_ECC_KV_RD_PKEY_STATUS_ERROR_MASK                                                    (32'h3fc)
`endif
`ifndef ECC_REG_ECC_KV_RD_SEED_CTRL
`define ECC_REG_ECC_KV_RD_SEED_CTRL                                                                 (32'h608)
`define ECC_REG_ECC_KV_RD_SEED_CTRL_READ_EN_LOW                                                     (0)
`define ECC_REG_ECC_KV_RD_SEED_CTRL_READ_EN_MASK                                                    (32'h1)
`define ECC_REG_ECC_KV_RD_SEED_CTRL_READ_ENTRY_LOW                                                  (1)
`define ECC_REG_ECC_KV_RD_SEED_CTRL_READ_ENTRY_MASK                                                 (32'h3e)
`define ECC_REG_ECC_KV_RD_SEED_CTRL_PCR_HASH_EXTEND_LOW                                             (6)
`define ECC_REG_ECC_KV_RD_SEED_CTRL_PCR_HASH_EXTEND_MASK                                            (32'h40)
`define ECC_REG_ECC_KV_RD_SEED_CTRL_RSVD_LOW                                                        (7)
`define ECC_REG_ECC_KV_RD_SEED_CTRL_RSVD_MASK                                                       (32'hffffff80)
`endif
`ifndef ECC_REG_ECC_KV_RD_SEED_STATUS
`define ECC_REG_ECC_KV_RD_SEED_STATUS                                                               (32'h60c)
`define ECC_REG_ECC_KV_RD_SEED_STATUS_READY_LOW                                                     (0)
`define ECC_REG_ECC_KV_RD_SEED_STATUS_READY_MASK                                                    (32'h1)
`define ECC_REG_ECC_KV_RD_SEED_STATUS_VALID_LOW                                                     (1)
`define ECC_REG_ECC_KV_RD_SEED_STATUS_VALID_MASK                                                    (32'h2)
`define ECC_REG_ECC_KV_RD_SEED_STATUS_ERROR_LOW                                                     (2)
`define ECC_REG_ECC_KV_RD_SEED_STATUS_ERROR_MASK                                                    (32'h3fc)
`endif
`ifndef ECC_REG_ECC_KV_WR_PKEY_CTRL
`define ECC_REG_ECC_KV_WR_PKEY_CTRL                                                                 (32'h610)
`define ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_EN_LOW                                                    (0)
`define ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_EN_MASK                                                   (32'h1)
`define ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_ENTRY_LOW                                                 (1)
`define ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_ENTRY_MASK                                                (32'h3e)
`define ECC_REG_ECC_KV_WR_PKEY_CTRL_HMAC_KEY_DEST_VALID_LOW                                         (6)
`define ECC_REG_ECC_KV_WR_PKEY_CTRL_HMAC_KEY_DEST_VALID_MASK                                        (32'h40)
`define ECC_REG_ECC_KV_WR_PKEY_CTRL_HMAC_BLOCK_DEST_VALID_LOW                                       (7)
`define ECC_REG_ECC_KV_WR_PKEY_CTRL_HMAC_BLOCK_DEST_VALID_MASK                                      (32'h80)
`define ECC_REG_ECC_KV_WR_PKEY_CTRL_MLDSA_SEED_DEST_VALID_LOW                                       (8)
`define ECC_REG_ECC_KV_WR_PKEY_CTRL_MLDSA_SEED_DEST_VALID_MASK                                      (32'h100)
`define ECC_REG_ECC_KV_WR_PKEY_CTRL_ECC_PKEY_DEST_VALID_LOW                                         (9)
`define ECC_REG_ECC_KV_WR_PKEY_CTRL_ECC_PKEY_DEST_VALID_MASK                                        (32'h200)
`define ECC_REG_ECC_KV_WR_PKEY_CTRL_ECC_SEED_DEST_VALID_LOW                                         (10)
`define ECC_REG_ECC_KV_WR_PKEY_CTRL_ECC_SEED_DEST_VALID_MASK                                        (32'h400)
`define ECC_REG_ECC_KV_WR_PKEY_CTRL_AES_KEY_DEST_VALID_LOW                                          (11)
`define ECC_REG_ECC_KV_WR_PKEY_CTRL_AES_KEY_DEST_VALID_MASK                                         (32'h800)
`define ECC_REG_ECC_KV_WR_PKEY_CTRL_MLKEM_SEED_DEST_VALID_LOW                                       (12)
`define ECC_REG_ECC_KV_WR_PKEY_CTRL_MLKEM_SEED_DEST_VALID_MASK                                      (32'h1000)
`define ECC_REG_ECC_KV_WR_PKEY_CTRL_MLKEM_MSG_DEST_VALID_LOW                                        (13)
`define ECC_REG_ECC_KV_WR_PKEY_CTRL_MLKEM_MSG_DEST_VALID_MASK                                       (32'h2000)
`define ECC_REG_ECC_KV_WR_PKEY_CTRL_DMA_DATA_DEST_VALID_LOW                                         (14)
`define ECC_REG_ECC_KV_WR_PKEY_CTRL_DMA_DATA_DEST_VALID_MASK                                        (32'h4000)
`define ECC_REG_ECC_KV_WR_PKEY_CTRL_RSVD_LOW                                                        (15)
`define ECC_REG_ECC_KV_WR_PKEY_CTRL_RSVD_MASK                                                       (32'hffff8000)
`endif
`ifndef ECC_REG_ECC_KV_WR_PKEY_STATUS
`define ECC_REG_ECC_KV_WR_PKEY_STATUS                                                               (32'h614)
`define ECC_REG_ECC_KV_WR_PKEY_STATUS_READY_LOW                                                     (0)
`define ECC_REG_ECC_KV_WR_PKEY_STATUS_READY_MASK                                                    (32'h1)
`define ECC_REG_ECC_KV_WR_PKEY_STATUS_VALID_LOW                                                     (1)
`define ECC_REG_ECC_KV_WR_PKEY_STATUS_VALID_MASK                                                    (32'h2)
`define ECC_REG_ECC_KV_WR_PKEY_STATUS_ERROR_LOW                                                     (2)
`define ECC_REG_ECC_KV_WR_PKEY_STATUS_ERROR_MASK                                                    (32'h3fc)
`endif
`ifndef ECC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R
`define ECC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R                                                      (32'h800)
`define ECC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_LOW                                         (0)
`define ECC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_MASK                                        (32'h1)
`define ECC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_LOW                                         (1)
`define ECC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_MASK                                        (32'h2)
`endif
`ifndef ECC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R
`define ECC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R                                                       (32'h804)
`define ECC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_INTERNAL_EN_LOW                                 (0)
`define ECC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_INTERNAL_EN_MASK                                (32'h1)
`endif
`ifndef ECC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R
`define ECC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R                                                       (32'h808)
`define ECC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_CMD_DONE_EN_LOW                                 (0)
`define ECC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_CMD_DONE_EN_MASK                                (32'h1)
`endif
`ifndef ECC_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R
`define ECC_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R                                                   (32'h80c)
`define ECC_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS_LOW                                       (0)
`define ECC_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS_MASK                                      (32'h1)
`endif
`ifndef ECC_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R
`define ECC_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R                                                   (32'h810)
`define ECC_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS_LOW                                       (0)
`define ECC_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS_MASK                                      (32'h1)
`endif
`ifndef ECC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R
`define ECC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R                                                 (32'h814)
`define ECC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_INTERNAL_STS_LOW                          (0)
`define ECC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_INTERNAL_STS_MASK                         (32'h1)
`endif
`ifndef ECC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R
`define ECC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R                                                 (32'h818)
`define ECC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_LOW                          (0)
`define ECC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK                         (32'h1)
`endif
`ifndef ECC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R
`define ECC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R                                                     (32'h81c)
`define ECC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_INTERNAL_TRIG_LOW                             (0)
`define ECC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_INTERNAL_TRIG_MASK                            (32'h1)
`endif
`ifndef ECC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R
`define ECC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R                                                     (32'h820)
`define ECC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_DONE_TRIG_LOW                             (0)
`define ECC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_DONE_TRIG_MASK                            (32'h1)
`endif
`ifndef ECC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_R
`define ECC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_R                                           (32'h900)
`endif
`ifndef ECC_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R
`define ECC_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R                                           (32'h980)
`endif
`ifndef ECC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R
`define ECC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R                                      (32'ha00)
`define ECC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R_PULSE_LOW                            (0)
`define ECC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R_PULSE_MASK                           (32'h1)
`endif
`ifndef ECC_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R
`define ECC_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R                                      (32'ha04)
`define ECC_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R_PULSE_LOW                            (0)
`define ECC_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R_PULSE_MASK                           (32'h1)
`endif
`ifndef HMAC_REG_HMAC512_NAME_0
`define HMAC_REG_HMAC512_NAME_0                                                                     (32'h0)
`endif
`ifndef HMAC_REG_HMAC512_NAME_1
`define HMAC_REG_HMAC512_NAME_1                                                                     (32'h4)
`endif
`ifndef HMAC_REG_HMAC512_VERSION_0
`define HMAC_REG_HMAC512_VERSION_0                                                                  (32'h8)
`endif
`ifndef HMAC_REG_HMAC512_VERSION_1
`define HMAC_REG_HMAC512_VERSION_1                                                                  (32'hc)
`endif
`ifndef HMAC_REG_HMAC512_CTRL
`define HMAC_REG_HMAC512_CTRL                                                                       (32'h10)
`define HMAC_REG_HMAC512_CTRL_INIT_LOW                                                              (0)
`define HMAC_REG_HMAC512_CTRL_INIT_MASK                                                             (32'h1)
`define HMAC_REG_HMAC512_CTRL_NEXT_LOW                                                              (1)
`define HMAC_REG_HMAC512_CTRL_NEXT_MASK                                                             (32'h2)
`define HMAC_REG_HMAC512_CTRL_ZEROIZE_LOW                                                           (2)
`define HMAC_REG_HMAC512_CTRL_ZEROIZE_MASK                                                          (32'h4)
`define HMAC_REG_HMAC512_CTRL_MODE_LOW                                                              (3)
`define HMAC_REG_HMAC512_CTRL_MODE_MASK                                                             (32'h8)
`define HMAC_REG_HMAC512_CTRL_CSR_MODE_LOW                                                          (4)
`define HMAC_REG_HMAC512_CTRL_CSR_MODE_MASK                                                         (32'h10)
`define HMAC_REG_HMAC512_CTRL_RESERVED_LOW                                                          (5)
`define HMAC_REG_HMAC512_CTRL_RESERVED_MASK                                                         (32'h20)
`endif
`ifndef HMAC_REG_HMAC512_STATUS
`define HMAC_REG_HMAC512_STATUS                                                                     (32'h18)
`define HMAC_REG_HMAC512_STATUS_READY_LOW                                                           (0)
`define HMAC_REG_HMAC512_STATUS_READY_MASK                                                          (32'h1)
`define HMAC_REG_HMAC512_STATUS_VALID_LOW                                                           (1)
`define HMAC_REG_HMAC512_STATUS_VALID_MASK                                                          (32'h2)
`endif
`ifndef HMAC_REG_HMAC512_KEY_0
`define HMAC_REG_HMAC512_KEY_0                                                                      (32'h40)
`endif
`ifndef HMAC_REG_HMAC512_KEY_1
`define HMAC_REG_HMAC512_KEY_1                                                                      (32'h44)
`endif
`ifndef HMAC_REG_HMAC512_KEY_2
`define HMAC_REG_HMAC512_KEY_2                                                                      (32'h48)
`endif
`ifndef HMAC_REG_HMAC512_KEY_3
`define HMAC_REG_HMAC512_KEY_3                                                                      (32'h4c)
`endif
`ifndef HMAC_REG_HMAC512_KEY_4
`define HMAC_REG_HMAC512_KEY_4                                                                      (32'h50)
`endif
`ifndef HMAC_REG_HMAC512_KEY_5
`define HMAC_REG_HMAC512_KEY_5                                                                      (32'h54)
`endif
`ifndef HMAC_REG_HMAC512_KEY_6
`define HMAC_REG_HMAC512_KEY_6                                                                      (32'h58)
`endif
`ifndef HMAC_REG_HMAC512_KEY_7
`define HMAC_REG_HMAC512_KEY_7                                                                      (32'h5c)
`endif
`ifndef HMAC_REG_HMAC512_KEY_8
`define HMAC_REG_HMAC512_KEY_8                                                                      (32'h60)
`endif
`ifndef HMAC_REG_HMAC512_KEY_9
`define HMAC_REG_HMAC512_KEY_9                                                                      (32'h64)
`endif
`ifndef HMAC_REG_HMAC512_KEY_10
`define HMAC_REG_HMAC512_KEY_10                                                                     (32'h68)
`endif
`ifndef HMAC_REG_HMAC512_KEY_11
`define HMAC_REG_HMAC512_KEY_11                                                                     (32'h6c)
`endif
`ifndef HMAC_REG_HMAC512_KEY_12
`define HMAC_REG_HMAC512_KEY_12                                                                     (32'h70)
`endif
`ifndef HMAC_REG_HMAC512_KEY_13
`define HMAC_REG_HMAC512_KEY_13                                                                     (32'h74)
`endif
`ifndef HMAC_REG_HMAC512_KEY_14
`define HMAC_REG_HMAC512_KEY_14                                                                     (32'h78)
`endif
`ifndef HMAC_REG_HMAC512_KEY_15
`define HMAC_REG_HMAC512_KEY_15                                                                     (32'h7c)
`endif
`ifndef HMAC_REG_HMAC512_BLOCK_0
`define HMAC_REG_HMAC512_BLOCK_0                                                                    (32'h80)
`endif
`ifndef HMAC_REG_HMAC512_BLOCK_1
`define HMAC_REG_HMAC512_BLOCK_1                                                                    (32'h84)
`endif
`ifndef HMAC_REG_HMAC512_BLOCK_2
`define HMAC_REG_HMAC512_BLOCK_2                                                                    (32'h88)
`endif
`ifndef HMAC_REG_HMAC512_BLOCK_3
`define HMAC_REG_HMAC512_BLOCK_3                                                                    (32'h8c)
`endif
`ifndef HMAC_REG_HMAC512_BLOCK_4
`define HMAC_REG_HMAC512_BLOCK_4                                                                    (32'h90)
`endif
`ifndef HMAC_REG_HMAC512_BLOCK_5
`define HMAC_REG_HMAC512_BLOCK_5                                                                    (32'h94)
`endif
`ifndef HMAC_REG_HMAC512_BLOCK_6
`define HMAC_REG_HMAC512_BLOCK_6                                                                    (32'h98)
`endif
`ifndef HMAC_REG_HMAC512_BLOCK_7
`define HMAC_REG_HMAC512_BLOCK_7                                                                    (32'h9c)
`endif
`ifndef HMAC_REG_HMAC512_BLOCK_8
`define HMAC_REG_HMAC512_BLOCK_8                                                                    (32'ha0)
`endif
`ifndef HMAC_REG_HMAC512_BLOCK_9
`define HMAC_REG_HMAC512_BLOCK_9                                                                    (32'ha4)
`endif
`ifndef HMAC_REG_HMAC512_BLOCK_10
`define HMAC_REG_HMAC512_BLOCK_10                                                                   (32'ha8)
`endif
`ifndef HMAC_REG_HMAC512_BLOCK_11
`define HMAC_REG_HMAC512_BLOCK_11                                                                   (32'hac)
`endif
`ifndef HMAC_REG_HMAC512_BLOCK_12
`define HMAC_REG_HMAC512_BLOCK_12                                                                   (32'hb0)
`endif
`ifndef HMAC_REG_HMAC512_BLOCK_13
`define HMAC_REG_HMAC512_BLOCK_13                                                                   (32'hb4)
`endif
`ifndef HMAC_REG_HMAC512_BLOCK_14
`define HMAC_REG_HMAC512_BLOCK_14                                                                   (32'hb8)
`endif
`ifndef HMAC_REG_HMAC512_BLOCK_15
`define HMAC_REG_HMAC512_BLOCK_15                                                                   (32'hbc)
`endif
`ifndef HMAC_REG_HMAC512_BLOCK_16
`define HMAC_REG_HMAC512_BLOCK_16                                                                   (32'hc0)
`endif
`ifndef HMAC_REG_HMAC512_BLOCK_17
`define HMAC_REG_HMAC512_BLOCK_17                                                                   (32'hc4)
`endif
`ifndef HMAC_REG_HMAC512_BLOCK_18
`define HMAC_REG_HMAC512_BLOCK_18                                                                   (32'hc8)
`endif
`ifndef HMAC_REG_HMAC512_BLOCK_19
`define HMAC_REG_HMAC512_BLOCK_19                                                                   (32'hcc)
`endif
`ifndef HMAC_REG_HMAC512_BLOCK_20
`define HMAC_REG_HMAC512_BLOCK_20                                                                   (32'hd0)
`endif
`ifndef HMAC_REG_HMAC512_BLOCK_21
`define HMAC_REG_HMAC512_BLOCK_21                                                                   (32'hd4)
`endif
`ifndef HMAC_REG_HMAC512_BLOCK_22
`define HMAC_REG_HMAC512_BLOCK_22                                                                   (32'hd8)
`endif
`ifndef HMAC_REG_HMAC512_BLOCK_23
`define HMAC_REG_HMAC512_BLOCK_23                                                                   (32'hdc)
`endif
`ifndef HMAC_REG_HMAC512_BLOCK_24
`define HMAC_REG_HMAC512_BLOCK_24                                                                   (32'he0)
`endif
`ifndef HMAC_REG_HMAC512_BLOCK_25
`define HMAC_REG_HMAC512_BLOCK_25                                                                   (32'he4)
`endif
`ifndef HMAC_REG_HMAC512_BLOCK_26
`define HMAC_REG_HMAC512_BLOCK_26                                                                   (32'he8)
`endif
`ifndef HMAC_REG_HMAC512_BLOCK_27
`define HMAC_REG_HMAC512_BLOCK_27                                                                   (32'hec)
`endif
`ifndef HMAC_REG_HMAC512_BLOCK_28
`define HMAC_REG_HMAC512_BLOCK_28                                                                   (32'hf0)
`endif
`ifndef HMAC_REG_HMAC512_BLOCK_29
`define HMAC_REG_HMAC512_BLOCK_29                                                                   (32'hf4)
`endif
`ifndef HMAC_REG_HMAC512_BLOCK_30
`define HMAC_REG_HMAC512_BLOCK_30                                                                   (32'hf8)
`endif
`ifndef HMAC_REG_HMAC512_BLOCK_31
`define HMAC_REG_HMAC512_BLOCK_31                                                                   (32'hfc)
`endif
`ifndef HMAC_REG_HMAC512_TAG_0
`define HMAC_REG_HMAC512_TAG_0                                                                      (32'h100)
`endif
`ifndef HMAC_REG_HMAC512_TAG_1
`define HMAC_REG_HMAC512_TAG_1                                                                      (32'h104)
`endif
`ifndef HMAC_REG_HMAC512_TAG_2
`define HMAC_REG_HMAC512_TAG_2                                                                      (32'h108)
`endif
`ifndef HMAC_REG_HMAC512_TAG_3
`define HMAC_REG_HMAC512_TAG_3                                                                      (32'h10c)
`endif
`ifndef HMAC_REG_HMAC512_TAG_4
`define HMAC_REG_HMAC512_TAG_4                                                                      (32'h110)
`endif
`ifndef HMAC_REG_HMAC512_TAG_5
`define HMAC_REG_HMAC512_TAG_5                                                                      (32'h114)
`endif
`ifndef HMAC_REG_HMAC512_TAG_6
`define HMAC_REG_HMAC512_TAG_6                                                                      (32'h118)
`endif
`ifndef HMAC_REG_HMAC512_TAG_7
`define HMAC_REG_HMAC512_TAG_7                                                                      (32'h11c)
`endif
`ifndef HMAC_REG_HMAC512_TAG_8
`define HMAC_REG_HMAC512_TAG_8                                                                      (32'h120)
`endif
`ifndef HMAC_REG_HMAC512_TAG_9
`define HMAC_REG_HMAC512_TAG_9                                                                      (32'h124)
`endif
`ifndef HMAC_REG_HMAC512_TAG_10
`define HMAC_REG_HMAC512_TAG_10                                                                     (32'h128)
`endif
`ifndef HMAC_REG_HMAC512_TAG_11
`define HMAC_REG_HMAC512_TAG_11                                                                     (32'h12c)
`endif
`ifndef HMAC_REG_HMAC512_TAG_12
`define HMAC_REG_HMAC512_TAG_12                                                                     (32'h130)
`endif
`ifndef HMAC_REG_HMAC512_TAG_13
`define HMAC_REG_HMAC512_TAG_13                                                                     (32'h134)
`endif
`ifndef HMAC_REG_HMAC512_TAG_14
`define HMAC_REG_HMAC512_TAG_14                                                                     (32'h138)
`endif
`ifndef HMAC_REG_HMAC512_TAG_15
`define HMAC_REG_HMAC512_TAG_15                                                                     (32'h13c)
`endif
`ifndef HMAC_REG_HMAC512_LFSR_SEED_0
`define HMAC_REG_HMAC512_LFSR_SEED_0                                                                (32'h140)
`endif
`ifndef HMAC_REG_HMAC512_LFSR_SEED_1
`define HMAC_REG_HMAC512_LFSR_SEED_1                                                                (32'h144)
`endif
`ifndef HMAC_REG_HMAC512_LFSR_SEED_2
`define HMAC_REG_HMAC512_LFSR_SEED_2                                                                (32'h148)
`endif
`ifndef HMAC_REG_HMAC512_LFSR_SEED_3
`define HMAC_REG_HMAC512_LFSR_SEED_3                                                                (32'h14c)
`endif
`ifndef HMAC_REG_HMAC512_LFSR_SEED_4
`define HMAC_REG_HMAC512_LFSR_SEED_4                                                                (32'h150)
`endif
`ifndef HMAC_REG_HMAC512_LFSR_SEED_5
`define HMAC_REG_HMAC512_LFSR_SEED_5                                                                (32'h154)
`endif
`ifndef HMAC_REG_HMAC512_LFSR_SEED_6
`define HMAC_REG_HMAC512_LFSR_SEED_6                                                                (32'h158)
`endif
`ifndef HMAC_REG_HMAC512_LFSR_SEED_7
`define HMAC_REG_HMAC512_LFSR_SEED_7                                                                (32'h15c)
`endif
`ifndef HMAC_REG_HMAC512_LFSR_SEED_8
`define HMAC_REG_HMAC512_LFSR_SEED_8                                                                (32'h160)
`endif
`ifndef HMAC_REG_HMAC512_LFSR_SEED_9
`define HMAC_REG_HMAC512_LFSR_SEED_9                                                                (32'h164)
`endif
`ifndef HMAC_REG_HMAC512_LFSR_SEED_10
`define HMAC_REG_HMAC512_LFSR_SEED_10                                                               (32'h168)
`endif
`ifndef HMAC_REG_HMAC512_LFSR_SEED_11
`define HMAC_REG_HMAC512_LFSR_SEED_11                                                               (32'h16c)
`endif
`ifndef HMAC_REG_HMAC512_KV_RD_KEY_CTRL
`define HMAC_REG_HMAC512_KV_RD_KEY_CTRL                                                             (32'h600)
`define HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_EN_LOW                                                 (0)
`define HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_EN_MASK                                                (32'h1)
`define HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_ENTRY_LOW                                              (1)
`define HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_ENTRY_MASK                                             (32'h3e)
`define HMAC_REG_HMAC512_KV_RD_KEY_CTRL_PCR_HASH_EXTEND_LOW                                         (6)
`define HMAC_REG_HMAC512_KV_RD_KEY_CTRL_PCR_HASH_EXTEND_MASK                                        (32'h40)
`define HMAC_REG_HMAC512_KV_RD_KEY_CTRL_RSVD_LOW                                                    (7)
`define HMAC_REG_HMAC512_KV_RD_KEY_CTRL_RSVD_MASK                                                   (32'hffffff80)
`endif
`ifndef HMAC_REG_HMAC512_KV_RD_KEY_STATUS
`define HMAC_REG_HMAC512_KV_RD_KEY_STATUS                                                           (32'h604)
`define HMAC_REG_HMAC512_KV_RD_KEY_STATUS_READY_LOW                                                 (0)
`define HMAC_REG_HMAC512_KV_RD_KEY_STATUS_READY_MASK                                                (32'h1)
`define HMAC_REG_HMAC512_KV_RD_KEY_STATUS_VALID_LOW                                                 (1)
`define HMAC_REG_HMAC512_KV_RD_KEY_STATUS_VALID_MASK                                                (32'h2)
`define HMAC_REG_HMAC512_KV_RD_KEY_STATUS_ERROR_LOW                                                 (2)
`define HMAC_REG_HMAC512_KV_RD_KEY_STATUS_ERROR_MASK                                                (32'h3fc)
`endif
`ifndef HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL
`define HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL                                                           (32'h608)
`define HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL_READ_EN_LOW                                               (0)
`define HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL_READ_EN_MASK                                              (32'h1)
`define HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL_READ_ENTRY_LOW                                            (1)
`define HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL_READ_ENTRY_MASK                                           (32'h3e)
`define HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL_PCR_HASH_EXTEND_LOW                                       (6)
`define HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL_PCR_HASH_EXTEND_MASK                                      (32'h40)
`define HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL_RSVD_LOW                                                  (7)
`define HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL_RSVD_MASK                                                 (32'hffffff80)
`endif
`ifndef HMAC_REG_HMAC512_KV_RD_BLOCK_STATUS
`define HMAC_REG_HMAC512_KV_RD_BLOCK_STATUS                                                         (32'h60c)
`define HMAC_REG_HMAC512_KV_RD_BLOCK_STATUS_READY_LOW                                               (0)
`define HMAC_REG_HMAC512_KV_RD_BLOCK_STATUS_READY_MASK                                              (32'h1)
`define HMAC_REG_HMAC512_KV_RD_BLOCK_STATUS_VALID_LOW                                               (1)
`define HMAC_REG_HMAC512_KV_RD_BLOCK_STATUS_VALID_MASK                                              (32'h2)
`define HMAC_REG_HMAC512_KV_RD_BLOCK_STATUS_ERROR_LOW                                               (2)
`define HMAC_REG_HMAC512_KV_RD_BLOCK_STATUS_ERROR_MASK                                              (32'h3fc)
`endif
`ifndef HMAC_REG_HMAC512_KV_WR_CTRL
`define HMAC_REG_HMAC512_KV_WR_CTRL                                                                 (32'h610)
`define HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_EN_LOW                                                    (0)
`define HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_EN_MASK                                                   (32'h1)
`define HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_ENTRY_LOW                                                 (1)
`define HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_ENTRY_MASK                                                (32'h3e)
`define HMAC_REG_HMAC512_KV_WR_CTRL_HMAC_KEY_DEST_VALID_LOW                                         (6)
`define HMAC_REG_HMAC512_KV_WR_CTRL_HMAC_KEY_DEST_VALID_MASK                                        (32'h40)
`define HMAC_REG_HMAC512_KV_WR_CTRL_HMAC_BLOCK_DEST_VALID_LOW                                       (7)
`define HMAC_REG_HMAC512_KV_WR_CTRL_HMAC_BLOCK_DEST_VALID_MASK                                      (32'h80)
`define HMAC_REG_HMAC512_KV_WR_CTRL_MLDSA_SEED_DEST_VALID_LOW                                       (8)
`define HMAC_REG_HMAC512_KV_WR_CTRL_MLDSA_SEED_DEST_VALID_MASK                                      (32'h100)
`define HMAC_REG_HMAC512_KV_WR_CTRL_ECC_PKEY_DEST_VALID_LOW                                         (9)
`define HMAC_REG_HMAC512_KV_WR_CTRL_ECC_PKEY_DEST_VALID_MASK                                        (32'h200)
`define HMAC_REG_HMAC512_KV_WR_CTRL_ECC_SEED_DEST_VALID_LOW                                         (10)
`define HMAC_REG_HMAC512_KV_WR_CTRL_ECC_SEED_DEST_VALID_MASK                                        (32'h400)
`define HMAC_REG_HMAC512_KV_WR_CTRL_AES_KEY_DEST_VALID_LOW                                          (11)
`define HMAC_REG_HMAC512_KV_WR_CTRL_AES_KEY_DEST_VALID_MASK                                         (32'h800)
`define HMAC_REG_HMAC512_KV_WR_CTRL_MLKEM_SEED_DEST_VALID_LOW                                       (12)
`define HMAC_REG_HMAC512_KV_WR_CTRL_MLKEM_SEED_DEST_VALID_MASK                                      (32'h1000)
`define HMAC_REG_HMAC512_KV_WR_CTRL_MLKEM_MSG_DEST_VALID_LOW                                        (13)
`define HMAC_REG_HMAC512_KV_WR_CTRL_MLKEM_MSG_DEST_VALID_MASK                                       (32'h2000)
`define HMAC_REG_HMAC512_KV_WR_CTRL_DMA_DATA_DEST_VALID_LOW                                         (14)
`define HMAC_REG_HMAC512_KV_WR_CTRL_DMA_DATA_DEST_VALID_MASK                                        (32'h4000)
`define HMAC_REG_HMAC512_KV_WR_CTRL_RSVD_LOW                                                        (15)
`define HMAC_REG_HMAC512_KV_WR_CTRL_RSVD_MASK                                                       (32'hffff8000)
`endif
`ifndef HMAC_REG_HMAC512_KV_WR_STATUS
`define HMAC_REG_HMAC512_KV_WR_STATUS                                                               (32'h614)
`define HMAC_REG_HMAC512_KV_WR_STATUS_READY_LOW                                                     (0)
`define HMAC_REG_HMAC512_KV_WR_STATUS_READY_MASK                                                    (32'h1)
`define HMAC_REG_HMAC512_KV_WR_STATUS_VALID_LOW                                                     (1)
`define HMAC_REG_HMAC512_KV_WR_STATUS_VALID_MASK                                                    (32'h2)
`define HMAC_REG_HMAC512_KV_WR_STATUS_ERROR_LOW                                                     (2)
`define HMAC_REG_HMAC512_KV_WR_STATUS_ERROR_MASK                                                    (32'h3fc)
`endif
`ifndef HMAC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R
`define HMAC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R                                                     (32'h800)
`define HMAC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_LOW                                        (0)
`define HMAC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_MASK                                       (32'h1)
`define HMAC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_LOW                                        (1)
`define HMAC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_MASK                                       (32'h2)
`endif
`ifndef HMAC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R
`define HMAC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R                                                      (32'h804)
`define HMAC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_KEY_MODE_ERROR_EN_LOW                                (0)
`define HMAC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_KEY_MODE_ERROR_EN_MASK                               (32'h1)
`define HMAC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_KEY_ZERO_ERROR_EN_LOW                                (1)
`define HMAC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_KEY_ZERO_ERROR_EN_MASK                               (32'h2)
`define HMAC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR2_EN_LOW                                        (2)
`define HMAC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR2_EN_MASK                                       (32'h4)
`define HMAC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR3_EN_LOW                                        (3)
`define HMAC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR3_EN_MASK                                       (32'h8)
`endif
`ifndef HMAC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R
`define HMAC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R                                                      (32'h808)
`define HMAC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_CMD_DONE_EN_LOW                                (0)
`define HMAC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_CMD_DONE_EN_MASK                               (32'h1)
`endif
`ifndef HMAC_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R
`define HMAC_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R                                                  (32'h80c)
`define HMAC_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS_LOW                                      (0)
`define HMAC_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS_MASK                                     (32'h1)
`endif
`ifndef HMAC_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R
`define HMAC_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R                                                  (32'h810)
`define HMAC_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS_LOW                                      (0)
`define HMAC_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS_MASK                                     (32'h1)
`endif
`ifndef HMAC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R
`define HMAC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R                                                (32'h814)
`define HMAC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_KEY_MODE_ERROR_STS_LOW                         (0)
`define HMAC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_KEY_MODE_ERROR_STS_MASK                        (32'h1)
`define HMAC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_KEY_ZERO_ERROR_STS_LOW                         (1)
`define HMAC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_KEY_ZERO_ERROR_STS_MASK                        (32'h2)
`define HMAC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR2_STS_LOW                                 (2)
`define HMAC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR2_STS_MASK                                (32'h4)
`define HMAC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR3_STS_LOW                                 (3)
`define HMAC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR3_STS_MASK                                (32'h8)
`endif
`ifndef HMAC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R
`define HMAC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R                                                (32'h818)
`define HMAC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_LOW                         (0)
`define HMAC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK                        (32'h1)
`endif
`ifndef HMAC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R
`define HMAC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R                                                    (32'h81c)
`define HMAC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_KEY_MODE_ERROR_TRIG_LOW                            (0)
`define HMAC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_KEY_MODE_ERROR_TRIG_MASK                           (32'h1)
`define HMAC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_KEY_ZERO_ERROR_TRIG_LOW                            (1)
`define HMAC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_KEY_ZERO_ERROR_TRIG_MASK                           (32'h2)
`define HMAC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR2_TRIG_LOW                                    (2)
`define HMAC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR2_TRIG_MASK                                   (32'h4)
`define HMAC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR3_TRIG_LOW                                    (3)
`define HMAC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR3_TRIG_MASK                                   (32'h8)
`endif
`ifndef HMAC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R
`define HMAC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R                                                    (32'h820)
`define HMAC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_DONE_TRIG_LOW                            (0)
`define HMAC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_DONE_TRIG_MASK                           (32'h1)
`endif
`ifndef HMAC_REG_INTR_BLOCK_RF_KEY_MODE_ERROR_INTR_COUNT_R
`define HMAC_REG_INTR_BLOCK_RF_KEY_MODE_ERROR_INTR_COUNT_R                                          (32'h900)
`endif
`ifndef HMAC_REG_INTR_BLOCK_RF_KEY_ZERO_ERROR_INTR_COUNT_R
`define HMAC_REG_INTR_BLOCK_RF_KEY_ZERO_ERROR_INTR_COUNT_R                                          (32'h904)
`endif
`ifndef HMAC_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_R
`define HMAC_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_R                                                  (32'h908)
`endif
`ifndef HMAC_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_R
`define HMAC_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_R                                                  (32'h90c)
`endif
`ifndef HMAC_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R
`define HMAC_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R                                          (32'h980)
`endif
`ifndef HMAC_REG_INTR_BLOCK_RF_KEY_MODE_ERROR_INTR_COUNT_INCR_R
`define HMAC_REG_INTR_BLOCK_RF_KEY_MODE_ERROR_INTR_COUNT_INCR_R                                     (32'ha00)
`define HMAC_REG_INTR_BLOCK_RF_KEY_MODE_ERROR_INTR_COUNT_INCR_R_PULSE_LOW                           (0)
`define HMAC_REG_INTR_BLOCK_RF_KEY_MODE_ERROR_INTR_COUNT_INCR_R_PULSE_MASK                          (32'h1)
`endif
`ifndef HMAC_REG_INTR_BLOCK_RF_KEY_ZERO_ERROR_INTR_COUNT_INCR_R
`define HMAC_REG_INTR_BLOCK_RF_KEY_ZERO_ERROR_INTR_COUNT_INCR_R                                     (32'ha04)
`define HMAC_REG_INTR_BLOCK_RF_KEY_ZERO_ERROR_INTR_COUNT_INCR_R_PULSE_LOW                           (0)
`define HMAC_REG_INTR_BLOCK_RF_KEY_ZERO_ERROR_INTR_COUNT_INCR_R_PULSE_MASK                          (32'h1)
`endif
`ifndef HMAC_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R
`define HMAC_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R                                             (32'ha08)
`define HMAC_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R_PULSE_LOW                                   (0)
`define HMAC_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R_PULSE_MASK                                  (32'h1)
`endif
`ifndef HMAC_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R
`define HMAC_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R                                             (32'ha0c)
`define HMAC_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R_PULSE_LOW                                   (0)
`define HMAC_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R_PULSE_MASK                                  (32'h1)
`endif
`ifndef HMAC_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R
`define HMAC_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R                                     (32'ha10)
`define HMAC_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R_PULSE_LOW                           (0)
`define HMAC_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R_PULSE_MASK                          (32'h1)
`endif
`ifndef AES_REG_KEY_SHARE0_0
`define AES_REG_KEY_SHARE0_0                                                                        (32'h4)
`endif
`ifndef AES_REG_KEY_SHARE0_1
`define AES_REG_KEY_SHARE0_1                                                                        (32'h8)
`endif
`ifndef AES_REG_KEY_SHARE0_2
`define AES_REG_KEY_SHARE0_2                                                                        (32'hc)
`endif
`ifndef AES_REG_KEY_SHARE0_3
`define AES_REG_KEY_SHARE0_3                                                                        (32'h10)
`endif
`ifndef AES_REG_KEY_SHARE0_4
`define AES_REG_KEY_SHARE0_4                                                                        (32'h14)
`endif
`ifndef AES_REG_KEY_SHARE0_5
`define AES_REG_KEY_SHARE0_5                                                                        (32'h18)
`endif
`ifndef AES_REG_KEY_SHARE0_6
`define AES_REG_KEY_SHARE0_6                                                                        (32'h1c)
`endif
`ifndef AES_REG_KEY_SHARE0_7
`define AES_REG_KEY_SHARE0_7                                                                        (32'h20)
`endif
`ifndef AES_REG_KEY_SHARE1_0
`define AES_REG_KEY_SHARE1_0                                                                        (32'h24)
`endif
`ifndef AES_REG_KEY_SHARE1_1
`define AES_REG_KEY_SHARE1_1                                                                        (32'h28)
`endif
`ifndef AES_REG_KEY_SHARE1_2
`define AES_REG_KEY_SHARE1_2                                                                        (32'h2c)
`endif
`ifndef AES_REG_KEY_SHARE1_3
`define AES_REG_KEY_SHARE1_3                                                                        (32'h30)
`endif
`ifndef AES_REG_KEY_SHARE1_4
`define AES_REG_KEY_SHARE1_4                                                                        (32'h34)
`endif
`ifndef AES_REG_KEY_SHARE1_5
`define AES_REG_KEY_SHARE1_5                                                                        (32'h38)
`endif
`ifndef AES_REG_KEY_SHARE1_6
`define AES_REG_KEY_SHARE1_6                                                                        (32'h3c)
`endif
`ifndef AES_REG_KEY_SHARE1_7
`define AES_REG_KEY_SHARE1_7                                                                        (32'h40)
`endif
`ifndef AES_REG_IV_0
`define AES_REG_IV_0                                                                                (32'h44)
`endif
`ifndef AES_REG_IV_1
`define AES_REG_IV_1                                                                                (32'h48)
`endif
`ifndef AES_REG_IV_2
`define AES_REG_IV_2                                                                                (32'h4c)
`endif
`ifndef AES_REG_IV_3
`define AES_REG_IV_3                                                                                (32'h50)
`endif
`ifndef AES_REG_DATA_IN_0
`define AES_REG_DATA_IN_0                                                                           (32'h54)
`endif
`ifndef AES_REG_DATA_IN_1
`define AES_REG_DATA_IN_1                                                                           (32'h58)
`endif
`ifndef AES_REG_DATA_IN_2
`define AES_REG_DATA_IN_2                                                                           (32'h5c)
`endif
`ifndef AES_REG_DATA_IN_3
`define AES_REG_DATA_IN_3                                                                           (32'h60)
`endif
`ifndef AES_REG_DATA_OUT_0
`define AES_REG_DATA_OUT_0                                                                          (32'h64)
`endif
`ifndef AES_REG_DATA_OUT_1
`define AES_REG_DATA_OUT_1                                                                          (32'h68)
`endif
`ifndef AES_REG_DATA_OUT_2
`define AES_REG_DATA_OUT_2                                                                          (32'h6c)
`endif
`ifndef AES_REG_DATA_OUT_3
`define AES_REG_DATA_OUT_3                                                                          (32'h70)
`endif
`ifndef AES_REG_CTRL_SHADOWED
`define AES_REG_CTRL_SHADOWED                                                                       (32'h74)
`define AES_REG_CTRL_SHADOWED_OPERATION_LOW                                                         (0)
`define AES_REG_CTRL_SHADOWED_OPERATION_MASK                                                        (32'h3)
`define AES_REG_CTRL_SHADOWED_MODE_LOW                                                              (2)
`define AES_REG_CTRL_SHADOWED_MODE_MASK                                                             (32'hfc)
`define AES_REG_CTRL_SHADOWED_KEY_LEN_LOW                                                           (8)
`define AES_REG_CTRL_SHADOWED_KEY_LEN_MASK                                                          (32'h700)
`define AES_REG_CTRL_SHADOWED_SIDELOAD_LOW                                                          (11)
`define AES_REG_CTRL_SHADOWED_SIDELOAD_MASK                                                         (32'h800)
`define AES_REG_CTRL_SHADOWED_PRNG_RESEED_RATE_LOW                                                  (12)
`define AES_REG_CTRL_SHADOWED_PRNG_RESEED_RATE_MASK                                                 (32'h7000)
`define AES_REG_CTRL_SHADOWED_MANUAL_OPERATION_LOW                                                  (15)
`define AES_REG_CTRL_SHADOWED_MANUAL_OPERATION_MASK                                                 (32'h8000)
`endif
`ifndef AES_REG_CTRL_AUX_SHADOWED
`define AES_REG_CTRL_AUX_SHADOWED                                                                   (32'h78)
`define AES_REG_CTRL_AUX_SHADOWED_KEY_TOUCH_FORCES_RESEED_LOW                                       (0)
`define AES_REG_CTRL_AUX_SHADOWED_KEY_TOUCH_FORCES_RESEED_MASK                                      (32'h1)
`define AES_REG_CTRL_AUX_SHADOWED_FORCE_MASKS_LOW                                                   (1)
`define AES_REG_CTRL_AUX_SHADOWED_FORCE_MASKS_MASK                                                  (32'h2)
`endif
`ifndef AES_REG_CTRL_AUX_REGWEN
`define AES_REG_CTRL_AUX_REGWEN                                                                     (32'h7c)
`define AES_REG_CTRL_AUX_REGWEN_CTRL_AUX_REGWEN_LOW                                                 (0)
`define AES_REG_CTRL_AUX_REGWEN_CTRL_AUX_REGWEN_MASK                                                (32'h1)
`endif
`ifndef AES_REG_TRIGGER
`define AES_REG_TRIGGER                                                                             (32'h80)
`define AES_REG_TRIGGER_START_LOW                                                                   (0)
`define AES_REG_TRIGGER_START_MASK                                                                  (32'h1)
`define AES_REG_TRIGGER_KEY_IV_DATA_IN_CLEAR_LOW                                                    (1)
`define AES_REG_TRIGGER_KEY_IV_DATA_IN_CLEAR_MASK                                                   (32'h2)
`define AES_REG_TRIGGER_DATA_OUT_CLEAR_LOW                                                          (2)
`define AES_REG_TRIGGER_DATA_OUT_CLEAR_MASK                                                         (32'h4)
`define AES_REG_TRIGGER_PRNG_RESEED_LOW                                                             (3)
`define AES_REG_TRIGGER_PRNG_RESEED_MASK                                                            (32'h8)
`endif
`ifndef AES_REG_STATUS
`define AES_REG_STATUS                                                                              (32'h84)
`define AES_REG_STATUS_IDLE_LOW                                                                     (0)
`define AES_REG_STATUS_IDLE_MASK                                                                    (32'h1)
`define AES_REG_STATUS_STALL_LOW                                                                    (1)
`define AES_REG_STATUS_STALL_MASK                                                                   (32'h2)
`define AES_REG_STATUS_OUTPUT_LOST_LOW                                                              (2)
`define AES_REG_STATUS_OUTPUT_LOST_MASK                                                             (32'h4)
`define AES_REG_STATUS_OUTPUT_VALID_LOW                                                             (3)
`define AES_REG_STATUS_OUTPUT_VALID_MASK                                                            (32'h8)
`define AES_REG_STATUS_INPUT_READY_LOW                                                              (4)
`define AES_REG_STATUS_INPUT_READY_MASK                                                             (32'h10)
`define AES_REG_STATUS_ALERT_RECOV_CTRL_UPDATE_ERR_LOW                                              (5)
`define AES_REG_STATUS_ALERT_RECOV_CTRL_UPDATE_ERR_MASK                                             (32'h20)
`define AES_REG_STATUS_ALERT_FATAL_FAULT_LOW                                                        (6)
`define AES_REG_STATUS_ALERT_FATAL_FAULT_MASK                                                       (32'h40)
`endif
`ifndef AES_REG_CTRL_GCM_SHADOWED
`define AES_REG_CTRL_GCM_SHADOWED                                                                   (32'h88)
`define AES_REG_CTRL_GCM_SHADOWED_PHASE_LOW                                                         (0)
`define AES_REG_CTRL_GCM_SHADOWED_PHASE_MASK                                                        (32'h3f)
`define AES_REG_CTRL_GCM_SHADOWED_NUM_VALID_BYTES_LOW                                               (6)
`define AES_REG_CTRL_GCM_SHADOWED_NUM_VALID_BYTES_MASK                                              (32'h7c0)
`endif
`ifndef AES_CLP_REG_AES_NAME_0
`define AES_CLP_REG_AES_NAME_0                                                                      (32'h0)
`endif
`ifndef AES_CLP_REG_AES_NAME_1
`define AES_CLP_REG_AES_NAME_1                                                                      (32'h4)
`endif
`ifndef AES_CLP_REG_AES_VERSION_0
`define AES_CLP_REG_AES_VERSION_0                                                                   (32'h8)
`endif
`ifndef AES_CLP_REG_AES_VERSION_1
`define AES_CLP_REG_AES_VERSION_1                                                                   (32'hc)
`endif
`ifndef AES_CLP_REG_ENTROPY_IF_SEED_0
`define AES_CLP_REG_ENTROPY_IF_SEED_0                                                               (32'h110)
`endif
`ifndef AES_CLP_REG_ENTROPY_IF_SEED_1
`define AES_CLP_REG_ENTROPY_IF_SEED_1                                                               (32'h114)
`endif
`ifndef AES_CLP_REG_ENTROPY_IF_SEED_2
`define AES_CLP_REG_ENTROPY_IF_SEED_2                                                               (32'h118)
`endif
`ifndef AES_CLP_REG_ENTROPY_IF_SEED_3
`define AES_CLP_REG_ENTROPY_IF_SEED_3                                                               (32'h11c)
`endif
`ifndef AES_CLP_REG_ENTROPY_IF_SEED_4
`define AES_CLP_REG_ENTROPY_IF_SEED_4                                                               (32'h120)
`endif
`ifndef AES_CLP_REG_ENTROPY_IF_SEED_5
`define AES_CLP_REG_ENTROPY_IF_SEED_5                                                               (32'h124)
`endif
`ifndef AES_CLP_REG_ENTROPY_IF_SEED_6
`define AES_CLP_REG_ENTROPY_IF_SEED_6                                                               (32'h128)
`endif
`ifndef AES_CLP_REG_ENTROPY_IF_SEED_7
`define AES_CLP_REG_ENTROPY_IF_SEED_7                                                               (32'h12c)
`endif
`ifndef AES_CLP_REG_ENTROPY_IF_SEED_8
`define AES_CLP_REG_ENTROPY_IF_SEED_8                                                               (32'h130)
`endif
`ifndef AES_CLP_REG_CTRL0
`define AES_CLP_REG_CTRL0                                                                           (32'h134)
`define AES_CLP_REG_CTRL0_ENDIAN_SWAP_LOW                                                           (0)
`define AES_CLP_REG_CTRL0_ENDIAN_SWAP_MASK                                                          (32'h1)
`endif
`ifndef AES_CLP_REG_AES_KV_RD_KEY_CTRL
`define AES_CLP_REG_AES_KV_RD_KEY_CTRL                                                              (32'h200)
`define AES_CLP_REG_AES_KV_RD_KEY_CTRL_READ_EN_LOW                                                  (0)
`define AES_CLP_REG_AES_KV_RD_KEY_CTRL_READ_EN_MASK                                                 (32'h1)
`define AES_CLP_REG_AES_KV_RD_KEY_CTRL_READ_ENTRY_LOW                                               (1)
`define AES_CLP_REG_AES_KV_RD_KEY_CTRL_READ_ENTRY_MASK                                              (32'h3e)
`define AES_CLP_REG_AES_KV_RD_KEY_CTRL_PCR_HASH_EXTEND_LOW                                          (6)
`define AES_CLP_REG_AES_KV_RD_KEY_CTRL_PCR_HASH_EXTEND_MASK                                         (32'h40)
`define AES_CLP_REG_AES_KV_RD_KEY_CTRL_RSVD_LOW                                                     (7)
`define AES_CLP_REG_AES_KV_RD_KEY_CTRL_RSVD_MASK                                                    (32'hffffff80)
`endif
`ifndef AES_CLP_REG_AES_KV_RD_KEY_STATUS
`define AES_CLP_REG_AES_KV_RD_KEY_STATUS                                                            (32'h204)
`define AES_CLP_REG_AES_KV_RD_KEY_STATUS_READY_LOW                                                  (0)
`define AES_CLP_REG_AES_KV_RD_KEY_STATUS_READY_MASK                                                 (32'h1)
`define AES_CLP_REG_AES_KV_RD_KEY_STATUS_VALID_LOW                                                  (1)
`define AES_CLP_REG_AES_KV_RD_KEY_STATUS_VALID_MASK                                                 (32'h2)
`define AES_CLP_REG_AES_KV_RD_KEY_STATUS_ERROR_LOW                                                  (2)
`define AES_CLP_REG_AES_KV_RD_KEY_STATUS_ERROR_MASK                                                 (32'h3fc)
`endif
`ifndef AES_CLP_REG_AES_KV_WR_CTRL
`define AES_CLP_REG_AES_KV_WR_CTRL                                                                  (32'h208)
`define AES_CLP_REG_AES_KV_WR_CTRL_WRITE_EN_LOW                                                     (0)
`define AES_CLP_REG_AES_KV_WR_CTRL_WRITE_EN_MASK                                                    (32'h1)
`define AES_CLP_REG_AES_KV_WR_CTRL_WRITE_ENTRY_LOW                                                  (1)
`define AES_CLP_REG_AES_KV_WR_CTRL_WRITE_ENTRY_MASK                                                 (32'h3e)
`define AES_CLP_REG_AES_KV_WR_CTRL_HMAC_KEY_DEST_VALID_LOW                                          (6)
`define AES_CLP_REG_AES_KV_WR_CTRL_HMAC_KEY_DEST_VALID_MASK                                         (32'h40)
`define AES_CLP_REG_AES_KV_WR_CTRL_HMAC_BLOCK_DEST_VALID_LOW                                        (7)
`define AES_CLP_REG_AES_KV_WR_CTRL_HMAC_BLOCK_DEST_VALID_MASK                                       (32'h80)
`define AES_CLP_REG_AES_KV_WR_CTRL_MLDSA_SEED_DEST_VALID_LOW                                        (8)
`define AES_CLP_REG_AES_KV_WR_CTRL_MLDSA_SEED_DEST_VALID_MASK                                       (32'h100)
`define AES_CLP_REG_AES_KV_WR_CTRL_ECC_PKEY_DEST_VALID_LOW                                          (9)
`define AES_CLP_REG_AES_KV_WR_CTRL_ECC_PKEY_DEST_VALID_MASK                                         (32'h200)
`define AES_CLP_REG_AES_KV_WR_CTRL_ECC_SEED_DEST_VALID_LOW                                          (10)
`define AES_CLP_REG_AES_KV_WR_CTRL_ECC_SEED_DEST_VALID_MASK                                         (32'h400)
`define AES_CLP_REG_AES_KV_WR_CTRL_AES_KEY_DEST_VALID_LOW                                           (11)
`define AES_CLP_REG_AES_KV_WR_CTRL_AES_KEY_DEST_VALID_MASK                                          (32'h800)
`define AES_CLP_REG_AES_KV_WR_CTRL_MLKEM_SEED_DEST_VALID_LOW                                        (12)
`define AES_CLP_REG_AES_KV_WR_CTRL_MLKEM_SEED_DEST_VALID_MASK                                       (32'h1000)
`define AES_CLP_REG_AES_KV_WR_CTRL_MLKEM_MSG_DEST_VALID_LOW                                         (13)
`define AES_CLP_REG_AES_KV_WR_CTRL_MLKEM_MSG_DEST_VALID_MASK                                        (32'h2000)
`define AES_CLP_REG_AES_KV_WR_CTRL_DMA_DATA_DEST_VALID_LOW                                          (14)
`define AES_CLP_REG_AES_KV_WR_CTRL_DMA_DATA_DEST_VALID_MASK                                         (32'h4000)
`define AES_CLP_REG_AES_KV_WR_CTRL_RSVD_LOW                                                         (15)
`define AES_CLP_REG_AES_KV_WR_CTRL_RSVD_MASK                                                        (32'hffff8000)
`endif
`ifndef AES_CLP_REG_AES_KV_WR_STATUS
`define AES_CLP_REG_AES_KV_WR_STATUS                                                                (32'h20c)
`define AES_CLP_REG_AES_KV_WR_STATUS_READY_LOW                                                      (0)
`define AES_CLP_REG_AES_KV_WR_STATUS_READY_MASK                                                     (32'h1)
`define AES_CLP_REG_AES_KV_WR_STATUS_VALID_LOW                                                      (1)
`define AES_CLP_REG_AES_KV_WR_STATUS_VALID_MASK                                                     (32'h2)
`define AES_CLP_REG_AES_KV_WR_STATUS_ERROR_LOW                                                      (2)
`define AES_CLP_REG_AES_KV_WR_STATUS_ERROR_MASK                                                     (32'h3fc)
`endif
`ifndef AES_CLP_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R
`define AES_CLP_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R                                                  (32'h400)
`define AES_CLP_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_LOW                                     (0)
`define AES_CLP_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_MASK                                    (32'h1)
`define AES_CLP_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_LOW                                     (1)
`define AES_CLP_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_MASK                                    (32'h2)
`endif
`ifndef AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R
`define AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R                                                   (32'h404)
`define AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR0_EN_LOW                                     (0)
`define AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR0_EN_MASK                                    (32'h1)
`define AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR1_EN_LOW                                     (1)
`define AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR1_EN_MASK                                    (32'h2)
`define AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR2_EN_LOW                                     (2)
`define AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR2_EN_MASK                                    (32'h4)
`define AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR3_EN_LOW                                     (3)
`define AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR3_EN_MASK                                    (32'h8)
`endif
`ifndef AES_CLP_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R
`define AES_CLP_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R                                                   (32'h408)
`define AES_CLP_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_CMD_DONE_EN_LOW                             (0)
`define AES_CLP_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_CMD_DONE_EN_MASK                            (32'h1)
`endif
`ifndef AES_CLP_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R
`define AES_CLP_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R                                               (32'h40c)
`define AES_CLP_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS_LOW                                   (0)
`define AES_CLP_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS_MASK                                  (32'h1)
`endif
`ifndef AES_CLP_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R
`define AES_CLP_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R                                               (32'h410)
`define AES_CLP_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS_LOW                                   (0)
`define AES_CLP_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS_MASK                                  (32'h1)
`endif
`ifndef AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R
`define AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R                                             (32'h414)
`define AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR0_STS_LOW                              (0)
`define AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR0_STS_MASK                             (32'h1)
`define AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR1_STS_LOW                              (1)
`define AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR1_STS_MASK                             (32'h2)
`define AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR2_STS_LOW                              (2)
`define AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR2_STS_MASK                             (32'h4)
`define AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR3_STS_LOW                              (3)
`define AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR3_STS_MASK                             (32'h8)
`endif
`ifndef AES_CLP_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R
`define AES_CLP_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R                                             (32'h418)
`define AES_CLP_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_LOW                      (0)
`define AES_CLP_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK                     (32'h1)
`endif
`ifndef AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R
`define AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R                                                 (32'h41c)
`define AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR0_TRIG_LOW                                 (0)
`define AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR0_TRIG_MASK                                (32'h1)
`define AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR1_TRIG_LOW                                 (1)
`define AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR1_TRIG_MASK                                (32'h2)
`define AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR2_TRIG_LOW                                 (2)
`define AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR2_TRIG_MASK                                (32'h4)
`define AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR3_TRIG_LOW                                 (3)
`define AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR3_TRIG_MASK                                (32'h8)
`endif
`ifndef AES_CLP_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R
`define AES_CLP_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R                                                 (32'h420)
`define AES_CLP_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_DONE_TRIG_LOW                         (0)
`define AES_CLP_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_DONE_TRIG_MASK                        (32'h1)
`endif
`ifndef AES_CLP_REG_INTR_BLOCK_RF_ERROR0_INTR_COUNT_R
`define AES_CLP_REG_INTR_BLOCK_RF_ERROR0_INTR_COUNT_R                                               (32'h500)
`endif
`ifndef AES_CLP_REG_INTR_BLOCK_RF_ERROR1_INTR_COUNT_R
`define AES_CLP_REG_INTR_BLOCK_RF_ERROR1_INTR_COUNT_R                                               (32'h504)
`endif
`ifndef AES_CLP_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_R
`define AES_CLP_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_R                                               (32'h508)
`endif
`ifndef AES_CLP_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_R
`define AES_CLP_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_R                                               (32'h50c)
`endif
`ifndef AES_CLP_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R
`define AES_CLP_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R                                       (32'h580)
`endif
`ifndef AES_CLP_REG_INTR_BLOCK_RF_ERROR0_INTR_COUNT_INCR_R
`define AES_CLP_REG_INTR_BLOCK_RF_ERROR0_INTR_COUNT_INCR_R                                          (32'h600)
`define AES_CLP_REG_INTR_BLOCK_RF_ERROR0_INTR_COUNT_INCR_R_PULSE_LOW                                (0)
`define AES_CLP_REG_INTR_BLOCK_RF_ERROR0_INTR_COUNT_INCR_R_PULSE_MASK                               (32'h1)
`endif
`ifndef AES_CLP_REG_INTR_BLOCK_RF_ERROR1_INTR_COUNT_INCR_R
`define AES_CLP_REG_INTR_BLOCK_RF_ERROR1_INTR_COUNT_INCR_R                                          (32'h604)
`define AES_CLP_REG_INTR_BLOCK_RF_ERROR1_INTR_COUNT_INCR_R_PULSE_LOW                                (0)
`define AES_CLP_REG_INTR_BLOCK_RF_ERROR1_INTR_COUNT_INCR_R_PULSE_MASK                               (32'h1)
`endif
`ifndef AES_CLP_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R
`define AES_CLP_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R                                          (32'h608)
`define AES_CLP_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R_PULSE_LOW                                (0)
`define AES_CLP_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R_PULSE_MASK                               (32'h1)
`endif
`ifndef AES_CLP_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R
`define AES_CLP_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R                                          (32'h60c)
`define AES_CLP_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R_PULSE_LOW                                (0)
`define AES_CLP_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R_PULSE_MASK                               (32'h1)
`endif
`ifndef AES_CLP_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R
`define AES_CLP_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R                                  (32'h610)
`define AES_CLP_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R_PULSE_LOW                        (0)
`define AES_CLP_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R_PULSE_MASK                       (32'h1)
`endif
`ifndef KV_REG_KEY_CTRL_0
`define KV_REG_KEY_CTRL_0                                                                           (32'h0)
`define KV_REG_KEY_CTRL_0_LOCK_WR_LOW                                                               (0)
`define KV_REG_KEY_CTRL_0_LOCK_WR_MASK                                                              (32'h1)
`define KV_REG_KEY_CTRL_0_LOCK_USE_LOW                                                              (1)
`define KV_REG_KEY_CTRL_0_LOCK_USE_MASK                                                             (32'h2)
`define KV_REG_KEY_CTRL_0_CLEAR_LOW                                                                 (2)
`define KV_REG_KEY_CTRL_0_CLEAR_MASK                                                                (32'h4)
`define KV_REG_KEY_CTRL_0_RSVD0_LOW                                                                 (3)
`define KV_REG_KEY_CTRL_0_RSVD0_MASK                                                                (32'h8)
`define KV_REG_KEY_CTRL_0_RSVD1_LOW                                                                 (4)
`define KV_REG_KEY_CTRL_0_RSVD1_MASK                                                                (32'h1f0)
`define KV_REG_KEY_CTRL_0_DEST_VALID_LOW                                                            (9)
`define KV_REG_KEY_CTRL_0_DEST_VALID_MASK                                                           (32'h3fe00)
`define KV_REG_KEY_CTRL_0_LAST_DWORD_LOW                                                            (18)
`define KV_REG_KEY_CTRL_0_LAST_DWORD_MASK                                                           (32'h3c0000)
`endif
`ifndef KV_REG_KEY_CTRL_1
`define KV_REG_KEY_CTRL_1                                                                           (32'h4)
`define KV_REG_KEY_CTRL_1_LOCK_WR_LOW                                                               (0)
`define KV_REG_KEY_CTRL_1_LOCK_WR_MASK                                                              (32'h1)
`define KV_REG_KEY_CTRL_1_LOCK_USE_LOW                                                              (1)
`define KV_REG_KEY_CTRL_1_LOCK_USE_MASK                                                             (32'h2)
`define KV_REG_KEY_CTRL_1_CLEAR_LOW                                                                 (2)
`define KV_REG_KEY_CTRL_1_CLEAR_MASK                                                                (32'h4)
`define KV_REG_KEY_CTRL_1_RSVD0_LOW                                                                 (3)
`define KV_REG_KEY_CTRL_1_RSVD0_MASK                                                                (32'h8)
`define KV_REG_KEY_CTRL_1_RSVD1_LOW                                                                 (4)
`define KV_REG_KEY_CTRL_1_RSVD1_MASK                                                                (32'h1f0)
`define KV_REG_KEY_CTRL_1_DEST_VALID_LOW                                                            (9)
`define KV_REG_KEY_CTRL_1_DEST_VALID_MASK                                                           (32'h3fe00)
`define KV_REG_KEY_CTRL_1_LAST_DWORD_LOW                                                            (18)
`define KV_REG_KEY_CTRL_1_LAST_DWORD_MASK                                                           (32'h3c0000)
`endif
`ifndef KV_REG_KEY_CTRL_2
`define KV_REG_KEY_CTRL_2                                                                           (32'h8)
`define KV_REG_KEY_CTRL_2_LOCK_WR_LOW                                                               (0)
`define KV_REG_KEY_CTRL_2_LOCK_WR_MASK                                                              (32'h1)
`define KV_REG_KEY_CTRL_2_LOCK_USE_LOW                                                              (1)
`define KV_REG_KEY_CTRL_2_LOCK_USE_MASK                                                             (32'h2)
`define KV_REG_KEY_CTRL_2_CLEAR_LOW                                                                 (2)
`define KV_REG_KEY_CTRL_2_CLEAR_MASK                                                                (32'h4)
`define KV_REG_KEY_CTRL_2_RSVD0_LOW                                                                 (3)
`define KV_REG_KEY_CTRL_2_RSVD0_MASK                                                                (32'h8)
`define KV_REG_KEY_CTRL_2_RSVD1_LOW                                                                 (4)
`define KV_REG_KEY_CTRL_2_RSVD1_MASK                                                                (32'h1f0)
`define KV_REG_KEY_CTRL_2_DEST_VALID_LOW                                                            (9)
`define KV_REG_KEY_CTRL_2_DEST_VALID_MASK                                                           (32'h3fe00)
`define KV_REG_KEY_CTRL_2_LAST_DWORD_LOW                                                            (18)
`define KV_REG_KEY_CTRL_2_LAST_DWORD_MASK                                                           (32'h3c0000)
`endif
`ifndef KV_REG_KEY_CTRL_3
`define KV_REG_KEY_CTRL_3                                                                           (32'hc)
`define KV_REG_KEY_CTRL_3_LOCK_WR_LOW                                                               (0)
`define KV_REG_KEY_CTRL_3_LOCK_WR_MASK                                                              (32'h1)
`define KV_REG_KEY_CTRL_3_LOCK_USE_LOW                                                              (1)
`define KV_REG_KEY_CTRL_3_LOCK_USE_MASK                                                             (32'h2)
`define KV_REG_KEY_CTRL_3_CLEAR_LOW                                                                 (2)
`define KV_REG_KEY_CTRL_3_CLEAR_MASK                                                                (32'h4)
`define KV_REG_KEY_CTRL_3_RSVD0_LOW                                                                 (3)
`define KV_REG_KEY_CTRL_3_RSVD0_MASK                                                                (32'h8)
`define KV_REG_KEY_CTRL_3_RSVD1_LOW                                                                 (4)
`define KV_REG_KEY_CTRL_3_RSVD1_MASK                                                                (32'h1f0)
`define KV_REG_KEY_CTRL_3_DEST_VALID_LOW                                                            (9)
`define KV_REG_KEY_CTRL_3_DEST_VALID_MASK                                                           (32'h3fe00)
`define KV_REG_KEY_CTRL_3_LAST_DWORD_LOW                                                            (18)
`define KV_REG_KEY_CTRL_3_LAST_DWORD_MASK                                                           (32'h3c0000)
`endif
`ifndef KV_REG_KEY_CTRL_4
`define KV_REG_KEY_CTRL_4                                                                           (32'h10)
`define KV_REG_KEY_CTRL_4_LOCK_WR_LOW                                                               (0)
`define KV_REG_KEY_CTRL_4_LOCK_WR_MASK                                                              (32'h1)
`define KV_REG_KEY_CTRL_4_LOCK_USE_LOW                                                              (1)
`define KV_REG_KEY_CTRL_4_LOCK_USE_MASK                                                             (32'h2)
`define KV_REG_KEY_CTRL_4_CLEAR_LOW                                                                 (2)
`define KV_REG_KEY_CTRL_4_CLEAR_MASK                                                                (32'h4)
`define KV_REG_KEY_CTRL_4_RSVD0_LOW                                                                 (3)
`define KV_REG_KEY_CTRL_4_RSVD0_MASK                                                                (32'h8)
`define KV_REG_KEY_CTRL_4_RSVD1_LOW                                                                 (4)
`define KV_REG_KEY_CTRL_4_RSVD1_MASK                                                                (32'h1f0)
`define KV_REG_KEY_CTRL_4_DEST_VALID_LOW                                                            (9)
`define KV_REG_KEY_CTRL_4_DEST_VALID_MASK                                                           (32'h3fe00)
`define KV_REG_KEY_CTRL_4_LAST_DWORD_LOW                                                            (18)
`define KV_REG_KEY_CTRL_4_LAST_DWORD_MASK                                                           (32'h3c0000)
`endif
`ifndef KV_REG_KEY_CTRL_5
`define KV_REG_KEY_CTRL_5                                                                           (32'h14)
`define KV_REG_KEY_CTRL_5_LOCK_WR_LOW                                                               (0)
`define KV_REG_KEY_CTRL_5_LOCK_WR_MASK                                                              (32'h1)
`define KV_REG_KEY_CTRL_5_LOCK_USE_LOW                                                              (1)
`define KV_REG_KEY_CTRL_5_LOCK_USE_MASK                                                             (32'h2)
`define KV_REG_KEY_CTRL_5_CLEAR_LOW                                                                 (2)
`define KV_REG_KEY_CTRL_5_CLEAR_MASK                                                                (32'h4)
`define KV_REG_KEY_CTRL_5_RSVD0_LOW                                                                 (3)
`define KV_REG_KEY_CTRL_5_RSVD0_MASK                                                                (32'h8)
`define KV_REG_KEY_CTRL_5_RSVD1_LOW                                                                 (4)
`define KV_REG_KEY_CTRL_5_RSVD1_MASK                                                                (32'h1f0)
`define KV_REG_KEY_CTRL_5_DEST_VALID_LOW                                                            (9)
`define KV_REG_KEY_CTRL_5_DEST_VALID_MASK                                                           (32'h3fe00)
`define KV_REG_KEY_CTRL_5_LAST_DWORD_LOW                                                            (18)
`define KV_REG_KEY_CTRL_5_LAST_DWORD_MASK                                                           (32'h3c0000)
`endif
`ifndef KV_REG_KEY_CTRL_6
`define KV_REG_KEY_CTRL_6                                                                           (32'h18)
`define KV_REG_KEY_CTRL_6_LOCK_WR_LOW                                                               (0)
`define KV_REG_KEY_CTRL_6_LOCK_WR_MASK                                                              (32'h1)
`define KV_REG_KEY_CTRL_6_LOCK_USE_LOW                                                              (1)
`define KV_REG_KEY_CTRL_6_LOCK_USE_MASK                                                             (32'h2)
`define KV_REG_KEY_CTRL_6_CLEAR_LOW                                                                 (2)
`define KV_REG_KEY_CTRL_6_CLEAR_MASK                                                                (32'h4)
`define KV_REG_KEY_CTRL_6_RSVD0_LOW                                                                 (3)
`define KV_REG_KEY_CTRL_6_RSVD0_MASK                                                                (32'h8)
`define KV_REG_KEY_CTRL_6_RSVD1_LOW                                                                 (4)
`define KV_REG_KEY_CTRL_6_RSVD1_MASK                                                                (32'h1f0)
`define KV_REG_KEY_CTRL_6_DEST_VALID_LOW                                                            (9)
`define KV_REG_KEY_CTRL_6_DEST_VALID_MASK                                                           (32'h3fe00)
`define KV_REG_KEY_CTRL_6_LAST_DWORD_LOW                                                            (18)
`define KV_REG_KEY_CTRL_6_LAST_DWORD_MASK                                                           (32'h3c0000)
`endif
`ifndef KV_REG_KEY_CTRL_7
`define KV_REG_KEY_CTRL_7                                                                           (32'h1c)
`define KV_REG_KEY_CTRL_7_LOCK_WR_LOW                                                               (0)
`define KV_REG_KEY_CTRL_7_LOCK_WR_MASK                                                              (32'h1)
`define KV_REG_KEY_CTRL_7_LOCK_USE_LOW                                                              (1)
`define KV_REG_KEY_CTRL_7_LOCK_USE_MASK                                                             (32'h2)
`define KV_REG_KEY_CTRL_7_CLEAR_LOW                                                                 (2)
`define KV_REG_KEY_CTRL_7_CLEAR_MASK                                                                (32'h4)
`define KV_REG_KEY_CTRL_7_RSVD0_LOW                                                                 (3)
`define KV_REG_KEY_CTRL_7_RSVD0_MASK                                                                (32'h8)
`define KV_REG_KEY_CTRL_7_RSVD1_LOW                                                                 (4)
`define KV_REG_KEY_CTRL_7_RSVD1_MASK                                                                (32'h1f0)
`define KV_REG_KEY_CTRL_7_DEST_VALID_LOW                                                            (9)
`define KV_REG_KEY_CTRL_7_DEST_VALID_MASK                                                           (32'h3fe00)
`define KV_REG_KEY_CTRL_7_LAST_DWORD_LOW                                                            (18)
`define KV_REG_KEY_CTRL_7_LAST_DWORD_MASK                                                           (32'h3c0000)
`endif
`ifndef KV_REG_KEY_CTRL_8
`define KV_REG_KEY_CTRL_8                                                                           (32'h20)
`define KV_REG_KEY_CTRL_8_LOCK_WR_LOW                                                               (0)
`define KV_REG_KEY_CTRL_8_LOCK_WR_MASK                                                              (32'h1)
`define KV_REG_KEY_CTRL_8_LOCK_USE_LOW                                                              (1)
`define KV_REG_KEY_CTRL_8_LOCK_USE_MASK                                                             (32'h2)
`define KV_REG_KEY_CTRL_8_CLEAR_LOW                                                                 (2)
`define KV_REG_KEY_CTRL_8_CLEAR_MASK                                                                (32'h4)
`define KV_REG_KEY_CTRL_8_RSVD0_LOW                                                                 (3)
`define KV_REG_KEY_CTRL_8_RSVD0_MASK                                                                (32'h8)
`define KV_REG_KEY_CTRL_8_RSVD1_LOW                                                                 (4)
`define KV_REG_KEY_CTRL_8_RSVD1_MASK                                                                (32'h1f0)
`define KV_REG_KEY_CTRL_8_DEST_VALID_LOW                                                            (9)
`define KV_REG_KEY_CTRL_8_DEST_VALID_MASK                                                           (32'h3fe00)
`define KV_REG_KEY_CTRL_8_LAST_DWORD_LOW                                                            (18)
`define KV_REG_KEY_CTRL_8_LAST_DWORD_MASK                                                           (32'h3c0000)
`endif
`ifndef KV_REG_KEY_CTRL_9
`define KV_REG_KEY_CTRL_9                                                                           (32'h24)
`define KV_REG_KEY_CTRL_9_LOCK_WR_LOW                                                               (0)
`define KV_REG_KEY_CTRL_9_LOCK_WR_MASK                                                              (32'h1)
`define KV_REG_KEY_CTRL_9_LOCK_USE_LOW                                                              (1)
`define KV_REG_KEY_CTRL_9_LOCK_USE_MASK                                                             (32'h2)
`define KV_REG_KEY_CTRL_9_CLEAR_LOW                                                                 (2)
`define KV_REG_KEY_CTRL_9_CLEAR_MASK                                                                (32'h4)
`define KV_REG_KEY_CTRL_9_RSVD0_LOW                                                                 (3)
`define KV_REG_KEY_CTRL_9_RSVD0_MASK                                                                (32'h8)
`define KV_REG_KEY_CTRL_9_RSVD1_LOW                                                                 (4)
`define KV_REG_KEY_CTRL_9_RSVD1_MASK                                                                (32'h1f0)
`define KV_REG_KEY_CTRL_9_DEST_VALID_LOW                                                            (9)
`define KV_REG_KEY_CTRL_9_DEST_VALID_MASK                                                           (32'h3fe00)
`define KV_REG_KEY_CTRL_9_LAST_DWORD_LOW                                                            (18)
`define KV_REG_KEY_CTRL_9_LAST_DWORD_MASK                                                           (32'h3c0000)
`endif
`ifndef KV_REG_KEY_CTRL_10
`define KV_REG_KEY_CTRL_10                                                                          (32'h28)
`define KV_REG_KEY_CTRL_10_LOCK_WR_LOW                                                              (0)
`define KV_REG_KEY_CTRL_10_LOCK_WR_MASK                                                             (32'h1)
`define KV_REG_KEY_CTRL_10_LOCK_USE_LOW                                                             (1)
`define KV_REG_KEY_CTRL_10_LOCK_USE_MASK                                                            (32'h2)
`define KV_REG_KEY_CTRL_10_CLEAR_LOW                                                                (2)
`define KV_REG_KEY_CTRL_10_CLEAR_MASK                                                               (32'h4)
`define KV_REG_KEY_CTRL_10_RSVD0_LOW                                                                (3)
`define KV_REG_KEY_CTRL_10_RSVD0_MASK                                                               (32'h8)
`define KV_REG_KEY_CTRL_10_RSVD1_LOW                                                                (4)
`define KV_REG_KEY_CTRL_10_RSVD1_MASK                                                               (32'h1f0)
`define KV_REG_KEY_CTRL_10_DEST_VALID_LOW                                                           (9)
`define KV_REG_KEY_CTRL_10_DEST_VALID_MASK                                                          (32'h3fe00)
`define KV_REG_KEY_CTRL_10_LAST_DWORD_LOW                                                           (18)
`define KV_REG_KEY_CTRL_10_LAST_DWORD_MASK                                                          (32'h3c0000)
`endif
`ifndef KV_REG_KEY_CTRL_11
`define KV_REG_KEY_CTRL_11                                                                          (32'h2c)
`define KV_REG_KEY_CTRL_11_LOCK_WR_LOW                                                              (0)
`define KV_REG_KEY_CTRL_11_LOCK_WR_MASK                                                             (32'h1)
`define KV_REG_KEY_CTRL_11_LOCK_USE_LOW                                                             (1)
`define KV_REG_KEY_CTRL_11_LOCK_USE_MASK                                                            (32'h2)
`define KV_REG_KEY_CTRL_11_CLEAR_LOW                                                                (2)
`define KV_REG_KEY_CTRL_11_CLEAR_MASK                                                               (32'h4)
`define KV_REG_KEY_CTRL_11_RSVD0_LOW                                                                (3)
`define KV_REG_KEY_CTRL_11_RSVD0_MASK                                                               (32'h8)
`define KV_REG_KEY_CTRL_11_RSVD1_LOW                                                                (4)
`define KV_REG_KEY_CTRL_11_RSVD1_MASK                                                               (32'h1f0)
`define KV_REG_KEY_CTRL_11_DEST_VALID_LOW                                                           (9)
`define KV_REG_KEY_CTRL_11_DEST_VALID_MASK                                                          (32'h3fe00)
`define KV_REG_KEY_CTRL_11_LAST_DWORD_LOW                                                           (18)
`define KV_REG_KEY_CTRL_11_LAST_DWORD_MASK                                                          (32'h3c0000)
`endif
`ifndef KV_REG_KEY_CTRL_12
`define KV_REG_KEY_CTRL_12                                                                          (32'h30)
`define KV_REG_KEY_CTRL_12_LOCK_WR_LOW                                                              (0)
`define KV_REG_KEY_CTRL_12_LOCK_WR_MASK                                                             (32'h1)
`define KV_REG_KEY_CTRL_12_LOCK_USE_LOW                                                             (1)
`define KV_REG_KEY_CTRL_12_LOCK_USE_MASK                                                            (32'h2)
`define KV_REG_KEY_CTRL_12_CLEAR_LOW                                                                (2)
`define KV_REG_KEY_CTRL_12_CLEAR_MASK                                                               (32'h4)
`define KV_REG_KEY_CTRL_12_RSVD0_LOW                                                                (3)
`define KV_REG_KEY_CTRL_12_RSVD0_MASK                                                               (32'h8)
`define KV_REG_KEY_CTRL_12_RSVD1_LOW                                                                (4)
`define KV_REG_KEY_CTRL_12_RSVD1_MASK                                                               (32'h1f0)
`define KV_REG_KEY_CTRL_12_DEST_VALID_LOW                                                           (9)
`define KV_REG_KEY_CTRL_12_DEST_VALID_MASK                                                          (32'h3fe00)
`define KV_REG_KEY_CTRL_12_LAST_DWORD_LOW                                                           (18)
`define KV_REG_KEY_CTRL_12_LAST_DWORD_MASK                                                          (32'h3c0000)
`endif
`ifndef KV_REG_KEY_CTRL_13
`define KV_REG_KEY_CTRL_13                                                                          (32'h34)
`define KV_REG_KEY_CTRL_13_LOCK_WR_LOW                                                              (0)
`define KV_REG_KEY_CTRL_13_LOCK_WR_MASK                                                             (32'h1)
`define KV_REG_KEY_CTRL_13_LOCK_USE_LOW                                                             (1)
`define KV_REG_KEY_CTRL_13_LOCK_USE_MASK                                                            (32'h2)
`define KV_REG_KEY_CTRL_13_CLEAR_LOW                                                                (2)
`define KV_REG_KEY_CTRL_13_CLEAR_MASK                                                               (32'h4)
`define KV_REG_KEY_CTRL_13_RSVD0_LOW                                                                (3)
`define KV_REG_KEY_CTRL_13_RSVD0_MASK                                                               (32'h8)
`define KV_REG_KEY_CTRL_13_RSVD1_LOW                                                                (4)
`define KV_REG_KEY_CTRL_13_RSVD1_MASK                                                               (32'h1f0)
`define KV_REG_KEY_CTRL_13_DEST_VALID_LOW                                                           (9)
`define KV_REG_KEY_CTRL_13_DEST_VALID_MASK                                                          (32'h3fe00)
`define KV_REG_KEY_CTRL_13_LAST_DWORD_LOW                                                           (18)
`define KV_REG_KEY_CTRL_13_LAST_DWORD_MASK                                                          (32'h3c0000)
`endif
`ifndef KV_REG_KEY_CTRL_14
`define KV_REG_KEY_CTRL_14                                                                          (32'h38)
`define KV_REG_KEY_CTRL_14_LOCK_WR_LOW                                                              (0)
`define KV_REG_KEY_CTRL_14_LOCK_WR_MASK                                                             (32'h1)
`define KV_REG_KEY_CTRL_14_LOCK_USE_LOW                                                             (1)
`define KV_REG_KEY_CTRL_14_LOCK_USE_MASK                                                            (32'h2)
`define KV_REG_KEY_CTRL_14_CLEAR_LOW                                                                (2)
`define KV_REG_KEY_CTRL_14_CLEAR_MASK                                                               (32'h4)
`define KV_REG_KEY_CTRL_14_RSVD0_LOW                                                                (3)
`define KV_REG_KEY_CTRL_14_RSVD0_MASK                                                               (32'h8)
`define KV_REG_KEY_CTRL_14_RSVD1_LOW                                                                (4)
`define KV_REG_KEY_CTRL_14_RSVD1_MASK                                                               (32'h1f0)
`define KV_REG_KEY_CTRL_14_DEST_VALID_LOW                                                           (9)
`define KV_REG_KEY_CTRL_14_DEST_VALID_MASK                                                          (32'h3fe00)
`define KV_REG_KEY_CTRL_14_LAST_DWORD_LOW                                                           (18)
`define KV_REG_KEY_CTRL_14_LAST_DWORD_MASK                                                          (32'h3c0000)
`endif
`ifndef KV_REG_KEY_CTRL_15
`define KV_REG_KEY_CTRL_15                                                                          (32'h3c)
`define KV_REG_KEY_CTRL_15_LOCK_WR_LOW                                                              (0)
`define KV_REG_KEY_CTRL_15_LOCK_WR_MASK                                                             (32'h1)
`define KV_REG_KEY_CTRL_15_LOCK_USE_LOW                                                             (1)
`define KV_REG_KEY_CTRL_15_LOCK_USE_MASK                                                            (32'h2)
`define KV_REG_KEY_CTRL_15_CLEAR_LOW                                                                (2)
`define KV_REG_KEY_CTRL_15_CLEAR_MASK                                                               (32'h4)
`define KV_REG_KEY_CTRL_15_RSVD0_LOW                                                                (3)
`define KV_REG_KEY_CTRL_15_RSVD0_MASK                                                               (32'h8)
`define KV_REG_KEY_CTRL_15_RSVD1_LOW                                                                (4)
`define KV_REG_KEY_CTRL_15_RSVD1_MASK                                                               (32'h1f0)
`define KV_REG_KEY_CTRL_15_DEST_VALID_LOW                                                           (9)
`define KV_REG_KEY_CTRL_15_DEST_VALID_MASK                                                          (32'h3fe00)
`define KV_REG_KEY_CTRL_15_LAST_DWORD_LOW                                                           (18)
`define KV_REG_KEY_CTRL_15_LAST_DWORD_MASK                                                          (32'h3c0000)
`endif
`ifndef KV_REG_KEY_CTRL_16
`define KV_REG_KEY_CTRL_16                                                                          (32'h40)
`define KV_REG_KEY_CTRL_16_LOCK_WR_LOW                                                              (0)
`define KV_REG_KEY_CTRL_16_LOCK_WR_MASK                                                             (32'h1)
`define KV_REG_KEY_CTRL_16_LOCK_USE_LOW                                                             (1)
`define KV_REG_KEY_CTRL_16_LOCK_USE_MASK                                                            (32'h2)
`define KV_REG_KEY_CTRL_16_CLEAR_LOW                                                                (2)
`define KV_REG_KEY_CTRL_16_CLEAR_MASK                                                               (32'h4)
`define KV_REG_KEY_CTRL_16_RSVD0_LOW                                                                (3)
`define KV_REG_KEY_CTRL_16_RSVD0_MASK                                                               (32'h8)
`define KV_REG_KEY_CTRL_16_RSVD1_LOW                                                                (4)
`define KV_REG_KEY_CTRL_16_RSVD1_MASK                                                               (32'h1f0)
`define KV_REG_KEY_CTRL_16_DEST_VALID_LOW                                                           (9)
`define KV_REG_KEY_CTRL_16_DEST_VALID_MASK                                                          (32'h3fe00)
`define KV_REG_KEY_CTRL_16_LAST_DWORD_LOW                                                           (18)
`define KV_REG_KEY_CTRL_16_LAST_DWORD_MASK                                                          (32'h3c0000)
`endif
`ifndef KV_REG_KEY_CTRL_17
`define KV_REG_KEY_CTRL_17                                                                          (32'h44)
`define KV_REG_KEY_CTRL_17_LOCK_WR_LOW                                                              (0)
`define KV_REG_KEY_CTRL_17_LOCK_WR_MASK                                                             (32'h1)
`define KV_REG_KEY_CTRL_17_LOCK_USE_LOW                                                             (1)
`define KV_REG_KEY_CTRL_17_LOCK_USE_MASK                                                            (32'h2)
`define KV_REG_KEY_CTRL_17_CLEAR_LOW                                                                (2)
`define KV_REG_KEY_CTRL_17_CLEAR_MASK                                                               (32'h4)
`define KV_REG_KEY_CTRL_17_RSVD0_LOW                                                                (3)
`define KV_REG_KEY_CTRL_17_RSVD0_MASK                                                               (32'h8)
`define KV_REG_KEY_CTRL_17_RSVD1_LOW                                                                (4)
`define KV_REG_KEY_CTRL_17_RSVD1_MASK                                                               (32'h1f0)
`define KV_REG_KEY_CTRL_17_DEST_VALID_LOW                                                           (9)
`define KV_REG_KEY_CTRL_17_DEST_VALID_MASK                                                          (32'h3fe00)
`define KV_REG_KEY_CTRL_17_LAST_DWORD_LOW                                                           (18)
`define KV_REG_KEY_CTRL_17_LAST_DWORD_MASK                                                          (32'h3c0000)
`endif
`ifndef KV_REG_KEY_CTRL_18
`define KV_REG_KEY_CTRL_18                                                                          (32'h48)
`define KV_REG_KEY_CTRL_18_LOCK_WR_LOW                                                              (0)
`define KV_REG_KEY_CTRL_18_LOCK_WR_MASK                                                             (32'h1)
`define KV_REG_KEY_CTRL_18_LOCK_USE_LOW                                                             (1)
`define KV_REG_KEY_CTRL_18_LOCK_USE_MASK                                                            (32'h2)
`define KV_REG_KEY_CTRL_18_CLEAR_LOW                                                                (2)
`define KV_REG_KEY_CTRL_18_CLEAR_MASK                                                               (32'h4)
`define KV_REG_KEY_CTRL_18_RSVD0_LOW                                                                (3)
`define KV_REG_KEY_CTRL_18_RSVD0_MASK                                                               (32'h8)
`define KV_REG_KEY_CTRL_18_RSVD1_LOW                                                                (4)
`define KV_REG_KEY_CTRL_18_RSVD1_MASK                                                               (32'h1f0)
`define KV_REG_KEY_CTRL_18_DEST_VALID_LOW                                                           (9)
`define KV_REG_KEY_CTRL_18_DEST_VALID_MASK                                                          (32'h3fe00)
`define KV_REG_KEY_CTRL_18_LAST_DWORD_LOW                                                           (18)
`define KV_REG_KEY_CTRL_18_LAST_DWORD_MASK                                                          (32'h3c0000)
`endif
`ifndef KV_REG_KEY_CTRL_19
`define KV_REG_KEY_CTRL_19                                                                          (32'h4c)
`define KV_REG_KEY_CTRL_19_LOCK_WR_LOW                                                              (0)
`define KV_REG_KEY_CTRL_19_LOCK_WR_MASK                                                             (32'h1)
`define KV_REG_KEY_CTRL_19_LOCK_USE_LOW                                                             (1)
`define KV_REG_KEY_CTRL_19_LOCK_USE_MASK                                                            (32'h2)
`define KV_REG_KEY_CTRL_19_CLEAR_LOW                                                                (2)
`define KV_REG_KEY_CTRL_19_CLEAR_MASK                                                               (32'h4)
`define KV_REG_KEY_CTRL_19_RSVD0_LOW                                                                (3)
`define KV_REG_KEY_CTRL_19_RSVD0_MASK                                                               (32'h8)
`define KV_REG_KEY_CTRL_19_RSVD1_LOW                                                                (4)
`define KV_REG_KEY_CTRL_19_RSVD1_MASK                                                               (32'h1f0)
`define KV_REG_KEY_CTRL_19_DEST_VALID_LOW                                                           (9)
`define KV_REG_KEY_CTRL_19_DEST_VALID_MASK                                                          (32'h3fe00)
`define KV_REG_KEY_CTRL_19_LAST_DWORD_LOW                                                           (18)
`define KV_REG_KEY_CTRL_19_LAST_DWORD_MASK                                                          (32'h3c0000)
`endif
`ifndef KV_REG_KEY_CTRL_20
`define KV_REG_KEY_CTRL_20                                                                          (32'h50)
`define KV_REG_KEY_CTRL_20_LOCK_WR_LOW                                                              (0)
`define KV_REG_KEY_CTRL_20_LOCK_WR_MASK                                                             (32'h1)
`define KV_REG_KEY_CTRL_20_LOCK_USE_LOW                                                             (1)
`define KV_REG_KEY_CTRL_20_LOCK_USE_MASK                                                            (32'h2)
`define KV_REG_KEY_CTRL_20_CLEAR_LOW                                                                (2)
`define KV_REG_KEY_CTRL_20_CLEAR_MASK                                                               (32'h4)
`define KV_REG_KEY_CTRL_20_RSVD0_LOW                                                                (3)
`define KV_REG_KEY_CTRL_20_RSVD0_MASK                                                               (32'h8)
`define KV_REG_KEY_CTRL_20_RSVD1_LOW                                                                (4)
`define KV_REG_KEY_CTRL_20_RSVD1_MASK                                                               (32'h1f0)
`define KV_REG_KEY_CTRL_20_DEST_VALID_LOW                                                           (9)
`define KV_REG_KEY_CTRL_20_DEST_VALID_MASK                                                          (32'h3fe00)
`define KV_REG_KEY_CTRL_20_LAST_DWORD_LOW                                                           (18)
`define KV_REG_KEY_CTRL_20_LAST_DWORD_MASK                                                          (32'h3c0000)
`endif
`ifndef KV_REG_KEY_CTRL_21
`define KV_REG_KEY_CTRL_21                                                                          (32'h54)
`define KV_REG_KEY_CTRL_21_LOCK_WR_LOW                                                              (0)
`define KV_REG_KEY_CTRL_21_LOCK_WR_MASK                                                             (32'h1)
`define KV_REG_KEY_CTRL_21_LOCK_USE_LOW                                                             (1)
`define KV_REG_KEY_CTRL_21_LOCK_USE_MASK                                                            (32'h2)
`define KV_REG_KEY_CTRL_21_CLEAR_LOW                                                                (2)
`define KV_REG_KEY_CTRL_21_CLEAR_MASK                                                               (32'h4)
`define KV_REG_KEY_CTRL_21_RSVD0_LOW                                                                (3)
`define KV_REG_KEY_CTRL_21_RSVD0_MASK                                                               (32'h8)
`define KV_REG_KEY_CTRL_21_RSVD1_LOW                                                                (4)
`define KV_REG_KEY_CTRL_21_RSVD1_MASK                                                               (32'h1f0)
`define KV_REG_KEY_CTRL_21_DEST_VALID_LOW                                                           (9)
`define KV_REG_KEY_CTRL_21_DEST_VALID_MASK                                                          (32'h3fe00)
`define KV_REG_KEY_CTRL_21_LAST_DWORD_LOW                                                           (18)
`define KV_REG_KEY_CTRL_21_LAST_DWORD_MASK                                                          (32'h3c0000)
`endif
`ifndef KV_REG_KEY_CTRL_22
`define KV_REG_KEY_CTRL_22                                                                          (32'h58)
`define KV_REG_KEY_CTRL_22_LOCK_WR_LOW                                                              (0)
`define KV_REG_KEY_CTRL_22_LOCK_WR_MASK                                                             (32'h1)
`define KV_REG_KEY_CTRL_22_LOCK_USE_LOW                                                             (1)
`define KV_REG_KEY_CTRL_22_LOCK_USE_MASK                                                            (32'h2)
`define KV_REG_KEY_CTRL_22_CLEAR_LOW                                                                (2)
`define KV_REG_KEY_CTRL_22_CLEAR_MASK                                                               (32'h4)
`define KV_REG_KEY_CTRL_22_RSVD0_LOW                                                                (3)
`define KV_REG_KEY_CTRL_22_RSVD0_MASK                                                               (32'h8)
`define KV_REG_KEY_CTRL_22_RSVD1_LOW                                                                (4)
`define KV_REG_KEY_CTRL_22_RSVD1_MASK                                                               (32'h1f0)
`define KV_REG_KEY_CTRL_22_DEST_VALID_LOW                                                           (9)
`define KV_REG_KEY_CTRL_22_DEST_VALID_MASK                                                          (32'h3fe00)
`define KV_REG_KEY_CTRL_22_LAST_DWORD_LOW                                                           (18)
`define KV_REG_KEY_CTRL_22_LAST_DWORD_MASK                                                          (32'h3c0000)
`endif
`ifndef KV_REG_KEY_CTRL_23
`define KV_REG_KEY_CTRL_23                                                                          (32'h5c)
`define KV_REG_KEY_CTRL_23_LOCK_WR_LOW                                                              (0)
`define KV_REG_KEY_CTRL_23_LOCK_WR_MASK                                                             (32'h1)
`define KV_REG_KEY_CTRL_23_LOCK_USE_LOW                                                             (1)
`define KV_REG_KEY_CTRL_23_LOCK_USE_MASK                                                            (32'h2)
`define KV_REG_KEY_CTRL_23_CLEAR_LOW                                                                (2)
`define KV_REG_KEY_CTRL_23_CLEAR_MASK                                                               (32'h4)
`define KV_REG_KEY_CTRL_23_RSVD0_LOW                                                                (3)
`define KV_REG_KEY_CTRL_23_RSVD0_MASK                                                               (32'h8)
`define KV_REG_KEY_CTRL_23_RSVD1_LOW                                                                (4)
`define KV_REG_KEY_CTRL_23_RSVD1_MASK                                                               (32'h1f0)
`define KV_REG_KEY_CTRL_23_DEST_VALID_LOW                                                           (9)
`define KV_REG_KEY_CTRL_23_DEST_VALID_MASK                                                          (32'h3fe00)
`define KV_REG_KEY_CTRL_23_LAST_DWORD_LOW                                                           (18)
`define KV_REG_KEY_CTRL_23_LAST_DWORD_MASK                                                          (32'h3c0000)
`endif
`ifndef KV_REG_KEY_ENTRY_0_0
`define KV_REG_KEY_ENTRY_0_0                                                                        (32'h600)
`endif
`ifndef KV_REG_KEY_ENTRY_0_1
`define KV_REG_KEY_ENTRY_0_1                                                                        (32'h604)
`endif
`ifndef KV_REG_KEY_ENTRY_0_2
`define KV_REG_KEY_ENTRY_0_2                                                                        (32'h608)
`endif
`ifndef KV_REG_KEY_ENTRY_0_3
`define KV_REG_KEY_ENTRY_0_3                                                                        (32'h60c)
`endif
`ifndef KV_REG_KEY_ENTRY_0_4
`define KV_REG_KEY_ENTRY_0_4                                                                        (32'h610)
`endif
`ifndef KV_REG_KEY_ENTRY_0_5
`define KV_REG_KEY_ENTRY_0_5                                                                        (32'h614)
`endif
`ifndef KV_REG_KEY_ENTRY_0_6
`define KV_REG_KEY_ENTRY_0_6                                                                        (32'h618)
`endif
`ifndef KV_REG_KEY_ENTRY_0_7
`define KV_REG_KEY_ENTRY_0_7                                                                        (32'h61c)
`endif
`ifndef KV_REG_KEY_ENTRY_0_8
`define KV_REG_KEY_ENTRY_0_8                                                                        (32'h620)
`endif
`ifndef KV_REG_KEY_ENTRY_0_9
`define KV_REG_KEY_ENTRY_0_9                                                                        (32'h624)
`endif
`ifndef KV_REG_KEY_ENTRY_0_10
`define KV_REG_KEY_ENTRY_0_10                                                                       (32'h628)
`endif
`ifndef KV_REG_KEY_ENTRY_0_11
`define KV_REG_KEY_ENTRY_0_11                                                                       (32'h62c)
`endif
`ifndef KV_REG_KEY_ENTRY_0_12
`define KV_REG_KEY_ENTRY_0_12                                                                       (32'h630)
`endif
`ifndef KV_REG_KEY_ENTRY_0_13
`define KV_REG_KEY_ENTRY_0_13                                                                       (32'h634)
`endif
`ifndef KV_REG_KEY_ENTRY_0_14
`define KV_REG_KEY_ENTRY_0_14                                                                       (32'h638)
`endif
`ifndef KV_REG_KEY_ENTRY_0_15
`define KV_REG_KEY_ENTRY_0_15                                                                       (32'h63c)
`endif
`ifndef KV_REG_KEY_ENTRY_1_0
`define KV_REG_KEY_ENTRY_1_0                                                                        (32'h640)
`endif
`ifndef KV_REG_KEY_ENTRY_1_1
`define KV_REG_KEY_ENTRY_1_1                                                                        (32'h644)
`endif
`ifndef KV_REG_KEY_ENTRY_1_2
`define KV_REG_KEY_ENTRY_1_2                                                                        (32'h648)
`endif
`ifndef KV_REG_KEY_ENTRY_1_3
`define KV_REG_KEY_ENTRY_1_3                                                                        (32'h64c)
`endif
`ifndef KV_REG_KEY_ENTRY_1_4
`define KV_REG_KEY_ENTRY_1_4                                                                        (32'h650)
`endif
`ifndef KV_REG_KEY_ENTRY_1_5
`define KV_REG_KEY_ENTRY_1_5                                                                        (32'h654)
`endif
`ifndef KV_REG_KEY_ENTRY_1_6
`define KV_REG_KEY_ENTRY_1_6                                                                        (32'h658)
`endif
`ifndef KV_REG_KEY_ENTRY_1_7
`define KV_REG_KEY_ENTRY_1_7                                                                        (32'h65c)
`endif
`ifndef KV_REG_KEY_ENTRY_1_8
`define KV_REG_KEY_ENTRY_1_8                                                                        (32'h660)
`endif
`ifndef KV_REG_KEY_ENTRY_1_9
`define KV_REG_KEY_ENTRY_1_9                                                                        (32'h664)
`endif
`ifndef KV_REG_KEY_ENTRY_1_10
`define KV_REG_KEY_ENTRY_1_10                                                                       (32'h668)
`endif
`ifndef KV_REG_KEY_ENTRY_1_11
`define KV_REG_KEY_ENTRY_1_11                                                                       (32'h66c)
`endif
`ifndef KV_REG_KEY_ENTRY_1_12
`define KV_REG_KEY_ENTRY_1_12                                                                       (32'h670)
`endif
`ifndef KV_REG_KEY_ENTRY_1_13
`define KV_REG_KEY_ENTRY_1_13                                                                       (32'h674)
`endif
`ifndef KV_REG_KEY_ENTRY_1_14
`define KV_REG_KEY_ENTRY_1_14                                                                       (32'h678)
`endif
`ifndef KV_REG_KEY_ENTRY_1_15
`define KV_REG_KEY_ENTRY_1_15                                                                       (32'h67c)
`endif
`ifndef KV_REG_KEY_ENTRY_2_0
`define KV_REG_KEY_ENTRY_2_0                                                                        (32'h680)
`endif
`ifndef KV_REG_KEY_ENTRY_2_1
`define KV_REG_KEY_ENTRY_2_1                                                                        (32'h684)
`endif
`ifndef KV_REG_KEY_ENTRY_2_2
`define KV_REG_KEY_ENTRY_2_2                                                                        (32'h688)
`endif
`ifndef KV_REG_KEY_ENTRY_2_3
`define KV_REG_KEY_ENTRY_2_3                                                                        (32'h68c)
`endif
`ifndef KV_REG_KEY_ENTRY_2_4
`define KV_REG_KEY_ENTRY_2_4                                                                        (32'h690)
`endif
`ifndef KV_REG_KEY_ENTRY_2_5
`define KV_REG_KEY_ENTRY_2_5                                                                        (32'h694)
`endif
`ifndef KV_REG_KEY_ENTRY_2_6
`define KV_REG_KEY_ENTRY_2_6                                                                        (32'h698)
`endif
`ifndef KV_REG_KEY_ENTRY_2_7
`define KV_REG_KEY_ENTRY_2_7                                                                        (32'h69c)
`endif
`ifndef KV_REG_KEY_ENTRY_2_8
`define KV_REG_KEY_ENTRY_2_8                                                                        (32'h6a0)
`endif
`ifndef KV_REG_KEY_ENTRY_2_9
`define KV_REG_KEY_ENTRY_2_9                                                                        (32'h6a4)
`endif
`ifndef KV_REG_KEY_ENTRY_2_10
`define KV_REG_KEY_ENTRY_2_10                                                                       (32'h6a8)
`endif
`ifndef KV_REG_KEY_ENTRY_2_11
`define KV_REG_KEY_ENTRY_2_11                                                                       (32'h6ac)
`endif
`ifndef KV_REG_KEY_ENTRY_2_12
`define KV_REG_KEY_ENTRY_2_12                                                                       (32'h6b0)
`endif
`ifndef KV_REG_KEY_ENTRY_2_13
`define KV_REG_KEY_ENTRY_2_13                                                                       (32'h6b4)
`endif
`ifndef KV_REG_KEY_ENTRY_2_14
`define KV_REG_KEY_ENTRY_2_14                                                                       (32'h6b8)
`endif
`ifndef KV_REG_KEY_ENTRY_2_15
`define KV_REG_KEY_ENTRY_2_15                                                                       (32'h6bc)
`endif
`ifndef KV_REG_KEY_ENTRY_3_0
`define KV_REG_KEY_ENTRY_3_0                                                                        (32'h6c0)
`endif
`ifndef KV_REG_KEY_ENTRY_3_1
`define KV_REG_KEY_ENTRY_3_1                                                                        (32'h6c4)
`endif
`ifndef KV_REG_KEY_ENTRY_3_2
`define KV_REG_KEY_ENTRY_3_2                                                                        (32'h6c8)
`endif
`ifndef KV_REG_KEY_ENTRY_3_3
`define KV_REG_KEY_ENTRY_3_3                                                                        (32'h6cc)
`endif
`ifndef KV_REG_KEY_ENTRY_3_4
`define KV_REG_KEY_ENTRY_3_4                                                                        (32'h6d0)
`endif
`ifndef KV_REG_KEY_ENTRY_3_5
`define KV_REG_KEY_ENTRY_3_5                                                                        (32'h6d4)
`endif
`ifndef KV_REG_KEY_ENTRY_3_6
`define KV_REG_KEY_ENTRY_3_6                                                                        (32'h6d8)
`endif
`ifndef KV_REG_KEY_ENTRY_3_7
`define KV_REG_KEY_ENTRY_3_7                                                                        (32'h6dc)
`endif
`ifndef KV_REG_KEY_ENTRY_3_8
`define KV_REG_KEY_ENTRY_3_8                                                                        (32'h6e0)
`endif
`ifndef KV_REG_KEY_ENTRY_3_9
`define KV_REG_KEY_ENTRY_3_9                                                                        (32'h6e4)
`endif
`ifndef KV_REG_KEY_ENTRY_3_10
`define KV_REG_KEY_ENTRY_3_10                                                                       (32'h6e8)
`endif
`ifndef KV_REG_KEY_ENTRY_3_11
`define KV_REG_KEY_ENTRY_3_11                                                                       (32'h6ec)
`endif
`ifndef KV_REG_KEY_ENTRY_3_12
`define KV_REG_KEY_ENTRY_3_12                                                                       (32'h6f0)
`endif
`ifndef KV_REG_KEY_ENTRY_3_13
`define KV_REG_KEY_ENTRY_3_13                                                                       (32'h6f4)
`endif
`ifndef KV_REG_KEY_ENTRY_3_14
`define KV_REG_KEY_ENTRY_3_14                                                                       (32'h6f8)
`endif
`ifndef KV_REG_KEY_ENTRY_3_15
`define KV_REG_KEY_ENTRY_3_15                                                                       (32'h6fc)
`endif
`ifndef KV_REG_KEY_ENTRY_4_0
`define KV_REG_KEY_ENTRY_4_0                                                                        (32'h700)
`endif
`ifndef KV_REG_KEY_ENTRY_4_1
`define KV_REG_KEY_ENTRY_4_1                                                                        (32'h704)
`endif
`ifndef KV_REG_KEY_ENTRY_4_2
`define KV_REG_KEY_ENTRY_4_2                                                                        (32'h708)
`endif
`ifndef KV_REG_KEY_ENTRY_4_3
`define KV_REG_KEY_ENTRY_4_3                                                                        (32'h70c)
`endif
`ifndef KV_REG_KEY_ENTRY_4_4
`define KV_REG_KEY_ENTRY_4_4                                                                        (32'h710)
`endif
`ifndef KV_REG_KEY_ENTRY_4_5
`define KV_REG_KEY_ENTRY_4_5                                                                        (32'h714)
`endif
`ifndef KV_REG_KEY_ENTRY_4_6
`define KV_REG_KEY_ENTRY_4_6                                                                        (32'h718)
`endif
`ifndef KV_REG_KEY_ENTRY_4_7
`define KV_REG_KEY_ENTRY_4_7                                                                        (32'h71c)
`endif
`ifndef KV_REG_KEY_ENTRY_4_8
`define KV_REG_KEY_ENTRY_4_8                                                                        (32'h720)
`endif
`ifndef KV_REG_KEY_ENTRY_4_9
`define KV_REG_KEY_ENTRY_4_9                                                                        (32'h724)
`endif
`ifndef KV_REG_KEY_ENTRY_4_10
`define KV_REG_KEY_ENTRY_4_10                                                                       (32'h728)
`endif
`ifndef KV_REG_KEY_ENTRY_4_11
`define KV_REG_KEY_ENTRY_4_11                                                                       (32'h72c)
`endif
`ifndef KV_REG_KEY_ENTRY_4_12
`define KV_REG_KEY_ENTRY_4_12                                                                       (32'h730)
`endif
`ifndef KV_REG_KEY_ENTRY_4_13
`define KV_REG_KEY_ENTRY_4_13                                                                       (32'h734)
`endif
`ifndef KV_REG_KEY_ENTRY_4_14
`define KV_REG_KEY_ENTRY_4_14                                                                       (32'h738)
`endif
`ifndef KV_REG_KEY_ENTRY_4_15
`define KV_REG_KEY_ENTRY_4_15                                                                       (32'h73c)
`endif
`ifndef KV_REG_KEY_ENTRY_5_0
`define KV_REG_KEY_ENTRY_5_0                                                                        (32'h740)
`endif
`ifndef KV_REG_KEY_ENTRY_5_1
`define KV_REG_KEY_ENTRY_5_1                                                                        (32'h744)
`endif
`ifndef KV_REG_KEY_ENTRY_5_2
`define KV_REG_KEY_ENTRY_5_2                                                                        (32'h748)
`endif
`ifndef KV_REG_KEY_ENTRY_5_3
`define KV_REG_KEY_ENTRY_5_3                                                                        (32'h74c)
`endif
`ifndef KV_REG_KEY_ENTRY_5_4
`define KV_REG_KEY_ENTRY_5_4                                                                        (32'h750)
`endif
`ifndef KV_REG_KEY_ENTRY_5_5
`define KV_REG_KEY_ENTRY_5_5                                                                        (32'h754)
`endif
`ifndef KV_REG_KEY_ENTRY_5_6
`define KV_REG_KEY_ENTRY_5_6                                                                        (32'h758)
`endif
`ifndef KV_REG_KEY_ENTRY_5_7
`define KV_REG_KEY_ENTRY_5_7                                                                        (32'h75c)
`endif
`ifndef KV_REG_KEY_ENTRY_5_8
`define KV_REG_KEY_ENTRY_5_8                                                                        (32'h760)
`endif
`ifndef KV_REG_KEY_ENTRY_5_9
`define KV_REG_KEY_ENTRY_5_9                                                                        (32'h764)
`endif
`ifndef KV_REG_KEY_ENTRY_5_10
`define KV_REG_KEY_ENTRY_5_10                                                                       (32'h768)
`endif
`ifndef KV_REG_KEY_ENTRY_5_11
`define KV_REG_KEY_ENTRY_5_11                                                                       (32'h76c)
`endif
`ifndef KV_REG_KEY_ENTRY_5_12
`define KV_REG_KEY_ENTRY_5_12                                                                       (32'h770)
`endif
`ifndef KV_REG_KEY_ENTRY_5_13
`define KV_REG_KEY_ENTRY_5_13                                                                       (32'h774)
`endif
`ifndef KV_REG_KEY_ENTRY_5_14
`define KV_REG_KEY_ENTRY_5_14                                                                       (32'h778)
`endif
`ifndef KV_REG_KEY_ENTRY_5_15
`define KV_REG_KEY_ENTRY_5_15                                                                       (32'h77c)
`endif
`ifndef KV_REG_KEY_ENTRY_6_0
`define KV_REG_KEY_ENTRY_6_0                                                                        (32'h780)
`endif
`ifndef KV_REG_KEY_ENTRY_6_1
`define KV_REG_KEY_ENTRY_6_1                                                                        (32'h784)
`endif
`ifndef KV_REG_KEY_ENTRY_6_2
`define KV_REG_KEY_ENTRY_6_2                                                                        (32'h788)
`endif
`ifndef KV_REG_KEY_ENTRY_6_3
`define KV_REG_KEY_ENTRY_6_3                                                                        (32'h78c)
`endif
`ifndef KV_REG_KEY_ENTRY_6_4
`define KV_REG_KEY_ENTRY_6_4                                                                        (32'h790)
`endif
`ifndef KV_REG_KEY_ENTRY_6_5
`define KV_REG_KEY_ENTRY_6_5                                                                        (32'h794)
`endif
`ifndef KV_REG_KEY_ENTRY_6_6
`define KV_REG_KEY_ENTRY_6_6                                                                        (32'h798)
`endif
`ifndef KV_REG_KEY_ENTRY_6_7
`define KV_REG_KEY_ENTRY_6_7                                                                        (32'h79c)
`endif
`ifndef KV_REG_KEY_ENTRY_6_8
`define KV_REG_KEY_ENTRY_6_8                                                                        (32'h7a0)
`endif
`ifndef KV_REG_KEY_ENTRY_6_9
`define KV_REG_KEY_ENTRY_6_9                                                                        (32'h7a4)
`endif
`ifndef KV_REG_KEY_ENTRY_6_10
`define KV_REG_KEY_ENTRY_6_10                                                                       (32'h7a8)
`endif
`ifndef KV_REG_KEY_ENTRY_6_11
`define KV_REG_KEY_ENTRY_6_11                                                                       (32'h7ac)
`endif
`ifndef KV_REG_KEY_ENTRY_6_12
`define KV_REG_KEY_ENTRY_6_12                                                                       (32'h7b0)
`endif
`ifndef KV_REG_KEY_ENTRY_6_13
`define KV_REG_KEY_ENTRY_6_13                                                                       (32'h7b4)
`endif
`ifndef KV_REG_KEY_ENTRY_6_14
`define KV_REG_KEY_ENTRY_6_14                                                                       (32'h7b8)
`endif
`ifndef KV_REG_KEY_ENTRY_6_15
`define KV_REG_KEY_ENTRY_6_15                                                                       (32'h7bc)
`endif
`ifndef KV_REG_KEY_ENTRY_7_0
`define KV_REG_KEY_ENTRY_7_0                                                                        (32'h7c0)
`endif
`ifndef KV_REG_KEY_ENTRY_7_1
`define KV_REG_KEY_ENTRY_7_1                                                                        (32'h7c4)
`endif
`ifndef KV_REG_KEY_ENTRY_7_2
`define KV_REG_KEY_ENTRY_7_2                                                                        (32'h7c8)
`endif
`ifndef KV_REG_KEY_ENTRY_7_3
`define KV_REG_KEY_ENTRY_7_3                                                                        (32'h7cc)
`endif
`ifndef KV_REG_KEY_ENTRY_7_4
`define KV_REG_KEY_ENTRY_7_4                                                                        (32'h7d0)
`endif
`ifndef KV_REG_KEY_ENTRY_7_5
`define KV_REG_KEY_ENTRY_7_5                                                                        (32'h7d4)
`endif
`ifndef KV_REG_KEY_ENTRY_7_6
`define KV_REG_KEY_ENTRY_7_6                                                                        (32'h7d8)
`endif
`ifndef KV_REG_KEY_ENTRY_7_7
`define KV_REG_KEY_ENTRY_7_7                                                                        (32'h7dc)
`endif
`ifndef KV_REG_KEY_ENTRY_7_8
`define KV_REG_KEY_ENTRY_7_8                                                                        (32'h7e0)
`endif
`ifndef KV_REG_KEY_ENTRY_7_9
`define KV_REG_KEY_ENTRY_7_9                                                                        (32'h7e4)
`endif
`ifndef KV_REG_KEY_ENTRY_7_10
`define KV_REG_KEY_ENTRY_7_10                                                                       (32'h7e8)
`endif
`ifndef KV_REG_KEY_ENTRY_7_11
`define KV_REG_KEY_ENTRY_7_11                                                                       (32'h7ec)
`endif
`ifndef KV_REG_KEY_ENTRY_7_12
`define KV_REG_KEY_ENTRY_7_12                                                                       (32'h7f0)
`endif
`ifndef KV_REG_KEY_ENTRY_7_13
`define KV_REG_KEY_ENTRY_7_13                                                                       (32'h7f4)
`endif
`ifndef KV_REG_KEY_ENTRY_7_14
`define KV_REG_KEY_ENTRY_7_14                                                                       (32'h7f8)
`endif
`ifndef KV_REG_KEY_ENTRY_7_15
`define KV_REG_KEY_ENTRY_7_15                                                                       (32'h7fc)
`endif
`ifndef KV_REG_KEY_ENTRY_8_0
`define KV_REG_KEY_ENTRY_8_0                                                                        (32'h800)
`endif
`ifndef KV_REG_KEY_ENTRY_8_1
`define KV_REG_KEY_ENTRY_8_1                                                                        (32'h804)
`endif
`ifndef KV_REG_KEY_ENTRY_8_2
`define KV_REG_KEY_ENTRY_8_2                                                                        (32'h808)
`endif
`ifndef KV_REG_KEY_ENTRY_8_3
`define KV_REG_KEY_ENTRY_8_3                                                                        (32'h80c)
`endif
`ifndef KV_REG_KEY_ENTRY_8_4
`define KV_REG_KEY_ENTRY_8_4                                                                        (32'h810)
`endif
`ifndef KV_REG_KEY_ENTRY_8_5
`define KV_REG_KEY_ENTRY_8_5                                                                        (32'h814)
`endif
`ifndef KV_REG_KEY_ENTRY_8_6
`define KV_REG_KEY_ENTRY_8_6                                                                        (32'h818)
`endif
`ifndef KV_REG_KEY_ENTRY_8_7
`define KV_REG_KEY_ENTRY_8_7                                                                        (32'h81c)
`endif
`ifndef KV_REG_KEY_ENTRY_8_8
`define KV_REG_KEY_ENTRY_8_8                                                                        (32'h820)
`endif
`ifndef KV_REG_KEY_ENTRY_8_9
`define KV_REG_KEY_ENTRY_8_9                                                                        (32'h824)
`endif
`ifndef KV_REG_KEY_ENTRY_8_10
`define KV_REG_KEY_ENTRY_8_10                                                                       (32'h828)
`endif
`ifndef KV_REG_KEY_ENTRY_8_11
`define KV_REG_KEY_ENTRY_8_11                                                                       (32'h82c)
`endif
`ifndef KV_REG_KEY_ENTRY_8_12
`define KV_REG_KEY_ENTRY_8_12                                                                       (32'h830)
`endif
`ifndef KV_REG_KEY_ENTRY_8_13
`define KV_REG_KEY_ENTRY_8_13                                                                       (32'h834)
`endif
`ifndef KV_REG_KEY_ENTRY_8_14
`define KV_REG_KEY_ENTRY_8_14                                                                       (32'h838)
`endif
`ifndef KV_REG_KEY_ENTRY_8_15
`define KV_REG_KEY_ENTRY_8_15                                                                       (32'h83c)
`endif
`ifndef KV_REG_KEY_ENTRY_9_0
`define KV_REG_KEY_ENTRY_9_0                                                                        (32'h840)
`endif
`ifndef KV_REG_KEY_ENTRY_9_1
`define KV_REG_KEY_ENTRY_9_1                                                                        (32'h844)
`endif
`ifndef KV_REG_KEY_ENTRY_9_2
`define KV_REG_KEY_ENTRY_9_2                                                                        (32'h848)
`endif
`ifndef KV_REG_KEY_ENTRY_9_3
`define KV_REG_KEY_ENTRY_9_3                                                                        (32'h84c)
`endif
`ifndef KV_REG_KEY_ENTRY_9_4
`define KV_REG_KEY_ENTRY_9_4                                                                        (32'h850)
`endif
`ifndef KV_REG_KEY_ENTRY_9_5
`define KV_REG_KEY_ENTRY_9_5                                                                        (32'h854)
`endif
`ifndef KV_REG_KEY_ENTRY_9_6
`define KV_REG_KEY_ENTRY_9_6                                                                        (32'h858)
`endif
`ifndef KV_REG_KEY_ENTRY_9_7
`define KV_REG_KEY_ENTRY_9_7                                                                        (32'h85c)
`endif
`ifndef KV_REG_KEY_ENTRY_9_8
`define KV_REG_KEY_ENTRY_9_8                                                                        (32'h860)
`endif
`ifndef KV_REG_KEY_ENTRY_9_9
`define KV_REG_KEY_ENTRY_9_9                                                                        (32'h864)
`endif
`ifndef KV_REG_KEY_ENTRY_9_10
`define KV_REG_KEY_ENTRY_9_10                                                                       (32'h868)
`endif
`ifndef KV_REG_KEY_ENTRY_9_11
`define KV_REG_KEY_ENTRY_9_11                                                                       (32'h86c)
`endif
`ifndef KV_REG_KEY_ENTRY_9_12
`define KV_REG_KEY_ENTRY_9_12                                                                       (32'h870)
`endif
`ifndef KV_REG_KEY_ENTRY_9_13
`define KV_REG_KEY_ENTRY_9_13                                                                       (32'h874)
`endif
`ifndef KV_REG_KEY_ENTRY_9_14
`define KV_REG_KEY_ENTRY_9_14                                                                       (32'h878)
`endif
`ifndef KV_REG_KEY_ENTRY_9_15
`define KV_REG_KEY_ENTRY_9_15                                                                       (32'h87c)
`endif
`ifndef KV_REG_KEY_ENTRY_10_0
`define KV_REG_KEY_ENTRY_10_0                                                                       (32'h880)
`endif
`ifndef KV_REG_KEY_ENTRY_10_1
`define KV_REG_KEY_ENTRY_10_1                                                                       (32'h884)
`endif
`ifndef KV_REG_KEY_ENTRY_10_2
`define KV_REG_KEY_ENTRY_10_2                                                                       (32'h888)
`endif
`ifndef KV_REG_KEY_ENTRY_10_3
`define KV_REG_KEY_ENTRY_10_3                                                                       (32'h88c)
`endif
`ifndef KV_REG_KEY_ENTRY_10_4
`define KV_REG_KEY_ENTRY_10_4                                                                       (32'h890)
`endif
`ifndef KV_REG_KEY_ENTRY_10_5
`define KV_REG_KEY_ENTRY_10_5                                                                       (32'h894)
`endif
`ifndef KV_REG_KEY_ENTRY_10_6
`define KV_REG_KEY_ENTRY_10_6                                                                       (32'h898)
`endif
`ifndef KV_REG_KEY_ENTRY_10_7
`define KV_REG_KEY_ENTRY_10_7                                                                       (32'h89c)
`endif
`ifndef KV_REG_KEY_ENTRY_10_8
`define KV_REG_KEY_ENTRY_10_8                                                                       (32'h8a0)
`endif
`ifndef KV_REG_KEY_ENTRY_10_9
`define KV_REG_KEY_ENTRY_10_9                                                                       (32'h8a4)
`endif
`ifndef KV_REG_KEY_ENTRY_10_10
`define KV_REG_KEY_ENTRY_10_10                                                                      (32'h8a8)
`endif
`ifndef KV_REG_KEY_ENTRY_10_11
`define KV_REG_KEY_ENTRY_10_11                                                                      (32'h8ac)
`endif
`ifndef KV_REG_KEY_ENTRY_10_12
`define KV_REG_KEY_ENTRY_10_12                                                                      (32'h8b0)
`endif
`ifndef KV_REG_KEY_ENTRY_10_13
`define KV_REG_KEY_ENTRY_10_13                                                                      (32'h8b4)
`endif
`ifndef KV_REG_KEY_ENTRY_10_14
`define KV_REG_KEY_ENTRY_10_14                                                                      (32'h8b8)
`endif
`ifndef KV_REG_KEY_ENTRY_10_15
`define KV_REG_KEY_ENTRY_10_15                                                                      (32'h8bc)
`endif
`ifndef KV_REG_KEY_ENTRY_11_0
`define KV_REG_KEY_ENTRY_11_0                                                                       (32'h8c0)
`endif
`ifndef KV_REG_KEY_ENTRY_11_1
`define KV_REG_KEY_ENTRY_11_1                                                                       (32'h8c4)
`endif
`ifndef KV_REG_KEY_ENTRY_11_2
`define KV_REG_KEY_ENTRY_11_2                                                                       (32'h8c8)
`endif
`ifndef KV_REG_KEY_ENTRY_11_3
`define KV_REG_KEY_ENTRY_11_3                                                                       (32'h8cc)
`endif
`ifndef KV_REG_KEY_ENTRY_11_4
`define KV_REG_KEY_ENTRY_11_4                                                                       (32'h8d0)
`endif
`ifndef KV_REG_KEY_ENTRY_11_5
`define KV_REG_KEY_ENTRY_11_5                                                                       (32'h8d4)
`endif
`ifndef KV_REG_KEY_ENTRY_11_6
`define KV_REG_KEY_ENTRY_11_6                                                                       (32'h8d8)
`endif
`ifndef KV_REG_KEY_ENTRY_11_7
`define KV_REG_KEY_ENTRY_11_7                                                                       (32'h8dc)
`endif
`ifndef KV_REG_KEY_ENTRY_11_8
`define KV_REG_KEY_ENTRY_11_8                                                                       (32'h8e0)
`endif
`ifndef KV_REG_KEY_ENTRY_11_9
`define KV_REG_KEY_ENTRY_11_9                                                                       (32'h8e4)
`endif
`ifndef KV_REG_KEY_ENTRY_11_10
`define KV_REG_KEY_ENTRY_11_10                                                                      (32'h8e8)
`endif
`ifndef KV_REG_KEY_ENTRY_11_11
`define KV_REG_KEY_ENTRY_11_11                                                                      (32'h8ec)
`endif
`ifndef KV_REG_KEY_ENTRY_11_12
`define KV_REG_KEY_ENTRY_11_12                                                                      (32'h8f0)
`endif
`ifndef KV_REG_KEY_ENTRY_11_13
`define KV_REG_KEY_ENTRY_11_13                                                                      (32'h8f4)
`endif
`ifndef KV_REG_KEY_ENTRY_11_14
`define KV_REG_KEY_ENTRY_11_14                                                                      (32'h8f8)
`endif
`ifndef KV_REG_KEY_ENTRY_11_15
`define KV_REG_KEY_ENTRY_11_15                                                                      (32'h8fc)
`endif
`ifndef KV_REG_KEY_ENTRY_12_0
`define KV_REG_KEY_ENTRY_12_0                                                                       (32'h900)
`endif
`ifndef KV_REG_KEY_ENTRY_12_1
`define KV_REG_KEY_ENTRY_12_1                                                                       (32'h904)
`endif
`ifndef KV_REG_KEY_ENTRY_12_2
`define KV_REG_KEY_ENTRY_12_2                                                                       (32'h908)
`endif
`ifndef KV_REG_KEY_ENTRY_12_3
`define KV_REG_KEY_ENTRY_12_3                                                                       (32'h90c)
`endif
`ifndef KV_REG_KEY_ENTRY_12_4
`define KV_REG_KEY_ENTRY_12_4                                                                       (32'h910)
`endif
`ifndef KV_REG_KEY_ENTRY_12_5
`define KV_REG_KEY_ENTRY_12_5                                                                       (32'h914)
`endif
`ifndef KV_REG_KEY_ENTRY_12_6
`define KV_REG_KEY_ENTRY_12_6                                                                       (32'h918)
`endif
`ifndef KV_REG_KEY_ENTRY_12_7
`define KV_REG_KEY_ENTRY_12_7                                                                       (32'h91c)
`endif
`ifndef KV_REG_KEY_ENTRY_12_8
`define KV_REG_KEY_ENTRY_12_8                                                                       (32'h920)
`endif
`ifndef KV_REG_KEY_ENTRY_12_9
`define KV_REG_KEY_ENTRY_12_9                                                                       (32'h924)
`endif
`ifndef KV_REG_KEY_ENTRY_12_10
`define KV_REG_KEY_ENTRY_12_10                                                                      (32'h928)
`endif
`ifndef KV_REG_KEY_ENTRY_12_11
`define KV_REG_KEY_ENTRY_12_11                                                                      (32'h92c)
`endif
`ifndef KV_REG_KEY_ENTRY_12_12
`define KV_REG_KEY_ENTRY_12_12                                                                      (32'h930)
`endif
`ifndef KV_REG_KEY_ENTRY_12_13
`define KV_REG_KEY_ENTRY_12_13                                                                      (32'h934)
`endif
`ifndef KV_REG_KEY_ENTRY_12_14
`define KV_REG_KEY_ENTRY_12_14                                                                      (32'h938)
`endif
`ifndef KV_REG_KEY_ENTRY_12_15
`define KV_REG_KEY_ENTRY_12_15                                                                      (32'h93c)
`endif
`ifndef KV_REG_KEY_ENTRY_13_0
`define KV_REG_KEY_ENTRY_13_0                                                                       (32'h940)
`endif
`ifndef KV_REG_KEY_ENTRY_13_1
`define KV_REG_KEY_ENTRY_13_1                                                                       (32'h944)
`endif
`ifndef KV_REG_KEY_ENTRY_13_2
`define KV_REG_KEY_ENTRY_13_2                                                                       (32'h948)
`endif
`ifndef KV_REG_KEY_ENTRY_13_3
`define KV_REG_KEY_ENTRY_13_3                                                                       (32'h94c)
`endif
`ifndef KV_REG_KEY_ENTRY_13_4
`define KV_REG_KEY_ENTRY_13_4                                                                       (32'h950)
`endif
`ifndef KV_REG_KEY_ENTRY_13_5
`define KV_REG_KEY_ENTRY_13_5                                                                       (32'h954)
`endif
`ifndef KV_REG_KEY_ENTRY_13_6
`define KV_REG_KEY_ENTRY_13_6                                                                       (32'h958)
`endif
`ifndef KV_REG_KEY_ENTRY_13_7
`define KV_REG_KEY_ENTRY_13_7                                                                       (32'h95c)
`endif
`ifndef KV_REG_KEY_ENTRY_13_8
`define KV_REG_KEY_ENTRY_13_8                                                                       (32'h960)
`endif
`ifndef KV_REG_KEY_ENTRY_13_9
`define KV_REG_KEY_ENTRY_13_9                                                                       (32'h964)
`endif
`ifndef KV_REG_KEY_ENTRY_13_10
`define KV_REG_KEY_ENTRY_13_10                                                                      (32'h968)
`endif
`ifndef KV_REG_KEY_ENTRY_13_11
`define KV_REG_KEY_ENTRY_13_11                                                                      (32'h96c)
`endif
`ifndef KV_REG_KEY_ENTRY_13_12
`define KV_REG_KEY_ENTRY_13_12                                                                      (32'h970)
`endif
`ifndef KV_REG_KEY_ENTRY_13_13
`define KV_REG_KEY_ENTRY_13_13                                                                      (32'h974)
`endif
`ifndef KV_REG_KEY_ENTRY_13_14
`define KV_REG_KEY_ENTRY_13_14                                                                      (32'h978)
`endif
`ifndef KV_REG_KEY_ENTRY_13_15
`define KV_REG_KEY_ENTRY_13_15                                                                      (32'h97c)
`endif
`ifndef KV_REG_KEY_ENTRY_14_0
`define KV_REG_KEY_ENTRY_14_0                                                                       (32'h980)
`endif
`ifndef KV_REG_KEY_ENTRY_14_1
`define KV_REG_KEY_ENTRY_14_1                                                                       (32'h984)
`endif
`ifndef KV_REG_KEY_ENTRY_14_2
`define KV_REG_KEY_ENTRY_14_2                                                                       (32'h988)
`endif
`ifndef KV_REG_KEY_ENTRY_14_3
`define KV_REG_KEY_ENTRY_14_3                                                                       (32'h98c)
`endif
`ifndef KV_REG_KEY_ENTRY_14_4
`define KV_REG_KEY_ENTRY_14_4                                                                       (32'h990)
`endif
`ifndef KV_REG_KEY_ENTRY_14_5
`define KV_REG_KEY_ENTRY_14_5                                                                       (32'h994)
`endif
`ifndef KV_REG_KEY_ENTRY_14_6
`define KV_REG_KEY_ENTRY_14_6                                                                       (32'h998)
`endif
`ifndef KV_REG_KEY_ENTRY_14_7
`define KV_REG_KEY_ENTRY_14_7                                                                       (32'h99c)
`endif
`ifndef KV_REG_KEY_ENTRY_14_8
`define KV_REG_KEY_ENTRY_14_8                                                                       (32'h9a0)
`endif
`ifndef KV_REG_KEY_ENTRY_14_9
`define KV_REG_KEY_ENTRY_14_9                                                                       (32'h9a4)
`endif
`ifndef KV_REG_KEY_ENTRY_14_10
`define KV_REG_KEY_ENTRY_14_10                                                                      (32'h9a8)
`endif
`ifndef KV_REG_KEY_ENTRY_14_11
`define KV_REG_KEY_ENTRY_14_11                                                                      (32'h9ac)
`endif
`ifndef KV_REG_KEY_ENTRY_14_12
`define KV_REG_KEY_ENTRY_14_12                                                                      (32'h9b0)
`endif
`ifndef KV_REG_KEY_ENTRY_14_13
`define KV_REG_KEY_ENTRY_14_13                                                                      (32'h9b4)
`endif
`ifndef KV_REG_KEY_ENTRY_14_14
`define KV_REG_KEY_ENTRY_14_14                                                                      (32'h9b8)
`endif
`ifndef KV_REG_KEY_ENTRY_14_15
`define KV_REG_KEY_ENTRY_14_15                                                                      (32'h9bc)
`endif
`ifndef KV_REG_KEY_ENTRY_15_0
`define KV_REG_KEY_ENTRY_15_0                                                                       (32'h9c0)
`endif
`ifndef KV_REG_KEY_ENTRY_15_1
`define KV_REG_KEY_ENTRY_15_1                                                                       (32'h9c4)
`endif
`ifndef KV_REG_KEY_ENTRY_15_2
`define KV_REG_KEY_ENTRY_15_2                                                                       (32'h9c8)
`endif
`ifndef KV_REG_KEY_ENTRY_15_3
`define KV_REG_KEY_ENTRY_15_3                                                                       (32'h9cc)
`endif
`ifndef KV_REG_KEY_ENTRY_15_4
`define KV_REG_KEY_ENTRY_15_4                                                                       (32'h9d0)
`endif
`ifndef KV_REG_KEY_ENTRY_15_5
`define KV_REG_KEY_ENTRY_15_5                                                                       (32'h9d4)
`endif
`ifndef KV_REG_KEY_ENTRY_15_6
`define KV_REG_KEY_ENTRY_15_6                                                                       (32'h9d8)
`endif
`ifndef KV_REG_KEY_ENTRY_15_7
`define KV_REG_KEY_ENTRY_15_7                                                                       (32'h9dc)
`endif
`ifndef KV_REG_KEY_ENTRY_15_8
`define KV_REG_KEY_ENTRY_15_8                                                                       (32'h9e0)
`endif
`ifndef KV_REG_KEY_ENTRY_15_9
`define KV_REG_KEY_ENTRY_15_9                                                                       (32'h9e4)
`endif
`ifndef KV_REG_KEY_ENTRY_15_10
`define KV_REG_KEY_ENTRY_15_10                                                                      (32'h9e8)
`endif
`ifndef KV_REG_KEY_ENTRY_15_11
`define KV_REG_KEY_ENTRY_15_11                                                                      (32'h9ec)
`endif
`ifndef KV_REG_KEY_ENTRY_15_12
`define KV_REG_KEY_ENTRY_15_12                                                                      (32'h9f0)
`endif
`ifndef KV_REG_KEY_ENTRY_15_13
`define KV_REG_KEY_ENTRY_15_13                                                                      (32'h9f4)
`endif
`ifndef KV_REG_KEY_ENTRY_15_14
`define KV_REG_KEY_ENTRY_15_14                                                                      (32'h9f8)
`endif
`ifndef KV_REG_KEY_ENTRY_15_15
`define KV_REG_KEY_ENTRY_15_15                                                                      (32'h9fc)
`endif
`ifndef KV_REG_KEY_ENTRY_16_0
`define KV_REG_KEY_ENTRY_16_0                                                                       (32'ha00)
`endif
`ifndef KV_REG_KEY_ENTRY_16_1
`define KV_REG_KEY_ENTRY_16_1                                                                       (32'ha04)
`endif
`ifndef KV_REG_KEY_ENTRY_16_2
`define KV_REG_KEY_ENTRY_16_2                                                                       (32'ha08)
`endif
`ifndef KV_REG_KEY_ENTRY_16_3
`define KV_REG_KEY_ENTRY_16_3                                                                       (32'ha0c)
`endif
`ifndef KV_REG_KEY_ENTRY_16_4
`define KV_REG_KEY_ENTRY_16_4                                                                       (32'ha10)
`endif
`ifndef KV_REG_KEY_ENTRY_16_5
`define KV_REG_KEY_ENTRY_16_5                                                                       (32'ha14)
`endif
`ifndef KV_REG_KEY_ENTRY_16_6
`define KV_REG_KEY_ENTRY_16_6                                                                       (32'ha18)
`endif
`ifndef KV_REG_KEY_ENTRY_16_7
`define KV_REG_KEY_ENTRY_16_7                                                                       (32'ha1c)
`endif
`ifndef KV_REG_KEY_ENTRY_16_8
`define KV_REG_KEY_ENTRY_16_8                                                                       (32'ha20)
`endif
`ifndef KV_REG_KEY_ENTRY_16_9
`define KV_REG_KEY_ENTRY_16_9                                                                       (32'ha24)
`endif
`ifndef KV_REG_KEY_ENTRY_16_10
`define KV_REG_KEY_ENTRY_16_10                                                                      (32'ha28)
`endif
`ifndef KV_REG_KEY_ENTRY_16_11
`define KV_REG_KEY_ENTRY_16_11                                                                      (32'ha2c)
`endif
`ifndef KV_REG_KEY_ENTRY_16_12
`define KV_REG_KEY_ENTRY_16_12                                                                      (32'ha30)
`endif
`ifndef KV_REG_KEY_ENTRY_16_13
`define KV_REG_KEY_ENTRY_16_13                                                                      (32'ha34)
`endif
`ifndef KV_REG_KEY_ENTRY_16_14
`define KV_REG_KEY_ENTRY_16_14                                                                      (32'ha38)
`endif
`ifndef KV_REG_KEY_ENTRY_16_15
`define KV_REG_KEY_ENTRY_16_15                                                                      (32'ha3c)
`endif
`ifndef KV_REG_KEY_ENTRY_17_0
`define KV_REG_KEY_ENTRY_17_0                                                                       (32'ha40)
`endif
`ifndef KV_REG_KEY_ENTRY_17_1
`define KV_REG_KEY_ENTRY_17_1                                                                       (32'ha44)
`endif
`ifndef KV_REG_KEY_ENTRY_17_2
`define KV_REG_KEY_ENTRY_17_2                                                                       (32'ha48)
`endif
`ifndef KV_REG_KEY_ENTRY_17_3
`define KV_REG_KEY_ENTRY_17_3                                                                       (32'ha4c)
`endif
`ifndef KV_REG_KEY_ENTRY_17_4
`define KV_REG_KEY_ENTRY_17_4                                                                       (32'ha50)
`endif
`ifndef KV_REG_KEY_ENTRY_17_5
`define KV_REG_KEY_ENTRY_17_5                                                                       (32'ha54)
`endif
`ifndef KV_REG_KEY_ENTRY_17_6
`define KV_REG_KEY_ENTRY_17_6                                                                       (32'ha58)
`endif
`ifndef KV_REG_KEY_ENTRY_17_7
`define KV_REG_KEY_ENTRY_17_7                                                                       (32'ha5c)
`endif
`ifndef KV_REG_KEY_ENTRY_17_8
`define KV_REG_KEY_ENTRY_17_8                                                                       (32'ha60)
`endif
`ifndef KV_REG_KEY_ENTRY_17_9
`define KV_REG_KEY_ENTRY_17_9                                                                       (32'ha64)
`endif
`ifndef KV_REG_KEY_ENTRY_17_10
`define KV_REG_KEY_ENTRY_17_10                                                                      (32'ha68)
`endif
`ifndef KV_REG_KEY_ENTRY_17_11
`define KV_REG_KEY_ENTRY_17_11                                                                      (32'ha6c)
`endif
`ifndef KV_REG_KEY_ENTRY_17_12
`define KV_REG_KEY_ENTRY_17_12                                                                      (32'ha70)
`endif
`ifndef KV_REG_KEY_ENTRY_17_13
`define KV_REG_KEY_ENTRY_17_13                                                                      (32'ha74)
`endif
`ifndef KV_REG_KEY_ENTRY_17_14
`define KV_REG_KEY_ENTRY_17_14                                                                      (32'ha78)
`endif
`ifndef KV_REG_KEY_ENTRY_17_15
`define KV_REG_KEY_ENTRY_17_15                                                                      (32'ha7c)
`endif
`ifndef KV_REG_KEY_ENTRY_18_0
`define KV_REG_KEY_ENTRY_18_0                                                                       (32'ha80)
`endif
`ifndef KV_REG_KEY_ENTRY_18_1
`define KV_REG_KEY_ENTRY_18_1                                                                       (32'ha84)
`endif
`ifndef KV_REG_KEY_ENTRY_18_2
`define KV_REG_KEY_ENTRY_18_2                                                                       (32'ha88)
`endif
`ifndef KV_REG_KEY_ENTRY_18_3
`define KV_REG_KEY_ENTRY_18_3                                                                       (32'ha8c)
`endif
`ifndef KV_REG_KEY_ENTRY_18_4
`define KV_REG_KEY_ENTRY_18_4                                                                       (32'ha90)
`endif
`ifndef KV_REG_KEY_ENTRY_18_5
`define KV_REG_KEY_ENTRY_18_5                                                                       (32'ha94)
`endif
`ifndef KV_REG_KEY_ENTRY_18_6
`define KV_REG_KEY_ENTRY_18_6                                                                       (32'ha98)
`endif
`ifndef KV_REG_KEY_ENTRY_18_7
`define KV_REG_KEY_ENTRY_18_7                                                                       (32'ha9c)
`endif
`ifndef KV_REG_KEY_ENTRY_18_8
`define KV_REG_KEY_ENTRY_18_8                                                                       (32'haa0)
`endif
`ifndef KV_REG_KEY_ENTRY_18_9
`define KV_REG_KEY_ENTRY_18_9                                                                       (32'haa4)
`endif
`ifndef KV_REG_KEY_ENTRY_18_10
`define KV_REG_KEY_ENTRY_18_10                                                                      (32'haa8)
`endif
`ifndef KV_REG_KEY_ENTRY_18_11
`define KV_REG_KEY_ENTRY_18_11                                                                      (32'haac)
`endif
`ifndef KV_REG_KEY_ENTRY_18_12
`define KV_REG_KEY_ENTRY_18_12                                                                      (32'hab0)
`endif
`ifndef KV_REG_KEY_ENTRY_18_13
`define KV_REG_KEY_ENTRY_18_13                                                                      (32'hab4)
`endif
`ifndef KV_REG_KEY_ENTRY_18_14
`define KV_REG_KEY_ENTRY_18_14                                                                      (32'hab8)
`endif
`ifndef KV_REG_KEY_ENTRY_18_15
`define KV_REG_KEY_ENTRY_18_15                                                                      (32'habc)
`endif
`ifndef KV_REG_KEY_ENTRY_19_0
`define KV_REG_KEY_ENTRY_19_0                                                                       (32'hac0)
`endif
`ifndef KV_REG_KEY_ENTRY_19_1
`define KV_REG_KEY_ENTRY_19_1                                                                       (32'hac4)
`endif
`ifndef KV_REG_KEY_ENTRY_19_2
`define KV_REG_KEY_ENTRY_19_2                                                                       (32'hac8)
`endif
`ifndef KV_REG_KEY_ENTRY_19_3
`define KV_REG_KEY_ENTRY_19_3                                                                       (32'hacc)
`endif
`ifndef KV_REG_KEY_ENTRY_19_4
`define KV_REG_KEY_ENTRY_19_4                                                                       (32'had0)
`endif
`ifndef KV_REG_KEY_ENTRY_19_5
`define KV_REG_KEY_ENTRY_19_5                                                                       (32'had4)
`endif
`ifndef KV_REG_KEY_ENTRY_19_6
`define KV_REG_KEY_ENTRY_19_6                                                                       (32'had8)
`endif
`ifndef KV_REG_KEY_ENTRY_19_7
`define KV_REG_KEY_ENTRY_19_7                                                                       (32'hadc)
`endif
`ifndef KV_REG_KEY_ENTRY_19_8
`define KV_REG_KEY_ENTRY_19_8                                                                       (32'hae0)
`endif
`ifndef KV_REG_KEY_ENTRY_19_9
`define KV_REG_KEY_ENTRY_19_9                                                                       (32'hae4)
`endif
`ifndef KV_REG_KEY_ENTRY_19_10
`define KV_REG_KEY_ENTRY_19_10                                                                      (32'hae8)
`endif
`ifndef KV_REG_KEY_ENTRY_19_11
`define KV_REG_KEY_ENTRY_19_11                                                                      (32'haec)
`endif
`ifndef KV_REG_KEY_ENTRY_19_12
`define KV_REG_KEY_ENTRY_19_12                                                                      (32'haf0)
`endif
`ifndef KV_REG_KEY_ENTRY_19_13
`define KV_REG_KEY_ENTRY_19_13                                                                      (32'haf4)
`endif
`ifndef KV_REG_KEY_ENTRY_19_14
`define KV_REG_KEY_ENTRY_19_14                                                                      (32'haf8)
`endif
`ifndef KV_REG_KEY_ENTRY_19_15
`define KV_REG_KEY_ENTRY_19_15                                                                      (32'hafc)
`endif
`ifndef KV_REG_KEY_ENTRY_20_0
`define KV_REG_KEY_ENTRY_20_0                                                                       (32'hb00)
`endif
`ifndef KV_REG_KEY_ENTRY_20_1
`define KV_REG_KEY_ENTRY_20_1                                                                       (32'hb04)
`endif
`ifndef KV_REG_KEY_ENTRY_20_2
`define KV_REG_KEY_ENTRY_20_2                                                                       (32'hb08)
`endif
`ifndef KV_REG_KEY_ENTRY_20_3
`define KV_REG_KEY_ENTRY_20_3                                                                       (32'hb0c)
`endif
`ifndef KV_REG_KEY_ENTRY_20_4
`define KV_REG_KEY_ENTRY_20_4                                                                       (32'hb10)
`endif
`ifndef KV_REG_KEY_ENTRY_20_5
`define KV_REG_KEY_ENTRY_20_5                                                                       (32'hb14)
`endif
`ifndef KV_REG_KEY_ENTRY_20_6
`define KV_REG_KEY_ENTRY_20_6                                                                       (32'hb18)
`endif
`ifndef KV_REG_KEY_ENTRY_20_7
`define KV_REG_KEY_ENTRY_20_7                                                                       (32'hb1c)
`endif
`ifndef KV_REG_KEY_ENTRY_20_8
`define KV_REG_KEY_ENTRY_20_8                                                                       (32'hb20)
`endif
`ifndef KV_REG_KEY_ENTRY_20_9
`define KV_REG_KEY_ENTRY_20_9                                                                       (32'hb24)
`endif
`ifndef KV_REG_KEY_ENTRY_20_10
`define KV_REG_KEY_ENTRY_20_10                                                                      (32'hb28)
`endif
`ifndef KV_REG_KEY_ENTRY_20_11
`define KV_REG_KEY_ENTRY_20_11                                                                      (32'hb2c)
`endif
`ifndef KV_REG_KEY_ENTRY_20_12
`define KV_REG_KEY_ENTRY_20_12                                                                      (32'hb30)
`endif
`ifndef KV_REG_KEY_ENTRY_20_13
`define KV_REG_KEY_ENTRY_20_13                                                                      (32'hb34)
`endif
`ifndef KV_REG_KEY_ENTRY_20_14
`define KV_REG_KEY_ENTRY_20_14                                                                      (32'hb38)
`endif
`ifndef KV_REG_KEY_ENTRY_20_15
`define KV_REG_KEY_ENTRY_20_15                                                                      (32'hb3c)
`endif
`ifndef KV_REG_KEY_ENTRY_21_0
`define KV_REG_KEY_ENTRY_21_0                                                                       (32'hb40)
`endif
`ifndef KV_REG_KEY_ENTRY_21_1
`define KV_REG_KEY_ENTRY_21_1                                                                       (32'hb44)
`endif
`ifndef KV_REG_KEY_ENTRY_21_2
`define KV_REG_KEY_ENTRY_21_2                                                                       (32'hb48)
`endif
`ifndef KV_REG_KEY_ENTRY_21_3
`define KV_REG_KEY_ENTRY_21_3                                                                       (32'hb4c)
`endif
`ifndef KV_REG_KEY_ENTRY_21_4
`define KV_REG_KEY_ENTRY_21_4                                                                       (32'hb50)
`endif
`ifndef KV_REG_KEY_ENTRY_21_5
`define KV_REG_KEY_ENTRY_21_5                                                                       (32'hb54)
`endif
`ifndef KV_REG_KEY_ENTRY_21_6
`define KV_REG_KEY_ENTRY_21_6                                                                       (32'hb58)
`endif
`ifndef KV_REG_KEY_ENTRY_21_7
`define KV_REG_KEY_ENTRY_21_7                                                                       (32'hb5c)
`endif
`ifndef KV_REG_KEY_ENTRY_21_8
`define KV_REG_KEY_ENTRY_21_8                                                                       (32'hb60)
`endif
`ifndef KV_REG_KEY_ENTRY_21_9
`define KV_REG_KEY_ENTRY_21_9                                                                       (32'hb64)
`endif
`ifndef KV_REG_KEY_ENTRY_21_10
`define KV_REG_KEY_ENTRY_21_10                                                                      (32'hb68)
`endif
`ifndef KV_REG_KEY_ENTRY_21_11
`define KV_REG_KEY_ENTRY_21_11                                                                      (32'hb6c)
`endif
`ifndef KV_REG_KEY_ENTRY_21_12
`define KV_REG_KEY_ENTRY_21_12                                                                      (32'hb70)
`endif
`ifndef KV_REG_KEY_ENTRY_21_13
`define KV_REG_KEY_ENTRY_21_13                                                                      (32'hb74)
`endif
`ifndef KV_REG_KEY_ENTRY_21_14
`define KV_REG_KEY_ENTRY_21_14                                                                      (32'hb78)
`endif
`ifndef KV_REG_KEY_ENTRY_21_15
`define KV_REG_KEY_ENTRY_21_15                                                                      (32'hb7c)
`endif
`ifndef KV_REG_KEY_ENTRY_22_0
`define KV_REG_KEY_ENTRY_22_0                                                                       (32'hb80)
`endif
`ifndef KV_REG_KEY_ENTRY_22_1
`define KV_REG_KEY_ENTRY_22_1                                                                       (32'hb84)
`endif
`ifndef KV_REG_KEY_ENTRY_22_2
`define KV_REG_KEY_ENTRY_22_2                                                                       (32'hb88)
`endif
`ifndef KV_REG_KEY_ENTRY_22_3
`define KV_REG_KEY_ENTRY_22_3                                                                       (32'hb8c)
`endif
`ifndef KV_REG_KEY_ENTRY_22_4
`define KV_REG_KEY_ENTRY_22_4                                                                       (32'hb90)
`endif
`ifndef KV_REG_KEY_ENTRY_22_5
`define KV_REG_KEY_ENTRY_22_5                                                                       (32'hb94)
`endif
`ifndef KV_REG_KEY_ENTRY_22_6
`define KV_REG_KEY_ENTRY_22_6                                                                       (32'hb98)
`endif
`ifndef KV_REG_KEY_ENTRY_22_7
`define KV_REG_KEY_ENTRY_22_7                                                                       (32'hb9c)
`endif
`ifndef KV_REG_KEY_ENTRY_22_8
`define KV_REG_KEY_ENTRY_22_8                                                                       (32'hba0)
`endif
`ifndef KV_REG_KEY_ENTRY_22_9
`define KV_REG_KEY_ENTRY_22_9                                                                       (32'hba4)
`endif
`ifndef KV_REG_KEY_ENTRY_22_10
`define KV_REG_KEY_ENTRY_22_10                                                                      (32'hba8)
`endif
`ifndef KV_REG_KEY_ENTRY_22_11
`define KV_REG_KEY_ENTRY_22_11                                                                      (32'hbac)
`endif
`ifndef KV_REG_KEY_ENTRY_22_12
`define KV_REG_KEY_ENTRY_22_12                                                                      (32'hbb0)
`endif
`ifndef KV_REG_KEY_ENTRY_22_13
`define KV_REG_KEY_ENTRY_22_13                                                                      (32'hbb4)
`endif
`ifndef KV_REG_KEY_ENTRY_22_14
`define KV_REG_KEY_ENTRY_22_14                                                                      (32'hbb8)
`endif
`ifndef KV_REG_KEY_ENTRY_22_15
`define KV_REG_KEY_ENTRY_22_15                                                                      (32'hbbc)
`endif
`ifndef KV_REG_KEY_ENTRY_23_0
`define KV_REG_KEY_ENTRY_23_0                                                                       (32'hbc0)
`endif
`ifndef KV_REG_KEY_ENTRY_23_1
`define KV_REG_KEY_ENTRY_23_1                                                                       (32'hbc4)
`endif
`ifndef KV_REG_KEY_ENTRY_23_2
`define KV_REG_KEY_ENTRY_23_2                                                                       (32'hbc8)
`endif
`ifndef KV_REG_KEY_ENTRY_23_3
`define KV_REG_KEY_ENTRY_23_3                                                                       (32'hbcc)
`endif
`ifndef KV_REG_KEY_ENTRY_23_4
`define KV_REG_KEY_ENTRY_23_4                                                                       (32'hbd0)
`endif
`ifndef KV_REG_KEY_ENTRY_23_5
`define KV_REG_KEY_ENTRY_23_5                                                                       (32'hbd4)
`endif
`ifndef KV_REG_KEY_ENTRY_23_6
`define KV_REG_KEY_ENTRY_23_6                                                                       (32'hbd8)
`endif
`ifndef KV_REG_KEY_ENTRY_23_7
`define KV_REG_KEY_ENTRY_23_7                                                                       (32'hbdc)
`endif
`ifndef KV_REG_KEY_ENTRY_23_8
`define KV_REG_KEY_ENTRY_23_8                                                                       (32'hbe0)
`endif
`ifndef KV_REG_KEY_ENTRY_23_9
`define KV_REG_KEY_ENTRY_23_9                                                                       (32'hbe4)
`endif
`ifndef KV_REG_KEY_ENTRY_23_10
`define KV_REG_KEY_ENTRY_23_10                                                                      (32'hbe8)
`endif
`ifndef KV_REG_KEY_ENTRY_23_11
`define KV_REG_KEY_ENTRY_23_11                                                                      (32'hbec)
`endif
`ifndef KV_REG_KEY_ENTRY_23_12
`define KV_REG_KEY_ENTRY_23_12                                                                      (32'hbf0)
`endif
`ifndef KV_REG_KEY_ENTRY_23_13
`define KV_REG_KEY_ENTRY_23_13                                                                      (32'hbf4)
`endif
`ifndef KV_REG_KEY_ENTRY_23_14
`define KV_REG_KEY_ENTRY_23_14                                                                      (32'hbf8)
`endif
`ifndef KV_REG_KEY_ENTRY_23_15
`define KV_REG_KEY_ENTRY_23_15                                                                      (32'hbfc)
`endif
`ifndef KV_REG_CLEAR_SECRETS
`define KV_REG_CLEAR_SECRETS                                                                        (32'hc00)
`define KV_REG_CLEAR_SECRETS_WR_DEBUG_VALUES_LOW                                                    (0)
`define KV_REG_CLEAR_SECRETS_WR_DEBUG_VALUES_MASK                                                   (32'h1)
`define KV_REG_CLEAR_SECRETS_SEL_DEBUG_VALUE_LOW                                                    (1)
`define KV_REG_CLEAR_SECRETS_SEL_DEBUG_VALUE_MASK                                                   (32'h2)
`endif
`ifndef PV_REG_PCR_CTRL_0
`define PV_REG_PCR_CTRL_0                                                                           (32'h0)
`define PV_REG_PCR_CTRL_0_LOCK_LOW                                                                  (0)
`define PV_REG_PCR_CTRL_0_LOCK_MASK                                                                 (32'h1)
`define PV_REG_PCR_CTRL_0_CLEAR_LOW                                                                 (1)
`define PV_REG_PCR_CTRL_0_CLEAR_MASK                                                                (32'h2)
`define PV_REG_PCR_CTRL_0_RSVD0_LOW                                                                 (2)
`define PV_REG_PCR_CTRL_0_RSVD0_MASK                                                                (32'h4)
`define PV_REG_PCR_CTRL_0_RSVD1_LOW                                                                 (3)
`define PV_REG_PCR_CTRL_0_RSVD1_MASK                                                                (32'hf8)
`endif
`ifndef PV_REG_PCR_CTRL_1
`define PV_REG_PCR_CTRL_1                                                                           (32'h4)
`define PV_REG_PCR_CTRL_1_LOCK_LOW                                                                  (0)
`define PV_REG_PCR_CTRL_1_LOCK_MASK                                                                 (32'h1)
`define PV_REG_PCR_CTRL_1_CLEAR_LOW                                                                 (1)
`define PV_REG_PCR_CTRL_1_CLEAR_MASK                                                                (32'h2)
`define PV_REG_PCR_CTRL_1_RSVD0_LOW                                                                 (2)
`define PV_REG_PCR_CTRL_1_RSVD0_MASK                                                                (32'h4)
`define PV_REG_PCR_CTRL_1_RSVD1_LOW                                                                 (3)
`define PV_REG_PCR_CTRL_1_RSVD1_MASK                                                                (32'hf8)
`endif
`ifndef PV_REG_PCR_CTRL_2
`define PV_REG_PCR_CTRL_2                                                                           (32'h8)
`define PV_REG_PCR_CTRL_2_LOCK_LOW                                                                  (0)
`define PV_REG_PCR_CTRL_2_LOCK_MASK                                                                 (32'h1)
`define PV_REG_PCR_CTRL_2_CLEAR_LOW                                                                 (1)
`define PV_REG_PCR_CTRL_2_CLEAR_MASK                                                                (32'h2)
`define PV_REG_PCR_CTRL_2_RSVD0_LOW                                                                 (2)
`define PV_REG_PCR_CTRL_2_RSVD0_MASK                                                                (32'h4)
`define PV_REG_PCR_CTRL_2_RSVD1_LOW                                                                 (3)
`define PV_REG_PCR_CTRL_2_RSVD1_MASK                                                                (32'hf8)
`endif
`ifndef PV_REG_PCR_CTRL_3
`define PV_REG_PCR_CTRL_3                                                                           (32'hc)
`define PV_REG_PCR_CTRL_3_LOCK_LOW                                                                  (0)
`define PV_REG_PCR_CTRL_3_LOCK_MASK                                                                 (32'h1)
`define PV_REG_PCR_CTRL_3_CLEAR_LOW                                                                 (1)
`define PV_REG_PCR_CTRL_3_CLEAR_MASK                                                                (32'h2)
`define PV_REG_PCR_CTRL_3_RSVD0_LOW                                                                 (2)
`define PV_REG_PCR_CTRL_3_RSVD0_MASK                                                                (32'h4)
`define PV_REG_PCR_CTRL_3_RSVD1_LOW                                                                 (3)
`define PV_REG_PCR_CTRL_3_RSVD1_MASK                                                                (32'hf8)
`endif
`ifndef PV_REG_PCR_CTRL_4
`define PV_REG_PCR_CTRL_4                                                                           (32'h10)
`define PV_REG_PCR_CTRL_4_LOCK_LOW                                                                  (0)
`define PV_REG_PCR_CTRL_4_LOCK_MASK                                                                 (32'h1)
`define PV_REG_PCR_CTRL_4_CLEAR_LOW                                                                 (1)
`define PV_REG_PCR_CTRL_4_CLEAR_MASK                                                                (32'h2)
`define PV_REG_PCR_CTRL_4_RSVD0_LOW                                                                 (2)
`define PV_REG_PCR_CTRL_4_RSVD0_MASK                                                                (32'h4)
`define PV_REG_PCR_CTRL_4_RSVD1_LOW                                                                 (3)
`define PV_REG_PCR_CTRL_4_RSVD1_MASK                                                                (32'hf8)
`endif
`ifndef PV_REG_PCR_CTRL_5
`define PV_REG_PCR_CTRL_5                                                                           (32'h14)
`define PV_REG_PCR_CTRL_5_LOCK_LOW                                                                  (0)
`define PV_REG_PCR_CTRL_5_LOCK_MASK                                                                 (32'h1)
`define PV_REG_PCR_CTRL_5_CLEAR_LOW                                                                 (1)
`define PV_REG_PCR_CTRL_5_CLEAR_MASK                                                                (32'h2)
`define PV_REG_PCR_CTRL_5_RSVD0_LOW                                                                 (2)
`define PV_REG_PCR_CTRL_5_RSVD0_MASK                                                                (32'h4)
`define PV_REG_PCR_CTRL_5_RSVD1_LOW                                                                 (3)
`define PV_REG_PCR_CTRL_5_RSVD1_MASK                                                                (32'hf8)
`endif
`ifndef PV_REG_PCR_CTRL_6
`define PV_REG_PCR_CTRL_6                                                                           (32'h18)
`define PV_REG_PCR_CTRL_6_LOCK_LOW                                                                  (0)
`define PV_REG_PCR_CTRL_6_LOCK_MASK                                                                 (32'h1)
`define PV_REG_PCR_CTRL_6_CLEAR_LOW                                                                 (1)
`define PV_REG_PCR_CTRL_6_CLEAR_MASK                                                                (32'h2)
`define PV_REG_PCR_CTRL_6_RSVD0_LOW                                                                 (2)
`define PV_REG_PCR_CTRL_6_RSVD0_MASK                                                                (32'h4)
`define PV_REG_PCR_CTRL_6_RSVD1_LOW                                                                 (3)
`define PV_REG_PCR_CTRL_6_RSVD1_MASK                                                                (32'hf8)
`endif
`ifndef PV_REG_PCR_CTRL_7
`define PV_REG_PCR_CTRL_7                                                                           (32'h1c)
`define PV_REG_PCR_CTRL_7_LOCK_LOW                                                                  (0)
`define PV_REG_PCR_CTRL_7_LOCK_MASK                                                                 (32'h1)
`define PV_REG_PCR_CTRL_7_CLEAR_LOW                                                                 (1)
`define PV_REG_PCR_CTRL_7_CLEAR_MASK                                                                (32'h2)
`define PV_REG_PCR_CTRL_7_RSVD0_LOW                                                                 (2)
`define PV_REG_PCR_CTRL_7_RSVD0_MASK                                                                (32'h4)
`define PV_REG_PCR_CTRL_7_RSVD1_LOW                                                                 (3)
`define PV_REG_PCR_CTRL_7_RSVD1_MASK                                                                (32'hf8)
`endif
`ifndef PV_REG_PCR_CTRL_8
`define PV_REG_PCR_CTRL_8                                                                           (32'h20)
`define PV_REG_PCR_CTRL_8_LOCK_LOW                                                                  (0)
`define PV_REG_PCR_CTRL_8_LOCK_MASK                                                                 (32'h1)
`define PV_REG_PCR_CTRL_8_CLEAR_LOW                                                                 (1)
`define PV_REG_PCR_CTRL_8_CLEAR_MASK                                                                (32'h2)
`define PV_REG_PCR_CTRL_8_RSVD0_LOW                                                                 (2)
`define PV_REG_PCR_CTRL_8_RSVD0_MASK                                                                (32'h4)
`define PV_REG_PCR_CTRL_8_RSVD1_LOW                                                                 (3)
`define PV_REG_PCR_CTRL_8_RSVD1_MASK                                                                (32'hf8)
`endif
`ifndef PV_REG_PCR_CTRL_9
`define PV_REG_PCR_CTRL_9                                                                           (32'h24)
`define PV_REG_PCR_CTRL_9_LOCK_LOW                                                                  (0)
`define PV_REG_PCR_CTRL_9_LOCK_MASK                                                                 (32'h1)
`define PV_REG_PCR_CTRL_9_CLEAR_LOW                                                                 (1)
`define PV_REG_PCR_CTRL_9_CLEAR_MASK                                                                (32'h2)
`define PV_REG_PCR_CTRL_9_RSVD0_LOW                                                                 (2)
`define PV_REG_PCR_CTRL_9_RSVD0_MASK                                                                (32'h4)
`define PV_REG_PCR_CTRL_9_RSVD1_LOW                                                                 (3)
`define PV_REG_PCR_CTRL_9_RSVD1_MASK                                                                (32'hf8)
`endif
`ifndef PV_REG_PCR_CTRL_10
`define PV_REG_PCR_CTRL_10                                                                          (32'h28)
`define PV_REG_PCR_CTRL_10_LOCK_LOW                                                                 (0)
`define PV_REG_PCR_CTRL_10_LOCK_MASK                                                                (32'h1)
`define PV_REG_PCR_CTRL_10_CLEAR_LOW                                                                (1)
`define PV_REG_PCR_CTRL_10_CLEAR_MASK                                                               (32'h2)
`define PV_REG_PCR_CTRL_10_RSVD0_LOW                                                                (2)
`define PV_REG_PCR_CTRL_10_RSVD0_MASK                                                               (32'h4)
`define PV_REG_PCR_CTRL_10_RSVD1_LOW                                                                (3)
`define PV_REG_PCR_CTRL_10_RSVD1_MASK                                                               (32'hf8)
`endif
`ifndef PV_REG_PCR_CTRL_11
`define PV_REG_PCR_CTRL_11                                                                          (32'h2c)
`define PV_REG_PCR_CTRL_11_LOCK_LOW                                                                 (0)
`define PV_REG_PCR_CTRL_11_LOCK_MASK                                                                (32'h1)
`define PV_REG_PCR_CTRL_11_CLEAR_LOW                                                                (1)
`define PV_REG_PCR_CTRL_11_CLEAR_MASK                                                               (32'h2)
`define PV_REG_PCR_CTRL_11_RSVD0_LOW                                                                (2)
`define PV_REG_PCR_CTRL_11_RSVD0_MASK                                                               (32'h4)
`define PV_REG_PCR_CTRL_11_RSVD1_LOW                                                                (3)
`define PV_REG_PCR_CTRL_11_RSVD1_MASK                                                               (32'hf8)
`endif
`ifndef PV_REG_PCR_CTRL_12
`define PV_REG_PCR_CTRL_12                                                                          (32'h30)
`define PV_REG_PCR_CTRL_12_LOCK_LOW                                                                 (0)
`define PV_REG_PCR_CTRL_12_LOCK_MASK                                                                (32'h1)
`define PV_REG_PCR_CTRL_12_CLEAR_LOW                                                                (1)
`define PV_REG_PCR_CTRL_12_CLEAR_MASK                                                               (32'h2)
`define PV_REG_PCR_CTRL_12_RSVD0_LOW                                                                (2)
`define PV_REG_PCR_CTRL_12_RSVD0_MASK                                                               (32'h4)
`define PV_REG_PCR_CTRL_12_RSVD1_LOW                                                                (3)
`define PV_REG_PCR_CTRL_12_RSVD1_MASK                                                               (32'hf8)
`endif
`ifndef PV_REG_PCR_CTRL_13
`define PV_REG_PCR_CTRL_13                                                                          (32'h34)
`define PV_REG_PCR_CTRL_13_LOCK_LOW                                                                 (0)
`define PV_REG_PCR_CTRL_13_LOCK_MASK                                                                (32'h1)
`define PV_REG_PCR_CTRL_13_CLEAR_LOW                                                                (1)
`define PV_REG_PCR_CTRL_13_CLEAR_MASK                                                               (32'h2)
`define PV_REG_PCR_CTRL_13_RSVD0_LOW                                                                (2)
`define PV_REG_PCR_CTRL_13_RSVD0_MASK                                                               (32'h4)
`define PV_REG_PCR_CTRL_13_RSVD1_LOW                                                                (3)
`define PV_REG_PCR_CTRL_13_RSVD1_MASK                                                               (32'hf8)
`endif
`ifndef PV_REG_PCR_CTRL_14
`define PV_REG_PCR_CTRL_14                                                                          (32'h38)
`define PV_REG_PCR_CTRL_14_LOCK_LOW                                                                 (0)
`define PV_REG_PCR_CTRL_14_LOCK_MASK                                                                (32'h1)
`define PV_REG_PCR_CTRL_14_CLEAR_LOW                                                                (1)
`define PV_REG_PCR_CTRL_14_CLEAR_MASK                                                               (32'h2)
`define PV_REG_PCR_CTRL_14_RSVD0_LOW                                                                (2)
`define PV_REG_PCR_CTRL_14_RSVD0_MASK                                                               (32'h4)
`define PV_REG_PCR_CTRL_14_RSVD1_LOW                                                                (3)
`define PV_REG_PCR_CTRL_14_RSVD1_MASK                                                               (32'hf8)
`endif
`ifndef PV_REG_PCR_CTRL_15
`define PV_REG_PCR_CTRL_15                                                                          (32'h3c)
`define PV_REG_PCR_CTRL_15_LOCK_LOW                                                                 (0)
`define PV_REG_PCR_CTRL_15_LOCK_MASK                                                                (32'h1)
`define PV_REG_PCR_CTRL_15_CLEAR_LOW                                                                (1)
`define PV_REG_PCR_CTRL_15_CLEAR_MASK                                                               (32'h2)
`define PV_REG_PCR_CTRL_15_RSVD0_LOW                                                                (2)
`define PV_REG_PCR_CTRL_15_RSVD0_MASK                                                               (32'h4)
`define PV_REG_PCR_CTRL_15_RSVD1_LOW                                                                (3)
`define PV_REG_PCR_CTRL_15_RSVD1_MASK                                                               (32'hf8)
`endif
`ifndef PV_REG_PCR_CTRL_16
`define PV_REG_PCR_CTRL_16                                                                          (32'h40)
`define PV_REG_PCR_CTRL_16_LOCK_LOW                                                                 (0)
`define PV_REG_PCR_CTRL_16_LOCK_MASK                                                                (32'h1)
`define PV_REG_PCR_CTRL_16_CLEAR_LOW                                                                (1)
`define PV_REG_PCR_CTRL_16_CLEAR_MASK                                                               (32'h2)
`define PV_REG_PCR_CTRL_16_RSVD0_LOW                                                                (2)
`define PV_REG_PCR_CTRL_16_RSVD0_MASK                                                               (32'h4)
`define PV_REG_PCR_CTRL_16_RSVD1_LOW                                                                (3)
`define PV_REG_PCR_CTRL_16_RSVD1_MASK                                                               (32'hf8)
`endif
`ifndef PV_REG_PCR_CTRL_17
`define PV_REG_PCR_CTRL_17                                                                          (32'h44)
`define PV_REG_PCR_CTRL_17_LOCK_LOW                                                                 (0)
`define PV_REG_PCR_CTRL_17_LOCK_MASK                                                                (32'h1)
`define PV_REG_PCR_CTRL_17_CLEAR_LOW                                                                (1)
`define PV_REG_PCR_CTRL_17_CLEAR_MASK                                                               (32'h2)
`define PV_REG_PCR_CTRL_17_RSVD0_LOW                                                                (2)
`define PV_REG_PCR_CTRL_17_RSVD0_MASK                                                               (32'h4)
`define PV_REG_PCR_CTRL_17_RSVD1_LOW                                                                (3)
`define PV_REG_PCR_CTRL_17_RSVD1_MASK                                                               (32'hf8)
`endif
`ifndef PV_REG_PCR_CTRL_18
`define PV_REG_PCR_CTRL_18                                                                          (32'h48)
`define PV_REG_PCR_CTRL_18_LOCK_LOW                                                                 (0)
`define PV_REG_PCR_CTRL_18_LOCK_MASK                                                                (32'h1)
`define PV_REG_PCR_CTRL_18_CLEAR_LOW                                                                (1)
`define PV_REG_PCR_CTRL_18_CLEAR_MASK                                                               (32'h2)
`define PV_REG_PCR_CTRL_18_RSVD0_LOW                                                                (2)
`define PV_REG_PCR_CTRL_18_RSVD0_MASK                                                               (32'h4)
`define PV_REG_PCR_CTRL_18_RSVD1_LOW                                                                (3)
`define PV_REG_PCR_CTRL_18_RSVD1_MASK                                                               (32'hf8)
`endif
`ifndef PV_REG_PCR_CTRL_19
`define PV_REG_PCR_CTRL_19                                                                          (32'h4c)
`define PV_REG_PCR_CTRL_19_LOCK_LOW                                                                 (0)
`define PV_REG_PCR_CTRL_19_LOCK_MASK                                                                (32'h1)
`define PV_REG_PCR_CTRL_19_CLEAR_LOW                                                                (1)
`define PV_REG_PCR_CTRL_19_CLEAR_MASK                                                               (32'h2)
`define PV_REG_PCR_CTRL_19_RSVD0_LOW                                                                (2)
`define PV_REG_PCR_CTRL_19_RSVD0_MASK                                                               (32'h4)
`define PV_REG_PCR_CTRL_19_RSVD1_LOW                                                                (3)
`define PV_REG_PCR_CTRL_19_RSVD1_MASK                                                               (32'hf8)
`endif
`ifndef PV_REG_PCR_CTRL_20
`define PV_REG_PCR_CTRL_20                                                                          (32'h50)
`define PV_REG_PCR_CTRL_20_LOCK_LOW                                                                 (0)
`define PV_REG_PCR_CTRL_20_LOCK_MASK                                                                (32'h1)
`define PV_REG_PCR_CTRL_20_CLEAR_LOW                                                                (1)
`define PV_REG_PCR_CTRL_20_CLEAR_MASK                                                               (32'h2)
`define PV_REG_PCR_CTRL_20_RSVD0_LOW                                                                (2)
`define PV_REG_PCR_CTRL_20_RSVD0_MASK                                                               (32'h4)
`define PV_REG_PCR_CTRL_20_RSVD1_LOW                                                                (3)
`define PV_REG_PCR_CTRL_20_RSVD1_MASK                                                               (32'hf8)
`endif
`ifndef PV_REG_PCR_CTRL_21
`define PV_REG_PCR_CTRL_21                                                                          (32'h54)
`define PV_REG_PCR_CTRL_21_LOCK_LOW                                                                 (0)
`define PV_REG_PCR_CTRL_21_LOCK_MASK                                                                (32'h1)
`define PV_REG_PCR_CTRL_21_CLEAR_LOW                                                                (1)
`define PV_REG_PCR_CTRL_21_CLEAR_MASK                                                               (32'h2)
`define PV_REG_PCR_CTRL_21_RSVD0_LOW                                                                (2)
`define PV_REG_PCR_CTRL_21_RSVD0_MASK                                                               (32'h4)
`define PV_REG_PCR_CTRL_21_RSVD1_LOW                                                                (3)
`define PV_REG_PCR_CTRL_21_RSVD1_MASK                                                               (32'hf8)
`endif
`ifndef PV_REG_PCR_CTRL_22
`define PV_REG_PCR_CTRL_22                                                                          (32'h58)
`define PV_REG_PCR_CTRL_22_LOCK_LOW                                                                 (0)
`define PV_REG_PCR_CTRL_22_LOCK_MASK                                                                (32'h1)
`define PV_REG_PCR_CTRL_22_CLEAR_LOW                                                                (1)
`define PV_REG_PCR_CTRL_22_CLEAR_MASK                                                               (32'h2)
`define PV_REG_PCR_CTRL_22_RSVD0_LOW                                                                (2)
`define PV_REG_PCR_CTRL_22_RSVD0_MASK                                                               (32'h4)
`define PV_REG_PCR_CTRL_22_RSVD1_LOW                                                                (3)
`define PV_REG_PCR_CTRL_22_RSVD1_MASK                                                               (32'hf8)
`endif
`ifndef PV_REG_PCR_CTRL_23
`define PV_REG_PCR_CTRL_23                                                                          (32'h5c)
`define PV_REG_PCR_CTRL_23_LOCK_LOW                                                                 (0)
`define PV_REG_PCR_CTRL_23_LOCK_MASK                                                                (32'h1)
`define PV_REG_PCR_CTRL_23_CLEAR_LOW                                                                (1)
`define PV_REG_PCR_CTRL_23_CLEAR_MASK                                                               (32'h2)
`define PV_REG_PCR_CTRL_23_RSVD0_LOW                                                                (2)
`define PV_REG_PCR_CTRL_23_RSVD0_MASK                                                               (32'h4)
`define PV_REG_PCR_CTRL_23_RSVD1_LOW                                                                (3)
`define PV_REG_PCR_CTRL_23_RSVD1_MASK                                                               (32'hf8)
`endif
`ifndef PV_REG_PCR_CTRL_24
`define PV_REG_PCR_CTRL_24                                                                          (32'h60)
`define PV_REG_PCR_CTRL_24_LOCK_LOW                                                                 (0)
`define PV_REG_PCR_CTRL_24_LOCK_MASK                                                                (32'h1)
`define PV_REG_PCR_CTRL_24_CLEAR_LOW                                                                (1)
`define PV_REG_PCR_CTRL_24_CLEAR_MASK                                                               (32'h2)
`define PV_REG_PCR_CTRL_24_RSVD0_LOW                                                                (2)
`define PV_REG_PCR_CTRL_24_RSVD0_MASK                                                               (32'h4)
`define PV_REG_PCR_CTRL_24_RSVD1_LOW                                                                (3)
`define PV_REG_PCR_CTRL_24_RSVD1_MASK                                                               (32'hf8)
`endif
`ifndef PV_REG_PCR_CTRL_25
`define PV_REG_PCR_CTRL_25                                                                          (32'h64)
`define PV_REG_PCR_CTRL_25_LOCK_LOW                                                                 (0)
`define PV_REG_PCR_CTRL_25_LOCK_MASK                                                                (32'h1)
`define PV_REG_PCR_CTRL_25_CLEAR_LOW                                                                (1)
`define PV_REG_PCR_CTRL_25_CLEAR_MASK                                                               (32'h2)
`define PV_REG_PCR_CTRL_25_RSVD0_LOW                                                                (2)
`define PV_REG_PCR_CTRL_25_RSVD0_MASK                                                               (32'h4)
`define PV_REG_PCR_CTRL_25_RSVD1_LOW                                                                (3)
`define PV_REG_PCR_CTRL_25_RSVD1_MASK                                                               (32'hf8)
`endif
`ifndef PV_REG_PCR_CTRL_26
`define PV_REG_PCR_CTRL_26                                                                          (32'h68)
`define PV_REG_PCR_CTRL_26_LOCK_LOW                                                                 (0)
`define PV_REG_PCR_CTRL_26_LOCK_MASK                                                                (32'h1)
`define PV_REG_PCR_CTRL_26_CLEAR_LOW                                                                (1)
`define PV_REG_PCR_CTRL_26_CLEAR_MASK                                                               (32'h2)
`define PV_REG_PCR_CTRL_26_RSVD0_LOW                                                                (2)
`define PV_REG_PCR_CTRL_26_RSVD0_MASK                                                               (32'h4)
`define PV_REG_PCR_CTRL_26_RSVD1_LOW                                                                (3)
`define PV_REG_PCR_CTRL_26_RSVD1_MASK                                                               (32'hf8)
`endif
`ifndef PV_REG_PCR_CTRL_27
`define PV_REG_PCR_CTRL_27                                                                          (32'h6c)
`define PV_REG_PCR_CTRL_27_LOCK_LOW                                                                 (0)
`define PV_REG_PCR_CTRL_27_LOCK_MASK                                                                (32'h1)
`define PV_REG_PCR_CTRL_27_CLEAR_LOW                                                                (1)
`define PV_REG_PCR_CTRL_27_CLEAR_MASK                                                               (32'h2)
`define PV_REG_PCR_CTRL_27_RSVD0_LOW                                                                (2)
`define PV_REG_PCR_CTRL_27_RSVD0_MASK                                                               (32'h4)
`define PV_REG_PCR_CTRL_27_RSVD1_LOW                                                                (3)
`define PV_REG_PCR_CTRL_27_RSVD1_MASK                                                               (32'hf8)
`endif
`ifndef PV_REG_PCR_CTRL_28
`define PV_REG_PCR_CTRL_28                                                                          (32'h70)
`define PV_REG_PCR_CTRL_28_LOCK_LOW                                                                 (0)
`define PV_REG_PCR_CTRL_28_LOCK_MASK                                                                (32'h1)
`define PV_REG_PCR_CTRL_28_CLEAR_LOW                                                                (1)
`define PV_REG_PCR_CTRL_28_CLEAR_MASK                                                               (32'h2)
`define PV_REG_PCR_CTRL_28_RSVD0_LOW                                                                (2)
`define PV_REG_PCR_CTRL_28_RSVD0_MASK                                                               (32'h4)
`define PV_REG_PCR_CTRL_28_RSVD1_LOW                                                                (3)
`define PV_REG_PCR_CTRL_28_RSVD1_MASK                                                               (32'hf8)
`endif
`ifndef PV_REG_PCR_CTRL_29
`define PV_REG_PCR_CTRL_29                                                                          (32'h74)
`define PV_REG_PCR_CTRL_29_LOCK_LOW                                                                 (0)
`define PV_REG_PCR_CTRL_29_LOCK_MASK                                                                (32'h1)
`define PV_REG_PCR_CTRL_29_CLEAR_LOW                                                                (1)
`define PV_REG_PCR_CTRL_29_CLEAR_MASK                                                               (32'h2)
`define PV_REG_PCR_CTRL_29_RSVD0_LOW                                                                (2)
`define PV_REG_PCR_CTRL_29_RSVD0_MASK                                                               (32'h4)
`define PV_REG_PCR_CTRL_29_RSVD1_LOW                                                                (3)
`define PV_REG_PCR_CTRL_29_RSVD1_MASK                                                               (32'hf8)
`endif
`ifndef PV_REG_PCR_CTRL_30
`define PV_REG_PCR_CTRL_30                                                                          (32'h78)
`define PV_REG_PCR_CTRL_30_LOCK_LOW                                                                 (0)
`define PV_REG_PCR_CTRL_30_LOCK_MASK                                                                (32'h1)
`define PV_REG_PCR_CTRL_30_CLEAR_LOW                                                                (1)
`define PV_REG_PCR_CTRL_30_CLEAR_MASK                                                               (32'h2)
`define PV_REG_PCR_CTRL_30_RSVD0_LOW                                                                (2)
`define PV_REG_PCR_CTRL_30_RSVD0_MASK                                                               (32'h4)
`define PV_REG_PCR_CTRL_30_RSVD1_LOW                                                                (3)
`define PV_REG_PCR_CTRL_30_RSVD1_MASK                                                               (32'hf8)
`endif
`ifndef PV_REG_PCR_CTRL_31
`define PV_REG_PCR_CTRL_31                                                                          (32'h7c)
`define PV_REG_PCR_CTRL_31_LOCK_LOW                                                                 (0)
`define PV_REG_PCR_CTRL_31_LOCK_MASK                                                                (32'h1)
`define PV_REG_PCR_CTRL_31_CLEAR_LOW                                                                (1)
`define PV_REG_PCR_CTRL_31_CLEAR_MASK                                                               (32'h2)
`define PV_REG_PCR_CTRL_31_RSVD0_LOW                                                                (2)
`define PV_REG_PCR_CTRL_31_RSVD0_MASK                                                               (32'h4)
`define PV_REG_PCR_CTRL_31_RSVD1_LOW                                                                (3)
`define PV_REG_PCR_CTRL_31_RSVD1_MASK                                                               (32'hf8)
`endif
`ifndef PV_REG_PCR_ENTRY_0_0
`define PV_REG_PCR_ENTRY_0_0                                                                        (32'h600)
`endif
`ifndef PV_REG_PCR_ENTRY_0_1
`define PV_REG_PCR_ENTRY_0_1                                                                        (32'h604)
`endif
`ifndef PV_REG_PCR_ENTRY_0_2
`define PV_REG_PCR_ENTRY_0_2                                                                        (32'h608)
`endif
`ifndef PV_REG_PCR_ENTRY_0_3
`define PV_REG_PCR_ENTRY_0_3                                                                        (32'h60c)
`endif
`ifndef PV_REG_PCR_ENTRY_0_4
`define PV_REG_PCR_ENTRY_0_4                                                                        (32'h610)
`endif
`ifndef PV_REG_PCR_ENTRY_0_5
`define PV_REG_PCR_ENTRY_0_5                                                                        (32'h614)
`endif
`ifndef PV_REG_PCR_ENTRY_0_6
`define PV_REG_PCR_ENTRY_0_6                                                                        (32'h618)
`endif
`ifndef PV_REG_PCR_ENTRY_0_7
`define PV_REG_PCR_ENTRY_0_7                                                                        (32'h61c)
`endif
`ifndef PV_REG_PCR_ENTRY_0_8
`define PV_REG_PCR_ENTRY_0_8                                                                        (32'h620)
`endif
`ifndef PV_REG_PCR_ENTRY_0_9
`define PV_REG_PCR_ENTRY_0_9                                                                        (32'h624)
`endif
`ifndef PV_REG_PCR_ENTRY_0_10
`define PV_REG_PCR_ENTRY_0_10                                                                       (32'h628)
`endif
`ifndef PV_REG_PCR_ENTRY_0_11
`define PV_REG_PCR_ENTRY_0_11                                                                       (32'h62c)
`endif
`ifndef PV_REG_PCR_ENTRY_1_0
`define PV_REG_PCR_ENTRY_1_0                                                                        (32'h630)
`endif
`ifndef PV_REG_PCR_ENTRY_1_1
`define PV_REG_PCR_ENTRY_1_1                                                                        (32'h634)
`endif
`ifndef PV_REG_PCR_ENTRY_1_2
`define PV_REG_PCR_ENTRY_1_2                                                                        (32'h638)
`endif
`ifndef PV_REG_PCR_ENTRY_1_3
`define PV_REG_PCR_ENTRY_1_3                                                                        (32'h63c)
`endif
`ifndef PV_REG_PCR_ENTRY_1_4
`define PV_REG_PCR_ENTRY_1_4                                                                        (32'h640)
`endif
`ifndef PV_REG_PCR_ENTRY_1_5
`define PV_REG_PCR_ENTRY_1_5                                                                        (32'h644)
`endif
`ifndef PV_REG_PCR_ENTRY_1_6
`define PV_REG_PCR_ENTRY_1_6                                                                        (32'h648)
`endif
`ifndef PV_REG_PCR_ENTRY_1_7
`define PV_REG_PCR_ENTRY_1_7                                                                        (32'h64c)
`endif
`ifndef PV_REG_PCR_ENTRY_1_8
`define PV_REG_PCR_ENTRY_1_8                                                                        (32'h650)
`endif
`ifndef PV_REG_PCR_ENTRY_1_9
`define PV_REG_PCR_ENTRY_1_9                                                                        (32'h654)
`endif
`ifndef PV_REG_PCR_ENTRY_1_10
`define PV_REG_PCR_ENTRY_1_10                                                                       (32'h658)
`endif
`ifndef PV_REG_PCR_ENTRY_1_11
`define PV_REG_PCR_ENTRY_1_11                                                                       (32'h65c)
`endif
`ifndef PV_REG_PCR_ENTRY_2_0
`define PV_REG_PCR_ENTRY_2_0                                                                        (32'h660)
`endif
`ifndef PV_REG_PCR_ENTRY_2_1
`define PV_REG_PCR_ENTRY_2_1                                                                        (32'h664)
`endif
`ifndef PV_REG_PCR_ENTRY_2_2
`define PV_REG_PCR_ENTRY_2_2                                                                        (32'h668)
`endif
`ifndef PV_REG_PCR_ENTRY_2_3
`define PV_REG_PCR_ENTRY_2_3                                                                        (32'h66c)
`endif
`ifndef PV_REG_PCR_ENTRY_2_4
`define PV_REG_PCR_ENTRY_2_4                                                                        (32'h670)
`endif
`ifndef PV_REG_PCR_ENTRY_2_5
`define PV_REG_PCR_ENTRY_2_5                                                                        (32'h674)
`endif
`ifndef PV_REG_PCR_ENTRY_2_6
`define PV_REG_PCR_ENTRY_2_6                                                                        (32'h678)
`endif
`ifndef PV_REG_PCR_ENTRY_2_7
`define PV_REG_PCR_ENTRY_2_7                                                                        (32'h67c)
`endif
`ifndef PV_REG_PCR_ENTRY_2_8
`define PV_REG_PCR_ENTRY_2_8                                                                        (32'h680)
`endif
`ifndef PV_REG_PCR_ENTRY_2_9
`define PV_REG_PCR_ENTRY_2_9                                                                        (32'h684)
`endif
`ifndef PV_REG_PCR_ENTRY_2_10
`define PV_REG_PCR_ENTRY_2_10                                                                       (32'h688)
`endif
`ifndef PV_REG_PCR_ENTRY_2_11
`define PV_REG_PCR_ENTRY_2_11                                                                       (32'h68c)
`endif
`ifndef PV_REG_PCR_ENTRY_3_0
`define PV_REG_PCR_ENTRY_3_0                                                                        (32'h690)
`endif
`ifndef PV_REG_PCR_ENTRY_3_1
`define PV_REG_PCR_ENTRY_3_1                                                                        (32'h694)
`endif
`ifndef PV_REG_PCR_ENTRY_3_2
`define PV_REG_PCR_ENTRY_3_2                                                                        (32'h698)
`endif
`ifndef PV_REG_PCR_ENTRY_3_3
`define PV_REG_PCR_ENTRY_3_3                                                                        (32'h69c)
`endif
`ifndef PV_REG_PCR_ENTRY_3_4
`define PV_REG_PCR_ENTRY_3_4                                                                        (32'h6a0)
`endif
`ifndef PV_REG_PCR_ENTRY_3_5
`define PV_REG_PCR_ENTRY_3_5                                                                        (32'h6a4)
`endif
`ifndef PV_REG_PCR_ENTRY_3_6
`define PV_REG_PCR_ENTRY_3_6                                                                        (32'h6a8)
`endif
`ifndef PV_REG_PCR_ENTRY_3_7
`define PV_REG_PCR_ENTRY_3_7                                                                        (32'h6ac)
`endif
`ifndef PV_REG_PCR_ENTRY_3_8
`define PV_REG_PCR_ENTRY_3_8                                                                        (32'h6b0)
`endif
`ifndef PV_REG_PCR_ENTRY_3_9
`define PV_REG_PCR_ENTRY_3_9                                                                        (32'h6b4)
`endif
`ifndef PV_REG_PCR_ENTRY_3_10
`define PV_REG_PCR_ENTRY_3_10                                                                       (32'h6b8)
`endif
`ifndef PV_REG_PCR_ENTRY_3_11
`define PV_REG_PCR_ENTRY_3_11                                                                       (32'h6bc)
`endif
`ifndef PV_REG_PCR_ENTRY_4_0
`define PV_REG_PCR_ENTRY_4_0                                                                        (32'h6c0)
`endif
`ifndef PV_REG_PCR_ENTRY_4_1
`define PV_REG_PCR_ENTRY_4_1                                                                        (32'h6c4)
`endif
`ifndef PV_REG_PCR_ENTRY_4_2
`define PV_REG_PCR_ENTRY_4_2                                                                        (32'h6c8)
`endif
`ifndef PV_REG_PCR_ENTRY_4_3
`define PV_REG_PCR_ENTRY_4_3                                                                        (32'h6cc)
`endif
`ifndef PV_REG_PCR_ENTRY_4_4
`define PV_REG_PCR_ENTRY_4_4                                                                        (32'h6d0)
`endif
`ifndef PV_REG_PCR_ENTRY_4_5
`define PV_REG_PCR_ENTRY_4_5                                                                        (32'h6d4)
`endif
`ifndef PV_REG_PCR_ENTRY_4_6
`define PV_REG_PCR_ENTRY_4_6                                                                        (32'h6d8)
`endif
`ifndef PV_REG_PCR_ENTRY_4_7
`define PV_REG_PCR_ENTRY_4_7                                                                        (32'h6dc)
`endif
`ifndef PV_REG_PCR_ENTRY_4_8
`define PV_REG_PCR_ENTRY_4_8                                                                        (32'h6e0)
`endif
`ifndef PV_REG_PCR_ENTRY_4_9
`define PV_REG_PCR_ENTRY_4_9                                                                        (32'h6e4)
`endif
`ifndef PV_REG_PCR_ENTRY_4_10
`define PV_REG_PCR_ENTRY_4_10                                                                       (32'h6e8)
`endif
`ifndef PV_REG_PCR_ENTRY_4_11
`define PV_REG_PCR_ENTRY_4_11                                                                       (32'h6ec)
`endif
`ifndef PV_REG_PCR_ENTRY_5_0
`define PV_REG_PCR_ENTRY_5_0                                                                        (32'h6f0)
`endif
`ifndef PV_REG_PCR_ENTRY_5_1
`define PV_REG_PCR_ENTRY_5_1                                                                        (32'h6f4)
`endif
`ifndef PV_REG_PCR_ENTRY_5_2
`define PV_REG_PCR_ENTRY_5_2                                                                        (32'h6f8)
`endif
`ifndef PV_REG_PCR_ENTRY_5_3
`define PV_REG_PCR_ENTRY_5_3                                                                        (32'h6fc)
`endif
`ifndef PV_REG_PCR_ENTRY_5_4
`define PV_REG_PCR_ENTRY_5_4                                                                        (32'h700)
`endif
`ifndef PV_REG_PCR_ENTRY_5_5
`define PV_REG_PCR_ENTRY_5_5                                                                        (32'h704)
`endif
`ifndef PV_REG_PCR_ENTRY_5_6
`define PV_REG_PCR_ENTRY_5_6                                                                        (32'h708)
`endif
`ifndef PV_REG_PCR_ENTRY_5_7
`define PV_REG_PCR_ENTRY_5_7                                                                        (32'h70c)
`endif
`ifndef PV_REG_PCR_ENTRY_5_8
`define PV_REG_PCR_ENTRY_5_8                                                                        (32'h710)
`endif
`ifndef PV_REG_PCR_ENTRY_5_9
`define PV_REG_PCR_ENTRY_5_9                                                                        (32'h714)
`endif
`ifndef PV_REG_PCR_ENTRY_5_10
`define PV_REG_PCR_ENTRY_5_10                                                                       (32'h718)
`endif
`ifndef PV_REG_PCR_ENTRY_5_11
`define PV_REG_PCR_ENTRY_5_11                                                                       (32'h71c)
`endif
`ifndef PV_REG_PCR_ENTRY_6_0
`define PV_REG_PCR_ENTRY_6_0                                                                        (32'h720)
`endif
`ifndef PV_REG_PCR_ENTRY_6_1
`define PV_REG_PCR_ENTRY_6_1                                                                        (32'h724)
`endif
`ifndef PV_REG_PCR_ENTRY_6_2
`define PV_REG_PCR_ENTRY_6_2                                                                        (32'h728)
`endif
`ifndef PV_REG_PCR_ENTRY_6_3
`define PV_REG_PCR_ENTRY_6_3                                                                        (32'h72c)
`endif
`ifndef PV_REG_PCR_ENTRY_6_4
`define PV_REG_PCR_ENTRY_6_4                                                                        (32'h730)
`endif
`ifndef PV_REG_PCR_ENTRY_6_5
`define PV_REG_PCR_ENTRY_6_5                                                                        (32'h734)
`endif
`ifndef PV_REG_PCR_ENTRY_6_6
`define PV_REG_PCR_ENTRY_6_6                                                                        (32'h738)
`endif
`ifndef PV_REG_PCR_ENTRY_6_7
`define PV_REG_PCR_ENTRY_6_7                                                                        (32'h73c)
`endif
`ifndef PV_REG_PCR_ENTRY_6_8
`define PV_REG_PCR_ENTRY_6_8                                                                        (32'h740)
`endif
`ifndef PV_REG_PCR_ENTRY_6_9
`define PV_REG_PCR_ENTRY_6_9                                                                        (32'h744)
`endif
`ifndef PV_REG_PCR_ENTRY_6_10
`define PV_REG_PCR_ENTRY_6_10                                                                       (32'h748)
`endif
`ifndef PV_REG_PCR_ENTRY_6_11
`define PV_REG_PCR_ENTRY_6_11                                                                       (32'h74c)
`endif
`ifndef PV_REG_PCR_ENTRY_7_0
`define PV_REG_PCR_ENTRY_7_0                                                                        (32'h750)
`endif
`ifndef PV_REG_PCR_ENTRY_7_1
`define PV_REG_PCR_ENTRY_7_1                                                                        (32'h754)
`endif
`ifndef PV_REG_PCR_ENTRY_7_2
`define PV_REG_PCR_ENTRY_7_2                                                                        (32'h758)
`endif
`ifndef PV_REG_PCR_ENTRY_7_3
`define PV_REG_PCR_ENTRY_7_3                                                                        (32'h75c)
`endif
`ifndef PV_REG_PCR_ENTRY_7_4
`define PV_REG_PCR_ENTRY_7_4                                                                        (32'h760)
`endif
`ifndef PV_REG_PCR_ENTRY_7_5
`define PV_REG_PCR_ENTRY_7_5                                                                        (32'h764)
`endif
`ifndef PV_REG_PCR_ENTRY_7_6
`define PV_REG_PCR_ENTRY_7_6                                                                        (32'h768)
`endif
`ifndef PV_REG_PCR_ENTRY_7_7
`define PV_REG_PCR_ENTRY_7_7                                                                        (32'h76c)
`endif
`ifndef PV_REG_PCR_ENTRY_7_8
`define PV_REG_PCR_ENTRY_7_8                                                                        (32'h770)
`endif
`ifndef PV_REG_PCR_ENTRY_7_9
`define PV_REG_PCR_ENTRY_7_9                                                                        (32'h774)
`endif
`ifndef PV_REG_PCR_ENTRY_7_10
`define PV_REG_PCR_ENTRY_7_10                                                                       (32'h778)
`endif
`ifndef PV_REG_PCR_ENTRY_7_11
`define PV_REG_PCR_ENTRY_7_11                                                                       (32'h77c)
`endif
`ifndef PV_REG_PCR_ENTRY_8_0
`define PV_REG_PCR_ENTRY_8_0                                                                        (32'h780)
`endif
`ifndef PV_REG_PCR_ENTRY_8_1
`define PV_REG_PCR_ENTRY_8_1                                                                        (32'h784)
`endif
`ifndef PV_REG_PCR_ENTRY_8_2
`define PV_REG_PCR_ENTRY_8_2                                                                        (32'h788)
`endif
`ifndef PV_REG_PCR_ENTRY_8_3
`define PV_REG_PCR_ENTRY_8_3                                                                        (32'h78c)
`endif
`ifndef PV_REG_PCR_ENTRY_8_4
`define PV_REG_PCR_ENTRY_8_4                                                                        (32'h790)
`endif
`ifndef PV_REG_PCR_ENTRY_8_5
`define PV_REG_PCR_ENTRY_8_5                                                                        (32'h794)
`endif
`ifndef PV_REG_PCR_ENTRY_8_6
`define PV_REG_PCR_ENTRY_8_6                                                                        (32'h798)
`endif
`ifndef PV_REG_PCR_ENTRY_8_7
`define PV_REG_PCR_ENTRY_8_7                                                                        (32'h79c)
`endif
`ifndef PV_REG_PCR_ENTRY_8_8
`define PV_REG_PCR_ENTRY_8_8                                                                        (32'h7a0)
`endif
`ifndef PV_REG_PCR_ENTRY_8_9
`define PV_REG_PCR_ENTRY_8_9                                                                        (32'h7a4)
`endif
`ifndef PV_REG_PCR_ENTRY_8_10
`define PV_REG_PCR_ENTRY_8_10                                                                       (32'h7a8)
`endif
`ifndef PV_REG_PCR_ENTRY_8_11
`define PV_REG_PCR_ENTRY_8_11                                                                       (32'h7ac)
`endif
`ifndef PV_REG_PCR_ENTRY_9_0
`define PV_REG_PCR_ENTRY_9_0                                                                        (32'h7b0)
`endif
`ifndef PV_REG_PCR_ENTRY_9_1
`define PV_REG_PCR_ENTRY_9_1                                                                        (32'h7b4)
`endif
`ifndef PV_REG_PCR_ENTRY_9_2
`define PV_REG_PCR_ENTRY_9_2                                                                        (32'h7b8)
`endif
`ifndef PV_REG_PCR_ENTRY_9_3
`define PV_REG_PCR_ENTRY_9_3                                                                        (32'h7bc)
`endif
`ifndef PV_REG_PCR_ENTRY_9_4
`define PV_REG_PCR_ENTRY_9_4                                                                        (32'h7c0)
`endif
`ifndef PV_REG_PCR_ENTRY_9_5
`define PV_REG_PCR_ENTRY_9_5                                                                        (32'h7c4)
`endif
`ifndef PV_REG_PCR_ENTRY_9_6
`define PV_REG_PCR_ENTRY_9_6                                                                        (32'h7c8)
`endif
`ifndef PV_REG_PCR_ENTRY_9_7
`define PV_REG_PCR_ENTRY_9_7                                                                        (32'h7cc)
`endif
`ifndef PV_REG_PCR_ENTRY_9_8
`define PV_REG_PCR_ENTRY_9_8                                                                        (32'h7d0)
`endif
`ifndef PV_REG_PCR_ENTRY_9_9
`define PV_REG_PCR_ENTRY_9_9                                                                        (32'h7d4)
`endif
`ifndef PV_REG_PCR_ENTRY_9_10
`define PV_REG_PCR_ENTRY_9_10                                                                       (32'h7d8)
`endif
`ifndef PV_REG_PCR_ENTRY_9_11
`define PV_REG_PCR_ENTRY_9_11                                                                       (32'h7dc)
`endif
`ifndef PV_REG_PCR_ENTRY_10_0
`define PV_REG_PCR_ENTRY_10_0                                                                       (32'h7e0)
`endif
`ifndef PV_REG_PCR_ENTRY_10_1
`define PV_REG_PCR_ENTRY_10_1                                                                       (32'h7e4)
`endif
`ifndef PV_REG_PCR_ENTRY_10_2
`define PV_REG_PCR_ENTRY_10_2                                                                       (32'h7e8)
`endif
`ifndef PV_REG_PCR_ENTRY_10_3
`define PV_REG_PCR_ENTRY_10_3                                                                       (32'h7ec)
`endif
`ifndef PV_REG_PCR_ENTRY_10_4
`define PV_REG_PCR_ENTRY_10_4                                                                       (32'h7f0)
`endif
`ifndef PV_REG_PCR_ENTRY_10_5
`define PV_REG_PCR_ENTRY_10_5                                                                       (32'h7f4)
`endif
`ifndef PV_REG_PCR_ENTRY_10_6
`define PV_REG_PCR_ENTRY_10_6                                                                       (32'h7f8)
`endif
`ifndef PV_REG_PCR_ENTRY_10_7
`define PV_REG_PCR_ENTRY_10_7                                                                       (32'h7fc)
`endif
`ifndef PV_REG_PCR_ENTRY_10_8
`define PV_REG_PCR_ENTRY_10_8                                                                       (32'h800)
`endif
`ifndef PV_REG_PCR_ENTRY_10_9
`define PV_REG_PCR_ENTRY_10_9                                                                       (32'h804)
`endif
`ifndef PV_REG_PCR_ENTRY_10_10
`define PV_REG_PCR_ENTRY_10_10                                                                      (32'h808)
`endif
`ifndef PV_REG_PCR_ENTRY_10_11
`define PV_REG_PCR_ENTRY_10_11                                                                      (32'h80c)
`endif
`ifndef PV_REG_PCR_ENTRY_11_0
`define PV_REG_PCR_ENTRY_11_0                                                                       (32'h810)
`endif
`ifndef PV_REG_PCR_ENTRY_11_1
`define PV_REG_PCR_ENTRY_11_1                                                                       (32'h814)
`endif
`ifndef PV_REG_PCR_ENTRY_11_2
`define PV_REG_PCR_ENTRY_11_2                                                                       (32'h818)
`endif
`ifndef PV_REG_PCR_ENTRY_11_3
`define PV_REG_PCR_ENTRY_11_3                                                                       (32'h81c)
`endif
`ifndef PV_REG_PCR_ENTRY_11_4
`define PV_REG_PCR_ENTRY_11_4                                                                       (32'h820)
`endif
`ifndef PV_REG_PCR_ENTRY_11_5
`define PV_REG_PCR_ENTRY_11_5                                                                       (32'h824)
`endif
`ifndef PV_REG_PCR_ENTRY_11_6
`define PV_REG_PCR_ENTRY_11_6                                                                       (32'h828)
`endif
`ifndef PV_REG_PCR_ENTRY_11_7
`define PV_REG_PCR_ENTRY_11_7                                                                       (32'h82c)
`endif
`ifndef PV_REG_PCR_ENTRY_11_8
`define PV_REG_PCR_ENTRY_11_8                                                                       (32'h830)
`endif
`ifndef PV_REG_PCR_ENTRY_11_9
`define PV_REG_PCR_ENTRY_11_9                                                                       (32'h834)
`endif
`ifndef PV_REG_PCR_ENTRY_11_10
`define PV_REG_PCR_ENTRY_11_10                                                                      (32'h838)
`endif
`ifndef PV_REG_PCR_ENTRY_11_11
`define PV_REG_PCR_ENTRY_11_11                                                                      (32'h83c)
`endif
`ifndef PV_REG_PCR_ENTRY_12_0
`define PV_REG_PCR_ENTRY_12_0                                                                       (32'h840)
`endif
`ifndef PV_REG_PCR_ENTRY_12_1
`define PV_REG_PCR_ENTRY_12_1                                                                       (32'h844)
`endif
`ifndef PV_REG_PCR_ENTRY_12_2
`define PV_REG_PCR_ENTRY_12_2                                                                       (32'h848)
`endif
`ifndef PV_REG_PCR_ENTRY_12_3
`define PV_REG_PCR_ENTRY_12_3                                                                       (32'h84c)
`endif
`ifndef PV_REG_PCR_ENTRY_12_4
`define PV_REG_PCR_ENTRY_12_4                                                                       (32'h850)
`endif
`ifndef PV_REG_PCR_ENTRY_12_5
`define PV_REG_PCR_ENTRY_12_5                                                                       (32'h854)
`endif
`ifndef PV_REG_PCR_ENTRY_12_6
`define PV_REG_PCR_ENTRY_12_6                                                                       (32'h858)
`endif
`ifndef PV_REG_PCR_ENTRY_12_7
`define PV_REG_PCR_ENTRY_12_7                                                                       (32'h85c)
`endif
`ifndef PV_REG_PCR_ENTRY_12_8
`define PV_REG_PCR_ENTRY_12_8                                                                       (32'h860)
`endif
`ifndef PV_REG_PCR_ENTRY_12_9
`define PV_REG_PCR_ENTRY_12_9                                                                       (32'h864)
`endif
`ifndef PV_REG_PCR_ENTRY_12_10
`define PV_REG_PCR_ENTRY_12_10                                                                      (32'h868)
`endif
`ifndef PV_REG_PCR_ENTRY_12_11
`define PV_REG_PCR_ENTRY_12_11                                                                      (32'h86c)
`endif
`ifndef PV_REG_PCR_ENTRY_13_0
`define PV_REG_PCR_ENTRY_13_0                                                                       (32'h870)
`endif
`ifndef PV_REG_PCR_ENTRY_13_1
`define PV_REG_PCR_ENTRY_13_1                                                                       (32'h874)
`endif
`ifndef PV_REG_PCR_ENTRY_13_2
`define PV_REG_PCR_ENTRY_13_2                                                                       (32'h878)
`endif
`ifndef PV_REG_PCR_ENTRY_13_3
`define PV_REG_PCR_ENTRY_13_3                                                                       (32'h87c)
`endif
`ifndef PV_REG_PCR_ENTRY_13_4
`define PV_REG_PCR_ENTRY_13_4                                                                       (32'h880)
`endif
`ifndef PV_REG_PCR_ENTRY_13_5
`define PV_REG_PCR_ENTRY_13_5                                                                       (32'h884)
`endif
`ifndef PV_REG_PCR_ENTRY_13_6
`define PV_REG_PCR_ENTRY_13_6                                                                       (32'h888)
`endif
`ifndef PV_REG_PCR_ENTRY_13_7
`define PV_REG_PCR_ENTRY_13_7                                                                       (32'h88c)
`endif
`ifndef PV_REG_PCR_ENTRY_13_8
`define PV_REG_PCR_ENTRY_13_8                                                                       (32'h890)
`endif
`ifndef PV_REG_PCR_ENTRY_13_9
`define PV_REG_PCR_ENTRY_13_9                                                                       (32'h894)
`endif
`ifndef PV_REG_PCR_ENTRY_13_10
`define PV_REG_PCR_ENTRY_13_10                                                                      (32'h898)
`endif
`ifndef PV_REG_PCR_ENTRY_13_11
`define PV_REG_PCR_ENTRY_13_11                                                                      (32'h89c)
`endif
`ifndef PV_REG_PCR_ENTRY_14_0
`define PV_REG_PCR_ENTRY_14_0                                                                       (32'h8a0)
`endif
`ifndef PV_REG_PCR_ENTRY_14_1
`define PV_REG_PCR_ENTRY_14_1                                                                       (32'h8a4)
`endif
`ifndef PV_REG_PCR_ENTRY_14_2
`define PV_REG_PCR_ENTRY_14_2                                                                       (32'h8a8)
`endif
`ifndef PV_REG_PCR_ENTRY_14_3
`define PV_REG_PCR_ENTRY_14_3                                                                       (32'h8ac)
`endif
`ifndef PV_REG_PCR_ENTRY_14_4
`define PV_REG_PCR_ENTRY_14_4                                                                       (32'h8b0)
`endif
`ifndef PV_REG_PCR_ENTRY_14_5
`define PV_REG_PCR_ENTRY_14_5                                                                       (32'h8b4)
`endif
`ifndef PV_REG_PCR_ENTRY_14_6
`define PV_REG_PCR_ENTRY_14_6                                                                       (32'h8b8)
`endif
`ifndef PV_REG_PCR_ENTRY_14_7
`define PV_REG_PCR_ENTRY_14_7                                                                       (32'h8bc)
`endif
`ifndef PV_REG_PCR_ENTRY_14_8
`define PV_REG_PCR_ENTRY_14_8                                                                       (32'h8c0)
`endif
`ifndef PV_REG_PCR_ENTRY_14_9
`define PV_REG_PCR_ENTRY_14_9                                                                       (32'h8c4)
`endif
`ifndef PV_REG_PCR_ENTRY_14_10
`define PV_REG_PCR_ENTRY_14_10                                                                      (32'h8c8)
`endif
`ifndef PV_REG_PCR_ENTRY_14_11
`define PV_REG_PCR_ENTRY_14_11                                                                      (32'h8cc)
`endif
`ifndef PV_REG_PCR_ENTRY_15_0
`define PV_REG_PCR_ENTRY_15_0                                                                       (32'h8d0)
`endif
`ifndef PV_REG_PCR_ENTRY_15_1
`define PV_REG_PCR_ENTRY_15_1                                                                       (32'h8d4)
`endif
`ifndef PV_REG_PCR_ENTRY_15_2
`define PV_REG_PCR_ENTRY_15_2                                                                       (32'h8d8)
`endif
`ifndef PV_REG_PCR_ENTRY_15_3
`define PV_REG_PCR_ENTRY_15_3                                                                       (32'h8dc)
`endif
`ifndef PV_REG_PCR_ENTRY_15_4
`define PV_REG_PCR_ENTRY_15_4                                                                       (32'h8e0)
`endif
`ifndef PV_REG_PCR_ENTRY_15_5
`define PV_REG_PCR_ENTRY_15_5                                                                       (32'h8e4)
`endif
`ifndef PV_REG_PCR_ENTRY_15_6
`define PV_REG_PCR_ENTRY_15_6                                                                       (32'h8e8)
`endif
`ifndef PV_REG_PCR_ENTRY_15_7
`define PV_REG_PCR_ENTRY_15_7                                                                       (32'h8ec)
`endif
`ifndef PV_REG_PCR_ENTRY_15_8
`define PV_REG_PCR_ENTRY_15_8                                                                       (32'h8f0)
`endif
`ifndef PV_REG_PCR_ENTRY_15_9
`define PV_REG_PCR_ENTRY_15_9                                                                       (32'h8f4)
`endif
`ifndef PV_REG_PCR_ENTRY_15_10
`define PV_REG_PCR_ENTRY_15_10                                                                      (32'h8f8)
`endif
`ifndef PV_REG_PCR_ENTRY_15_11
`define PV_REG_PCR_ENTRY_15_11                                                                      (32'h8fc)
`endif
`ifndef PV_REG_PCR_ENTRY_16_0
`define PV_REG_PCR_ENTRY_16_0                                                                       (32'h900)
`endif
`ifndef PV_REG_PCR_ENTRY_16_1
`define PV_REG_PCR_ENTRY_16_1                                                                       (32'h904)
`endif
`ifndef PV_REG_PCR_ENTRY_16_2
`define PV_REG_PCR_ENTRY_16_2                                                                       (32'h908)
`endif
`ifndef PV_REG_PCR_ENTRY_16_3
`define PV_REG_PCR_ENTRY_16_3                                                                       (32'h90c)
`endif
`ifndef PV_REG_PCR_ENTRY_16_4
`define PV_REG_PCR_ENTRY_16_4                                                                       (32'h910)
`endif
`ifndef PV_REG_PCR_ENTRY_16_5
`define PV_REG_PCR_ENTRY_16_5                                                                       (32'h914)
`endif
`ifndef PV_REG_PCR_ENTRY_16_6
`define PV_REG_PCR_ENTRY_16_6                                                                       (32'h918)
`endif
`ifndef PV_REG_PCR_ENTRY_16_7
`define PV_REG_PCR_ENTRY_16_7                                                                       (32'h91c)
`endif
`ifndef PV_REG_PCR_ENTRY_16_8
`define PV_REG_PCR_ENTRY_16_8                                                                       (32'h920)
`endif
`ifndef PV_REG_PCR_ENTRY_16_9
`define PV_REG_PCR_ENTRY_16_9                                                                       (32'h924)
`endif
`ifndef PV_REG_PCR_ENTRY_16_10
`define PV_REG_PCR_ENTRY_16_10                                                                      (32'h928)
`endif
`ifndef PV_REG_PCR_ENTRY_16_11
`define PV_REG_PCR_ENTRY_16_11                                                                      (32'h92c)
`endif
`ifndef PV_REG_PCR_ENTRY_17_0
`define PV_REG_PCR_ENTRY_17_0                                                                       (32'h930)
`endif
`ifndef PV_REG_PCR_ENTRY_17_1
`define PV_REG_PCR_ENTRY_17_1                                                                       (32'h934)
`endif
`ifndef PV_REG_PCR_ENTRY_17_2
`define PV_REG_PCR_ENTRY_17_2                                                                       (32'h938)
`endif
`ifndef PV_REG_PCR_ENTRY_17_3
`define PV_REG_PCR_ENTRY_17_3                                                                       (32'h93c)
`endif
`ifndef PV_REG_PCR_ENTRY_17_4
`define PV_REG_PCR_ENTRY_17_4                                                                       (32'h940)
`endif
`ifndef PV_REG_PCR_ENTRY_17_5
`define PV_REG_PCR_ENTRY_17_5                                                                       (32'h944)
`endif
`ifndef PV_REG_PCR_ENTRY_17_6
`define PV_REG_PCR_ENTRY_17_6                                                                       (32'h948)
`endif
`ifndef PV_REG_PCR_ENTRY_17_7
`define PV_REG_PCR_ENTRY_17_7                                                                       (32'h94c)
`endif
`ifndef PV_REG_PCR_ENTRY_17_8
`define PV_REG_PCR_ENTRY_17_8                                                                       (32'h950)
`endif
`ifndef PV_REG_PCR_ENTRY_17_9
`define PV_REG_PCR_ENTRY_17_9                                                                       (32'h954)
`endif
`ifndef PV_REG_PCR_ENTRY_17_10
`define PV_REG_PCR_ENTRY_17_10                                                                      (32'h958)
`endif
`ifndef PV_REG_PCR_ENTRY_17_11
`define PV_REG_PCR_ENTRY_17_11                                                                      (32'h95c)
`endif
`ifndef PV_REG_PCR_ENTRY_18_0
`define PV_REG_PCR_ENTRY_18_0                                                                       (32'h960)
`endif
`ifndef PV_REG_PCR_ENTRY_18_1
`define PV_REG_PCR_ENTRY_18_1                                                                       (32'h964)
`endif
`ifndef PV_REG_PCR_ENTRY_18_2
`define PV_REG_PCR_ENTRY_18_2                                                                       (32'h968)
`endif
`ifndef PV_REG_PCR_ENTRY_18_3
`define PV_REG_PCR_ENTRY_18_3                                                                       (32'h96c)
`endif
`ifndef PV_REG_PCR_ENTRY_18_4
`define PV_REG_PCR_ENTRY_18_4                                                                       (32'h970)
`endif
`ifndef PV_REG_PCR_ENTRY_18_5
`define PV_REG_PCR_ENTRY_18_5                                                                       (32'h974)
`endif
`ifndef PV_REG_PCR_ENTRY_18_6
`define PV_REG_PCR_ENTRY_18_6                                                                       (32'h978)
`endif
`ifndef PV_REG_PCR_ENTRY_18_7
`define PV_REG_PCR_ENTRY_18_7                                                                       (32'h97c)
`endif
`ifndef PV_REG_PCR_ENTRY_18_8
`define PV_REG_PCR_ENTRY_18_8                                                                       (32'h980)
`endif
`ifndef PV_REG_PCR_ENTRY_18_9
`define PV_REG_PCR_ENTRY_18_9                                                                       (32'h984)
`endif
`ifndef PV_REG_PCR_ENTRY_18_10
`define PV_REG_PCR_ENTRY_18_10                                                                      (32'h988)
`endif
`ifndef PV_REG_PCR_ENTRY_18_11
`define PV_REG_PCR_ENTRY_18_11                                                                      (32'h98c)
`endif
`ifndef PV_REG_PCR_ENTRY_19_0
`define PV_REG_PCR_ENTRY_19_0                                                                       (32'h990)
`endif
`ifndef PV_REG_PCR_ENTRY_19_1
`define PV_REG_PCR_ENTRY_19_1                                                                       (32'h994)
`endif
`ifndef PV_REG_PCR_ENTRY_19_2
`define PV_REG_PCR_ENTRY_19_2                                                                       (32'h998)
`endif
`ifndef PV_REG_PCR_ENTRY_19_3
`define PV_REG_PCR_ENTRY_19_3                                                                       (32'h99c)
`endif
`ifndef PV_REG_PCR_ENTRY_19_4
`define PV_REG_PCR_ENTRY_19_4                                                                       (32'h9a0)
`endif
`ifndef PV_REG_PCR_ENTRY_19_5
`define PV_REG_PCR_ENTRY_19_5                                                                       (32'h9a4)
`endif
`ifndef PV_REG_PCR_ENTRY_19_6
`define PV_REG_PCR_ENTRY_19_6                                                                       (32'h9a8)
`endif
`ifndef PV_REG_PCR_ENTRY_19_7
`define PV_REG_PCR_ENTRY_19_7                                                                       (32'h9ac)
`endif
`ifndef PV_REG_PCR_ENTRY_19_8
`define PV_REG_PCR_ENTRY_19_8                                                                       (32'h9b0)
`endif
`ifndef PV_REG_PCR_ENTRY_19_9
`define PV_REG_PCR_ENTRY_19_9                                                                       (32'h9b4)
`endif
`ifndef PV_REG_PCR_ENTRY_19_10
`define PV_REG_PCR_ENTRY_19_10                                                                      (32'h9b8)
`endif
`ifndef PV_REG_PCR_ENTRY_19_11
`define PV_REG_PCR_ENTRY_19_11                                                                      (32'h9bc)
`endif
`ifndef PV_REG_PCR_ENTRY_20_0
`define PV_REG_PCR_ENTRY_20_0                                                                       (32'h9c0)
`endif
`ifndef PV_REG_PCR_ENTRY_20_1
`define PV_REG_PCR_ENTRY_20_1                                                                       (32'h9c4)
`endif
`ifndef PV_REG_PCR_ENTRY_20_2
`define PV_REG_PCR_ENTRY_20_2                                                                       (32'h9c8)
`endif
`ifndef PV_REG_PCR_ENTRY_20_3
`define PV_REG_PCR_ENTRY_20_3                                                                       (32'h9cc)
`endif
`ifndef PV_REG_PCR_ENTRY_20_4
`define PV_REG_PCR_ENTRY_20_4                                                                       (32'h9d0)
`endif
`ifndef PV_REG_PCR_ENTRY_20_5
`define PV_REG_PCR_ENTRY_20_5                                                                       (32'h9d4)
`endif
`ifndef PV_REG_PCR_ENTRY_20_6
`define PV_REG_PCR_ENTRY_20_6                                                                       (32'h9d8)
`endif
`ifndef PV_REG_PCR_ENTRY_20_7
`define PV_REG_PCR_ENTRY_20_7                                                                       (32'h9dc)
`endif
`ifndef PV_REG_PCR_ENTRY_20_8
`define PV_REG_PCR_ENTRY_20_8                                                                       (32'h9e0)
`endif
`ifndef PV_REG_PCR_ENTRY_20_9
`define PV_REG_PCR_ENTRY_20_9                                                                       (32'h9e4)
`endif
`ifndef PV_REG_PCR_ENTRY_20_10
`define PV_REG_PCR_ENTRY_20_10                                                                      (32'h9e8)
`endif
`ifndef PV_REG_PCR_ENTRY_20_11
`define PV_REG_PCR_ENTRY_20_11                                                                      (32'h9ec)
`endif
`ifndef PV_REG_PCR_ENTRY_21_0
`define PV_REG_PCR_ENTRY_21_0                                                                       (32'h9f0)
`endif
`ifndef PV_REG_PCR_ENTRY_21_1
`define PV_REG_PCR_ENTRY_21_1                                                                       (32'h9f4)
`endif
`ifndef PV_REG_PCR_ENTRY_21_2
`define PV_REG_PCR_ENTRY_21_2                                                                       (32'h9f8)
`endif
`ifndef PV_REG_PCR_ENTRY_21_3
`define PV_REG_PCR_ENTRY_21_3                                                                       (32'h9fc)
`endif
`ifndef PV_REG_PCR_ENTRY_21_4
`define PV_REG_PCR_ENTRY_21_4                                                                       (32'ha00)
`endif
`ifndef PV_REG_PCR_ENTRY_21_5
`define PV_REG_PCR_ENTRY_21_5                                                                       (32'ha04)
`endif
`ifndef PV_REG_PCR_ENTRY_21_6
`define PV_REG_PCR_ENTRY_21_6                                                                       (32'ha08)
`endif
`ifndef PV_REG_PCR_ENTRY_21_7
`define PV_REG_PCR_ENTRY_21_7                                                                       (32'ha0c)
`endif
`ifndef PV_REG_PCR_ENTRY_21_8
`define PV_REG_PCR_ENTRY_21_8                                                                       (32'ha10)
`endif
`ifndef PV_REG_PCR_ENTRY_21_9
`define PV_REG_PCR_ENTRY_21_9                                                                       (32'ha14)
`endif
`ifndef PV_REG_PCR_ENTRY_21_10
`define PV_REG_PCR_ENTRY_21_10                                                                      (32'ha18)
`endif
`ifndef PV_REG_PCR_ENTRY_21_11
`define PV_REG_PCR_ENTRY_21_11                                                                      (32'ha1c)
`endif
`ifndef PV_REG_PCR_ENTRY_22_0
`define PV_REG_PCR_ENTRY_22_0                                                                       (32'ha20)
`endif
`ifndef PV_REG_PCR_ENTRY_22_1
`define PV_REG_PCR_ENTRY_22_1                                                                       (32'ha24)
`endif
`ifndef PV_REG_PCR_ENTRY_22_2
`define PV_REG_PCR_ENTRY_22_2                                                                       (32'ha28)
`endif
`ifndef PV_REG_PCR_ENTRY_22_3
`define PV_REG_PCR_ENTRY_22_3                                                                       (32'ha2c)
`endif
`ifndef PV_REG_PCR_ENTRY_22_4
`define PV_REG_PCR_ENTRY_22_4                                                                       (32'ha30)
`endif
`ifndef PV_REG_PCR_ENTRY_22_5
`define PV_REG_PCR_ENTRY_22_5                                                                       (32'ha34)
`endif
`ifndef PV_REG_PCR_ENTRY_22_6
`define PV_REG_PCR_ENTRY_22_6                                                                       (32'ha38)
`endif
`ifndef PV_REG_PCR_ENTRY_22_7
`define PV_REG_PCR_ENTRY_22_7                                                                       (32'ha3c)
`endif
`ifndef PV_REG_PCR_ENTRY_22_8
`define PV_REG_PCR_ENTRY_22_8                                                                       (32'ha40)
`endif
`ifndef PV_REG_PCR_ENTRY_22_9
`define PV_REG_PCR_ENTRY_22_9                                                                       (32'ha44)
`endif
`ifndef PV_REG_PCR_ENTRY_22_10
`define PV_REG_PCR_ENTRY_22_10                                                                      (32'ha48)
`endif
`ifndef PV_REG_PCR_ENTRY_22_11
`define PV_REG_PCR_ENTRY_22_11                                                                      (32'ha4c)
`endif
`ifndef PV_REG_PCR_ENTRY_23_0
`define PV_REG_PCR_ENTRY_23_0                                                                       (32'ha50)
`endif
`ifndef PV_REG_PCR_ENTRY_23_1
`define PV_REG_PCR_ENTRY_23_1                                                                       (32'ha54)
`endif
`ifndef PV_REG_PCR_ENTRY_23_2
`define PV_REG_PCR_ENTRY_23_2                                                                       (32'ha58)
`endif
`ifndef PV_REG_PCR_ENTRY_23_3
`define PV_REG_PCR_ENTRY_23_3                                                                       (32'ha5c)
`endif
`ifndef PV_REG_PCR_ENTRY_23_4
`define PV_REG_PCR_ENTRY_23_4                                                                       (32'ha60)
`endif
`ifndef PV_REG_PCR_ENTRY_23_5
`define PV_REG_PCR_ENTRY_23_5                                                                       (32'ha64)
`endif
`ifndef PV_REG_PCR_ENTRY_23_6
`define PV_REG_PCR_ENTRY_23_6                                                                       (32'ha68)
`endif
`ifndef PV_REG_PCR_ENTRY_23_7
`define PV_REG_PCR_ENTRY_23_7                                                                       (32'ha6c)
`endif
`ifndef PV_REG_PCR_ENTRY_23_8
`define PV_REG_PCR_ENTRY_23_8                                                                       (32'ha70)
`endif
`ifndef PV_REG_PCR_ENTRY_23_9
`define PV_REG_PCR_ENTRY_23_9                                                                       (32'ha74)
`endif
`ifndef PV_REG_PCR_ENTRY_23_10
`define PV_REG_PCR_ENTRY_23_10                                                                      (32'ha78)
`endif
`ifndef PV_REG_PCR_ENTRY_23_11
`define PV_REG_PCR_ENTRY_23_11                                                                      (32'ha7c)
`endif
`ifndef PV_REG_PCR_ENTRY_24_0
`define PV_REG_PCR_ENTRY_24_0                                                                       (32'ha80)
`endif
`ifndef PV_REG_PCR_ENTRY_24_1
`define PV_REG_PCR_ENTRY_24_1                                                                       (32'ha84)
`endif
`ifndef PV_REG_PCR_ENTRY_24_2
`define PV_REG_PCR_ENTRY_24_2                                                                       (32'ha88)
`endif
`ifndef PV_REG_PCR_ENTRY_24_3
`define PV_REG_PCR_ENTRY_24_3                                                                       (32'ha8c)
`endif
`ifndef PV_REG_PCR_ENTRY_24_4
`define PV_REG_PCR_ENTRY_24_4                                                                       (32'ha90)
`endif
`ifndef PV_REG_PCR_ENTRY_24_5
`define PV_REG_PCR_ENTRY_24_5                                                                       (32'ha94)
`endif
`ifndef PV_REG_PCR_ENTRY_24_6
`define PV_REG_PCR_ENTRY_24_6                                                                       (32'ha98)
`endif
`ifndef PV_REG_PCR_ENTRY_24_7
`define PV_REG_PCR_ENTRY_24_7                                                                       (32'ha9c)
`endif
`ifndef PV_REG_PCR_ENTRY_24_8
`define PV_REG_PCR_ENTRY_24_8                                                                       (32'haa0)
`endif
`ifndef PV_REG_PCR_ENTRY_24_9
`define PV_REG_PCR_ENTRY_24_9                                                                       (32'haa4)
`endif
`ifndef PV_REG_PCR_ENTRY_24_10
`define PV_REG_PCR_ENTRY_24_10                                                                      (32'haa8)
`endif
`ifndef PV_REG_PCR_ENTRY_24_11
`define PV_REG_PCR_ENTRY_24_11                                                                      (32'haac)
`endif
`ifndef PV_REG_PCR_ENTRY_25_0
`define PV_REG_PCR_ENTRY_25_0                                                                       (32'hab0)
`endif
`ifndef PV_REG_PCR_ENTRY_25_1
`define PV_REG_PCR_ENTRY_25_1                                                                       (32'hab4)
`endif
`ifndef PV_REG_PCR_ENTRY_25_2
`define PV_REG_PCR_ENTRY_25_2                                                                       (32'hab8)
`endif
`ifndef PV_REG_PCR_ENTRY_25_3
`define PV_REG_PCR_ENTRY_25_3                                                                       (32'habc)
`endif
`ifndef PV_REG_PCR_ENTRY_25_4
`define PV_REG_PCR_ENTRY_25_4                                                                       (32'hac0)
`endif
`ifndef PV_REG_PCR_ENTRY_25_5
`define PV_REG_PCR_ENTRY_25_5                                                                       (32'hac4)
`endif
`ifndef PV_REG_PCR_ENTRY_25_6
`define PV_REG_PCR_ENTRY_25_6                                                                       (32'hac8)
`endif
`ifndef PV_REG_PCR_ENTRY_25_7
`define PV_REG_PCR_ENTRY_25_7                                                                       (32'hacc)
`endif
`ifndef PV_REG_PCR_ENTRY_25_8
`define PV_REG_PCR_ENTRY_25_8                                                                       (32'had0)
`endif
`ifndef PV_REG_PCR_ENTRY_25_9
`define PV_REG_PCR_ENTRY_25_9                                                                       (32'had4)
`endif
`ifndef PV_REG_PCR_ENTRY_25_10
`define PV_REG_PCR_ENTRY_25_10                                                                      (32'had8)
`endif
`ifndef PV_REG_PCR_ENTRY_25_11
`define PV_REG_PCR_ENTRY_25_11                                                                      (32'hadc)
`endif
`ifndef PV_REG_PCR_ENTRY_26_0
`define PV_REG_PCR_ENTRY_26_0                                                                       (32'hae0)
`endif
`ifndef PV_REG_PCR_ENTRY_26_1
`define PV_REG_PCR_ENTRY_26_1                                                                       (32'hae4)
`endif
`ifndef PV_REG_PCR_ENTRY_26_2
`define PV_REG_PCR_ENTRY_26_2                                                                       (32'hae8)
`endif
`ifndef PV_REG_PCR_ENTRY_26_3
`define PV_REG_PCR_ENTRY_26_3                                                                       (32'haec)
`endif
`ifndef PV_REG_PCR_ENTRY_26_4
`define PV_REG_PCR_ENTRY_26_4                                                                       (32'haf0)
`endif
`ifndef PV_REG_PCR_ENTRY_26_5
`define PV_REG_PCR_ENTRY_26_5                                                                       (32'haf4)
`endif
`ifndef PV_REG_PCR_ENTRY_26_6
`define PV_REG_PCR_ENTRY_26_6                                                                       (32'haf8)
`endif
`ifndef PV_REG_PCR_ENTRY_26_7
`define PV_REG_PCR_ENTRY_26_7                                                                       (32'hafc)
`endif
`ifndef PV_REG_PCR_ENTRY_26_8
`define PV_REG_PCR_ENTRY_26_8                                                                       (32'hb00)
`endif
`ifndef PV_REG_PCR_ENTRY_26_9
`define PV_REG_PCR_ENTRY_26_9                                                                       (32'hb04)
`endif
`ifndef PV_REG_PCR_ENTRY_26_10
`define PV_REG_PCR_ENTRY_26_10                                                                      (32'hb08)
`endif
`ifndef PV_REG_PCR_ENTRY_26_11
`define PV_REG_PCR_ENTRY_26_11                                                                      (32'hb0c)
`endif
`ifndef PV_REG_PCR_ENTRY_27_0
`define PV_REG_PCR_ENTRY_27_0                                                                       (32'hb10)
`endif
`ifndef PV_REG_PCR_ENTRY_27_1
`define PV_REG_PCR_ENTRY_27_1                                                                       (32'hb14)
`endif
`ifndef PV_REG_PCR_ENTRY_27_2
`define PV_REG_PCR_ENTRY_27_2                                                                       (32'hb18)
`endif
`ifndef PV_REG_PCR_ENTRY_27_3
`define PV_REG_PCR_ENTRY_27_3                                                                       (32'hb1c)
`endif
`ifndef PV_REG_PCR_ENTRY_27_4
`define PV_REG_PCR_ENTRY_27_4                                                                       (32'hb20)
`endif
`ifndef PV_REG_PCR_ENTRY_27_5
`define PV_REG_PCR_ENTRY_27_5                                                                       (32'hb24)
`endif
`ifndef PV_REG_PCR_ENTRY_27_6
`define PV_REG_PCR_ENTRY_27_6                                                                       (32'hb28)
`endif
`ifndef PV_REG_PCR_ENTRY_27_7
`define PV_REG_PCR_ENTRY_27_7                                                                       (32'hb2c)
`endif
`ifndef PV_REG_PCR_ENTRY_27_8
`define PV_REG_PCR_ENTRY_27_8                                                                       (32'hb30)
`endif
`ifndef PV_REG_PCR_ENTRY_27_9
`define PV_REG_PCR_ENTRY_27_9                                                                       (32'hb34)
`endif
`ifndef PV_REG_PCR_ENTRY_27_10
`define PV_REG_PCR_ENTRY_27_10                                                                      (32'hb38)
`endif
`ifndef PV_REG_PCR_ENTRY_27_11
`define PV_REG_PCR_ENTRY_27_11                                                                      (32'hb3c)
`endif
`ifndef PV_REG_PCR_ENTRY_28_0
`define PV_REG_PCR_ENTRY_28_0                                                                       (32'hb40)
`endif
`ifndef PV_REG_PCR_ENTRY_28_1
`define PV_REG_PCR_ENTRY_28_1                                                                       (32'hb44)
`endif
`ifndef PV_REG_PCR_ENTRY_28_2
`define PV_REG_PCR_ENTRY_28_2                                                                       (32'hb48)
`endif
`ifndef PV_REG_PCR_ENTRY_28_3
`define PV_REG_PCR_ENTRY_28_3                                                                       (32'hb4c)
`endif
`ifndef PV_REG_PCR_ENTRY_28_4
`define PV_REG_PCR_ENTRY_28_4                                                                       (32'hb50)
`endif
`ifndef PV_REG_PCR_ENTRY_28_5
`define PV_REG_PCR_ENTRY_28_5                                                                       (32'hb54)
`endif
`ifndef PV_REG_PCR_ENTRY_28_6
`define PV_REG_PCR_ENTRY_28_6                                                                       (32'hb58)
`endif
`ifndef PV_REG_PCR_ENTRY_28_7
`define PV_REG_PCR_ENTRY_28_7                                                                       (32'hb5c)
`endif
`ifndef PV_REG_PCR_ENTRY_28_8
`define PV_REG_PCR_ENTRY_28_8                                                                       (32'hb60)
`endif
`ifndef PV_REG_PCR_ENTRY_28_9
`define PV_REG_PCR_ENTRY_28_9                                                                       (32'hb64)
`endif
`ifndef PV_REG_PCR_ENTRY_28_10
`define PV_REG_PCR_ENTRY_28_10                                                                      (32'hb68)
`endif
`ifndef PV_REG_PCR_ENTRY_28_11
`define PV_REG_PCR_ENTRY_28_11                                                                      (32'hb6c)
`endif
`ifndef PV_REG_PCR_ENTRY_29_0
`define PV_REG_PCR_ENTRY_29_0                                                                       (32'hb70)
`endif
`ifndef PV_REG_PCR_ENTRY_29_1
`define PV_REG_PCR_ENTRY_29_1                                                                       (32'hb74)
`endif
`ifndef PV_REG_PCR_ENTRY_29_2
`define PV_REG_PCR_ENTRY_29_2                                                                       (32'hb78)
`endif
`ifndef PV_REG_PCR_ENTRY_29_3
`define PV_REG_PCR_ENTRY_29_3                                                                       (32'hb7c)
`endif
`ifndef PV_REG_PCR_ENTRY_29_4
`define PV_REG_PCR_ENTRY_29_4                                                                       (32'hb80)
`endif
`ifndef PV_REG_PCR_ENTRY_29_5
`define PV_REG_PCR_ENTRY_29_5                                                                       (32'hb84)
`endif
`ifndef PV_REG_PCR_ENTRY_29_6
`define PV_REG_PCR_ENTRY_29_6                                                                       (32'hb88)
`endif
`ifndef PV_REG_PCR_ENTRY_29_7
`define PV_REG_PCR_ENTRY_29_7                                                                       (32'hb8c)
`endif
`ifndef PV_REG_PCR_ENTRY_29_8
`define PV_REG_PCR_ENTRY_29_8                                                                       (32'hb90)
`endif
`ifndef PV_REG_PCR_ENTRY_29_9
`define PV_REG_PCR_ENTRY_29_9                                                                       (32'hb94)
`endif
`ifndef PV_REG_PCR_ENTRY_29_10
`define PV_REG_PCR_ENTRY_29_10                                                                      (32'hb98)
`endif
`ifndef PV_REG_PCR_ENTRY_29_11
`define PV_REG_PCR_ENTRY_29_11                                                                      (32'hb9c)
`endif
`ifndef PV_REG_PCR_ENTRY_30_0
`define PV_REG_PCR_ENTRY_30_0                                                                       (32'hba0)
`endif
`ifndef PV_REG_PCR_ENTRY_30_1
`define PV_REG_PCR_ENTRY_30_1                                                                       (32'hba4)
`endif
`ifndef PV_REG_PCR_ENTRY_30_2
`define PV_REG_PCR_ENTRY_30_2                                                                       (32'hba8)
`endif
`ifndef PV_REG_PCR_ENTRY_30_3
`define PV_REG_PCR_ENTRY_30_3                                                                       (32'hbac)
`endif
`ifndef PV_REG_PCR_ENTRY_30_4
`define PV_REG_PCR_ENTRY_30_4                                                                       (32'hbb0)
`endif
`ifndef PV_REG_PCR_ENTRY_30_5
`define PV_REG_PCR_ENTRY_30_5                                                                       (32'hbb4)
`endif
`ifndef PV_REG_PCR_ENTRY_30_6
`define PV_REG_PCR_ENTRY_30_6                                                                       (32'hbb8)
`endif
`ifndef PV_REG_PCR_ENTRY_30_7
`define PV_REG_PCR_ENTRY_30_7                                                                       (32'hbbc)
`endif
`ifndef PV_REG_PCR_ENTRY_30_8
`define PV_REG_PCR_ENTRY_30_8                                                                       (32'hbc0)
`endif
`ifndef PV_REG_PCR_ENTRY_30_9
`define PV_REG_PCR_ENTRY_30_9                                                                       (32'hbc4)
`endif
`ifndef PV_REG_PCR_ENTRY_30_10
`define PV_REG_PCR_ENTRY_30_10                                                                      (32'hbc8)
`endif
`ifndef PV_REG_PCR_ENTRY_30_11
`define PV_REG_PCR_ENTRY_30_11                                                                      (32'hbcc)
`endif
`ifndef PV_REG_PCR_ENTRY_31_0
`define PV_REG_PCR_ENTRY_31_0                                                                       (32'hbd0)
`endif
`ifndef PV_REG_PCR_ENTRY_31_1
`define PV_REG_PCR_ENTRY_31_1                                                                       (32'hbd4)
`endif
`ifndef PV_REG_PCR_ENTRY_31_2
`define PV_REG_PCR_ENTRY_31_2                                                                       (32'hbd8)
`endif
`ifndef PV_REG_PCR_ENTRY_31_3
`define PV_REG_PCR_ENTRY_31_3                                                                       (32'hbdc)
`endif
`ifndef PV_REG_PCR_ENTRY_31_4
`define PV_REG_PCR_ENTRY_31_4                                                                       (32'hbe0)
`endif
`ifndef PV_REG_PCR_ENTRY_31_5
`define PV_REG_PCR_ENTRY_31_5                                                                       (32'hbe4)
`endif
`ifndef PV_REG_PCR_ENTRY_31_6
`define PV_REG_PCR_ENTRY_31_6                                                                       (32'hbe8)
`endif
`ifndef PV_REG_PCR_ENTRY_31_7
`define PV_REG_PCR_ENTRY_31_7                                                                       (32'hbec)
`endif
`ifndef PV_REG_PCR_ENTRY_31_8
`define PV_REG_PCR_ENTRY_31_8                                                                       (32'hbf0)
`endif
`ifndef PV_REG_PCR_ENTRY_31_9
`define PV_REG_PCR_ENTRY_31_9                                                                       (32'hbf4)
`endif
`ifndef PV_REG_PCR_ENTRY_31_10
`define PV_REG_PCR_ENTRY_31_10                                                                      (32'hbf8)
`endif
`ifndef PV_REG_PCR_ENTRY_31_11
`define PV_REG_PCR_ENTRY_31_11                                                                      (32'hbfc)
`endif
`ifndef DV_REG_STICKYDATAVAULTCTRL_0
`define DV_REG_STICKYDATAVAULTCTRL_0                                                                (32'h0)
`define DV_REG_STICKYDATAVAULTCTRL_0_LOCK_ENTRY_LOW                                                 (0)
`define DV_REG_STICKYDATAVAULTCTRL_0_LOCK_ENTRY_MASK                                                (32'h1)
`endif
`ifndef DV_REG_STICKYDATAVAULTCTRL_1
`define DV_REG_STICKYDATAVAULTCTRL_1                                                                (32'h4)
`define DV_REG_STICKYDATAVAULTCTRL_1_LOCK_ENTRY_LOW                                                 (0)
`define DV_REG_STICKYDATAVAULTCTRL_1_LOCK_ENTRY_MASK                                                (32'h1)
`endif
`ifndef DV_REG_STICKYDATAVAULTCTRL_2
`define DV_REG_STICKYDATAVAULTCTRL_2                                                                (32'h8)
`define DV_REG_STICKYDATAVAULTCTRL_2_LOCK_ENTRY_LOW                                                 (0)
`define DV_REG_STICKYDATAVAULTCTRL_2_LOCK_ENTRY_MASK                                                (32'h1)
`endif
`ifndef DV_REG_STICKYDATAVAULTCTRL_3
`define DV_REG_STICKYDATAVAULTCTRL_3                                                                (32'hc)
`define DV_REG_STICKYDATAVAULTCTRL_3_LOCK_ENTRY_LOW                                                 (0)
`define DV_REG_STICKYDATAVAULTCTRL_3_LOCK_ENTRY_MASK                                                (32'h1)
`endif
`ifndef DV_REG_STICKYDATAVAULTCTRL_4
`define DV_REG_STICKYDATAVAULTCTRL_4                                                                (32'h10)
`define DV_REG_STICKYDATAVAULTCTRL_4_LOCK_ENTRY_LOW                                                 (0)
`define DV_REG_STICKYDATAVAULTCTRL_4_LOCK_ENTRY_MASK                                                (32'h1)
`endif
`ifndef DV_REG_STICKYDATAVAULTCTRL_5
`define DV_REG_STICKYDATAVAULTCTRL_5                                                                (32'h14)
`define DV_REG_STICKYDATAVAULTCTRL_5_LOCK_ENTRY_LOW                                                 (0)
`define DV_REG_STICKYDATAVAULTCTRL_5_LOCK_ENTRY_MASK                                                (32'h1)
`endif
`ifndef DV_REG_STICKYDATAVAULTCTRL_6
`define DV_REG_STICKYDATAVAULTCTRL_6                                                                (32'h18)
`define DV_REG_STICKYDATAVAULTCTRL_6_LOCK_ENTRY_LOW                                                 (0)
`define DV_REG_STICKYDATAVAULTCTRL_6_LOCK_ENTRY_MASK                                                (32'h1)
`endif
`ifndef DV_REG_STICKYDATAVAULTCTRL_7
`define DV_REG_STICKYDATAVAULTCTRL_7                                                                (32'h1c)
`define DV_REG_STICKYDATAVAULTCTRL_7_LOCK_ENTRY_LOW                                                 (0)
`define DV_REG_STICKYDATAVAULTCTRL_7_LOCK_ENTRY_MASK                                                (32'h1)
`endif
`ifndef DV_REG_STICKYDATAVAULTCTRL_8
`define DV_REG_STICKYDATAVAULTCTRL_8                                                                (32'h20)
`define DV_REG_STICKYDATAVAULTCTRL_8_LOCK_ENTRY_LOW                                                 (0)
`define DV_REG_STICKYDATAVAULTCTRL_8_LOCK_ENTRY_MASK                                                (32'h1)
`endif
`ifndef DV_REG_STICKYDATAVAULTCTRL_9
`define DV_REG_STICKYDATAVAULTCTRL_9                                                                (32'h24)
`define DV_REG_STICKYDATAVAULTCTRL_9_LOCK_ENTRY_LOW                                                 (0)
`define DV_REG_STICKYDATAVAULTCTRL_9_LOCK_ENTRY_MASK                                                (32'h1)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_0_0
`define DV_REG_STICKY_DATA_VAULT_ENTRY_0_0                                                          (32'h28)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_0_1
`define DV_REG_STICKY_DATA_VAULT_ENTRY_0_1                                                          (32'h2c)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_0_2
`define DV_REG_STICKY_DATA_VAULT_ENTRY_0_2                                                          (32'h30)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_0_3
`define DV_REG_STICKY_DATA_VAULT_ENTRY_0_3                                                          (32'h34)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_0_4
`define DV_REG_STICKY_DATA_VAULT_ENTRY_0_4                                                          (32'h38)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_0_5
`define DV_REG_STICKY_DATA_VAULT_ENTRY_0_5                                                          (32'h3c)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_0_6
`define DV_REG_STICKY_DATA_VAULT_ENTRY_0_6                                                          (32'h40)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_0_7
`define DV_REG_STICKY_DATA_VAULT_ENTRY_0_7                                                          (32'h44)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_0_8
`define DV_REG_STICKY_DATA_VAULT_ENTRY_0_8                                                          (32'h48)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_0_9
`define DV_REG_STICKY_DATA_VAULT_ENTRY_0_9                                                          (32'h4c)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_0_10
`define DV_REG_STICKY_DATA_VAULT_ENTRY_0_10                                                         (32'h50)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_0_11
`define DV_REG_STICKY_DATA_VAULT_ENTRY_0_11                                                         (32'h54)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_1_0
`define DV_REG_STICKY_DATA_VAULT_ENTRY_1_0                                                          (32'h58)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_1_1
`define DV_REG_STICKY_DATA_VAULT_ENTRY_1_1                                                          (32'h5c)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_1_2
`define DV_REG_STICKY_DATA_VAULT_ENTRY_1_2                                                          (32'h60)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_1_3
`define DV_REG_STICKY_DATA_VAULT_ENTRY_1_3                                                          (32'h64)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_1_4
`define DV_REG_STICKY_DATA_VAULT_ENTRY_1_4                                                          (32'h68)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_1_5
`define DV_REG_STICKY_DATA_VAULT_ENTRY_1_5                                                          (32'h6c)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_1_6
`define DV_REG_STICKY_DATA_VAULT_ENTRY_1_6                                                          (32'h70)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_1_7
`define DV_REG_STICKY_DATA_VAULT_ENTRY_1_7                                                          (32'h74)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_1_8
`define DV_REG_STICKY_DATA_VAULT_ENTRY_1_8                                                          (32'h78)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_1_9
`define DV_REG_STICKY_DATA_VAULT_ENTRY_1_9                                                          (32'h7c)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_1_10
`define DV_REG_STICKY_DATA_VAULT_ENTRY_1_10                                                         (32'h80)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_1_11
`define DV_REG_STICKY_DATA_VAULT_ENTRY_1_11                                                         (32'h84)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_2_0
`define DV_REG_STICKY_DATA_VAULT_ENTRY_2_0                                                          (32'h88)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_2_1
`define DV_REG_STICKY_DATA_VAULT_ENTRY_2_1                                                          (32'h8c)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_2_2
`define DV_REG_STICKY_DATA_VAULT_ENTRY_2_2                                                          (32'h90)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_2_3
`define DV_REG_STICKY_DATA_VAULT_ENTRY_2_3                                                          (32'h94)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_2_4
`define DV_REG_STICKY_DATA_VAULT_ENTRY_2_4                                                          (32'h98)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_2_5
`define DV_REG_STICKY_DATA_VAULT_ENTRY_2_5                                                          (32'h9c)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_2_6
`define DV_REG_STICKY_DATA_VAULT_ENTRY_2_6                                                          (32'ha0)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_2_7
`define DV_REG_STICKY_DATA_VAULT_ENTRY_2_7                                                          (32'ha4)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_2_8
`define DV_REG_STICKY_DATA_VAULT_ENTRY_2_8                                                          (32'ha8)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_2_9
`define DV_REG_STICKY_DATA_VAULT_ENTRY_2_9                                                          (32'hac)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_2_10
`define DV_REG_STICKY_DATA_VAULT_ENTRY_2_10                                                         (32'hb0)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_2_11
`define DV_REG_STICKY_DATA_VAULT_ENTRY_2_11                                                         (32'hb4)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_3_0
`define DV_REG_STICKY_DATA_VAULT_ENTRY_3_0                                                          (32'hb8)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_3_1
`define DV_REG_STICKY_DATA_VAULT_ENTRY_3_1                                                          (32'hbc)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_3_2
`define DV_REG_STICKY_DATA_VAULT_ENTRY_3_2                                                          (32'hc0)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_3_3
`define DV_REG_STICKY_DATA_VAULT_ENTRY_3_3                                                          (32'hc4)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_3_4
`define DV_REG_STICKY_DATA_VAULT_ENTRY_3_4                                                          (32'hc8)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_3_5
`define DV_REG_STICKY_DATA_VAULT_ENTRY_3_5                                                          (32'hcc)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_3_6
`define DV_REG_STICKY_DATA_VAULT_ENTRY_3_6                                                          (32'hd0)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_3_7
`define DV_REG_STICKY_DATA_VAULT_ENTRY_3_7                                                          (32'hd4)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_3_8
`define DV_REG_STICKY_DATA_VAULT_ENTRY_3_8                                                          (32'hd8)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_3_9
`define DV_REG_STICKY_DATA_VAULT_ENTRY_3_9                                                          (32'hdc)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_3_10
`define DV_REG_STICKY_DATA_VAULT_ENTRY_3_10                                                         (32'he0)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_3_11
`define DV_REG_STICKY_DATA_VAULT_ENTRY_3_11                                                         (32'he4)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_4_0
`define DV_REG_STICKY_DATA_VAULT_ENTRY_4_0                                                          (32'he8)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_4_1
`define DV_REG_STICKY_DATA_VAULT_ENTRY_4_1                                                          (32'hec)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_4_2
`define DV_REG_STICKY_DATA_VAULT_ENTRY_4_2                                                          (32'hf0)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_4_3
`define DV_REG_STICKY_DATA_VAULT_ENTRY_4_3                                                          (32'hf4)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_4_4
`define DV_REG_STICKY_DATA_VAULT_ENTRY_4_4                                                          (32'hf8)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_4_5
`define DV_REG_STICKY_DATA_VAULT_ENTRY_4_5                                                          (32'hfc)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_4_6
`define DV_REG_STICKY_DATA_VAULT_ENTRY_4_6                                                          (32'h100)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_4_7
`define DV_REG_STICKY_DATA_VAULT_ENTRY_4_7                                                          (32'h104)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_4_8
`define DV_REG_STICKY_DATA_VAULT_ENTRY_4_8                                                          (32'h108)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_4_9
`define DV_REG_STICKY_DATA_VAULT_ENTRY_4_9                                                          (32'h10c)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_4_10
`define DV_REG_STICKY_DATA_VAULT_ENTRY_4_10                                                         (32'h110)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_4_11
`define DV_REG_STICKY_DATA_VAULT_ENTRY_4_11                                                         (32'h114)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_5_0
`define DV_REG_STICKY_DATA_VAULT_ENTRY_5_0                                                          (32'h118)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_5_1
`define DV_REG_STICKY_DATA_VAULT_ENTRY_5_1                                                          (32'h11c)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_5_2
`define DV_REG_STICKY_DATA_VAULT_ENTRY_5_2                                                          (32'h120)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_5_3
`define DV_REG_STICKY_DATA_VAULT_ENTRY_5_3                                                          (32'h124)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_5_4
`define DV_REG_STICKY_DATA_VAULT_ENTRY_5_4                                                          (32'h128)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_5_5
`define DV_REG_STICKY_DATA_VAULT_ENTRY_5_5                                                          (32'h12c)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_5_6
`define DV_REG_STICKY_DATA_VAULT_ENTRY_5_6                                                          (32'h130)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_5_7
`define DV_REG_STICKY_DATA_VAULT_ENTRY_5_7                                                          (32'h134)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_5_8
`define DV_REG_STICKY_DATA_VAULT_ENTRY_5_8                                                          (32'h138)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_5_9
`define DV_REG_STICKY_DATA_VAULT_ENTRY_5_9                                                          (32'h13c)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_5_10
`define DV_REG_STICKY_DATA_VAULT_ENTRY_5_10                                                         (32'h140)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_5_11
`define DV_REG_STICKY_DATA_VAULT_ENTRY_5_11                                                         (32'h144)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_6_0
`define DV_REG_STICKY_DATA_VAULT_ENTRY_6_0                                                          (32'h148)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_6_1
`define DV_REG_STICKY_DATA_VAULT_ENTRY_6_1                                                          (32'h14c)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_6_2
`define DV_REG_STICKY_DATA_VAULT_ENTRY_6_2                                                          (32'h150)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_6_3
`define DV_REG_STICKY_DATA_VAULT_ENTRY_6_3                                                          (32'h154)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_6_4
`define DV_REG_STICKY_DATA_VAULT_ENTRY_6_4                                                          (32'h158)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_6_5
`define DV_REG_STICKY_DATA_VAULT_ENTRY_6_5                                                          (32'h15c)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_6_6
`define DV_REG_STICKY_DATA_VAULT_ENTRY_6_6                                                          (32'h160)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_6_7
`define DV_REG_STICKY_DATA_VAULT_ENTRY_6_7                                                          (32'h164)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_6_8
`define DV_REG_STICKY_DATA_VAULT_ENTRY_6_8                                                          (32'h168)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_6_9
`define DV_REG_STICKY_DATA_VAULT_ENTRY_6_9                                                          (32'h16c)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_6_10
`define DV_REG_STICKY_DATA_VAULT_ENTRY_6_10                                                         (32'h170)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_6_11
`define DV_REG_STICKY_DATA_VAULT_ENTRY_6_11                                                         (32'h174)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_7_0
`define DV_REG_STICKY_DATA_VAULT_ENTRY_7_0                                                          (32'h178)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_7_1
`define DV_REG_STICKY_DATA_VAULT_ENTRY_7_1                                                          (32'h17c)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_7_2
`define DV_REG_STICKY_DATA_VAULT_ENTRY_7_2                                                          (32'h180)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_7_3
`define DV_REG_STICKY_DATA_VAULT_ENTRY_7_3                                                          (32'h184)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_7_4
`define DV_REG_STICKY_DATA_VAULT_ENTRY_7_4                                                          (32'h188)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_7_5
`define DV_REG_STICKY_DATA_VAULT_ENTRY_7_5                                                          (32'h18c)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_7_6
`define DV_REG_STICKY_DATA_VAULT_ENTRY_7_6                                                          (32'h190)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_7_7
`define DV_REG_STICKY_DATA_VAULT_ENTRY_7_7                                                          (32'h194)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_7_8
`define DV_REG_STICKY_DATA_VAULT_ENTRY_7_8                                                          (32'h198)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_7_9
`define DV_REG_STICKY_DATA_VAULT_ENTRY_7_9                                                          (32'h19c)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_7_10
`define DV_REG_STICKY_DATA_VAULT_ENTRY_7_10                                                         (32'h1a0)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_7_11
`define DV_REG_STICKY_DATA_VAULT_ENTRY_7_11                                                         (32'h1a4)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_8_0
`define DV_REG_STICKY_DATA_VAULT_ENTRY_8_0                                                          (32'h1a8)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_8_1
`define DV_REG_STICKY_DATA_VAULT_ENTRY_8_1                                                          (32'h1ac)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_8_2
`define DV_REG_STICKY_DATA_VAULT_ENTRY_8_2                                                          (32'h1b0)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_8_3
`define DV_REG_STICKY_DATA_VAULT_ENTRY_8_3                                                          (32'h1b4)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_8_4
`define DV_REG_STICKY_DATA_VAULT_ENTRY_8_4                                                          (32'h1b8)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_8_5
`define DV_REG_STICKY_DATA_VAULT_ENTRY_8_5                                                          (32'h1bc)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_8_6
`define DV_REG_STICKY_DATA_VAULT_ENTRY_8_6                                                          (32'h1c0)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_8_7
`define DV_REG_STICKY_DATA_VAULT_ENTRY_8_7                                                          (32'h1c4)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_8_8
`define DV_REG_STICKY_DATA_VAULT_ENTRY_8_8                                                          (32'h1c8)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_8_9
`define DV_REG_STICKY_DATA_VAULT_ENTRY_8_9                                                          (32'h1cc)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_8_10
`define DV_REG_STICKY_DATA_VAULT_ENTRY_8_10                                                         (32'h1d0)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_8_11
`define DV_REG_STICKY_DATA_VAULT_ENTRY_8_11                                                         (32'h1d4)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_9_0
`define DV_REG_STICKY_DATA_VAULT_ENTRY_9_0                                                          (32'h1d8)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_9_1
`define DV_REG_STICKY_DATA_VAULT_ENTRY_9_1                                                          (32'h1dc)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_9_2
`define DV_REG_STICKY_DATA_VAULT_ENTRY_9_2                                                          (32'h1e0)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_9_3
`define DV_REG_STICKY_DATA_VAULT_ENTRY_9_3                                                          (32'h1e4)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_9_4
`define DV_REG_STICKY_DATA_VAULT_ENTRY_9_4                                                          (32'h1e8)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_9_5
`define DV_REG_STICKY_DATA_VAULT_ENTRY_9_5                                                          (32'h1ec)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_9_6
`define DV_REG_STICKY_DATA_VAULT_ENTRY_9_6                                                          (32'h1f0)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_9_7
`define DV_REG_STICKY_DATA_VAULT_ENTRY_9_7                                                          (32'h1f4)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_9_8
`define DV_REG_STICKY_DATA_VAULT_ENTRY_9_8                                                          (32'h1f8)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_9_9
`define DV_REG_STICKY_DATA_VAULT_ENTRY_9_9                                                          (32'h1fc)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_9_10
`define DV_REG_STICKY_DATA_VAULT_ENTRY_9_10                                                         (32'h200)
`endif
`ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_9_11
`define DV_REG_STICKY_DATA_VAULT_ENTRY_9_11                                                         (32'h204)
`endif
`ifndef DV_REG_DATAVAULTCTRL_0
`define DV_REG_DATAVAULTCTRL_0                                                                      (32'h208)
`define DV_REG_DATAVAULTCTRL_0_LOCK_ENTRY_LOW                                                       (0)
`define DV_REG_DATAVAULTCTRL_0_LOCK_ENTRY_MASK                                                      (32'h1)
`endif
`ifndef DV_REG_DATAVAULTCTRL_1
`define DV_REG_DATAVAULTCTRL_1                                                                      (32'h20c)
`define DV_REG_DATAVAULTCTRL_1_LOCK_ENTRY_LOW                                                       (0)
`define DV_REG_DATAVAULTCTRL_1_LOCK_ENTRY_MASK                                                      (32'h1)
`endif
`ifndef DV_REG_DATAVAULTCTRL_2
`define DV_REG_DATAVAULTCTRL_2                                                                      (32'h210)
`define DV_REG_DATAVAULTCTRL_2_LOCK_ENTRY_LOW                                                       (0)
`define DV_REG_DATAVAULTCTRL_2_LOCK_ENTRY_MASK                                                      (32'h1)
`endif
`ifndef DV_REG_DATAVAULTCTRL_3
`define DV_REG_DATAVAULTCTRL_3                                                                      (32'h214)
`define DV_REG_DATAVAULTCTRL_3_LOCK_ENTRY_LOW                                                       (0)
`define DV_REG_DATAVAULTCTRL_3_LOCK_ENTRY_MASK                                                      (32'h1)
`endif
`ifndef DV_REG_DATAVAULTCTRL_4
`define DV_REG_DATAVAULTCTRL_4                                                                      (32'h218)
`define DV_REG_DATAVAULTCTRL_4_LOCK_ENTRY_LOW                                                       (0)
`define DV_REG_DATAVAULTCTRL_4_LOCK_ENTRY_MASK                                                      (32'h1)
`endif
`ifndef DV_REG_DATAVAULTCTRL_5
`define DV_REG_DATAVAULTCTRL_5                                                                      (32'h21c)
`define DV_REG_DATAVAULTCTRL_5_LOCK_ENTRY_LOW                                                       (0)
`define DV_REG_DATAVAULTCTRL_5_LOCK_ENTRY_MASK                                                      (32'h1)
`endif
`ifndef DV_REG_DATAVAULTCTRL_6
`define DV_REG_DATAVAULTCTRL_6                                                                      (32'h220)
`define DV_REG_DATAVAULTCTRL_6_LOCK_ENTRY_LOW                                                       (0)
`define DV_REG_DATAVAULTCTRL_6_LOCK_ENTRY_MASK                                                      (32'h1)
`endif
`ifndef DV_REG_DATAVAULTCTRL_7
`define DV_REG_DATAVAULTCTRL_7                                                                      (32'h224)
`define DV_REG_DATAVAULTCTRL_7_LOCK_ENTRY_LOW                                                       (0)
`define DV_REG_DATAVAULTCTRL_7_LOCK_ENTRY_MASK                                                      (32'h1)
`endif
`ifndef DV_REG_DATAVAULTCTRL_8
`define DV_REG_DATAVAULTCTRL_8                                                                      (32'h228)
`define DV_REG_DATAVAULTCTRL_8_LOCK_ENTRY_LOW                                                       (0)
`define DV_REG_DATAVAULTCTRL_8_LOCK_ENTRY_MASK                                                      (32'h1)
`endif
`ifndef DV_REG_DATAVAULTCTRL_9
`define DV_REG_DATAVAULTCTRL_9                                                                      (32'h22c)
`define DV_REG_DATAVAULTCTRL_9_LOCK_ENTRY_LOW                                                       (0)
`define DV_REG_DATAVAULTCTRL_9_LOCK_ENTRY_MASK                                                      (32'h1)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_0_0
`define DV_REG_DATA_VAULT_ENTRY_0_0                                                                 (32'h230)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_0_1
`define DV_REG_DATA_VAULT_ENTRY_0_1                                                                 (32'h234)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_0_2
`define DV_REG_DATA_VAULT_ENTRY_0_2                                                                 (32'h238)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_0_3
`define DV_REG_DATA_VAULT_ENTRY_0_3                                                                 (32'h23c)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_0_4
`define DV_REG_DATA_VAULT_ENTRY_0_4                                                                 (32'h240)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_0_5
`define DV_REG_DATA_VAULT_ENTRY_0_5                                                                 (32'h244)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_0_6
`define DV_REG_DATA_VAULT_ENTRY_0_6                                                                 (32'h248)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_0_7
`define DV_REG_DATA_VAULT_ENTRY_0_7                                                                 (32'h24c)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_0_8
`define DV_REG_DATA_VAULT_ENTRY_0_8                                                                 (32'h250)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_0_9
`define DV_REG_DATA_VAULT_ENTRY_0_9                                                                 (32'h254)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_0_10
`define DV_REG_DATA_VAULT_ENTRY_0_10                                                                (32'h258)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_0_11
`define DV_REG_DATA_VAULT_ENTRY_0_11                                                                (32'h25c)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_1_0
`define DV_REG_DATA_VAULT_ENTRY_1_0                                                                 (32'h260)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_1_1
`define DV_REG_DATA_VAULT_ENTRY_1_1                                                                 (32'h264)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_1_2
`define DV_REG_DATA_VAULT_ENTRY_1_2                                                                 (32'h268)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_1_3
`define DV_REG_DATA_VAULT_ENTRY_1_3                                                                 (32'h26c)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_1_4
`define DV_REG_DATA_VAULT_ENTRY_1_4                                                                 (32'h270)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_1_5
`define DV_REG_DATA_VAULT_ENTRY_1_5                                                                 (32'h274)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_1_6
`define DV_REG_DATA_VAULT_ENTRY_1_6                                                                 (32'h278)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_1_7
`define DV_REG_DATA_VAULT_ENTRY_1_7                                                                 (32'h27c)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_1_8
`define DV_REG_DATA_VAULT_ENTRY_1_8                                                                 (32'h280)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_1_9
`define DV_REG_DATA_VAULT_ENTRY_1_9                                                                 (32'h284)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_1_10
`define DV_REG_DATA_VAULT_ENTRY_1_10                                                                (32'h288)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_1_11
`define DV_REG_DATA_VAULT_ENTRY_1_11                                                                (32'h28c)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_2_0
`define DV_REG_DATA_VAULT_ENTRY_2_0                                                                 (32'h290)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_2_1
`define DV_REG_DATA_VAULT_ENTRY_2_1                                                                 (32'h294)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_2_2
`define DV_REG_DATA_VAULT_ENTRY_2_2                                                                 (32'h298)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_2_3
`define DV_REG_DATA_VAULT_ENTRY_2_3                                                                 (32'h29c)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_2_4
`define DV_REG_DATA_VAULT_ENTRY_2_4                                                                 (32'h2a0)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_2_5
`define DV_REG_DATA_VAULT_ENTRY_2_5                                                                 (32'h2a4)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_2_6
`define DV_REG_DATA_VAULT_ENTRY_2_6                                                                 (32'h2a8)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_2_7
`define DV_REG_DATA_VAULT_ENTRY_2_7                                                                 (32'h2ac)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_2_8
`define DV_REG_DATA_VAULT_ENTRY_2_8                                                                 (32'h2b0)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_2_9
`define DV_REG_DATA_VAULT_ENTRY_2_9                                                                 (32'h2b4)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_2_10
`define DV_REG_DATA_VAULT_ENTRY_2_10                                                                (32'h2b8)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_2_11
`define DV_REG_DATA_VAULT_ENTRY_2_11                                                                (32'h2bc)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_3_0
`define DV_REG_DATA_VAULT_ENTRY_3_0                                                                 (32'h2c0)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_3_1
`define DV_REG_DATA_VAULT_ENTRY_3_1                                                                 (32'h2c4)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_3_2
`define DV_REG_DATA_VAULT_ENTRY_3_2                                                                 (32'h2c8)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_3_3
`define DV_REG_DATA_VAULT_ENTRY_3_3                                                                 (32'h2cc)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_3_4
`define DV_REG_DATA_VAULT_ENTRY_3_4                                                                 (32'h2d0)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_3_5
`define DV_REG_DATA_VAULT_ENTRY_3_5                                                                 (32'h2d4)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_3_6
`define DV_REG_DATA_VAULT_ENTRY_3_6                                                                 (32'h2d8)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_3_7
`define DV_REG_DATA_VAULT_ENTRY_3_7                                                                 (32'h2dc)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_3_8
`define DV_REG_DATA_VAULT_ENTRY_3_8                                                                 (32'h2e0)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_3_9
`define DV_REG_DATA_VAULT_ENTRY_3_9                                                                 (32'h2e4)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_3_10
`define DV_REG_DATA_VAULT_ENTRY_3_10                                                                (32'h2e8)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_3_11
`define DV_REG_DATA_VAULT_ENTRY_3_11                                                                (32'h2ec)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_4_0
`define DV_REG_DATA_VAULT_ENTRY_4_0                                                                 (32'h2f0)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_4_1
`define DV_REG_DATA_VAULT_ENTRY_4_1                                                                 (32'h2f4)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_4_2
`define DV_REG_DATA_VAULT_ENTRY_4_2                                                                 (32'h2f8)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_4_3
`define DV_REG_DATA_VAULT_ENTRY_4_3                                                                 (32'h2fc)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_4_4
`define DV_REG_DATA_VAULT_ENTRY_4_4                                                                 (32'h300)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_4_5
`define DV_REG_DATA_VAULT_ENTRY_4_5                                                                 (32'h304)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_4_6
`define DV_REG_DATA_VAULT_ENTRY_4_6                                                                 (32'h308)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_4_7
`define DV_REG_DATA_VAULT_ENTRY_4_7                                                                 (32'h30c)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_4_8
`define DV_REG_DATA_VAULT_ENTRY_4_8                                                                 (32'h310)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_4_9
`define DV_REG_DATA_VAULT_ENTRY_4_9                                                                 (32'h314)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_4_10
`define DV_REG_DATA_VAULT_ENTRY_4_10                                                                (32'h318)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_4_11
`define DV_REG_DATA_VAULT_ENTRY_4_11                                                                (32'h31c)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_5_0
`define DV_REG_DATA_VAULT_ENTRY_5_0                                                                 (32'h320)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_5_1
`define DV_REG_DATA_VAULT_ENTRY_5_1                                                                 (32'h324)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_5_2
`define DV_REG_DATA_VAULT_ENTRY_5_2                                                                 (32'h328)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_5_3
`define DV_REG_DATA_VAULT_ENTRY_5_3                                                                 (32'h32c)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_5_4
`define DV_REG_DATA_VAULT_ENTRY_5_4                                                                 (32'h330)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_5_5
`define DV_REG_DATA_VAULT_ENTRY_5_5                                                                 (32'h334)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_5_6
`define DV_REG_DATA_VAULT_ENTRY_5_6                                                                 (32'h338)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_5_7
`define DV_REG_DATA_VAULT_ENTRY_5_7                                                                 (32'h33c)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_5_8
`define DV_REG_DATA_VAULT_ENTRY_5_8                                                                 (32'h340)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_5_9
`define DV_REG_DATA_VAULT_ENTRY_5_9                                                                 (32'h344)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_5_10
`define DV_REG_DATA_VAULT_ENTRY_5_10                                                                (32'h348)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_5_11
`define DV_REG_DATA_VAULT_ENTRY_5_11                                                                (32'h34c)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_6_0
`define DV_REG_DATA_VAULT_ENTRY_6_0                                                                 (32'h350)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_6_1
`define DV_REG_DATA_VAULT_ENTRY_6_1                                                                 (32'h354)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_6_2
`define DV_REG_DATA_VAULT_ENTRY_6_2                                                                 (32'h358)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_6_3
`define DV_REG_DATA_VAULT_ENTRY_6_3                                                                 (32'h35c)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_6_4
`define DV_REG_DATA_VAULT_ENTRY_6_4                                                                 (32'h360)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_6_5
`define DV_REG_DATA_VAULT_ENTRY_6_5                                                                 (32'h364)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_6_6
`define DV_REG_DATA_VAULT_ENTRY_6_6                                                                 (32'h368)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_6_7
`define DV_REG_DATA_VAULT_ENTRY_6_7                                                                 (32'h36c)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_6_8
`define DV_REG_DATA_VAULT_ENTRY_6_8                                                                 (32'h370)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_6_9
`define DV_REG_DATA_VAULT_ENTRY_6_9                                                                 (32'h374)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_6_10
`define DV_REG_DATA_VAULT_ENTRY_6_10                                                                (32'h378)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_6_11
`define DV_REG_DATA_VAULT_ENTRY_6_11                                                                (32'h37c)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_7_0
`define DV_REG_DATA_VAULT_ENTRY_7_0                                                                 (32'h380)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_7_1
`define DV_REG_DATA_VAULT_ENTRY_7_1                                                                 (32'h384)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_7_2
`define DV_REG_DATA_VAULT_ENTRY_7_2                                                                 (32'h388)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_7_3
`define DV_REG_DATA_VAULT_ENTRY_7_3                                                                 (32'h38c)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_7_4
`define DV_REG_DATA_VAULT_ENTRY_7_4                                                                 (32'h390)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_7_5
`define DV_REG_DATA_VAULT_ENTRY_7_5                                                                 (32'h394)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_7_6
`define DV_REG_DATA_VAULT_ENTRY_7_6                                                                 (32'h398)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_7_7
`define DV_REG_DATA_VAULT_ENTRY_7_7                                                                 (32'h39c)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_7_8
`define DV_REG_DATA_VAULT_ENTRY_7_8                                                                 (32'h3a0)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_7_9
`define DV_REG_DATA_VAULT_ENTRY_7_9                                                                 (32'h3a4)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_7_10
`define DV_REG_DATA_VAULT_ENTRY_7_10                                                                (32'h3a8)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_7_11
`define DV_REG_DATA_VAULT_ENTRY_7_11                                                                (32'h3ac)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_8_0
`define DV_REG_DATA_VAULT_ENTRY_8_0                                                                 (32'h3b0)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_8_1
`define DV_REG_DATA_VAULT_ENTRY_8_1                                                                 (32'h3b4)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_8_2
`define DV_REG_DATA_VAULT_ENTRY_8_2                                                                 (32'h3b8)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_8_3
`define DV_REG_DATA_VAULT_ENTRY_8_3                                                                 (32'h3bc)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_8_4
`define DV_REG_DATA_VAULT_ENTRY_8_4                                                                 (32'h3c0)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_8_5
`define DV_REG_DATA_VAULT_ENTRY_8_5                                                                 (32'h3c4)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_8_6
`define DV_REG_DATA_VAULT_ENTRY_8_6                                                                 (32'h3c8)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_8_7
`define DV_REG_DATA_VAULT_ENTRY_8_7                                                                 (32'h3cc)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_8_8
`define DV_REG_DATA_VAULT_ENTRY_8_8                                                                 (32'h3d0)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_8_9
`define DV_REG_DATA_VAULT_ENTRY_8_9                                                                 (32'h3d4)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_8_10
`define DV_REG_DATA_VAULT_ENTRY_8_10                                                                (32'h3d8)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_8_11
`define DV_REG_DATA_VAULT_ENTRY_8_11                                                                (32'h3dc)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_9_0
`define DV_REG_DATA_VAULT_ENTRY_9_0                                                                 (32'h3e0)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_9_1
`define DV_REG_DATA_VAULT_ENTRY_9_1                                                                 (32'h3e4)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_9_2
`define DV_REG_DATA_VAULT_ENTRY_9_2                                                                 (32'h3e8)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_9_3
`define DV_REG_DATA_VAULT_ENTRY_9_3                                                                 (32'h3ec)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_9_4
`define DV_REG_DATA_VAULT_ENTRY_9_4                                                                 (32'h3f0)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_9_5
`define DV_REG_DATA_VAULT_ENTRY_9_5                                                                 (32'h3f4)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_9_6
`define DV_REG_DATA_VAULT_ENTRY_9_6                                                                 (32'h3f8)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_9_7
`define DV_REG_DATA_VAULT_ENTRY_9_7                                                                 (32'h3fc)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_9_8
`define DV_REG_DATA_VAULT_ENTRY_9_8                                                                 (32'h400)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_9_9
`define DV_REG_DATA_VAULT_ENTRY_9_9                                                                 (32'h404)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_9_10
`define DV_REG_DATA_VAULT_ENTRY_9_10                                                                (32'h408)
`endif
`ifndef DV_REG_DATA_VAULT_ENTRY_9_11
`define DV_REG_DATA_VAULT_ENTRY_9_11                                                                (32'h40c)
`endif
`ifndef DV_REG_LOCKABLESCRATCHREGCTRL_0
`define DV_REG_LOCKABLESCRATCHREGCTRL_0                                                             (32'h410)
`define DV_REG_LOCKABLESCRATCHREGCTRL_0_LOCK_ENTRY_LOW                                              (0)
`define DV_REG_LOCKABLESCRATCHREGCTRL_0_LOCK_ENTRY_MASK                                             (32'h1)
`endif
`ifndef DV_REG_LOCKABLESCRATCHREGCTRL_1
`define DV_REG_LOCKABLESCRATCHREGCTRL_1                                                             (32'h414)
`define DV_REG_LOCKABLESCRATCHREGCTRL_1_LOCK_ENTRY_LOW                                              (0)
`define DV_REG_LOCKABLESCRATCHREGCTRL_1_LOCK_ENTRY_MASK                                             (32'h1)
`endif
`ifndef DV_REG_LOCKABLESCRATCHREGCTRL_2
`define DV_REG_LOCKABLESCRATCHREGCTRL_2                                                             (32'h418)
`define DV_REG_LOCKABLESCRATCHREGCTRL_2_LOCK_ENTRY_LOW                                              (0)
`define DV_REG_LOCKABLESCRATCHREGCTRL_2_LOCK_ENTRY_MASK                                             (32'h1)
`endif
`ifndef DV_REG_LOCKABLESCRATCHREGCTRL_3
`define DV_REG_LOCKABLESCRATCHREGCTRL_3                                                             (32'h41c)
`define DV_REG_LOCKABLESCRATCHREGCTRL_3_LOCK_ENTRY_LOW                                              (0)
`define DV_REG_LOCKABLESCRATCHREGCTRL_3_LOCK_ENTRY_MASK                                             (32'h1)
`endif
`ifndef DV_REG_LOCKABLESCRATCHREGCTRL_4
`define DV_REG_LOCKABLESCRATCHREGCTRL_4                                                             (32'h420)
`define DV_REG_LOCKABLESCRATCHREGCTRL_4_LOCK_ENTRY_LOW                                              (0)
`define DV_REG_LOCKABLESCRATCHREGCTRL_4_LOCK_ENTRY_MASK                                             (32'h1)
`endif
`ifndef DV_REG_LOCKABLESCRATCHREGCTRL_5
`define DV_REG_LOCKABLESCRATCHREGCTRL_5                                                             (32'h424)
`define DV_REG_LOCKABLESCRATCHREGCTRL_5_LOCK_ENTRY_LOW                                              (0)
`define DV_REG_LOCKABLESCRATCHREGCTRL_5_LOCK_ENTRY_MASK                                             (32'h1)
`endif
`ifndef DV_REG_LOCKABLESCRATCHREGCTRL_6
`define DV_REG_LOCKABLESCRATCHREGCTRL_6                                                             (32'h428)
`define DV_REG_LOCKABLESCRATCHREGCTRL_6_LOCK_ENTRY_LOW                                              (0)
`define DV_REG_LOCKABLESCRATCHREGCTRL_6_LOCK_ENTRY_MASK                                             (32'h1)
`endif
`ifndef DV_REG_LOCKABLESCRATCHREGCTRL_7
`define DV_REG_LOCKABLESCRATCHREGCTRL_7                                                             (32'h42c)
`define DV_REG_LOCKABLESCRATCHREGCTRL_7_LOCK_ENTRY_LOW                                              (0)
`define DV_REG_LOCKABLESCRATCHREGCTRL_7_LOCK_ENTRY_MASK                                             (32'h1)
`endif
`ifndef DV_REG_LOCKABLESCRATCHREGCTRL_8
`define DV_REG_LOCKABLESCRATCHREGCTRL_8                                                             (32'h430)
`define DV_REG_LOCKABLESCRATCHREGCTRL_8_LOCK_ENTRY_LOW                                              (0)
`define DV_REG_LOCKABLESCRATCHREGCTRL_8_LOCK_ENTRY_MASK                                             (32'h1)
`endif
`ifndef DV_REG_LOCKABLESCRATCHREGCTRL_9
`define DV_REG_LOCKABLESCRATCHREGCTRL_9                                                             (32'h434)
`define DV_REG_LOCKABLESCRATCHREGCTRL_9_LOCK_ENTRY_LOW                                              (0)
`define DV_REG_LOCKABLESCRATCHREGCTRL_9_LOCK_ENTRY_MASK                                             (32'h1)
`endif
`ifndef DV_REG_LOCKABLESCRATCHREG_0
`define DV_REG_LOCKABLESCRATCHREG_0                                                                 (32'h438)
`endif
`ifndef DV_REG_LOCKABLESCRATCHREG_1
`define DV_REG_LOCKABLESCRATCHREG_1                                                                 (32'h43c)
`endif
`ifndef DV_REG_LOCKABLESCRATCHREG_2
`define DV_REG_LOCKABLESCRATCHREG_2                                                                 (32'h440)
`endif
`ifndef DV_REG_LOCKABLESCRATCHREG_3
`define DV_REG_LOCKABLESCRATCHREG_3                                                                 (32'h444)
`endif
`ifndef DV_REG_LOCKABLESCRATCHREG_4
`define DV_REG_LOCKABLESCRATCHREG_4                                                                 (32'h448)
`endif
`ifndef DV_REG_LOCKABLESCRATCHREG_5
`define DV_REG_LOCKABLESCRATCHREG_5                                                                 (32'h44c)
`endif
`ifndef DV_REG_LOCKABLESCRATCHREG_6
`define DV_REG_LOCKABLESCRATCHREG_6                                                                 (32'h450)
`endif
`ifndef DV_REG_LOCKABLESCRATCHREG_7
`define DV_REG_LOCKABLESCRATCHREG_7                                                                 (32'h454)
`endif
`ifndef DV_REG_LOCKABLESCRATCHREG_8
`define DV_REG_LOCKABLESCRATCHREG_8                                                                 (32'h458)
`endif
`ifndef DV_REG_LOCKABLESCRATCHREG_9
`define DV_REG_LOCKABLESCRATCHREG_9                                                                 (32'h45c)
`endif
`ifndef DV_REG_NONSTICKYGENERICSCRATCHREG_0
`define DV_REG_NONSTICKYGENERICSCRATCHREG_0                                                         (32'h460)
`endif
`ifndef DV_REG_NONSTICKYGENERICSCRATCHREG_1
`define DV_REG_NONSTICKYGENERICSCRATCHREG_1                                                         (32'h464)
`endif
`ifndef DV_REG_NONSTICKYGENERICSCRATCHREG_2
`define DV_REG_NONSTICKYGENERICSCRATCHREG_2                                                         (32'h468)
`endif
`ifndef DV_REG_NONSTICKYGENERICSCRATCHREG_3
`define DV_REG_NONSTICKYGENERICSCRATCHREG_3                                                         (32'h46c)
`endif
`ifndef DV_REG_NONSTICKYGENERICSCRATCHREG_4
`define DV_REG_NONSTICKYGENERICSCRATCHREG_4                                                         (32'h470)
`endif
`ifndef DV_REG_NONSTICKYGENERICSCRATCHREG_5
`define DV_REG_NONSTICKYGENERICSCRATCHREG_5                                                         (32'h474)
`endif
`ifndef DV_REG_NONSTICKYGENERICSCRATCHREG_6
`define DV_REG_NONSTICKYGENERICSCRATCHREG_6                                                         (32'h478)
`endif
`ifndef DV_REG_NONSTICKYGENERICSCRATCHREG_7
`define DV_REG_NONSTICKYGENERICSCRATCHREG_7                                                         (32'h47c)
`endif
`ifndef DV_REG_STICKYLOCKABLESCRATCHREGCTRL_0
`define DV_REG_STICKYLOCKABLESCRATCHREGCTRL_0                                                       (32'h480)
`define DV_REG_STICKYLOCKABLESCRATCHREGCTRL_0_LOCK_ENTRY_LOW                                        (0)
`define DV_REG_STICKYLOCKABLESCRATCHREGCTRL_0_LOCK_ENTRY_MASK                                       (32'h1)
`endif
`ifndef DV_REG_STICKYLOCKABLESCRATCHREGCTRL_1
`define DV_REG_STICKYLOCKABLESCRATCHREGCTRL_1                                                       (32'h484)
`define DV_REG_STICKYLOCKABLESCRATCHREGCTRL_1_LOCK_ENTRY_LOW                                        (0)
`define DV_REG_STICKYLOCKABLESCRATCHREGCTRL_1_LOCK_ENTRY_MASK                                       (32'h1)
`endif
`ifndef DV_REG_STICKYLOCKABLESCRATCHREGCTRL_2
`define DV_REG_STICKYLOCKABLESCRATCHREGCTRL_2                                                       (32'h488)
`define DV_REG_STICKYLOCKABLESCRATCHREGCTRL_2_LOCK_ENTRY_LOW                                        (0)
`define DV_REG_STICKYLOCKABLESCRATCHREGCTRL_2_LOCK_ENTRY_MASK                                       (32'h1)
`endif
`ifndef DV_REG_STICKYLOCKABLESCRATCHREGCTRL_3
`define DV_REG_STICKYLOCKABLESCRATCHREGCTRL_3                                                       (32'h48c)
`define DV_REG_STICKYLOCKABLESCRATCHREGCTRL_3_LOCK_ENTRY_LOW                                        (0)
`define DV_REG_STICKYLOCKABLESCRATCHREGCTRL_3_LOCK_ENTRY_MASK                                       (32'h1)
`endif
`ifndef DV_REG_STICKYLOCKABLESCRATCHREGCTRL_4
`define DV_REG_STICKYLOCKABLESCRATCHREGCTRL_4                                                       (32'h490)
`define DV_REG_STICKYLOCKABLESCRATCHREGCTRL_4_LOCK_ENTRY_LOW                                        (0)
`define DV_REG_STICKYLOCKABLESCRATCHREGCTRL_4_LOCK_ENTRY_MASK                                       (32'h1)
`endif
`ifndef DV_REG_STICKYLOCKABLESCRATCHREGCTRL_5
`define DV_REG_STICKYLOCKABLESCRATCHREGCTRL_5                                                       (32'h494)
`define DV_REG_STICKYLOCKABLESCRATCHREGCTRL_5_LOCK_ENTRY_LOW                                        (0)
`define DV_REG_STICKYLOCKABLESCRATCHREGCTRL_5_LOCK_ENTRY_MASK                                       (32'h1)
`endif
`ifndef DV_REG_STICKYLOCKABLESCRATCHREGCTRL_6
`define DV_REG_STICKYLOCKABLESCRATCHREGCTRL_6                                                       (32'h498)
`define DV_REG_STICKYLOCKABLESCRATCHREGCTRL_6_LOCK_ENTRY_LOW                                        (0)
`define DV_REG_STICKYLOCKABLESCRATCHREGCTRL_6_LOCK_ENTRY_MASK                                       (32'h1)
`endif
`ifndef DV_REG_STICKYLOCKABLESCRATCHREGCTRL_7
`define DV_REG_STICKYLOCKABLESCRATCHREGCTRL_7                                                       (32'h49c)
`define DV_REG_STICKYLOCKABLESCRATCHREGCTRL_7_LOCK_ENTRY_LOW                                        (0)
`define DV_REG_STICKYLOCKABLESCRATCHREGCTRL_7_LOCK_ENTRY_MASK                                       (32'h1)
`endif
`ifndef DV_REG_STICKYLOCKABLESCRATCHREG_0
`define DV_REG_STICKYLOCKABLESCRATCHREG_0                                                           (32'h4a0)
`endif
`ifndef DV_REG_STICKYLOCKABLESCRATCHREG_1
`define DV_REG_STICKYLOCKABLESCRATCHREG_1                                                           (32'h4a4)
`endif
`ifndef DV_REG_STICKYLOCKABLESCRATCHREG_2
`define DV_REG_STICKYLOCKABLESCRATCHREG_2                                                           (32'h4a8)
`endif
`ifndef DV_REG_STICKYLOCKABLESCRATCHREG_3
`define DV_REG_STICKYLOCKABLESCRATCHREG_3                                                           (32'h4ac)
`endif
`ifndef DV_REG_STICKYLOCKABLESCRATCHREG_4
`define DV_REG_STICKYLOCKABLESCRATCHREG_4                                                           (32'h4b0)
`endif
`ifndef DV_REG_STICKYLOCKABLESCRATCHREG_5
`define DV_REG_STICKYLOCKABLESCRATCHREG_5                                                           (32'h4b4)
`endif
`ifndef DV_REG_STICKYLOCKABLESCRATCHREG_6
`define DV_REG_STICKYLOCKABLESCRATCHREG_6                                                           (32'h4b8)
`endif
`ifndef DV_REG_STICKYLOCKABLESCRATCHREG_7
`define DV_REG_STICKYLOCKABLESCRATCHREG_7                                                           (32'h4bc)
`endif
`ifndef SHA512_REG_SHA512_NAME_0
`define SHA512_REG_SHA512_NAME_0                                                                    (32'h0)
`endif
`ifndef SHA512_REG_SHA512_NAME_1
`define SHA512_REG_SHA512_NAME_1                                                                    (32'h4)
`endif
`ifndef SHA512_REG_SHA512_VERSION_0
`define SHA512_REG_SHA512_VERSION_0                                                                 (32'h8)
`endif
`ifndef SHA512_REG_SHA512_VERSION_1
`define SHA512_REG_SHA512_VERSION_1                                                                 (32'hc)
`endif
`ifndef SHA512_REG_SHA512_CTRL
`define SHA512_REG_SHA512_CTRL                                                                      (32'h10)
`define SHA512_REG_SHA512_CTRL_INIT_LOW                                                             (0)
`define SHA512_REG_SHA512_CTRL_INIT_MASK                                                            (32'h1)
`define SHA512_REG_SHA512_CTRL_NEXT_LOW                                                             (1)
`define SHA512_REG_SHA512_CTRL_NEXT_MASK                                                            (32'h2)
`define SHA512_REG_SHA512_CTRL_MODE_LOW                                                             (2)
`define SHA512_REG_SHA512_CTRL_MODE_MASK                                                            (32'hc)
`define SHA512_REG_SHA512_CTRL_ZEROIZE_LOW                                                          (4)
`define SHA512_REG_SHA512_CTRL_ZEROIZE_MASK                                                         (32'h10)
`define SHA512_REG_SHA512_CTRL_LAST_LOW                                                             (5)
`define SHA512_REG_SHA512_CTRL_LAST_MASK                                                            (32'h20)
`define SHA512_REG_SHA512_CTRL_RESTORE_LOW                                                          (6)
`define SHA512_REG_SHA512_CTRL_RESTORE_MASK                                                         (32'h40)
`endif
`ifndef SHA512_REG_SHA512_STATUS
`define SHA512_REG_SHA512_STATUS                                                                    (32'h18)
`define SHA512_REG_SHA512_STATUS_READY_LOW                                                          (0)
`define SHA512_REG_SHA512_STATUS_READY_MASK                                                         (32'h1)
`define SHA512_REG_SHA512_STATUS_VALID_LOW                                                          (1)
`define SHA512_REG_SHA512_STATUS_VALID_MASK                                                         (32'h2)
`endif
`ifndef SHA512_REG_SHA512_BLOCK_0
`define SHA512_REG_SHA512_BLOCK_0                                                                   (32'h80)
`endif
`ifndef SHA512_REG_SHA512_BLOCK_1
`define SHA512_REG_SHA512_BLOCK_1                                                                   (32'h84)
`endif
`ifndef SHA512_REG_SHA512_BLOCK_2
`define SHA512_REG_SHA512_BLOCK_2                                                                   (32'h88)
`endif
`ifndef SHA512_REG_SHA512_BLOCK_3
`define SHA512_REG_SHA512_BLOCK_3                                                                   (32'h8c)
`endif
`ifndef SHA512_REG_SHA512_BLOCK_4
`define SHA512_REG_SHA512_BLOCK_4                                                                   (32'h90)
`endif
`ifndef SHA512_REG_SHA512_BLOCK_5
`define SHA512_REG_SHA512_BLOCK_5                                                                   (32'h94)
`endif
`ifndef SHA512_REG_SHA512_BLOCK_6
`define SHA512_REG_SHA512_BLOCK_6                                                                   (32'h98)
`endif
`ifndef SHA512_REG_SHA512_BLOCK_7
`define SHA512_REG_SHA512_BLOCK_7                                                                   (32'h9c)
`endif
`ifndef SHA512_REG_SHA512_BLOCK_8
`define SHA512_REG_SHA512_BLOCK_8                                                                   (32'ha0)
`endif
`ifndef SHA512_REG_SHA512_BLOCK_9
`define SHA512_REG_SHA512_BLOCK_9                                                                   (32'ha4)
`endif
`ifndef SHA512_REG_SHA512_BLOCK_10
`define SHA512_REG_SHA512_BLOCK_10                                                                  (32'ha8)
`endif
`ifndef SHA512_REG_SHA512_BLOCK_11
`define SHA512_REG_SHA512_BLOCK_11                                                                  (32'hac)
`endif
`ifndef SHA512_REG_SHA512_BLOCK_12
`define SHA512_REG_SHA512_BLOCK_12                                                                  (32'hb0)
`endif
`ifndef SHA512_REG_SHA512_BLOCK_13
`define SHA512_REG_SHA512_BLOCK_13                                                                  (32'hb4)
`endif
`ifndef SHA512_REG_SHA512_BLOCK_14
`define SHA512_REG_SHA512_BLOCK_14                                                                  (32'hb8)
`endif
`ifndef SHA512_REG_SHA512_BLOCK_15
`define SHA512_REG_SHA512_BLOCK_15                                                                  (32'hbc)
`endif
`ifndef SHA512_REG_SHA512_BLOCK_16
`define SHA512_REG_SHA512_BLOCK_16                                                                  (32'hc0)
`endif
`ifndef SHA512_REG_SHA512_BLOCK_17
`define SHA512_REG_SHA512_BLOCK_17                                                                  (32'hc4)
`endif
`ifndef SHA512_REG_SHA512_BLOCK_18
`define SHA512_REG_SHA512_BLOCK_18                                                                  (32'hc8)
`endif
`ifndef SHA512_REG_SHA512_BLOCK_19
`define SHA512_REG_SHA512_BLOCK_19                                                                  (32'hcc)
`endif
`ifndef SHA512_REG_SHA512_BLOCK_20
`define SHA512_REG_SHA512_BLOCK_20                                                                  (32'hd0)
`endif
`ifndef SHA512_REG_SHA512_BLOCK_21
`define SHA512_REG_SHA512_BLOCK_21                                                                  (32'hd4)
`endif
`ifndef SHA512_REG_SHA512_BLOCK_22
`define SHA512_REG_SHA512_BLOCK_22                                                                  (32'hd8)
`endif
`ifndef SHA512_REG_SHA512_BLOCK_23
`define SHA512_REG_SHA512_BLOCK_23                                                                  (32'hdc)
`endif
`ifndef SHA512_REG_SHA512_BLOCK_24
`define SHA512_REG_SHA512_BLOCK_24                                                                  (32'he0)
`endif
`ifndef SHA512_REG_SHA512_BLOCK_25
`define SHA512_REG_SHA512_BLOCK_25                                                                  (32'he4)
`endif
`ifndef SHA512_REG_SHA512_BLOCK_26
`define SHA512_REG_SHA512_BLOCK_26                                                                  (32'he8)
`endif
`ifndef SHA512_REG_SHA512_BLOCK_27
`define SHA512_REG_SHA512_BLOCK_27                                                                  (32'hec)
`endif
`ifndef SHA512_REG_SHA512_BLOCK_28
`define SHA512_REG_SHA512_BLOCK_28                                                                  (32'hf0)
`endif
`ifndef SHA512_REG_SHA512_BLOCK_29
`define SHA512_REG_SHA512_BLOCK_29                                                                  (32'hf4)
`endif
`ifndef SHA512_REG_SHA512_BLOCK_30
`define SHA512_REG_SHA512_BLOCK_30                                                                  (32'hf8)
`endif
`ifndef SHA512_REG_SHA512_BLOCK_31
`define SHA512_REG_SHA512_BLOCK_31                                                                  (32'hfc)
`endif
`ifndef SHA512_REG_SHA512_DIGEST_0
`define SHA512_REG_SHA512_DIGEST_0                                                                  (32'h100)
`endif
`ifndef SHA512_REG_SHA512_DIGEST_1
`define SHA512_REG_SHA512_DIGEST_1                                                                  (32'h104)
`endif
`ifndef SHA512_REG_SHA512_DIGEST_2
`define SHA512_REG_SHA512_DIGEST_2                                                                  (32'h108)
`endif
`ifndef SHA512_REG_SHA512_DIGEST_3
`define SHA512_REG_SHA512_DIGEST_3                                                                  (32'h10c)
`endif
`ifndef SHA512_REG_SHA512_DIGEST_4
`define SHA512_REG_SHA512_DIGEST_4                                                                  (32'h110)
`endif
`ifndef SHA512_REG_SHA512_DIGEST_5
`define SHA512_REG_SHA512_DIGEST_5                                                                  (32'h114)
`endif
`ifndef SHA512_REG_SHA512_DIGEST_6
`define SHA512_REG_SHA512_DIGEST_6                                                                  (32'h118)
`endif
`ifndef SHA512_REG_SHA512_DIGEST_7
`define SHA512_REG_SHA512_DIGEST_7                                                                  (32'h11c)
`endif
`ifndef SHA512_REG_SHA512_DIGEST_8
`define SHA512_REG_SHA512_DIGEST_8                                                                  (32'h120)
`endif
`ifndef SHA512_REG_SHA512_DIGEST_9
`define SHA512_REG_SHA512_DIGEST_9                                                                  (32'h124)
`endif
`ifndef SHA512_REG_SHA512_DIGEST_10
`define SHA512_REG_SHA512_DIGEST_10                                                                 (32'h128)
`endif
`ifndef SHA512_REG_SHA512_DIGEST_11
`define SHA512_REG_SHA512_DIGEST_11                                                                 (32'h12c)
`endif
`ifndef SHA512_REG_SHA512_DIGEST_12
`define SHA512_REG_SHA512_DIGEST_12                                                                 (32'h130)
`endif
`ifndef SHA512_REG_SHA512_DIGEST_13
`define SHA512_REG_SHA512_DIGEST_13                                                                 (32'h134)
`endif
`ifndef SHA512_REG_SHA512_DIGEST_14
`define SHA512_REG_SHA512_DIGEST_14                                                                 (32'h138)
`endif
`ifndef SHA512_REG_SHA512_DIGEST_15
`define SHA512_REG_SHA512_DIGEST_15                                                                 (32'h13c)
`endif
`ifndef SHA512_REG_SHA512_VAULT_RD_CTRL
`define SHA512_REG_SHA512_VAULT_RD_CTRL                                                             (32'h600)
`define SHA512_REG_SHA512_VAULT_RD_CTRL_READ_EN_LOW                                                 (0)
`define SHA512_REG_SHA512_VAULT_RD_CTRL_READ_EN_MASK                                                (32'h1)
`define SHA512_REG_SHA512_VAULT_RD_CTRL_READ_ENTRY_LOW                                              (1)
`define SHA512_REG_SHA512_VAULT_RD_CTRL_READ_ENTRY_MASK                                             (32'h3e)
`define SHA512_REG_SHA512_VAULT_RD_CTRL_PCR_HASH_EXTEND_LOW                                         (6)
`define SHA512_REG_SHA512_VAULT_RD_CTRL_PCR_HASH_EXTEND_MASK                                        (32'h40)
`define SHA512_REG_SHA512_VAULT_RD_CTRL_RSVD_LOW                                                    (7)
`define SHA512_REG_SHA512_VAULT_RD_CTRL_RSVD_MASK                                                   (32'hffffff80)
`endif
`ifndef SHA512_REG_SHA512_VAULT_RD_STATUS
`define SHA512_REG_SHA512_VAULT_RD_STATUS                                                           (32'h604)
`define SHA512_REG_SHA512_VAULT_RD_STATUS_READY_LOW                                                 (0)
`define SHA512_REG_SHA512_VAULT_RD_STATUS_READY_MASK                                                (32'h1)
`define SHA512_REG_SHA512_VAULT_RD_STATUS_VALID_LOW                                                 (1)
`define SHA512_REG_SHA512_VAULT_RD_STATUS_VALID_MASK                                                (32'h2)
`define SHA512_REG_SHA512_VAULT_RD_STATUS_ERROR_LOW                                                 (2)
`define SHA512_REG_SHA512_VAULT_RD_STATUS_ERROR_MASK                                                (32'h3fc)
`endif
`ifndef SHA512_REG_SHA512_KV_WR_CTRL
`define SHA512_REG_SHA512_KV_WR_CTRL                                                                (32'h608)
`define SHA512_REG_SHA512_KV_WR_CTRL_WRITE_EN_LOW                                                   (0)
`define SHA512_REG_SHA512_KV_WR_CTRL_WRITE_EN_MASK                                                  (32'h1)
`define SHA512_REG_SHA512_KV_WR_CTRL_WRITE_ENTRY_LOW                                                (1)
`define SHA512_REG_SHA512_KV_WR_CTRL_WRITE_ENTRY_MASK                                               (32'h3e)
`define SHA512_REG_SHA512_KV_WR_CTRL_HMAC_KEY_DEST_VALID_LOW                                        (6)
`define SHA512_REG_SHA512_KV_WR_CTRL_HMAC_KEY_DEST_VALID_MASK                                       (32'h40)
`define SHA512_REG_SHA512_KV_WR_CTRL_HMAC_BLOCK_DEST_VALID_LOW                                      (7)
`define SHA512_REG_SHA512_KV_WR_CTRL_HMAC_BLOCK_DEST_VALID_MASK                                     (32'h80)
`define SHA512_REG_SHA512_KV_WR_CTRL_MLDSA_SEED_DEST_VALID_LOW                                      (8)
`define SHA512_REG_SHA512_KV_WR_CTRL_MLDSA_SEED_DEST_VALID_MASK                                     (32'h100)
`define SHA512_REG_SHA512_KV_WR_CTRL_ECC_PKEY_DEST_VALID_LOW                                        (9)
`define SHA512_REG_SHA512_KV_WR_CTRL_ECC_PKEY_DEST_VALID_MASK                                       (32'h200)
`define SHA512_REG_SHA512_KV_WR_CTRL_ECC_SEED_DEST_VALID_LOW                                        (10)
`define SHA512_REG_SHA512_KV_WR_CTRL_ECC_SEED_DEST_VALID_MASK                                       (32'h400)
`define SHA512_REG_SHA512_KV_WR_CTRL_AES_KEY_DEST_VALID_LOW                                         (11)
`define SHA512_REG_SHA512_KV_WR_CTRL_AES_KEY_DEST_VALID_MASK                                        (32'h800)
`define SHA512_REG_SHA512_KV_WR_CTRL_MLKEM_SEED_DEST_VALID_LOW                                      (12)
`define SHA512_REG_SHA512_KV_WR_CTRL_MLKEM_SEED_DEST_VALID_MASK                                     (32'h1000)
`define SHA512_REG_SHA512_KV_WR_CTRL_MLKEM_MSG_DEST_VALID_LOW                                       (13)
`define SHA512_REG_SHA512_KV_WR_CTRL_MLKEM_MSG_DEST_VALID_MASK                                      (32'h2000)
`define SHA512_REG_SHA512_KV_WR_CTRL_DMA_DATA_DEST_VALID_LOW                                        (14)
`define SHA512_REG_SHA512_KV_WR_CTRL_DMA_DATA_DEST_VALID_MASK                                       (32'h4000)
`define SHA512_REG_SHA512_KV_WR_CTRL_RSVD_LOW                                                       (15)
`define SHA512_REG_SHA512_KV_WR_CTRL_RSVD_MASK                                                      (32'hffff8000)
`endif
`ifndef SHA512_REG_SHA512_KV_WR_STATUS
`define SHA512_REG_SHA512_KV_WR_STATUS                                                              (32'h60c)
`define SHA512_REG_SHA512_KV_WR_STATUS_READY_LOW                                                    (0)
`define SHA512_REG_SHA512_KV_WR_STATUS_READY_MASK                                                   (32'h1)
`define SHA512_REG_SHA512_KV_WR_STATUS_VALID_LOW                                                    (1)
`define SHA512_REG_SHA512_KV_WR_STATUS_VALID_MASK                                                   (32'h2)
`define SHA512_REG_SHA512_KV_WR_STATUS_ERROR_LOW                                                    (2)
`define SHA512_REG_SHA512_KV_WR_STATUS_ERROR_MASK                                                   (32'h3fc)
`endif
`ifndef SHA512_REG_SHA512_GEN_PCR_HASH_NONCE_0
`define SHA512_REG_SHA512_GEN_PCR_HASH_NONCE_0                                                      (32'h610)
`endif
`ifndef SHA512_REG_SHA512_GEN_PCR_HASH_NONCE_1
`define SHA512_REG_SHA512_GEN_PCR_HASH_NONCE_1                                                      (32'h614)
`endif
`ifndef SHA512_REG_SHA512_GEN_PCR_HASH_NONCE_2
`define SHA512_REG_SHA512_GEN_PCR_HASH_NONCE_2                                                      (32'h618)
`endif
`ifndef SHA512_REG_SHA512_GEN_PCR_HASH_NONCE_3
`define SHA512_REG_SHA512_GEN_PCR_HASH_NONCE_3                                                      (32'h61c)
`endif
`ifndef SHA512_REG_SHA512_GEN_PCR_HASH_NONCE_4
`define SHA512_REG_SHA512_GEN_PCR_HASH_NONCE_4                                                      (32'h620)
`endif
`ifndef SHA512_REG_SHA512_GEN_PCR_HASH_NONCE_5
`define SHA512_REG_SHA512_GEN_PCR_HASH_NONCE_5                                                      (32'h624)
`endif
`ifndef SHA512_REG_SHA512_GEN_PCR_HASH_NONCE_6
`define SHA512_REG_SHA512_GEN_PCR_HASH_NONCE_6                                                      (32'h628)
`endif
`ifndef SHA512_REG_SHA512_GEN_PCR_HASH_NONCE_7
`define SHA512_REG_SHA512_GEN_PCR_HASH_NONCE_7                                                      (32'h62c)
`endif
`ifndef SHA512_REG_SHA512_GEN_PCR_HASH_CTRL
`define SHA512_REG_SHA512_GEN_PCR_HASH_CTRL                                                         (32'h630)
`define SHA512_REG_SHA512_GEN_PCR_HASH_CTRL_START_LOW                                               (0)
`define SHA512_REG_SHA512_GEN_PCR_HASH_CTRL_START_MASK                                              (32'h1)
`endif
`ifndef SHA512_REG_SHA512_GEN_PCR_HASH_STATUS
`define SHA512_REG_SHA512_GEN_PCR_HASH_STATUS                                                       (32'h634)
`define SHA512_REG_SHA512_GEN_PCR_HASH_STATUS_READY_LOW                                             (0)
`define SHA512_REG_SHA512_GEN_PCR_HASH_STATUS_READY_MASK                                            (32'h1)
`define SHA512_REG_SHA512_GEN_PCR_HASH_STATUS_VALID_LOW                                             (1)
`define SHA512_REG_SHA512_GEN_PCR_HASH_STATUS_VALID_MASK                                            (32'h2)
`endif
`ifndef SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_0
`define SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_0                                                     (32'h638)
`endif
`ifndef SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_1
`define SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_1                                                     (32'h63c)
`endif
`ifndef SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_2
`define SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_2                                                     (32'h640)
`endif
`ifndef SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_3
`define SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_3                                                     (32'h644)
`endif
`ifndef SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_4
`define SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_4                                                     (32'h648)
`endif
`ifndef SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_5
`define SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_5                                                     (32'h64c)
`endif
`ifndef SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_6
`define SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_6                                                     (32'h650)
`endif
`ifndef SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_7
`define SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_7                                                     (32'h654)
`endif
`ifndef SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_8
`define SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_8                                                     (32'h658)
`endif
`ifndef SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_9
`define SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_9                                                     (32'h65c)
`endif
`ifndef SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_10
`define SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_10                                                    (32'h660)
`endif
`ifndef SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_11
`define SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_11                                                    (32'h664)
`endif
`ifndef SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_12
`define SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_12                                                    (32'h668)
`endif
`ifndef SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_13
`define SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_13                                                    (32'h66c)
`endif
`ifndef SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_14
`define SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_14                                                    (32'h670)
`endif
`ifndef SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_15
`define SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_15                                                    (32'h674)
`endif
`ifndef SHA512_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R
`define SHA512_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R                                                   (32'h800)
`define SHA512_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_LOW                                      (0)
`define SHA512_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_MASK                                     (32'h1)
`define SHA512_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_LOW                                      (1)
`define SHA512_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_MASK                                     (32'h2)
`endif
`ifndef SHA512_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R
`define SHA512_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R                                                    (32'h804)
`define SHA512_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR0_EN_LOW                                      (0)
`define SHA512_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR0_EN_MASK                                     (32'h1)
`define SHA512_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR1_EN_LOW                                      (1)
`define SHA512_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR1_EN_MASK                                     (32'h2)
`define SHA512_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR2_EN_LOW                                      (2)
`define SHA512_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR2_EN_MASK                                     (32'h4)
`define SHA512_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR3_EN_LOW                                      (3)
`define SHA512_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR3_EN_MASK                                     (32'h8)
`endif
`ifndef SHA512_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R
`define SHA512_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R                                                    (32'h808)
`define SHA512_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_CMD_DONE_EN_LOW                              (0)
`define SHA512_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_CMD_DONE_EN_MASK                             (32'h1)
`endif
`ifndef SHA512_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R
`define SHA512_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R                                                (32'h80c)
`define SHA512_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS_LOW                                    (0)
`define SHA512_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS_MASK                                   (32'h1)
`endif
`ifndef SHA512_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R
`define SHA512_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R                                                (32'h810)
`define SHA512_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS_LOW                                    (0)
`define SHA512_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS_MASK                                   (32'h1)
`endif
`ifndef SHA512_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R
`define SHA512_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R                                              (32'h814)
`define SHA512_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR0_STS_LOW                               (0)
`define SHA512_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR0_STS_MASK                              (32'h1)
`define SHA512_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR1_STS_LOW                               (1)
`define SHA512_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR1_STS_MASK                              (32'h2)
`define SHA512_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR2_STS_LOW                               (2)
`define SHA512_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR2_STS_MASK                              (32'h4)
`define SHA512_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR3_STS_LOW                               (3)
`define SHA512_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR3_STS_MASK                              (32'h8)
`endif
`ifndef SHA512_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R
`define SHA512_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R                                              (32'h818)
`define SHA512_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_LOW                       (0)
`define SHA512_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK                      (32'h1)
`endif
`ifndef SHA512_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R
`define SHA512_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R                                                  (32'h81c)
`define SHA512_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR0_TRIG_LOW                                  (0)
`define SHA512_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR0_TRIG_MASK                                 (32'h1)
`define SHA512_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR1_TRIG_LOW                                  (1)
`define SHA512_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR1_TRIG_MASK                                 (32'h2)
`define SHA512_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR2_TRIG_LOW                                  (2)
`define SHA512_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR2_TRIG_MASK                                 (32'h4)
`define SHA512_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR3_TRIG_LOW                                  (3)
`define SHA512_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR3_TRIG_MASK                                 (32'h8)
`endif
`ifndef SHA512_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R
`define SHA512_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R                                                  (32'h820)
`define SHA512_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_DONE_TRIG_LOW                          (0)
`define SHA512_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_DONE_TRIG_MASK                         (32'h1)
`endif
`ifndef SHA512_REG_INTR_BLOCK_RF_ERROR0_INTR_COUNT_R
`define SHA512_REG_INTR_BLOCK_RF_ERROR0_INTR_COUNT_R                                                (32'h900)
`endif
`ifndef SHA512_REG_INTR_BLOCK_RF_ERROR1_INTR_COUNT_R
`define SHA512_REG_INTR_BLOCK_RF_ERROR1_INTR_COUNT_R                                                (32'h904)
`endif
`ifndef SHA512_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_R
`define SHA512_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_R                                                (32'h908)
`endif
`ifndef SHA512_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_R
`define SHA512_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_R                                                (32'h90c)
`endif
`ifndef SHA512_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R
`define SHA512_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R                                        (32'h980)
`endif
`ifndef SHA512_REG_INTR_BLOCK_RF_ERROR0_INTR_COUNT_INCR_R
`define SHA512_REG_INTR_BLOCK_RF_ERROR0_INTR_COUNT_INCR_R                                           (32'ha00)
`define SHA512_REG_INTR_BLOCK_RF_ERROR0_INTR_COUNT_INCR_R_PULSE_LOW                                 (0)
`define SHA512_REG_INTR_BLOCK_RF_ERROR0_INTR_COUNT_INCR_R_PULSE_MASK                                (32'h1)
`endif
`ifndef SHA512_REG_INTR_BLOCK_RF_ERROR1_INTR_COUNT_INCR_R
`define SHA512_REG_INTR_BLOCK_RF_ERROR1_INTR_COUNT_INCR_R                                           (32'ha04)
`define SHA512_REG_INTR_BLOCK_RF_ERROR1_INTR_COUNT_INCR_R_PULSE_LOW                                 (0)
`define SHA512_REG_INTR_BLOCK_RF_ERROR1_INTR_COUNT_INCR_R_PULSE_MASK                                (32'h1)
`endif
`ifndef SHA512_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R
`define SHA512_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R                                           (32'ha08)
`define SHA512_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R_PULSE_LOW                                 (0)
`define SHA512_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R_PULSE_MASK                                (32'h1)
`endif
`ifndef SHA512_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R
`define SHA512_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R                                           (32'ha0c)
`define SHA512_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R_PULSE_LOW                                 (0)
`define SHA512_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R_PULSE_MASK                                (32'h1)
`endif
`ifndef SHA512_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R
`define SHA512_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R                                   (32'ha10)
`define SHA512_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R_PULSE_LOW                         (0)
`define SHA512_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R_PULSE_MASK                        (32'h1)
`endif
`ifndef SHA256_REG_SHA256_NAME_0
`define SHA256_REG_SHA256_NAME_0                                                                    (32'h0)
`endif
`ifndef SHA256_REG_SHA256_NAME_1
`define SHA256_REG_SHA256_NAME_1                                                                    (32'h4)
`endif
`ifndef SHA256_REG_SHA256_VERSION_0
`define SHA256_REG_SHA256_VERSION_0                                                                 (32'h8)
`endif
`ifndef SHA256_REG_SHA256_VERSION_1
`define SHA256_REG_SHA256_VERSION_1                                                                 (32'hc)
`endif
`ifndef SHA256_REG_SHA256_CTRL
`define SHA256_REG_SHA256_CTRL                                                                      (32'h10)
`define SHA256_REG_SHA256_CTRL_INIT_LOW                                                             (0)
`define SHA256_REG_SHA256_CTRL_INIT_MASK                                                            (32'h1)
`define SHA256_REG_SHA256_CTRL_NEXT_LOW                                                             (1)
`define SHA256_REG_SHA256_CTRL_NEXT_MASK                                                            (32'h2)
`define SHA256_REG_SHA256_CTRL_MODE_LOW                                                             (2)
`define SHA256_REG_SHA256_CTRL_MODE_MASK                                                            (32'h4)
`define SHA256_REG_SHA256_CTRL_ZEROIZE_LOW                                                          (3)
`define SHA256_REG_SHA256_CTRL_ZEROIZE_MASK                                                         (32'h8)
`define SHA256_REG_SHA256_CTRL_WNTZ_MODE_LOW                                                        (4)
`define SHA256_REG_SHA256_CTRL_WNTZ_MODE_MASK                                                       (32'h10)
`define SHA256_REG_SHA256_CTRL_WNTZ_W_LOW                                                           (5)
`define SHA256_REG_SHA256_CTRL_WNTZ_W_MASK                                                          (32'h1e0)
`define SHA256_REG_SHA256_CTRL_WNTZ_N_MODE_LOW                                                      (9)
`define SHA256_REG_SHA256_CTRL_WNTZ_N_MODE_MASK                                                     (32'h200)
`endif
`ifndef SHA256_REG_SHA256_STATUS
`define SHA256_REG_SHA256_STATUS                                                                    (32'h18)
`define SHA256_REG_SHA256_STATUS_READY_LOW                                                          (0)
`define SHA256_REG_SHA256_STATUS_READY_MASK                                                         (32'h1)
`define SHA256_REG_SHA256_STATUS_VALID_LOW                                                          (1)
`define SHA256_REG_SHA256_STATUS_VALID_MASK                                                         (32'h2)
`define SHA256_REG_SHA256_STATUS_WNTZ_BUSY_LOW                                                      (2)
`define SHA256_REG_SHA256_STATUS_WNTZ_BUSY_MASK                                                     (32'h4)
`endif
`ifndef SHA256_REG_SHA256_BLOCK_0
`define SHA256_REG_SHA256_BLOCK_0                                                                   (32'h80)
`endif
`ifndef SHA256_REG_SHA256_BLOCK_1
`define SHA256_REG_SHA256_BLOCK_1                                                                   (32'h84)
`endif
`ifndef SHA256_REG_SHA256_BLOCK_2
`define SHA256_REG_SHA256_BLOCK_2                                                                   (32'h88)
`endif
`ifndef SHA256_REG_SHA256_BLOCK_3
`define SHA256_REG_SHA256_BLOCK_3                                                                   (32'h8c)
`endif
`ifndef SHA256_REG_SHA256_BLOCK_4
`define SHA256_REG_SHA256_BLOCK_4                                                                   (32'h90)
`endif
`ifndef SHA256_REG_SHA256_BLOCK_5
`define SHA256_REG_SHA256_BLOCK_5                                                                   (32'h94)
`endif
`ifndef SHA256_REG_SHA256_BLOCK_6
`define SHA256_REG_SHA256_BLOCK_6                                                                   (32'h98)
`endif
`ifndef SHA256_REG_SHA256_BLOCK_7
`define SHA256_REG_SHA256_BLOCK_7                                                                   (32'h9c)
`endif
`ifndef SHA256_REG_SHA256_BLOCK_8
`define SHA256_REG_SHA256_BLOCK_8                                                                   (32'ha0)
`endif
`ifndef SHA256_REG_SHA256_BLOCK_9
`define SHA256_REG_SHA256_BLOCK_9                                                                   (32'ha4)
`endif
`ifndef SHA256_REG_SHA256_BLOCK_10
`define SHA256_REG_SHA256_BLOCK_10                                                                  (32'ha8)
`endif
`ifndef SHA256_REG_SHA256_BLOCK_11
`define SHA256_REG_SHA256_BLOCK_11                                                                  (32'hac)
`endif
`ifndef SHA256_REG_SHA256_BLOCK_12
`define SHA256_REG_SHA256_BLOCK_12                                                                  (32'hb0)
`endif
`ifndef SHA256_REG_SHA256_BLOCK_13
`define SHA256_REG_SHA256_BLOCK_13                                                                  (32'hb4)
`endif
`ifndef SHA256_REG_SHA256_BLOCK_14
`define SHA256_REG_SHA256_BLOCK_14                                                                  (32'hb8)
`endif
`ifndef SHA256_REG_SHA256_BLOCK_15
`define SHA256_REG_SHA256_BLOCK_15                                                                  (32'hbc)
`endif
`ifndef SHA256_REG_SHA256_DIGEST_0
`define SHA256_REG_SHA256_DIGEST_0                                                                  (32'h100)
`endif
`ifndef SHA256_REG_SHA256_DIGEST_1
`define SHA256_REG_SHA256_DIGEST_1                                                                  (32'h104)
`endif
`ifndef SHA256_REG_SHA256_DIGEST_2
`define SHA256_REG_SHA256_DIGEST_2                                                                  (32'h108)
`endif
`ifndef SHA256_REG_SHA256_DIGEST_3
`define SHA256_REG_SHA256_DIGEST_3                                                                  (32'h10c)
`endif
`ifndef SHA256_REG_SHA256_DIGEST_4
`define SHA256_REG_SHA256_DIGEST_4                                                                  (32'h110)
`endif
`ifndef SHA256_REG_SHA256_DIGEST_5
`define SHA256_REG_SHA256_DIGEST_5                                                                  (32'h114)
`endif
`ifndef SHA256_REG_SHA256_DIGEST_6
`define SHA256_REG_SHA256_DIGEST_6                                                                  (32'h118)
`endif
`ifndef SHA256_REG_SHA256_DIGEST_7
`define SHA256_REG_SHA256_DIGEST_7                                                                  (32'h11c)
`endif
`ifndef SHA256_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R
`define SHA256_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R                                                   (32'h800)
`define SHA256_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_LOW                                      (0)
`define SHA256_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_MASK                                     (32'h1)
`define SHA256_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_LOW                                      (1)
`define SHA256_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_MASK                                     (32'h2)
`endif
`ifndef SHA256_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R
`define SHA256_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R                                                    (32'h804)
`define SHA256_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR0_EN_LOW                                      (0)
`define SHA256_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR0_EN_MASK                                     (32'h1)
`define SHA256_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR1_EN_LOW                                      (1)
`define SHA256_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR1_EN_MASK                                     (32'h2)
`define SHA256_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR2_EN_LOW                                      (2)
`define SHA256_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR2_EN_MASK                                     (32'h4)
`define SHA256_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR3_EN_LOW                                      (3)
`define SHA256_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR3_EN_MASK                                     (32'h8)
`endif
`ifndef SHA256_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R
`define SHA256_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R                                                    (32'h808)
`define SHA256_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_CMD_DONE_EN_LOW                              (0)
`define SHA256_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_CMD_DONE_EN_MASK                             (32'h1)
`endif
`ifndef SHA256_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R
`define SHA256_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R                                                (32'h80c)
`define SHA256_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS_LOW                                    (0)
`define SHA256_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS_MASK                                   (32'h1)
`endif
`ifndef SHA256_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R
`define SHA256_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R                                                (32'h810)
`define SHA256_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS_LOW                                    (0)
`define SHA256_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS_MASK                                   (32'h1)
`endif
`ifndef SHA256_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R
`define SHA256_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R                                              (32'h814)
`define SHA256_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR0_STS_LOW                               (0)
`define SHA256_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR0_STS_MASK                              (32'h1)
`define SHA256_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR1_STS_LOW                               (1)
`define SHA256_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR1_STS_MASK                              (32'h2)
`define SHA256_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR2_STS_LOW                               (2)
`define SHA256_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR2_STS_MASK                              (32'h4)
`define SHA256_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR3_STS_LOW                               (3)
`define SHA256_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR3_STS_MASK                              (32'h8)
`endif
`ifndef SHA256_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R
`define SHA256_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R                                              (32'h818)
`define SHA256_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_LOW                       (0)
`define SHA256_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK                      (32'h1)
`endif
`ifndef SHA256_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R
`define SHA256_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R                                                  (32'h81c)
`define SHA256_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR0_TRIG_LOW                                  (0)
`define SHA256_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR0_TRIG_MASK                                 (32'h1)
`define SHA256_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR1_TRIG_LOW                                  (1)
`define SHA256_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR1_TRIG_MASK                                 (32'h2)
`define SHA256_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR2_TRIG_LOW                                  (2)
`define SHA256_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR2_TRIG_MASK                                 (32'h4)
`define SHA256_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR3_TRIG_LOW                                  (3)
`define SHA256_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR3_TRIG_MASK                                 (32'h8)
`endif
`ifndef SHA256_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R
`define SHA256_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R                                                  (32'h820)
`define SHA256_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_DONE_TRIG_LOW                          (0)
`define SHA256_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_DONE_TRIG_MASK                         (32'h1)
`endif
`ifndef SHA256_REG_INTR_BLOCK_RF_ERROR0_INTR_COUNT_R
`define SHA256_REG_INTR_BLOCK_RF_ERROR0_INTR_COUNT_R                                                (32'h900)
`endif
`ifndef SHA256_REG_INTR_BLOCK_RF_ERROR1_INTR_COUNT_R
`define SHA256_REG_INTR_BLOCK_RF_ERROR1_INTR_COUNT_R                                                (32'h904)
`endif
`ifndef SHA256_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_R
`define SHA256_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_R                                                (32'h908)
`endif
`ifndef SHA256_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_R
`define SHA256_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_R                                                (32'h90c)
`endif
`ifndef SHA256_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R
`define SHA256_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R                                        (32'h980)
`endif
`ifndef SHA256_REG_INTR_BLOCK_RF_ERROR0_INTR_COUNT_INCR_R
`define SHA256_REG_INTR_BLOCK_RF_ERROR0_INTR_COUNT_INCR_R                                           (32'ha00)
`define SHA256_REG_INTR_BLOCK_RF_ERROR0_INTR_COUNT_INCR_R_PULSE_LOW                                 (0)
`define SHA256_REG_INTR_BLOCK_RF_ERROR0_INTR_COUNT_INCR_R_PULSE_MASK                                (32'h1)
`endif
`ifndef SHA256_REG_INTR_BLOCK_RF_ERROR1_INTR_COUNT_INCR_R
`define SHA256_REG_INTR_BLOCK_RF_ERROR1_INTR_COUNT_INCR_R                                           (32'ha04)
`define SHA256_REG_INTR_BLOCK_RF_ERROR1_INTR_COUNT_INCR_R_PULSE_LOW                                 (0)
`define SHA256_REG_INTR_BLOCK_RF_ERROR1_INTR_COUNT_INCR_R_PULSE_MASK                                (32'h1)
`endif
`ifndef SHA256_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R
`define SHA256_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R                                           (32'ha08)
`define SHA256_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R_PULSE_LOW                                 (0)
`define SHA256_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R_PULSE_MASK                                (32'h1)
`endif
`ifndef SHA256_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R
`define SHA256_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R                                           (32'ha0c)
`define SHA256_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R_PULSE_LOW                                 (0)
`define SHA256_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R_PULSE_MASK                                (32'h1)
`endif
`ifndef SHA256_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R
`define SHA256_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R                                   (32'ha10)
`define SHA256_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R_PULSE_LOW                         (0)
`define SHA256_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R_PULSE_MASK                        (32'h1)
`endif
`ifndef ABR_REG_MLDSA_NAME_0
`define ABR_REG_MLDSA_NAME_0                                                                        (32'h0)
`endif
`ifndef ABR_REG_MLDSA_NAME_1
`define ABR_REG_MLDSA_NAME_1                                                                        (32'h4)
`endif
`ifndef ABR_REG_MLDSA_VERSION_0
`define ABR_REG_MLDSA_VERSION_0                                                                     (32'h8)
`endif
`ifndef ABR_REG_MLDSA_VERSION_1
`define ABR_REG_MLDSA_VERSION_1                                                                     (32'hc)
`endif
`ifndef ABR_REG_MLDSA_CTRL
`define ABR_REG_MLDSA_CTRL                                                                          (32'h10)
`define ABR_REG_MLDSA_CTRL_CTRL_LOW                                                                 (0)
`define ABR_REG_MLDSA_CTRL_CTRL_MASK                                                                (32'h7)
`define ABR_REG_MLDSA_CTRL_ZEROIZE_LOW                                                              (3)
`define ABR_REG_MLDSA_CTRL_ZEROIZE_MASK                                                             (32'h8)
`define ABR_REG_MLDSA_CTRL_PCR_SIGN_LOW                                                             (4)
`define ABR_REG_MLDSA_CTRL_PCR_SIGN_MASK                                                            (32'h10)
`define ABR_REG_MLDSA_CTRL_EXTERNAL_MU_LOW                                                          (5)
`define ABR_REG_MLDSA_CTRL_EXTERNAL_MU_MASK                                                         (32'h20)
`define ABR_REG_MLDSA_CTRL_STREAM_MSG_LOW                                                           (6)
`define ABR_REG_MLDSA_CTRL_STREAM_MSG_MASK                                                          (32'h40)
`endif
`ifndef ABR_REG_MLDSA_STATUS
`define ABR_REG_MLDSA_STATUS                                                                        (32'h14)
`define ABR_REG_MLDSA_STATUS_READY_LOW                                                              (0)
`define ABR_REG_MLDSA_STATUS_READY_MASK                                                             (32'h1)
`define ABR_REG_MLDSA_STATUS_VALID_LOW                                                              (1)
`define ABR_REG_MLDSA_STATUS_VALID_MASK                                                             (32'h2)
`define ABR_REG_MLDSA_STATUS_MSG_STREAM_READY_LOW                                                   (2)
`define ABR_REG_MLDSA_STATUS_MSG_STREAM_READY_MASK                                                  (32'h4)
`define ABR_REG_MLDSA_STATUS_ERROR_LOW                                                              (3)
`define ABR_REG_MLDSA_STATUS_ERROR_MASK                                                             (32'h8)
`endif
`ifndef ABR_REG_ABR_ENTROPY_0
`define ABR_REG_ABR_ENTROPY_0                                                                       (32'h18)
`endif
`ifndef ABR_REG_ABR_ENTROPY_1
`define ABR_REG_ABR_ENTROPY_1                                                                       (32'h1c)
`endif
`ifndef ABR_REG_ABR_ENTROPY_2
`define ABR_REG_ABR_ENTROPY_2                                                                       (32'h20)
`endif
`ifndef ABR_REG_ABR_ENTROPY_3
`define ABR_REG_ABR_ENTROPY_3                                                                       (32'h24)
`endif
`ifndef ABR_REG_ABR_ENTROPY_4
`define ABR_REG_ABR_ENTROPY_4                                                                       (32'h28)
`endif
`ifndef ABR_REG_ABR_ENTROPY_5
`define ABR_REG_ABR_ENTROPY_5                                                                       (32'h2c)
`endif
`ifndef ABR_REG_ABR_ENTROPY_6
`define ABR_REG_ABR_ENTROPY_6                                                                       (32'h30)
`endif
`ifndef ABR_REG_ABR_ENTROPY_7
`define ABR_REG_ABR_ENTROPY_7                                                                       (32'h34)
`endif
`ifndef ABR_REG_ABR_ENTROPY_8
`define ABR_REG_ABR_ENTROPY_8                                                                       (32'h38)
`endif
`ifndef ABR_REG_ABR_ENTROPY_9
`define ABR_REG_ABR_ENTROPY_9                                                                       (32'h3c)
`endif
`ifndef ABR_REG_ABR_ENTROPY_10
`define ABR_REG_ABR_ENTROPY_10                                                                      (32'h40)
`endif
`ifndef ABR_REG_ABR_ENTROPY_11
`define ABR_REG_ABR_ENTROPY_11                                                                      (32'h44)
`endif
`ifndef ABR_REG_ABR_ENTROPY_12
`define ABR_REG_ABR_ENTROPY_12                                                                      (32'h48)
`endif
`ifndef ABR_REG_ABR_ENTROPY_13
`define ABR_REG_ABR_ENTROPY_13                                                                      (32'h4c)
`endif
`ifndef ABR_REG_ABR_ENTROPY_14
`define ABR_REG_ABR_ENTROPY_14                                                                      (32'h50)
`endif
`ifndef ABR_REG_ABR_ENTROPY_15
`define ABR_REG_ABR_ENTROPY_15                                                                      (32'h54)
`endif
`ifndef ABR_REG_MLDSA_SEED_0
`define ABR_REG_MLDSA_SEED_0                                                                        (32'h58)
`endif
`ifndef ABR_REG_MLDSA_SEED_1
`define ABR_REG_MLDSA_SEED_1                                                                        (32'h5c)
`endif
`ifndef ABR_REG_MLDSA_SEED_2
`define ABR_REG_MLDSA_SEED_2                                                                        (32'h60)
`endif
`ifndef ABR_REG_MLDSA_SEED_3
`define ABR_REG_MLDSA_SEED_3                                                                        (32'h64)
`endif
`ifndef ABR_REG_MLDSA_SEED_4
`define ABR_REG_MLDSA_SEED_4                                                                        (32'h68)
`endif
`ifndef ABR_REG_MLDSA_SEED_5
`define ABR_REG_MLDSA_SEED_5                                                                        (32'h6c)
`endif
`ifndef ABR_REG_MLDSA_SEED_6
`define ABR_REG_MLDSA_SEED_6                                                                        (32'h70)
`endif
`ifndef ABR_REG_MLDSA_SEED_7
`define ABR_REG_MLDSA_SEED_7                                                                        (32'h74)
`endif
`ifndef ABR_REG_MLDSA_SIGN_RND_0
`define ABR_REG_MLDSA_SIGN_RND_0                                                                    (32'h78)
`endif
`ifndef ABR_REG_MLDSA_SIGN_RND_1
`define ABR_REG_MLDSA_SIGN_RND_1                                                                    (32'h7c)
`endif
`ifndef ABR_REG_MLDSA_SIGN_RND_2
`define ABR_REG_MLDSA_SIGN_RND_2                                                                    (32'h80)
`endif
`ifndef ABR_REG_MLDSA_SIGN_RND_3
`define ABR_REG_MLDSA_SIGN_RND_3                                                                    (32'h84)
`endif
`ifndef ABR_REG_MLDSA_SIGN_RND_4
`define ABR_REG_MLDSA_SIGN_RND_4                                                                    (32'h88)
`endif
`ifndef ABR_REG_MLDSA_SIGN_RND_5
`define ABR_REG_MLDSA_SIGN_RND_5                                                                    (32'h8c)
`endif
`ifndef ABR_REG_MLDSA_SIGN_RND_6
`define ABR_REG_MLDSA_SIGN_RND_6                                                                    (32'h90)
`endif
`ifndef ABR_REG_MLDSA_SIGN_RND_7
`define ABR_REG_MLDSA_SIGN_RND_7                                                                    (32'h94)
`endif
`ifndef ABR_REG_MLDSA_MSG_0
`define ABR_REG_MLDSA_MSG_0                                                                         (32'h98)
`endif
`ifndef ABR_REG_MLDSA_MSG_1
`define ABR_REG_MLDSA_MSG_1                                                                         (32'h9c)
`endif
`ifndef ABR_REG_MLDSA_MSG_2
`define ABR_REG_MLDSA_MSG_2                                                                         (32'ha0)
`endif
`ifndef ABR_REG_MLDSA_MSG_3
`define ABR_REG_MLDSA_MSG_3                                                                         (32'ha4)
`endif
`ifndef ABR_REG_MLDSA_MSG_4
`define ABR_REG_MLDSA_MSG_4                                                                         (32'ha8)
`endif
`ifndef ABR_REG_MLDSA_MSG_5
`define ABR_REG_MLDSA_MSG_5                                                                         (32'hac)
`endif
`ifndef ABR_REG_MLDSA_MSG_6
`define ABR_REG_MLDSA_MSG_6                                                                         (32'hb0)
`endif
`ifndef ABR_REG_MLDSA_MSG_7
`define ABR_REG_MLDSA_MSG_7                                                                         (32'hb4)
`endif
`ifndef ABR_REG_MLDSA_MSG_8
`define ABR_REG_MLDSA_MSG_8                                                                         (32'hb8)
`endif
`ifndef ABR_REG_MLDSA_MSG_9
`define ABR_REG_MLDSA_MSG_9                                                                         (32'hbc)
`endif
`ifndef ABR_REG_MLDSA_MSG_10
`define ABR_REG_MLDSA_MSG_10                                                                        (32'hc0)
`endif
`ifndef ABR_REG_MLDSA_MSG_11
`define ABR_REG_MLDSA_MSG_11                                                                        (32'hc4)
`endif
`ifndef ABR_REG_MLDSA_MSG_12
`define ABR_REG_MLDSA_MSG_12                                                                        (32'hc8)
`endif
`ifndef ABR_REG_MLDSA_MSG_13
`define ABR_REG_MLDSA_MSG_13                                                                        (32'hcc)
`endif
`ifndef ABR_REG_MLDSA_MSG_14
`define ABR_REG_MLDSA_MSG_14                                                                        (32'hd0)
`endif
`ifndef ABR_REG_MLDSA_MSG_15
`define ABR_REG_MLDSA_MSG_15                                                                        (32'hd4)
`endif
`ifndef ABR_REG_MLDSA_VERIFY_RES_0
`define ABR_REG_MLDSA_VERIFY_RES_0                                                                  (32'hd8)
`endif
`ifndef ABR_REG_MLDSA_VERIFY_RES_1
`define ABR_REG_MLDSA_VERIFY_RES_1                                                                  (32'hdc)
`endif
`ifndef ABR_REG_MLDSA_VERIFY_RES_2
`define ABR_REG_MLDSA_VERIFY_RES_2                                                                  (32'he0)
`endif
`ifndef ABR_REG_MLDSA_VERIFY_RES_3
`define ABR_REG_MLDSA_VERIFY_RES_3                                                                  (32'he4)
`endif
`ifndef ABR_REG_MLDSA_VERIFY_RES_4
`define ABR_REG_MLDSA_VERIFY_RES_4                                                                  (32'he8)
`endif
`ifndef ABR_REG_MLDSA_VERIFY_RES_5
`define ABR_REG_MLDSA_VERIFY_RES_5                                                                  (32'hec)
`endif
`ifndef ABR_REG_MLDSA_VERIFY_RES_6
`define ABR_REG_MLDSA_VERIFY_RES_6                                                                  (32'hf0)
`endif
`ifndef ABR_REG_MLDSA_VERIFY_RES_7
`define ABR_REG_MLDSA_VERIFY_RES_7                                                                  (32'hf4)
`endif
`ifndef ABR_REG_MLDSA_VERIFY_RES_8
`define ABR_REG_MLDSA_VERIFY_RES_8                                                                  (32'hf8)
`endif
`ifndef ABR_REG_MLDSA_VERIFY_RES_9
`define ABR_REG_MLDSA_VERIFY_RES_9                                                                  (32'hfc)
`endif
`ifndef ABR_REG_MLDSA_VERIFY_RES_10
`define ABR_REG_MLDSA_VERIFY_RES_10                                                                 (32'h100)
`endif
`ifndef ABR_REG_MLDSA_VERIFY_RES_11
`define ABR_REG_MLDSA_VERIFY_RES_11                                                                 (32'h104)
`endif
`ifndef ABR_REG_MLDSA_VERIFY_RES_12
`define ABR_REG_MLDSA_VERIFY_RES_12                                                                 (32'h108)
`endif
`ifndef ABR_REG_MLDSA_VERIFY_RES_13
`define ABR_REG_MLDSA_VERIFY_RES_13                                                                 (32'h10c)
`endif
`ifndef ABR_REG_MLDSA_VERIFY_RES_14
`define ABR_REG_MLDSA_VERIFY_RES_14                                                                 (32'h110)
`endif
`ifndef ABR_REG_MLDSA_VERIFY_RES_15
`define ABR_REG_MLDSA_VERIFY_RES_15                                                                 (32'h114)
`endif
`ifndef ABR_REG_MLDSA_EXTERNAL_MU_0
`define ABR_REG_MLDSA_EXTERNAL_MU_0                                                                 (32'h118)
`endif
`ifndef ABR_REG_MLDSA_EXTERNAL_MU_1
`define ABR_REG_MLDSA_EXTERNAL_MU_1                                                                 (32'h11c)
`endif
`ifndef ABR_REG_MLDSA_EXTERNAL_MU_2
`define ABR_REG_MLDSA_EXTERNAL_MU_2                                                                 (32'h120)
`endif
`ifndef ABR_REG_MLDSA_EXTERNAL_MU_3
`define ABR_REG_MLDSA_EXTERNAL_MU_3                                                                 (32'h124)
`endif
`ifndef ABR_REG_MLDSA_EXTERNAL_MU_4
`define ABR_REG_MLDSA_EXTERNAL_MU_4                                                                 (32'h128)
`endif
`ifndef ABR_REG_MLDSA_EXTERNAL_MU_5
`define ABR_REG_MLDSA_EXTERNAL_MU_5                                                                 (32'h12c)
`endif
`ifndef ABR_REG_MLDSA_EXTERNAL_MU_6
`define ABR_REG_MLDSA_EXTERNAL_MU_6                                                                 (32'h130)
`endif
`ifndef ABR_REG_MLDSA_EXTERNAL_MU_7
`define ABR_REG_MLDSA_EXTERNAL_MU_7                                                                 (32'h134)
`endif
`ifndef ABR_REG_MLDSA_EXTERNAL_MU_8
`define ABR_REG_MLDSA_EXTERNAL_MU_8                                                                 (32'h138)
`endif
`ifndef ABR_REG_MLDSA_EXTERNAL_MU_9
`define ABR_REG_MLDSA_EXTERNAL_MU_9                                                                 (32'h13c)
`endif
`ifndef ABR_REG_MLDSA_EXTERNAL_MU_10
`define ABR_REG_MLDSA_EXTERNAL_MU_10                                                                (32'h140)
`endif
`ifndef ABR_REG_MLDSA_EXTERNAL_MU_11
`define ABR_REG_MLDSA_EXTERNAL_MU_11                                                                (32'h144)
`endif
`ifndef ABR_REG_MLDSA_EXTERNAL_MU_12
`define ABR_REG_MLDSA_EXTERNAL_MU_12                                                                (32'h148)
`endif
`ifndef ABR_REG_MLDSA_EXTERNAL_MU_13
`define ABR_REG_MLDSA_EXTERNAL_MU_13                                                                (32'h14c)
`endif
`ifndef ABR_REG_MLDSA_EXTERNAL_MU_14
`define ABR_REG_MLDSA_EXTERNAL_MU_14                                                                (32'h150)
`endif
`ifndef ABR_REG_MLDSA_EXTERNAL_MU_15
`define ABR_REG_MLDSA_EXTERNAL_MU_15                                                                (32'h154)
`endif
`ifndef ABR_REG_MLDSA_MSG_STROBE
`define ABR_REG_MLDSA_MSG_STROBE                                                                    (32'h158)
`define ABR_REG_MLDSA_MSG_STROBE_STROBE_LOW                                                         (0)
`define ABR_REG_MLDSA_MSG_STROBE_STROBE_MASK                                                        (32'hf)
`endif
`ifndef ABR_REG_MLDSA_CTX_CONFIG
`define ABR_REG_MLDSA_CTX_CONFIG                                                                    (32'h15c)
`define ABR_REG_MLDSA_CTX_CONFIG_CTX_SIZE_LOW                                                       (0)
`define ABR_REG_MLDSA_CTX_CONFIG_CTX_SIZE_MASK                                                      (32'hff)
`endif
`ifndef ABR_REG_MLDSA_CTX_0
`define ABR_REG_MLDSA_CTX_0                                                                         (32'h160)
`endif
`ifndef ABR_REG_MLDSA_CTX_1
`define ABR_REG_MLDSA_CTX_1                                                                         (32'h164)
`endif
`ifndef ABR_REG_MLDSA_CTX_2
`define ABR_REG_MLDSA_CTX_2                                                                         (32'h168)
`endif
`ifndef ABR_REG_MLDSA_CTX_3
`define ABR_REG_MLDSA_CTX_3                                                                         (32'h16c)
`endif
`ifndef ABR_REG_MLDSA_CTX_4
`define ABR_REG_MLDSA_CTX_4                                                                         (32'h170)
`endif
`ifndef ABR_REG_MLDSA_CTX_5
`define ABR_REG_MLDSA_CTX_5                                                                         (32'h174)
`endif
`ifndef ABR_REG_MLDSA_CTX_6
`define ABR_REG_MLDSA_CTX_6                                                                         (32'h178)
`endif
`ifndef ABR_REG_MLDSA_CTX_7
`define ABR_REG_MLDSA_CTX_7                                                                         (32'h17c)
`endif
`ifndef ABR_REG_MLDSA_CTX_8
`define ABR_REG_MLDSA_CTX_8                                                                         (32'h180)
`endif
`ifndef ABR_REG_MLDSA_CTX_9
`define ABR_REG_MLDSA_CTX_9                                                                         (32'h184)
`endif
`ifndef ABR_REG_MLDSA_CTX_10
`define ABR_REG_MLDSA_CTX_10                                                                        (32'h188)
`endif
`ifndef ABR_REG_MLDSA_CTX_11
`define ABR_REG_MLDSA_CTX_11                                                                        (32'h18c)
`endif
`ifndef ABR_REG_MLDSA_CTX_12
`define ABR_REG_MLDSA_CTX_12                                                                        (32'h190)
`endif
`ifndef ABR_REG_MLDSA_CTX_13
`define ABR_REG_MLDSA_CTX_13                                                                        (32'h194)
`endif
`ifndef ABR_REG_MLDSA_CTX_14
`define ABR_REG_MLDSA_CTX_14                                                                        (32'h198)
`endif
`ifndef ABR_REG_MLDSA_CTX_15
`define ABR_REG_MLDSA_CTX_15                                                                        (32'h19c)
`endif
`ifndef ABR_REG_MLDSA_CTX_16
`define ABR_REG_MLDSA_CTX_16                                                                        (32'h1a0)
`endif
`ifndef ABR_REG_MLDSA_CTX_17
`define ABR_REG_MLDSA_CTX_17                                                                        (32'h1a4)
`endif
`ifndef ABR_REG_MLDSA_CTX_18
`define ABR_REG_MLDSA_CTX_18                                                                        (32'h1a8)
`endif
`ifndef ABR_REG_MLDSA_CTX_19
`define ABR_REG_MLDSA_CTX_19                                                                        (32'h1ac)
`endif
`ifndef ABR_REG_MLDSA_CTX_20
`define ABR_REG_MLDSA_CTX_20                                                                        (32'h1b0)
`endif
`ifndef ABR_REG_MLDSA_CTX_21
`define ABR_REG_MLDSA_CTX_21                                                                        (32'h1b4)
`endif
`ifndef ABR_REG_MLDSA_CTX_22
`define ABR_REG_MLDSA_CTX_22                                                                        (32'h1b8)
`endif
`ifndef ABR_REG_MLDSA_CTX_23
`define ABR_REG_MLDSA_CTX_23                                                                        (32'h1bc)
`endif
`ifndef ABR_REG_MLDSA_CTX_24
`define ABR_REG_MLDSA_CTX_24                                                                        (32'h1c0)
`endif
`ifndef ABR_REG_MLDSA_CTX_25
`define ABR_REG_MLDSA_CTX_25                                                                        (32'h1c4)
`endif
`ifndef ABR_REG_MLDSA_CTX_26
`define ABR_REG_MLDSA_CTX_26                                                                        (32'h1c8)
`endif
`ifndef ABR_REG_MLDSA_CTX_27
`define ABR_REG_MLDSA_CTX_27                                                                        (32'h1cc)
`endif
`ifndef ABR_REG_MLDSA_CTX_28
`define ABR_REG_MLDSA_CTX_28                                                                        (32'h1d0)
`endif
`ifndef ABR_REG_MLDSA_CTX_29
`define ABR_REG_MLDSA_CTX_29                                                                        (32'h1d4)
`endif
`ifndef ABR_REG_MLDSA_CTX_30
`define ABR_REG_MLDSA_CTX_30                                                                        (32'h1d8)
`endif
`ifndef ABR_REG_MLDSA_CTX_31
`define ABR_REG_MLDSA_CTX_31                                                                        (32'h1dc)
`endif
`ifndef ABR_REG_MLDSA_CTX_32
`define ABR_REG_MLDSA_CTX_32                                                                        (32'h1e0)
`endif
`ifndef ABR_REG_MLDSA_CTX_33
`define ABR_REG_MLDSA_CTX_33                                                                        (32'h1e4)
`endif
`ifndef ABR_REG_MLDSA_CTX_34
`define ABR_REG_MLDSA_CTX_34                                                                        (32'h1e8)
`endif
`ifndef ABR_REG_MLDSA_CTX_35
`define ABR_REG_MLDSA_CTX_35                                                                        (32'h1ec)
`endif
`ifndef ABR_REG_MLDSA_CTX_36
`define ABR_REG_MLDSA_CTX_36                                                                        (32'h1f0)
`endif
`ifndef ABR_REG_MLDSA_CTX_37
`define ABR_REG_MLDSA_CTX_37                                                                        (32'h1f4)
`endif
`ifndef ABR_REG_MLDSA_CTX_38
`define ABR_REG_MLDSA_CTX_38                                                                        (32'h1f8)
`endif
`ifndef ABR_REG_MLDSA_CTX_39
`define ABR_REG_MLDSA_CTX_39                                                                        (32'h1fc)
`endif
`ifndef ABR_REG_MLDSA_CTX_40
`define ABR_REG_MLDSA_CTX_40                                                                        (32'h200)
`endif
`ifndef ABR_REG_MLDSA_CTX_41
`define ABR_REG_MLDSA_CTX_41                                                                        (32'h204)
`endif
`ifndef ABR_REG_MLDSA_CTX_42
`define ABR_REG_MLDSA_CTX_42                                                                        (32'h208)
`endif
`ifndef ABR_REG_MLDSA_CTX_43
`define ABR_REG_MLDSA_CTX_43                                                                        (32'h20c)
`endif
`ifndef ABR_REG_MLDSA_CTX_44
`define ABR_REG_MLDSA_CTX_44                                                                        (32'h210)
`endif
`ifndef ABR_REG_MLDSA_CTX_45
`define ABR_REG_MLDSA_CTX_45                                                                        (32'h214)
`endif
`ifndef ABR_REG_MLDSA_CTX_46
`define ABR_REG_MLDSA_CTX_46                                                                        (32'h218)
`endif
`ifndef ABR_REG_MLDSA_CTX_47
`define ABR_REG_MLDSA_CTX_47                                                                        (32'h21c)
`endif
`ifndef ABR_REG_MLDSA_CTX_48
`define ABR_REG_MLDSA_CTX_48                                                                        (32'h220)
`endif
`ifndef ABR_REG_MLDSA_CTX_49
`define ABR_REG_MLDSA_CTX_49                                                                        (32'h224)
`endif
`ifndef ABR_REG_MLDSA_CTX_50
`define ABR_REG_MLDSA_CTX_50                                                                        (32'h228)
`endif
`ifndef ABR_REG_MLDSA_CTX_51
`define ABR_REG_MLDSA_CTX_51                                                                        (32'h22c)
`endif
`ifndef ABR_REG_MLDSA_CTX_52
`define ABR_REG_MLDSA_CTX_52                                                                        (32'h230)
`endif
`ifndef ABR_REG_MLDSA_CTX_53
`define ABR_REG_MLDSA_CTX_53                                                                        (32'h234)
`endif
`ifndef ABR_REG_MLDSA_CTX_54
`define ABR_REG_MLDSA_CTX_54                                                                        (32'h238)
`endif
`ifndef ABR_REG_MLDSA_CTX_55
`define ABR_REG_MLDSA_CTX_55                                                                        (32'h23c)
`endif
`ifndef ABR_REG_MLDSA_CTX_56
`define ABR_REG_MLDSA_CTX_56                                                                        (32'h240)
`endif
`ifndef ABR_REG_MLDSA_CTX_57
`define ABR_REG_MLDSA_CTX_57                                                                        (32'h244)
`endif
`ifndef ABR_REG_MLDSA_CTX_58
`define ABR_REG_MLDSA_CTX_58                                                                        (32'h248)
`endif
`ifndef ABR_REG_MLDSA_CTX_59
`define ABR_REG_MLDSA_CTX_59                                                                        (32'h24c)
`endif
`ifndef ABR_REG_MLDSA_CTX_60
`define ABR_REG_MLDSA_CTX_60                                                                        (32'h250)
`endif
`ifndef ABR_REG_MLDSA_CTX_61
`define ABR_REG_MLDSA_CTX_61                                                                        (32'h254)
`endif
`ifndef ABR_REG_MLDSA_CTX_62
`define ABR_REG_MLDSA_CTX_62                                                                        (32'h258)
`endif
`ifndef ABR_REG_MLDSA_CTX_63
`define ABR_REG_MLDSA_CTX_63                                                                        (32'h25c)
`endif
`ifndef ABR_REG_KV_MLDSA_SEED_RD_CTRL
`define ABR_REG_KV_MLDSA_SEED_RD_CTRL                                                               (32'h8000)
`define ABR_REG_KV_MLDSA_SEED_RD_CTRL_READ_EN_LOW                                                   (0)
`define ABR_REG_KV_MLDSA_SEED_RD_CTRL_READ_EN_MASK                                                  (32'h1)
`define ABR_REG_KV_MLDSA_SEED_RD_CTRL_READ_ENTRY_LOW                                                (1)
`define ABR_REG_KV_MLDSA_SEED_RD_CTRL_READ_ENTRY_MASK                                               (32'h3e)
`define ABR_REG_KV_MLDSA_SEED_RD_CTRL_PCR_HASH_EXTEND_LOW                                           (6)
`define ABR_REG_KV_MLDSA_SEED_RD_CTRL_PCR_HASH_EXTEND_MASK                                          (32'h40)
`define ABR_REG_KV_MLDSA_SEED_RD_CTRL_RSVD_LOW                                                      (7)
`define ABR_REG_KV_MLDSA_SEED_RD_CTRL_RSVD_MASK                                                     (32'hffffff80)
`endif
`ifndef ABR_REG_KV_MLDSA_SEED_RD_STATUS
`define ABR_REG_KV_MLDSA_SEED_RD_STATUS                                                             (32'h8004)
`define ABR_REG_KV_MLDSA_SEED_RD_STATUS_READY_LOW                                                   (0)
`define ABR_REG_KV_MLDSA_SEED_RD_STATUS_READY_MASK                                                  (32'h1)
`define ABR_REG_KV_MLDSA_SEED_RD_STATUS_VALID_LOW                                                   (1)
`define ABR_REG_KV_MLDSA_SEED_RD_STATUS_VALID_MASK                                                  (32'h2)
`define ABR_REG_KV_MLDSA_SEED_RD_STATUS_ERROR_LOW                                                   (2)
`define ABR_REG_KV_MLDSA_SEED_RD_STATUS_ERROR_MASK                                                  (32'h3fc)
`endif
`ifndef ABR_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R
`define ABR_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R                                                      (32'h8100)
`define ABR_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_LOW                                         (0)
`define ABR_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_MASK                                        (32'h1)
`define ABR_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_LOW                                         (1)
`define ABR_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_MASK                                        (32'h2)
`endif
`ifndef ABR_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R
`define ABR_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R                                                       (32'h8104)
`define ABR_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_INTERNAL_EN_LOW                                 (0)
`define ABR_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_INTERNAL_EN_MASK                                (32'h1)
`endif
`ifndef ABR_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R
`define ABR_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R                                                       (32'h8108)
`define ABR_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_CMD_DONE_EN_LOW                                 (0)
`define ABR_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_CMD_DONE_EN_MASK                                (32'h1)
`endif
`ifndef ABR_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R
`define ABR_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R                                                   (32'h810c)
`define ABR_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS_LOW                                       (0)
`define ABR_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS_MASK                                      (32'h1)
`endif
`ifndef ABR_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R
`define ABR_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R                                                   (32'h8110)
`define ABR_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS_LOW                                       (0)
`define ABR_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS_MASK                                      (32'h1)
`endif
`ifndef ABR_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R
`define ABR_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R                                                 (32'h8114)
`define ABR_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_INTERNAL_STS_LOW                          (0)
`define ABR_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_INTERNAL_STS_MASK                         (32'h1)
`endif
`ifndef ABR_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R
`define ABR_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R                                                 (32'h8118)
`define ABR_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_LOW                          (0)
`define ABR_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK                         (32'h1)
`endif
`ifndef ABR_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R
`define ABR_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R                                                     (32'h811c)
`define ABR_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_INTERNAL_TRIG_LOW                             (0)
`define ABR_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_INTERNAL_TRIG_MASK                            (32'h1)
`endif
`ifndef ABR_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R
`define ABR_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R                                                     (32'h8120)
`define ABR_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_DONE_TRIG_LOW                             (0)
`define ABR_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_DONE_TRIG_MASK                            (32'h1)
`endif
`ifndef ABR_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_R
`define ABR_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_R                                           (32'h8200)
`endif
`ifndef ABR_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R
`define ABR_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R                                           (32'h8280)
`endif
`ifndef ABR_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R
`define ABR_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R                                      (32'h8300)
`define ABR_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R_PULSE_LOW                            (0)
`define ABR_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R_PULSE_MASK                           (32'h1)
`endif
`ifndef ABR_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R
`define ABR_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R                                      (32'h8304)
`define ABR_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R_PULSE_LOW                            (0)
`define ABR_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R_PULSE_MASK                           (32'h1)
`endif
`ifndef ABR_REG_MLKEM_NAME_0
`define ABR_REG_MLKEM_NAME_0                                                                        (32'h9000)
`endif
`ifndef ABR_REG_MLKEM_NAME_1
`define ABR_REG_MLKEM_NAME_1                                                                        (32'h9004)
`endif
`ifndef ABR_REG_MLKEM_VERSION_0
`define ABR_REG_MLKEM_VERSION_0                                                                     (32'h9008)
`endif
`ifndef ABR_REG_MLKEM_VERSION_1
`define ABR_REG_MLKEM_VERSION_1                                                                     (32'h900c)
`endif
`ifndef ABR_REG_MLKEM_CTRL
`define ABR_REG_MLKEM_CTRL                                                                          (32'h9010)
`define ABR_REG_MLKEM_CTRL_CTRL_LOW                                                                 (0)
`define ABR_REG_MLKEM_CTRL_CTRL_MASK                                                                (32'h7)
`define ABR_REG_MLKEM_CTRL_ZEROIZE_LOW                                                              (3)
`define ABR_REG_MLKEM_CTRL_ZEROIZE_MASK                                                             (32'h8)
`endif
`ifndef ABR_REG_MLKEM_STATUS
`define ABR_REG_MLKEM_STATUS                                                                        (32'h9014)
`define ABR_REG_MLKEM_STATUS_READY_LOW                                                              (0)
`define ABR_REG_MLKEM_STATUS_READY_MASK                                                             (32'h1)
`define ABR_REG_MLKEM_STATUS_VALID_LOW                                                              (1)
`define ABR_REG_MLKEM_STATUS_VALID_MASK                                                             (32'h2)
`define ABR_REG_MLKEM_STATUS_ERROR_LOW                                                              (2)
`define ABR_REG_MLKEM_STATUS_ERROR_MASK                                                             (32'h4)
`endif
`ifndef ABR_REG_MLKEM_SEED_D_0
`define ABR_REG_MLKEM_SEED_D_0                                                                      (32'h9018)
`endif
`ifndef ABR_REG_MLKEM_SEED_D_1
`define ABR_REG_MLKEM_SEED_D_1                                                                      (32'h901c)
`endif
`ifndef ABR_REG_MLKEM_SEED_D_2
`define ABR_REG_MLKEM_SEED_D_2                                                                      (32'h9020)
`endif
`ifndef ABR_REG_MLKEM_SEED_D_3
`define ABR_REG_MLKEM_SEED_D_3                                                                      (32'h9024)
`endif
`ifndef ABR_REG_MLKEM_SEED_D_4
`define ABR_REG_MLKEM_SEED_D_4                                                                      (32'h9028)
`endif
`ifndef ABR_REG_MLKEM_SEED_D_5
`define ABR_REG_MLKEM_SEED_D_5                                                                      (32'h902c)
`endif
`ifndef ABR_REG_MLKEM_SEED_D_6
`define ABR_REG_MLKEM_SEED_D_6                                                                      (32'h9030)
`endif
`ifndef ABR_REG_MLKEM_SEED_D_7
`define ABR_REG_MLKEM_SEED_D_7                                                                      (32'h9034)
`endif
`ifndef ABR_REG_MLKEM_SEED_Z_0
`define ABR_REG_MLKEM_SEED_Z_0                                                                      (32'h9038)
`endif
`ifndef ABR_REG_MLKEM_SEED_Z_1
`define ABR_REG_MLKEM_SEED_Z_1                                                                      (32'h903c)
`endif
`ifndef ABR_REG_MLKEM_SEED_Z_2
`define ABR_REG_MLKEM_SEED_Z_2                                                                      (32'h9040)
`endif
`ifndef ABR_REG_MLKEM_SEED_Z_3
`define ABR_REG_MLKEM_SEED_Z_3                                                                      (32'h9044)
`endif
`ifndef ABR_REG_MLKEM_SEED_Z_4
`define ABR_REG_MLKEM_SEED_Z_4                                                                      (32'h9048)
`endif
`ifndef ABR_REG_MLKEM_SEED_Z_5
`define ABR_REG_MLKEM_SEED_Z_5                                                                      (32'h904c)
`endif
`ifndef ABR_REG_MLKEM_SEED_Z_6
`define ABR_REG_MLKEM_SEED_Z_6                                                                      (32'h9050)
`endif
`ifndef ABR_REG_MLKEM_SEED_Z_7
`define ABR_REG_MLKEM_SEED_Z_7                                                                      (32'h9054)
`endif
`ifndef ABR_REG_MLKEM_SHARED_KEY_0
`define ABR_REG_MLKEM_SHARED_KEY_0                                                                  (32'h9058)
`endif
`ifndef ABR_REG_MLKEM_SHARED_KEY_1
`define ABR_REG_MLKEM_SHARED_KEY_1                                                                  (32'h905c)
`endif
`ifndef ABR_REG_MLKEM_SHARED_KEY_2
`define ABR_REG_MLKEM_SHARED_KEY_2                                                                  (32'h9060)
`endif
`ifndef ABR_REG_MLKEM_SHARED_KEY_3
`define ABR_REG_MLKEM_SHARED_KEY_3                                                                  (32'h9064)
`endif
`ifndef ABR_REG_MLKEM_SHARED_KEY_4
`define ABR_REG_MLKEM_SHARED_KEY_4                                                                  (32'h9068)
`endif
`ifndef ABR_REG_MLKEM_SHARED_KEY_5
`define ABR_REG_MLKEM_SHARED_KEY_5                                                                  (32'h906c)
`endif
`ifndef ABR_REG_MLKEM_SHARED_KEY_6
`define ABR_REG_MLKEM_SHARED_KEY_6                                                                  (32'h9070)
`endif
`ifndef ABR_REG_MLKEM_SHARED_KEY_7
`define ABR_REG_MLKEM_SHARED_KEY_7                                                                  (32'h9074)
`endif
`ifndef ABR_REG_KV_MLKEM_SEED_RD_CTRL
`define ABR_REG_KV_MLKEM_SEED_RD_CTRL                                                               (32'hc000)
`define ABR_REG_KV_MLKEM_SEED_RD_CTRL_READ_EN_LOW                                                   (0)
`define ABR_REG_KV_MLKEM_SEED_RD_CTRL_READ_EN_MASK                                                  (32'h1)
`define ABR_REG_KV_MLKEM_SEED_RD_CTRL_READ_ENTRY_LOW                                                (1)
`define ABR_REG_KV_MLKEM_SEED_RD_CTRL_READ_ENTRY_MASK                                               (32'h3e)
`define ABR_REG_KV_MLKEM_SEED_RD_CTRL_PCR_HASH_EXTEND_LOW                                           (6)
`define ABR_REG_KV_MLKEM_SEED_RD_CTRL_PCR_HASH_EXTEND_MASK                                          (32'h40)
`define ABR_REG_KV_MLKEM_SEED_RD_CTRL_RSVD_LOW                                                      (7)
`define ABR_REG_KV_MLKEM_SEED_RD_CTRL_RSVD_MASK                                                     (32'hffffff80)
`endif
`ifndef ABR_REG_KV_MLKEM_SEED_RD_STATUS
`define ABR_REG_KV_MLKEM_SEED_RD_STATUS                                                             (32'hc004)
`define ABR_REG_KV_MLKEM_SEED_RD_STATUS_READY_LOW                                                   (0)
`define ABR_REG_KV_MLKEM_SEED_RD_STATUS_READY_MASK                                                  (32'h1)
`define ABR_REG_KV_MLKEM_SEED_RD_STATUS_VALID_LOW                                                   (1)
`define ABR_REG_KV_MLKEM_SEED_RD_STATUS_VALID_MASK                                                  (32'h2)
`define ABR_REG_KV_MLKEM_SEED_RD_STATUS_ERROR_LOW                                                   (2)
`define ABR_REG_KV_MLKEM_SEED_RD_STATUS_ERROR_MASK                                                  (32'h3fc)
`endif
`ifndef ABR_REG_KV_MLKEM_MSG_RD_CTRL
`define ABR_REG_KV_MLKEM_MSG_RD_CTRL                                                                (32'hc008)
`define ABR_REG_KV_MLKEM_MSG_RD_CTRL_READ_EN_LOW                                                    (0)
`define ABR_REG_KV_MLKEM_MSG_RD_CTRL_READ_EN_MASK                                                   (32'h1)
`define ABR_REG_KV_MLKEM_MSG_RD_CTRL_READ_ENTRY_LOW                                                 (1)
`define ABR_REG_KV_MLKEM_MSG_RD_CTRL_READ_ENTRY_MASK                                                (32'h3e)
`define ABR_REG_KV_MLKEM_MSG_RD_CTRL_PCR_HASH_EXTEND_LOW                                            (6)
`define ABR_REG_KV_MLKEM_MSG_RD_CTRL_PCR_HASH_EXTEND_MASK                                           (32'h40)
`define ABR_REG_KV_MLKEM_MSG_RD_CTRL_RSVD_LOW                                                       (7)
`define ABR_REG_KV_MLKEM_MSG_RD_CTRL_RSVD_MASK                                                      (32'hffffff80)
`endif
`ifndef ABR_REG_KV_MLKEM_MSG_RD_STATUS
`define ABR_REG_KV_MLKEM_MSG_RD_STATUS                                                              (32'hc00c)
`define ABR_REG_KV_MLKEM_MSG_RD_STATUS_READY_LOW                                                    (0)
`define ABR_REG_KV_MLKEM_MSG_RD_STATUS_READY_MASK                                                   (32'h1)
`define ABR_REG_KV_MLKEM_MSG_RD_STATUS_VALID_LOW                                                    (1)
`define ABR_REG_KV_MLKEM_MSG_RD_STATUS_VALID_MASK                                                   (32'h2)
`define ABR_REG_KV_MLKEM_MSG_RD_STATUS_ERROR_LOW                                                    (2)
`define ABR_REG_KV_MLKEM_MSG_RD_STATUS_ERROR_MASK                                                   (32'h3fc)
`endif
`ifndef ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL
`define ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL                                                          (32'hc010)
`define ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_WRITE_EN_LOW                                             (0)
`define ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_WRITE_EN_MASK                                            (32'h1)
`define ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_WRITE_ENTRY_LOW                                          (1)
`define ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_WRITE_ENTRY_MASK                                         (32'h3e)
`define ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_HMAC_KEY_DEST_VALID_LOW                                  (6)
`define ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_HMAC_KEY_DEST_VALID_MASK                                 (32'h40)
`define ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_HMAC_BLOCK_DEST_VALID_LOW                                (7)
`define ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_HMAC_BLOCK_DEST_VALID_MASK                               (32'h80)
`define ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_MLDSA_SEED_DEST_VALID_LOW                                (8)
`define ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_MLDSA_SEED_DEST_VALID_MASK                               (32'h100)
`define ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_ECC_PKEY_DEST_VALID_LOW                                  (9)
`define ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_ECC_PKEY_DEST_VALID_MASK                                 (32'h200)
`define ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_ECC_SEED_DEST_VALID_LOW                                  (10)
`define ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_ECC_SEED_DEST_VALID_MASK                                 (32'h400)
`define ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_AES_KEY_DEST_VALID_LOW                                   (11)
`define ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_AES_KEY_DEST_VALID_MASK                                  (32'h800)
`define ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_MLKEM_SEED_DEST_VALID_LOW                                (12)
`define ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_MLKEM_SEED_DEST_VALID_MASK                               (32'h1000)
`define ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_MLKEM_MSG_DEST_VALID_LOW                                 (13)
`define ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_MLKEM_MSG_DEST_VALID_MASK                                (32'h2000)
`define ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_DMA_DATA_DEST_VALID_LOW                                  (14)
`define ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_DMA_DATA_DEST_VALID_MASK                                 (32'h4000)
`define ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_RSVD_LOW                                                 (15)
`define ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_RSVD_MASK                                                (32'hffff8000)
`endif
`ifndef ABR_REG_KV_MLKEM_SHAREDKEY_WR_STATUS
`define ABR_REG_KV_MLKEM_SHAREDKEY_WR_STATUS                                                        (32'hc014)
`define ABR_REG_KV_MLKEM_SHAREDKEY_WR_STATUS_READY_LOW                                              (0)
`define ABR_REG_KV_MLKEM_SHAREDKEY_WR_STATUS_READY_MASK                                             (32'h1)
`define ABR_REG_KV_MLKEM_SHAREDKEY_WR_STATUS_VALID_LOW                                              (1)
`define ABR_REG_KV_MLKEM_SHAREDKEY_WR_STATUS_VALID_MASK                                             (32'h2)
`define ABR_REG_KV_MLKEM_SHAREDKEY_WR_STATUS_ERROR_LOW                                              (2)
`define ABR_REG_KV_MLKEM_SHAREDKEY_WR_STATUS_ERROR_MASK                                             (32'h3fc)
`endif
`ifndef KMAC_INTR_STATE
`define KMAC_INTR_STATE                                                                             (32'h0)
`define KMAC_INTR_STATE_KMAC_DONE_LOW                                                               (0)
`define KMAC_INTR_STATE_KMAC_DONE_MASK                                                              (32'h1)
`define KMAC_INTR_STATE_FIFO_EMPTY_LOW                                                              (1)
`define KMAC_INTR_STATE_FIFO_EMPTY_MASK                                                             (32'h2)
`define KMAC_INTR_STATE_KMAC_ERR_LOW                                                                (2)
`define KMAC_INTR_STATE_KMAC_ERR_MASK                                                               (32'h4)
`endif
`ifndef KMAC_INTR_ENABLE
`define KMAC_INTR_ENABLE                                                                            (32'h4)
`define KMAC_INTR_ENABLE_KMAC_DONE_LOW                                                              (0)
`define KMAC_INTR_ENABLE_KMAC_DONE_MASK                                                             (32'h1)
`define KMAC_INTR_ENABLE_FIFO_EMPTY_LOW                                                             (1)
`define KMAC_INTR_ENABLE_FIFO_EMPTY_MASK                                                            (32'h2)
`define KMAC_INTR_ENABLE_KMAC_ERR_LOW                                                               (2)
`define KMAC_INTR_ENABLE_KMAC_ERR_MASK                                                              (32'h4)
`endif
`ifndef KMAC_INTR_TEST
`define KMAC_INTR_TEST                                                                              (32'h8)
`define KMAC_INTR_TEST_KMAC_DONE_LOW                                                                (0)
`define KMAC_INTR_TEST_KMAC_DONE_MASK                                                               (32'h1)
`define KMAC_INTR_TEST_FIFO_EMPTY_LOW                                                               (1)
`define KMAC_INTR_TEST_FIFO_EMPTY_MASK                                                              (32'h2)
`define KMAC_INTR_TEST_KMAC_ERR_LOW                                                                 (2)
`define KMAC_INTR_TEST_KMAC_ERR_MASK                                                                (32'h4)
`endif
`ifndef KMAC_ALERT_TEST
`define KMAC_ALERT_TEST                                                                             (32'hc)
`define KMAC_ALERT_TEST_RECOV_OPERATION_ERR_LOW                                                     (0)
`define KMAC_ALERT_TEST_RECOV_OPERATION_ERR_MASK                                                    (32'h1)
`define KMAC_ALERT_TEST_FATAL_FAULT_ERR_LOW                                                         (1)
`define KMAC_ALERT_TEST_FATAL_FAULT_ERR_MASK                                                        (32'h2)
`endif
`ifndef KMAC_CFG_REGWEN
`define KMAC_CFG_REGWEN                                                                             (32'h10)
`define KMAC_CFG_REGWEN_EN_LOW                                                                      (0)
`define KMAC_CFG_REGWEN_EN_MASK                                                                     (32'h1)
`endif
`ifndef KMAC_CFG_SHADOWED
`define KMAC_CFG_SHADOWED                                                                           (32'h14)
`define KMAC_CFG_SHADOWED_KSTRENGTH_LOW                                                             (1)
`define KMAC_CFG_SHADOWED_KSTRENGTH_MASK                                                            (32'he)
`define KMAC_CFG_SHADOWED_MODE_LOW                                                                  (4)
`define KMAC_CFG_SHADOWED_MODE_MASK                                                                 (32'h30)
`define KMAC_CFG_SHADOWED_MSG_ENDIANNESS_LOW                                                        (8)
`define KMAC_CFG_SHADOWED_MSG_ENDIANNESS_MASK                                                       (32'h100)
`define KMAC_CFG_SHADOWED_STATE_ENDIANNESS_LOW                                                      (9)
`define KMAC_CFG_SHADOWED_STATE_ENDIANNESS_MASK                                                     (32'h200)
`endif
`ifndef KMAC_CMD
`define KMAC_CMD                                                                                    (32'h18)
`define KMAC_CMD_CMD_LOW                                                                            (0)
`define KMAC_CMD_CMD_MASK                                                                           (32'h3f)
`define KMAC_CMD_ERR_PROCESSED_LOW                                                                  (10)
`define KMAC_CMD_ERR_PROCESSED_MASK                                                                 (32'h400)
`endif
`ifndef KMAC_STATUS
`define KMAC_STATUS                                                                                 (32'h1c)
`define KMAC_STATUS_SHA3_IDLE_LOW                                                                   (0)
`define KMAC_STATUS_SHA3_IDLE_MASK                                                                  (32'h1)
`define KMAC_STATUS_SHA3_ABSORB_LOW                                                                 (1)
`define KMAC_STATUS_SHA3_ABSORB_MASK                                                                (32'h2)
`define KMAC_STATUS_SHA3_SQUEEZE_LOW                                                                (2)
`define KMAC_STATUS_SHA3_SQUEEZE_MASK                                                               (32'h4)
`define KMAC_STATUS_FIFO_DEPTH_LOW                                                                  (8)
`define KMAC_STATUS_FIFO_DEPTH_MASK                                                                 (32'h1f00)
`define KMAC_STATUS_FIFO_EMPTY_LOW                                                                  (14)
`define KMAC_STATUS_FIFO_EMPTY_MASK                                                                 (32'h4000)
`define KMAC_STATUS_FIFO_FULL_LOW                                                                   (15)
`define KMAC_STATUS_FIFO_FULL_MASK                                                                  (32'h8000)
`define KMAC_STATUS_ALERT_FATAL_FAULT_LOW                                                           (16)
`define KMAC_STATUS_ALERT_FATAL_FAULT_MASK                                                          (32'h10000)
`define KMAC_STATUS_ALERT_RECOV_CTRL_UPDATE_ERR_LOW                                                 (17)
`define KMAC_STATUS_ALERT_RECOV_CTRL_UPDATE_ERR_MASK                                                (32'h20000)
`endif
`ifndef KMAC_PREFIX_0
`define KMAC_PREFIX_0                                                                               (32'h20)
`endif
`ifndef KMAC_PREFIX_1
`define KMAC_PREFIX_1                                                                               (32'h24)
`endif
`ifndef KMAC_PREFIX_2
`define KMAC_PREFIX_2                                                                               (32'h28)
`endif
`ifndef KMAC_PREFIX_3
`define KMAC_PREFIX_3                                                                               (32'h2c)
`endif
`ifndef KMAC_PREFIX_4
`define KMAC_PREFIX_4                                                                               (32'h30)
`endif
`ifndef KMAC_PREFIX_5
`define KMAC_PREFIX_5                                                                               (32'h34)
`endif
`ifndef KMAC_PREFIX_6
`define KMAC_PREFIX_6                                                                               (32'h38)
`endif
`ifndef KMAC_PREFIX_7
`define KMAC_PREFIX_7                                                                               (32'h3c)
`endif
`ifndef KMAC_PREFIX_8
`define KMAC_PREFIX_8                                                                               (32'h40)
`endif
`ifndef KMAC_PREFIX_9
`define KMAC_PREFIX_9                                                                               (32'h44)
`endif
`ifndef KMAC_PREFIX_10
`define KMAC_PREFIX_10                                                                              (32'h48)
`endif
`ifndef KMAC_ERR_CODE
`define KMAC_ERR_CODE                                                                               (32'h4c)
`endif
`ifndef SHA3_SHA3_NAME_0
`define SHA3_SHA3_NAME_0                                                                            (32'h0)
`endif
`ifndef SHA3_SHA3_NAME_1
`define SHA3_SHA3_NAME_1                                                                            (32'h4)
`endif
`ifndef SHA3_SHA3_VERSION_0
`define SHA3_SHA3_VERSION_0                                                                         (32'h8)
`endif
`ifndef SHA3_SHA3_VERSION_1
`define SHA3_SHA3_VERSION_1                                                                         (32'hc)
`endif
`ifndef SHA3_ALERT_TEST
`define SHA3_ALERT_TEST                                                                             (32'h1c)
`define SHA3_ALERT_TEST_RECOV_OPERATION_ERR_LOW                                                     (0)
`define SHA3_ALERT_TEST_RECOV_OPERATION_ERR_MASK                                                    (32'h1)
`define SHA3_ALERT_TEST_FATAL_FAULT_ERR_LOW                                                         (1)
`define SHA3_ALERT_TEST_FATAL_FAULT_ERR_MASK                                                        (32'h2)
`endif
`ifndef SHA3_CFG_REGWEN
`define SHA3_CFG_REGWEN                                                                             (32'h20)
`define SHA3_CFG_REGWEN_EN_LOW                                                                      (0)
`define SHA3_CFG_REGWEN_EN_MASK                                                                     (32'h1)
`endif
`ifndef SHA3_CFG_SHADOWED
`define SHA3_CFG_SHADOWED                                                                           (32'h24)
`define SHA3_CFG_SHADOWED_KSTRENGTH_LOW                                                             (1)
`define SHA3_CFG_SHADOWED_KSTRENGTH_MASK                                                            (32'he)
`define SHA3_CFG_SHADOWED_MODE_LOW                                                                  (4)
`define SHA3_CFG_SHADOWED_MODE_MASK                                                                 (32'h30)
`define SHA3_CFG_SHADOWED_MSG_ENDIANNESS_LOW                                                        (8)
`define SHA3_CFG_SHADOWED_MSG_ENDIANNESS_MASK                                                       (32'h100)
`define SHA3_CFG_SHADOWED_STATE_ENDIANNESS_LOW                                                      (9)
`define SHA3_CFG_SHADOWED_STATE_ENDIANNESS_MASK                                                     (32'h200)
`endif
`ifndef SHA3_CMD
`define SHA3_CMD                                                                                    (32'h28)
`define SHA3_CMD_CMD_LOW                                                                            (0)
`define SHA3_CMD_CMD_MASK                                                                           (32'h3f)
`define SHA3_CMD_ERR_PROCESSED_LOW                                                                  (10)
`define SHA3_CMD_ERR_PROCESSED_MASK                                                                 (32'h400)
`endif
`ifndef SHA3_STATUS
`define SHA3_STATUS                                                                                 (32'h2c)
`define SHA3_STATUS_SHA3_IDLE_LOW                                                                   (0)
`define SHA3_STATUS_SHA3_IDLE_MASK                                                                  (32'h1)
`define SHA3_STATUS_SHA3_ABSORB_LOW                                                                 (1)
`define SHA3_STATUS_SHA3_ABSORB_MASK                                                                (32'h2)
`define SHA3_STATUS_SHA3_SQUEEZE_LOW                                                                (2)
`define SHA3_STATUS_SHA3_SQUEEZE_MASK                                                               (32'h4)
`define SHA3_STATUS_FIFO_DEPTH_LOW                                                                  (8)
`define SHA3_STATUS_FIFO_DEPTH_MASK                                                                 (32'h1f00)
`define SHA3_STATUS_FIFO_EMPTY_LOW                                                                  (14)
`define SHA3_STATUS_FIFO_EMPTY_MASK                                                                 (32'h4000)
`define SHA3_STATUS_FIFO_FULL_LOW                                                                   (15)
`define SHA3_STATUS_FIFO_FULL_MASK                                                                  (32'h8000)
`define SHA3_STATUS_ALERT_FATAL_FAULT_LOW                                                           (16)
`define SHA3_STATUS_ALERT_FATAL_FAULT_MASK                                                          (32'h10000)
`define SHA3_STATUS_ALERT_RECOV_CTRL_UPDATE_ERR_LOW                                                 (17)
`define SHA3_STATUS_ALERT_RECOV_CTRL_UPDATE_ERR_MASK                                                (32'h20000)
`endif
`ifndef SHA3_ERR_CODE
`define SHA3_ERR_CODE                                                                               (32'hd0)
`endif
`ifndef SHA3_INTR_BLOCK_RF_GLOBAL_INTR_EN_R
`define SHA3_INTR_BLOCK_RF_GLOBAL_INTR_EN_R                                                         (32'h400)
`define SHA3_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_LOW                                            (0)
`define SHA3_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_MASK                                           (32'h1)
`define SHA3_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_LOW                                            (1)
`define SHA3_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_MASK                                           (32'h2)
`endif
`ifndef SHA3_INTR_BLOCK_RF_ERROR_INTR_EN_R
`define SHA3_INTR_BLOCK_RF_ERROR_INTR_EN_R                                                          (32'h404)
`define SHA3_INTR_BLOCK_RF_ERROR_INTR_EN_R_SHA3_ERROR_EN_LOW                                        (0)
`define SHA3_INTR_BLOCK_RF_ERROR_INTR_EN_R_SHA3_ERROR_EN_MASK                                       (32'h1)
`define SHA3_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR1_EN_LOW                                            (1)
`define SHA3_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR1_EN_MASK                                           (32'h2)
`define SHA3_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR2_EN_LOW                                            (2)
`define SHA3_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR2_EN_MASK                                           (32'h4)
`define SHA3_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR3_EN_LOW                                            (3)
`define SHA3_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR3_EN_MASK                                           (32'h8)
`endif
`ifndef SHA3_INTR_BLOCK_RF_NOTIF_INTR_EN_R
`define SHA3_INTR_BLOCK_RF_NOTIF_INTR_EN_R                                                          (32'h408)
`define SHA3_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_CMD_DONE_EN_LOW                                    (0)
`define SHA3_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_CMD_DONE_EN_MASK                                   (32'h1)
`define SHA3_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_MSG_FIFO_EMPTY_EN_LOW                              (1)
`define SHA3_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_MSG_FIFO_EMPTY_EN_MASK                             (32'h2)
`endif
`ifndef SHA3_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R
`define SHA3_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R                                                      (32'h40c)
`define SHA3_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS_LOW                                          (0)
`define SHA3_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS_MASK                                         (32'h1)
`endif
`ifndef SHA3_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R
`define SHA3_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R                                                      (32'h410)
`define SHA3_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS_LOW                                          (0)
`define SHA3_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS_MASK                                         (32'h1)
`endif
`ifndef SHA3_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R
`define SHA3_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R                                                    (32'h414)
`define SHA3_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_SHA3_ERROR_STS_LOW                                 (0)
`define SHA3_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_SHA3_ERROR_STS_MASK                                (32'h1)
`define SHA3_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR1_STS_LOW                                     (1)
`define SHA3_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR1_STS_MASK                                    (32'h2)
`define SHA3_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR2_STS_LOW                                     (2)
`define SHA3_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR2_STS_MASK                                    (32'h4)
`define SHA3_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR3_STS_LOW                                     (3)
`define SHA3_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR3_STS_MASK                                    (32'h8)
`endif
`ifndef SHA3_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R
`define SHA3_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R                                                    (32'h418)
`define SHA3_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_LOW                             (0)
`define SHA3_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK                            (32'h1)
`define SHA3_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_MSG_FIFO_EMPTY_STS_LOW                       (1)
`define SHA3_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_MSG_FIFO_EMPTY_STS_MASK                      (32'h2)
`endif
`ifndef SHA3_INTR_BLOCK_RF_ERROR_INTR_TRIG_R
`define SHA3_INTR_BLOCK_RF_ERROR_INTR_TRIG_R                                                        (32'h41c)
`define SHA3_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_SHA3_ERROR_TRIG_LOW                                    (0)
`define SHA3_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_SHA3_ERROR_TRIG_MASK                                   (32'h1)
`define SHA3_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR1_TRIG_LOW                                        (1)
`define SHA3_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR1_TRIG_MASK                                       (32'h2)
`define SHA3_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR2_TRIG_LOW                                        (2)
`define SHA3_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR2_TRIG_MASK                                       (32'h4)
`define SHA3_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR3_TRIG_LOW                                        (3)
`define SHA3_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR3_TRIG_MASK                                       (32'h8)
`endif
`ifndef SHA3_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R
`define SHA3_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R                                                        (32'h420)
`define SHA3_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_DONE_TRIG_LOW                                (0)
`define SHA3_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_DONE_TRIG_MASK                               (32'h1)
`define SHA3_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_MSG_FIFO_EMPTY_TRIG_LOW                          (1)
`define SHA3_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_MSG_FIFO_EMPTY_TRIG_MASK                         (32'h2)
`endif
`ifndef SHA3_INTR_BLOCK_RF_SHA3_ERROR_INTR_COUNT_R
`define SHA3_INTR_BLOCK_RF_SHA3_ERROR_INTR_COUNT_R                                                  (32'h500)
`endif
`ifndef SHA3_INTR_BLOCK_RF_ERROR1_INTR_COUNT_R
`define SHA3_INTR_BLOCK_RF_ERROR1_INTR_COUNT_R                                                      (32'h504)
`endif
`ifndef SHA3_INTR_BLOCK_RF_ERROR2_INTR_COUNT_R
`define SHA3_INTR_BLOCK_RF_ERROR2_INTR_COUNT_R                                                      (32'h508)
`endif
`ifndef SHA3_INTR_BLOCK_RF_ERROR3_INTR_COUNT_R
`define SHA3_INTR_BLOCK_RF_ERROR3_INTR_COUNT_R                                                      (32'h50c)
`endif
`ifndef SHA3_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R
`define SHA3_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R                                              (32'h580)
`endif
`ifndef SHA3_INTR_BLOCK_RF_SHA3_ERROR_INTR_COUNT_INCR_R
`define SHA3_INTR_BLOCK_RF_SHA3_ERROR_INTR_COUNT_INCR_R                                             (32'h600)
`define SHA3_INTR_BLOCK_RF_SHA3_ERROR_INTR_COUNT_INCR_R_PULSE_LOW                                   (0)
`define SHA3_INTR_BLOCK_RF_SHA3_ERROR_INTR_COUNT_INCR_R_PULSE_MASK                                  (32'h1)
`endif
`ifndef SHA3_INTR_BLOCK_RF_ERROR1_INTR_COUNT_INCR_R
`define SHA3_INTR_BLOCK_RF_ERROR1_INTR_COUNT_INCR_R                                                 (32'h604)
`define SHA3_INTR_BLOCK_RF_ERROR1_INTR_COUNT_INCR_R_PULSE_LOW                                       (0)
`define SHA3_INTR_BLOCK_RF_ERROR1_INTR_COUNT_INCR_R_PULSE_MASK                                      (32'h1)
`endif
`ifndef SHA3_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R
`define SHA3_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R                                                 (32'h608)
`define SHA3_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R_PULSE_LOW                                       (0)
`define SHA3_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R_PULSE_MASK                                      (32'h1)
`endif
`ifndef SHA3_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R
`define SHA3_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R                                                 (32'h60c)
`define SHA3_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R_PULSE_LOW                                       (0)
`define SHA3_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R_PULSE_MASK                                      (32'h1)
`endif
`ifndef SHA3_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R
`define SHA3_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R                                         (32'h610)
`define SHA3_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R_PULSE_LOW                               (0)
`define SHA3_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R_PULSE_MASK                              (32'h1)
`endif
`ifndef CSRNG_REG_INTERRUPT_STATE
`define CSRNG_REG_INTERRUPT_STATE                                                                   (32'h0)
`define CSRNG_REG_INTERRUPT_STATE_CS_CMD_REQ_DONE_LOW                                               (0)
`define CSRNG_REG_INTERRUPT_STATE_CS_CMD_REQ_DONE_MASK                                              (32'h1)
`define CSRNG_REG_INTERRUPT_STATE_CS_ENTROPY_REQ_LOW                                                (1)
`define CSRNG_REG_INTERRUPT_STATE_CS_ENTROPY_REQ_MASK                                               (32'h2)
`define CSRNG_REG_INTERRUPT_STATE_CS_HW_INST_EXC_LOW                                                (2)
`define CSRNG_REG_INTERRUPT_STATE_CS_HW_INST_EXC_MASK                                               (32'h4)
`define CSRNG_REG_INTERRUPT_STATE_CS_FATAL_ERR_LOW                                                  (3)
`define CSRNG_REG_INTERRUPT_STATE_CS_FATAL_ERR_MASK                                                 (32'h8)
`endif
`ifndef CSRNG_REG_INTERRUPT_ENABLE
`define CSRNG_REG_INTERRUPT_ENABLE                                                                  (32'h4)
`define CSRNG_REG_INTERRUPT_ENABLE_CS_CMD_REQ_DONE_LOW                                              (0)
`define CSRNG_REG_INTERRUPT_ENABLE_CS_CMD_REQ_DONE_MASK                                             (32'h1)
`define CSRNG_REG_INTERRUPT_ENABLE_CS_ENTROPY_REQ_LOW                                               (1)
`define CSRNG_REG_INTERRUPT_ENABLE_CS_ENTROPY_REQ_MASK                                              (32'h2)
`define CSRNG_REG_INTERRUPT_ENABLE_CS_HW_INST_EXC_LOW                                               (2)
`define CSRNG_REG_INTERRUPT_ENABLE_CS_HW_INST_EXC_MASK                                              (32'h4)
`define CSRNG_REG_INTERRUPT_ENABLE_CS_FATAL_ERR_LOW                                                 (3)
`define CSRNG_REG_INTERRUPT_ENABLE_CS_FATAL_ERR_MASK                                                (32'h8)
`endif
`ifndef CSRNG_REG_INTERRUPT_TEST
`define CSRNG_REG_INTERRUPT_TEST                                                                    (32'h8)
`define CSRNG_REG_INTERRUPT_TEST_CS_CMD_REQ_DONE_LOW                                                (0)
`define CSRNG_REG_INTERRUPT_TEST_CS_CMD_REQ_DONE_MASK                                               (32'h1)
`define CSRNG_REG_INTERRUPT_TEST_CS_ENTROPY_REQ_LOW                                                 (1)
`define CSRNG_REG_INTERRUPT_TEST_CS_ENTROPY_REQ_MASK                                                (32'h2)
`define CSRNG_REG_INTERRUPT_TEST_CS_HW_INST_EXC_LOW                                                 (2)
`define CSRNG_REG_INTERRUPT_TEST_CS_HW_INST_EXC_MASK                                                (32'h4)
`define CSRNG_REG_INTERRUPT_TEST_CS_FATAL_ERR_LOW                                                   (3)
`define CSRNG_REG_INTERRUPT_TEST_CS_FATAL_ERR_MASK                                                  (32'h8)
`endif
`ifndef CSRNG_REG_ALERT_TEST
`define CSRNG_REG_ALERT_TEST                                                                        (32'hc)
`define CSRNG_REG_ALERT_TEST_RECOV_ALERT_LOW                                                        (0)
`define CSRNG_REG_ALERT_TEST_RECOV_ALERT_MASK                                                       (32'h1)
`define CSRNG_REG_ALERT_TEST_FATAL_ALERT_LOW                                                        (1)
`define CSRNG_REG_ALERT_TEST_FATAL_ALERT_MASK                                                       (32'h2)
`endif
`ifndef CSRNG_REG_REGWEN
`define CSRNG_REG_REGWEN                                                                            (32'h10)
`define CSRNG_REG_REGWEN_REGWEN_LOW                                                                 (0)
`define CSRNG_REG_REGWEN_REGWEN_MASK                                                                (32'h1)
`endif
`ifndef CSRNG_REG_CTRL
`define CSRNG_REG_CTRL                                                                              (32'h14)
`define CSRNG_REG_CTRL_ENABLE_LOW                                                                   (0)
`define CSRNG_REG_CTRL_ENABLE_MASK                                                                  (32'hf)
`define CSRNG_REG_CTRL_SW_APP_ENABLE_LOW                                                            (4)
`define CSRNG_REG_CTRL_SW_APP_ENABLE_MASK                                                           (32'hf0)
`define CSRNG_REG_CTRL_READ_INT_STATE_LOW                                                           (8)
`define CSRNG_REG_CTRL_READ_INT_STATE_MASK                                                          (32'hf00)
`define CSRNG_REG_CTRL_FIPS_FORCE_ENABLE_LOW                                                        (12)
`define CSRNG_REG_CTRL_FIPS_FORCE_ENABLE_MASK                                                       (32'hf000)
`endif
`ifndef CSRNG_REG_CMD_REQ
`define CSRNG_REG_CMD_REQ                                                                           (32'h18)
`define CSRNG_REG_CMD_REQ_ACMD_LOW                                                                  (0)
`define CSRNG_REG_CMD_REQ_ACMD_MASK                                                                 (32'hf)
`define CSRNG_REG_CMD_REQ_CLEN_LOW                                                                  (4)
`define CSRNG_REG_CMD_REQ_CLEN_MASK                                                                 (32'hf0)
`define CSRNG_REG_CMD_REQ_FLAG0_LOW                                                                 (8)
`define CSRNG_REG_CMD_REQ_FLAG0_MASK                                                                (32'hf00)
`define CSRNG_REG_CMD_REQ_GLEN_LOW                                                                  (12)
`define CSRNG_REG_CMD_REQ_GLEN_MASK                                                                 (32'h1fff000)
`endif
`ifndef CSRNG_REG_RESEED_INTERVAL
`define CSRNG_REG_RESEED_INTERVAL                                                                   (32'h1c)
`endif
`ifndef CSRNG_REG_RESEED_COUNTER_0
`define CSRNG_REG_RESEED_COUNTER_0                                                                  (32'h20)
`endif
`ifndef CSRNG_REG_RESEED_COUNTER_1
`define CSRNG_REG_RESEED_COUNTER_1                                                                  (32'h24)
`endif
`ifndef CSRNG_REG_RESEED_COUNTER_2
`define CSRNG_REG_RESEED_COUNTER_2                                                                  (32'h28)
`endif
`ifndef CSRNG_REG_SW_CMD_STS
`define CSRNG_REG_SW_CMD_STS                                                                        (32'h2c)
`define CSRNG_REG_SW_CMD_STS_CMD_RDY_LOW                                                            (1)
`define CSRNG_REG_SW_CMD_STS_CMD_RDY_MASK                                                           (32'h2)
`define CSRNG_REG_SW_CMD_STS_CMD_ACK_LOW                                                            (2)
`define CSRNG_REG_SW_CMD_STS_CMD_ACK_MASK                                                           (32'h4)
`define CSRNG_REG_SW_CMD_STS_CMD_STS_LOW                                                            (3)
`define CSRNG_REG_SW_CMD_STS_CMD_STS_MASK                                                           (32'h38)
`endif
`ifndef CSRNG_REG_GENBITS_VLD
`define CSRNG_REG_GENBITS_VLD                                                                       (32'h30)
`define CSRNG_REG_GENBITS_VLD_GENBITS_VLD_LOW                                                       (0)
`define CSRNG_REG_GENBITS_VLD_GENBITS_VLD_MASK                                                      (32'h1)
`define CSRNG_REG_GENBITS_VLD_GENBITS_FIPS_LOW                                                      (1)
`define CSRNG_REG_GENBITS_VLD_GENBITS_FIPS_MASK                                                     (32'h2)
`endif
`ifndef CSRNG_REG_GENBITS
`define CSRNG_REG_GENBITS                                                                           (32'h34)
`endif
`ifndef CSRNG_REG_INT_STATE_READ_ENABLE
`define CSRNG_REG_INT_STATE_READ_ENABLE                                                             (32'h38)
`define CSRNG_REG_INT_STATE_READ_ENABLE_INT_STATE_READ_ENABLE_LOW                                   (0)
`define CSRNG_REG_INT_STATE_READ_ENABLE_INT_STATE_READ_ENABLE_MASK                                  (32'h7)
`endif
`ifndef CSRNG_REG_INT_STATE_READ_ENABLE_REGWEN
`define CSRNG_REG_INT_STATE_READ_ENABLE_REGWEN                                                      (32'h3c)
`define CSRNG_REG_INT_STATE_READ_ENABLE_REGWEN_INT_STATE_READ_ENABLE_REGWEN_LOW                     (0)
`define CSRNG_REG_INT_STATE_READ_ENABLE_REGWEN_INT_STATE_READ_ENABLE_REGWEN_MASK                    (32'h1)
`endif
`ifndef CSRNG_REG_INT_STATE_NUM
`define CSRNG_REG_INT_STATE_NUM                                                                     (32'h40)
`define CSRNG_REG_INT_STATE_NUM_INT_STATE_NUM_LOW                                                   (0)
`define CSRNG_REG_INT_STATE_NUM_INT_STATE_NUM_MASK                                                  (32'hf)
`endif
`ifndef CSRNG_REG_INT_STATE_VAL
`define CSRNG_REG_INT_STATE_VAL                                                                     (32'h44)
`endif
`ifndef CSRNG_REG_FIPS_FORCE
`define CSRNG_REG_FIPS_FORCE                                                                        (32'h48)
`define CSRNG_REG_FIPS_FORCE_FIPS_FORCE_LOW                                                         (0)
`define CSRNG_REG_FIPS_FORCE_FIPS_FORCE_MASK                                                        (32'h7)
`endif
`ifndef CSRNG_REG_HW_EXC_STS
`define CSRNG_REG_HW_EXC_STS                                                                        (32'h4c)
`define CSRNG_REG_HW_EXC_STS_HW_EXC_STS_LOW                                                         (0)
`define CSRNG_REG_HW_EXC_STS_HW_EXC_STS_MASK                                                        (32'hffff)
`endif
`ifndef CSRNG_REG_RECOV_ALERT_STS
`define CSRNG_REG_RECOV_ALERT_STS                                                                   (32'h50)
`define CSRNG_REG_RECOV_ALERT_STS_ENABLE_FIELD_ALERT_LOW                                            (0)
`define CSRNG_REG_RECOV_ALERT_STS_ENABLE_FIELD_ALERT_MASK                                           (32'h1)
`define CSRNG_REG_RECOV_ALERT_STS_SW_APP_ENABLE_FIELD_ALERT_LOW                                     (1)
`define CSRNG_REG_RECOV_ALERT_STS_SW_APP_ENABLE_FIELD_ALERT_MASK                                    (32'h2)
`define CSRNG_REG_RECOV_ALERT_STS_READ_INT_STATE_FIELD_ALERT_LOW                                    (2)
`define CSRNG_REG_RECOV_ALERT_STS_READ_INT_STATE_FIELD_ALERT_MASK                                   (32'h4)
`define CSRNG_REG_RECOV_ALERT_STS_FIPS_FORCE_ENABLE_FIELD_ALERT_LOW                                 (3)
`define CSRNG_REG_RECOV_ALERT_STS_FIPS_FORCE_ENABLE_FIELD_ALERT_MASK                                (32'h8)
`define CSRNG_REG_RECOV_ALERT_STS_ACMD_FLAG0_FIELD_ALERT_LOW                                        (4)
`define CSRNG_REG_RECOV_ALERT_STS_ACMD_FLAG0_FIELD_ALERT_MASK                                       (32'h10)
`define CSRNG_REG_RECOV_ALERT_STS_CS_BUS_CMP_ALERT_LOW                                              (12)
`define CSRNG_REG_RECOV_ALERT_STS_CS_BUS_CMP_ALERT_MASK                                             (32'h1000)
`define CSRNG_REG_RECOV_ALERT_STS_CMD_STAGE_INVALID_ACMD_ALERT_LOW                                  (13)
`define CSRNG_REG_RECOV_ALERT_STS_CMD_STAGE_INVALID_ACMD_ALERT_MASK                                 (32'h2000)
`define CSRNG_REG_RECOV_ALERT_STS_CMD_STAGE_INVALID_CMD_SEQ_ALERT_LOW                               (14)
`define CSRNG_REG_RECOV_ALERT_STS_CMD_STAGE_INVALID_CMD_SEQ_ALERT_MASK                              (32'h4000)
`define CSRNG_REG_RECOV_ALERT_STS_CMD_STAGE_RESEED_CNT_ALERT_LOW                                    (15)
`define CSRNG_REG_RECOV_ALERT_STS_CMD_STAGE_RESEED_CNT_ALERT_MASK                                   (32'h8000)
`endif
`ifndef CSRNG_REG_ERR_CODE
`define CSRNG_REG_ERR_CODE                                                                          (32'h54)
`define CSRNG_REG_ERR_CODE_SFIFO_CMD_ERR_LOW                                                        (0)
`define CSRNG_REG_ERR_CODE_SFIFO_CMD_ERR_MASK                                                       (32'h1)
`define CSRNG_REG_ERR_CODE_SFIFO_GENBITS_ERR_LOW                                                    (1)
`define CSRNG_REG_ERR_CODE_SFIFO_GENBITS_ERR_MASK                                                   (32'h2)
`define CSRNG_REG_ERR_CODE_SFIFO_CMDREQ_ERR_LOW                                                     (2)
`define CSRNG_REG_ERR_CODE_SFIFO_CMDREQ_ERR_MASK                                                    (32'h4)
`define CSRNG_REG_ERR_CODE_SFIFO_RCSTAGE_ERR_LOW                                                    (3)
`define CSRNG_REG_ERR_CODE_SFIFO_RCSTAGE_ERR_MASK                                                   (32'h8)
`define CSRNG_REG_ERR_CODE_SFIFO_KEYVRC_ERR_LOW                                                     (4)
`define CSRNG_REG_ERR_CODE_SFIFO_KEYVRC_ERR_MASK                                                    (32'h10)
`define CSRNG_REG_ERR_CODE_SFIFO_UPDREQ_ERR_LOW                                                     (5)
`define CSRNG_REG_ERR_CODE_SFIFO_UPDREQ_ERR_MASK                                                    (32'h20)
`define CSRNG_REG_ERR_CODE_SFIFO_BENCREQ_ERR_LOW                                                    (6)
`define CSRNG_REG_ERR_CODE_SFIFO_BENCREQ_ERR_MASK                                                   (32'h40)
`define CSRNG_REG_ERR_CODE_SFIFO_BENCACK_ERR_LOW                                                    (7)
`define CSRNG_REG_ERR_CODE_SFIFO_BENCACK_ERR_MASK                                                   (32'h80)
`define CSRNG_REG_ERR_CODE_SFIFO_PDATA_ERR_LOW                                                      (8)
`define CSRNG_REG_ERR_CODE_SFIFO_PDATA_ERR_MASK                                                     (32'h100)
`define CSRNG_REG_ERR_CODE_SFIFO_FINAL_ERR_LOW                                                      (9)
`define CSRNG_REG_ERR_CODE_SFIFO_FINAL_ERR_MASK                                                     (32'h200)
`define CSRNG_REG_ERR_CODE_SFIFO_GBENCACK_ERR_LOW                                                   (10)
`define CSRNG_REG_ERR_CODE_SFIFO_GBENCACK_ERR_MASK                                                  (32'h400)
`define CSRNG_REG_ERR_CODE_SFIFO_GRCSTAGE_ERR_LOW                                                   (11)
`define CSRNG_REG_ERR_CODE_SFIFO_GRCSTAGE_ERR_MASK                                                  (32'h800)
`define CSRNG_REG_ERR_CODE_SFIFO_GGENREQ_ERR_LOW                                                    (12)
`define CSRNG_REG_ERR_CODE_SFIFO_GGENREQ_ERR_MASK                                                   (32'h1000)
`define CSRNG_REG_ERR_CODE_SFIFO_GADSTAGE_ERR_LOW                                                   (13)
`define CSRNG_REG_ERR_CODE_SFIFO_GADSTAGE_ERR_MASK                                                  (32'h2000)
`define CSRNG_REG_ERR_CODE_SFIFO_GGENBITS_ERR_LOW                                                   (14)
`define CSRNG_REG_ERR_CODE_SFIFO_GGENBITS_ERR_MASK                                                  (32'h4000)
`define CSRNG_REG_ERR_CODE_SFIFO_BLKENC_ERR_LOW                                                     (15)
`define CSRNG_REG_ERR_CODE_SFIFO_BLKENC_ERR_MASK                                                    (32'h8000)
`define CSRNG_REG_ERR_CODE_CMD_STAGE_SM_ERR_LOW                                                     (20)
`define CSRNG_REG_ERR_CODE_CMD_STAGE_SM_ERR_MASK                                                    (32'h100000)
`define CSRNG_REG_ERR_CODE_MAIN_SM_ERR_LOW                                                          (21)
`define CSRNG_REG_ERR_CODE_MAIN_SM_ERR_MASK                                                         (32'h200000)
`define CSRNG_REG_ERR_CODE_DRBG_GEN_SM_ERR_LOW                                                      (22)
`define CSRNG_REG_ERR_CODE_DRBG_GEN_SM_ERR_MASK                                                     (32'h400000)
`define CSRNG_REG_ERR_CODE_DRBG_UPDBE_SM_ERR_LOW                                                    (23)
`define CSRNG_REG_ERR_CODE_DRBG_UPDBE_SM_ERR_MASK                                                   (32'h800000)
`define CSRNG_REG_ERR_CODE_DRBG_UPDOB_SM_ERR_LOW                                                    (24)
`define CSRNG_REG_ERR_CODE_DRBG_UPDOB_SM_ERR_MASK                                                   (32'h1000000)
`define CSRNG_REG_ERR_CODE_AES_CIPHER_SM_ERR_LOW                                                    (25)
`define CSRNG_REG_ERR_CODE_AES_CIPHER_SM_ERR_MASK                                                   (32'h2000000)
`define CSRNG_REG_ERR_CODE_CMD_GEN_CNT_ERR_LOW                                                      (26)
`define CSRNG_REG_ERR_CODE_CMD_GEN_CNT_ERR_MASK                                                     (32'h4000000)
`define CSRNG_REG_ERR_CODE_FIFO_WRITE_ERR_LOW                                                       (28)
`define CSRNG_REG_ERR_CODE_FIFO_WRITE_ERR_MASK                                                      (32'h10000000)
`define CSRNG_REG_ERR_CODE_FIFO_READ_ERR_LOW                                                        (29)
`define CSRNG_REG_ERR_CODE_FIFO_READ_ERR_MASK                                                       (32'h20000000)
`define CSRNG_REG_ERR_CODE_FIFO_STATE_ERR_LOW                                                       (30)
`define CSRNG_REG_ERR_CODE_FIFO_STATE_ERR_MASK                                                      (32'h40000000)
`endif
`ifndef CSRNG_REG_ERR_CODE_TEST
`define CSRNG_REG_ERR_CODE_TEST                                                                     (32'h58)
`define CSRNG_REG_ERR_CODE_TEST_ERR_CODE_TEST_LOW                                                   (0)
`define CSRNG_REG_ERR_CODE_TEST_ERR_CODE_TEST_MASK                                                  (32'h1f)
`endif
`ifndef CSRNG_REG_MAIN_SM_STATE
`define CSRNG_REG_MAIN_SM_STATE                                                                     (32'h5c)
`define CSRNG_REG_MAIN_SM_STATE_MAIN_SM_STATE_LOW                                                   (0)
`define CSRNG_REG_MAIN_SM_STATE_MAIN_SM_STATE_MASK                                                  (32'hff)
`endif
`ifndef ENTROPY_SRC_REG_INTERRUPT_STATE
`define ENTROPY_SRC_REG_INTERRUPT_STATE                                                             (32'h0)
`define ENTROPY_SRC_REG_INTERRUPT_STATE_ES_ENTROPY_VALID_LOW                                        (0)
`define ENTROPY_SRC_REG_INTERRUPT_STATE_ES_ENTROPY_VALID_MASK                                       (32'h1)
`define ENTROPY_SRC_REG_INTERRUPT_STATE_ES_HEALTH_TEST_FAILED_LOW                                   (1)
`define ENTROPY_SRC_REG_INTERRUPT_STATE_ES_HEALTH_TEST_FAILED_MASK                                  (32'h2)
`define ENTROPY_SRC_REG_INTERRUPT_STATE_ES_OBSERVE_FIFO_READY_LOW                                   (2)
`define ENTROPY_SRC_REG_INTERRUPT_STATE_ES_OBSERVE_FIFO_READY_MASK                                  (32'h4)
`define ENTROPY_SRC_REG_INTERRUPT_STATE_ES_FATAL_ERR_LOW                                            (3)
`define ENTROPY_SRC_REG_INTERRUPT_STATE_ES_FATAL_ERR_MASK                                           (32'h8)
`endif
`ifndef ENTROPY_SRC_REG_INTERRUPT_ENABLE
`define ENTROPY_SRC_REG_INTERRUPT_ENABLE                                                            (32'h4)
`define ENTROPY_SRC_REG_INTERRUPT_ENABLE_ES_ENTROPY_VALID_LOW                                       (0)
`define ENTROPY_SRC_REG_INTERRUPT_ENABLE_ES_ENTROPY_VALID_MASK                                      (32'h1)
`define ENTROPY_SRC_REG_INTERRUPT_ENABLE_ES_HEALTH_TEST_FAILED_LOW                                  (1)
`define ENTROPY_SRC_REG_INTERRUPT_ENABLE_ES_HEALTH_TEST_FAILED_MASK                                 (32'h2)
`define ENTROPY_SRC_REG_INTERRUPT_ENABLE_ES_OBSERVE_FIFO_READY_LOW                                  (2)
`define ENTROPY_SRC_REG_INTERRUPT_ENABLE_ES_OBSERVE_FIFO_READY_MASK                                 (32'h4)
`define ENTROPY_SRC_REG_INTERRUPT_ENABLE_ES_FATAL_ERR_LOW                                           (3)
`define ENTROPY_SRC_REG_INTERRUPT_ENABLE_ES_FATAL_ERR_MASK                                          (32'h8)
`endif
`ifndef ENTROPY_SRC_REG_INTERRUPT_TEST
`define ENTROPY_SRC_REG_INTERRUPT_TEST                                                              (32'h8)
`define ENTROPY_SRC_REG_INTERRUPT_TEST_ES_ENTROPY_VALID_LOW                                         (0)
`define ENTROPY_SRC_REG_INTERRUPT_TEST_ES_ENTROPY_VALID_MASK                                        (32'h1)
`define ENTROPY_SRC_REG_INTERRUPT_TEST_ES_HEALTH_TEST_FAILED_LOW                                    (1)
`define ENTROPY_SRC_REG_INTERRUPT_TEST_ES_HEALTH_TEST_FAILED_MASK                                   (32'h2)
`define ENTROPY_SRC_REG_INTERRUPT_TEST_ES_OBSERVE_FIFO_READY_LOW                                    (2)
`define ENTROPY_SRC_REG_INTERRUPT_TEST_ES_OBSERVE_FIFO_READY_MASK                                   (32'h4)
`define ENTROPY_SRC_REG_INTERRUPT_TEST_ES_FATAL_ERR_LOW                                             (3)
`define ENTROPY_SRC_REG_INTERRUPT_TEST_ES_FATAL_ERR_MASK                                            (32'h8)
`endif
`ifndef ENTROPY_SRC_REG_ALERT_TEST
`define ENTROPY_SRC_REG_ALERT_TEST                                                                  (32'hc)
`define ENTROPY_SRC_REG_ALERT_TEST_RECOV_ALERT_LOW                                                  (0)
`define ENTROPY_SRC_REG_ALERT_TEST_RECOV_ALERT_MASK                                                 (32'h1)
`define ENTROPY_SRC_REG_ALERT_TEST_FATAL_ALERT_LOW                                                  (1)
`define ENTROPY_SRC_REG_ALERT_TEST_FATAL_ALERT_MASK                                                 (32'h2)
`endif
`ifndef ENTROPY_SRC_REG_ME_REGWEN
`define ENTROPY_SRC_REG_ME_REGWEN                                                                   (32'h10)
`define ENTROPY_SRC_REG_ME_REGWEN_ME_REGWEN_LOW                                                     (0)
`define ENTROPY_SRC_REG_ME_REGWEN_ME_REGWEN_MASK                                                    (32'h1)
`endif
`ifndef ENTROPY_SRC_REG_SW_REGUPD
`define ENTROPY_SRC_REG_SW_REGUPD                                                                   (32'h14)
`define ENTROPY_SRC_REG_SW_REGUPD_SW_REGUPD_LOW                                                     (0)
`define ENTROPY_SRC_REG_SW_REGUPD_SW_REGUPD_MASK                                                    (32'h1)
`endif
`ifndef ENTROPY_SRC_REG_REGWEN
`define ENTROPY_SRC_REG_REGWEN                                                                      (32'h18)
`define ENTROPY_SRC_REG_REGWEN_REGWEN_LOW                                                           (0)
`define ENTROPY_SRC_REG_REGWEN_REGWEN_MASK                                                          (32'h1)
`endif
`ifndef ENTROPY_SRC_REG_REV
`define ENTROPY_SRC_REG_REV                                                                         (32'h1c)
`define ENTROPY_SRC_REG_REV_ABI_REVISION_LOW                                                        (0)
`define ENTROPY_SRC_REG_REV_ABI_REVISION_MASK                                                       (32'hff)
`define ENTROPY_SRC_REG_REV_HW_REVISION_LOW                                                         (8)
`define ENTROPY_SRC_REG_REV_HW_REVISION_MASK                                                        (32'hff00)
`define ENTROPY_SRC_REG_REV_CHIP_TYPE_LOW                                                           (16)
`define ENTROPY_SRC_REG_REV_CHIP_TYPE_MASK                                                          (32'hff0000)
`endif
`ifndef ENTROPY_SRC_REG_MODULE_ENABLE
`define ENTROPY_SRC_REG_MODULE_ENABLE                                                               (32'h20)
`define ENTROPY_SRC_REG_MODULE_ENABLE_MODULE_ENABLE_LOW                                             (0)
`define ENTROPY_SRC_REG_MODULE_ENABLE_MODULE_ENABLE_MASK                                            (32'hf)
`endif
`ifndef ENTROPY_SRC_REG_CONF
`define ENTROPY_SRC_REG_CONF                                                                        (32'h24)
`define ENTROPY_SRC_REG_CONF_FIPS_ENABLE_LOW                                                        (0)
`define ENTROPY_SRC_REG_CONF_FIPS_ENABLE_MASK                                                       (32'hf)
`define ENTROPY_SRC_REG_CONF_FIPS_FLAG_LOW                                                          (4)
`define ENTROPY_SRC_REG_CONF_FIPS_FLAG_MASK                                                         (32'hf0)
`define ENTROPY_SRC_REG_CONF_RNG_FIPS_LOW                                                           (8)
`define ENTROPY_SRC_REG_CONF_RNG_FIPS_MASK                                                          (32'hf00)
`define ENTROPY_SRC_REG_CONF_RNG_BIT_ENABLE_LOW                                                     (12)
`define ENTROPY_SRC_REG_CONF_RNG_BIT_ENABLE_MASK                                                    (32'hf000)
`define ENTROPY_SRC_REG_CONF_RNG_BIT_SEL_LOW                                                        (16)
`define ENTROPY_SRC_REG_CONF_RNG_BIT_SEL_MASK                                                       (32'h30000)
`define ENTROPY_SRC_REG_CONF_THRESHOLD_SCOPE_LOW                                                    (18)
`define ENTROPY_SRC_REG_CONF_THRESHOLD_SCOPE_MASK                                                   (32'h3c0000)
`define ENTROPY_SRC_REG_CONF_ENTROPY_DATA_REG_ENABLE_LOW                                            (22)
`define ENTROPY_SRC_REG_CONF_ENTROPY_DATA_REG_ENABLE_MASK                                           (32'h3c00000)
`endif
`ifndef ENTROPY_SRC_REG_ENTROPY_CONTROL
`define ENTROPY_SRC_REG_ENTROPY_CONTROL                                                             (32'h28)
`define ENTROPY_SRC_REG_ENTROPY_CONTROL_ES_ROUTE_LOW                                                (0)
`define ENTROPY_SRC_REG_ENTROPY_CONTROL_ES_ROUTE_MASK                                               (32'hf)
`define ENTROPY_SRC_REG_ENTROPY_CONTROL_ES_TYPE_LOW                                                 (4)
`define ENTROPY_SRC_REG_ENTROPY_CONTROL_ES_TYPE_MASK                                                (32'hf0)
`endif
`ifndef ENTROPY_SRC_REG_ENTROPY_DATA
`define ENTROPY_SRC_REG_ENTROPY_DATA                                                                (32'h2c)
`endif
`ifndef ENTROPY_SRC_REG_HEALTH_TEST_WINDOWS
`define ENTROPY_SRC_REG_HEALTH_TEST_WINDOWS                                                         (32'h30)
`define ENTROPY_SRC_REG_HEALTH_TEST_WINDOWS_FIPS_WINDOW_LOW                                         (0)
`define ENTROPY_SRC_REG_HEALTH_TEST_WINDOWS_FIPS_WINDOW_MASK                                        (32'hffff)
`define ENTROPY_SRC_REG_HEALTH_TEST_WINDOWS_BYPASS_WINDOW_LOW                                       (16)
`define ENTROPY_SRC_REG_HEALTH_TEST_WINDOWS_BYPASS_WINDOW_MASK                                      (32'hffff0000)
`endif
`ifndef ENTROPY_SRC_REG_REPCNT_THRESHOLDS
`define ENTROPY_SRC_REG_REPCNT_THRESHOLDS                                                           (32'h34)
`define ENTROPY_SRC_REG_REPCNT_THRESHOLDS_FIPS_THRESH_LOW                                           (0)
`define ENTROPY_SRC_REG_REPCNT_THRESHOLDS_FIPS_THRESH_MASK                                          (32'hffff)
`define ENTROPY_SRC_REG_REPCNT_THRESHOLDS_BYPASS_THRESH_LOW                                         (16)
`define ENTROPY_SRC_REG_REPCNT_THRESHOLDS_BYPASS_THRESH_MASK                                        (32'hffff0000)
`endif
`ifndef ENTROPY_SRC_REG_REPCNTS_THRESHOLDS
`define ENTROPY_SRC_REG_REPCNTS_THRESHOLDS                                                          (32'h38)
`define ENTROPY_SRC_REG_REPCNTS_THRESHOLDS_FIPS_THRESH_LOW                                          (0)
`define ENTROPY_SRC_REG_REPCNTS_THRESHOLDS_FIPS_THRESH_MASK                                         (32'hffff)
`define ENTROPY_SRC_REG_REPCNTS_THRESHOLDS_BYPASS_THRESH_LOW                                        (16)
`define ENTROPY_SRC_REG_REPCNTS_THRESHOLDS_BYPASS_THRESH_MASK                                       (32'hffff0000)
`endif
`ifndef ENTROPY_SRC_REG_ADAPTP_HI_THRESHOLDS
`define ENTROPY_SRC_REG_ADAPTP_HI_THRESHOLDS                                                        (32'h3c)
`define ENTROPY_SRC_REG_ADAPTP_HI_THRESHOLDS_FIPS_THRESH_LOW                                        (0)
`define ENTROPY_SRC_REG_ADAPTP_HI_THRESHOLDS_FIPS_THRESH_MASK                                       (32'hffff)
`define ENTROPY_SRC_REG_ADAPTP_HI_THRESHOLDS_BYPASS_THRESH_LOW                                      (16)
`define ENTROPY_SRC_REG_ADAPTP_HI_THRESHOLDS_BYPASS_THRESH_MASK                                     (32'hffff0000)
`endif
`ifndef ENTROPY_SRC_REG_ADAPTP_LO_THRESHOLDS
`define ENTROPY_SRC_REG_ADAPTP_LO_THRESHOLDS                                                        (32'h40)
`define ENTROPY_SRC_REG_ADAPTP_LO_THRESHOLDS_FIPS_THRESH_LOW                                        (0)
`define ENTROPY_SRC_REG_ADAPTP_LO_THRESHOLDS_FIPS_THRESH_MASK                                       (32'hffff)
`define ENTROPY_SRC_REG_ADAPTP_LO_THRESHOLDS_BYPASS_THRESH_LOW                                      (16)
`define ENTROPY_SRC_REG_ADAPTP_LO_THRESHOLDS_BYPASS_THRESH_MASK                                     (32'hffff0000)
`endif
`ifndef ENTROPY_SRC_REG_BUCKET_THRESHOLDS
`define ENTROPY_SRC_REG_BUCKET_THRESHOLDS                                                           (32'h44)
`define ENTROPY_SRC_REG_BUCKET_THRESHOLDS_FIPS_THRESH_LOW                                           (0)
`define ENTROPY_SRC_REG_BUCKET_THRESHOLDS_FIPS_THRESH_MASK                                          (32'hffff)
`define ENTROPY_SRC_REG_BUCKET_THRESHOLDS_BYPASS_THRESH_LOW                                         (16)
`define ENTROPY_SRC_REG_BUCKET_THRESHOLDS_BYPASS_THRESH_MASK                                        (32'hffff0000)
`endif
`ifndef ENTROPY_SRC_REG_MARKOV_HI_THRESHOLDS
`define ENTROPY_SRC_REG_MARKOV_HI_THRESHOLDS                                                        (32'h48)
`define ENTROPY_SRC_REG_MARKOV_HI_THRESHOLDS_FIPS_THRESH_LOW                                        (0)
`define ENTROPY_SRC_REG_MARKOV_HI_THRESHOLDS_FIPS_THRESH_MASK                                       (32'hffff)
`define ENTROPY_SRC_REG_MARKOV_HI_THRESHOLDS_BYPASS_THRESH_LOW                                      (16)
`define ENTROPY_SRC_REG_MARKOV_HI_THRESHOLDS_BYPASS_THRESH_MASK                                     (32'hffff0000)
`endif
`ifndef ENTROPY_SRC_REG_MARKOV_LO_THRESHOLDS
`define ENTROPY_SRC_REG_MARKOV_LO_THRESHOLDS                                                        (32'h4c)
`define ENTROPY_SRC_REG_MARKOV_LO_THRESHOLDS_FIPS_THRESH_LOW                                        (0)
`define ENTROPY_SRC_REG_MARKOV_LO_THRESHOLDS_FIPS_THRESH_MASK                                       (32'hffff)
`define ENTROPY_SRC_REG_MARKOV_LO_THRESHOLDS_BYPASS_THRESH_LOW                                      (16)
`define ENTROPY_SRC_REG_MARKOV_LO_THRESHOLDS_BYPASS_THRESH_MASK                                     (32'hffff0000)
`endif
`ifndef ENTROPY_SRC_REG_EXTHT_HI_THRESHOLDS
`define ENTROPY_SRC_REG_EXTHT_HI_THRESHOLDS                                                         (32'h50)
`define ENTROPY_SRC_REG_EXTHT_HI_THRESHOLDS_FIPS_THRESH_LOW                                         (0)
`define ENTROPY_SRC_REG_EXTHT_HI_THRESHOLDS_FIPS_THRESH_MASK                                        (32'hffff)
`define ENTROPY_SRC_REG_EXTHT_HI_THRESHOLDS_BYPASS_THRESH_LOW                                       (16)
`define ENTROPY_SRC_REG_EXTHT_HI_THRESHOLDS_BYPASS_THRESH_MASK                                      (32'hffff0000)
`endif
`ifndef ENTROPY_SRC_REG_EXTHT_LO_THRESHOLDS
`define ENTROPY_SRC_REG_EXTHT_LO_THRESHOLDS                                                         (32'h54)
`define ENTROPY_SRC_REG_EXTHT_LO_THRESHOLDS_FIPS_THRESH_LOW                                         (0)
`define ENTROPY_SRC_REG_EXTHT_LO_THRESHOLDS_FIPS_THRESH_MASK                                        (32'hffff)
`define ENTROPY_SRC_REG_EXTHT_LO_THRESHOLDS_BYPASS_THRESH_LOW                                       (16)
`define ENTROPY_SRC_REG_EXTHT_LO_THRESHOLDS_BYPASS_THRESH_MASK                                      (32'hffff0000)
`endif
`ifndef ENTROPY_SRC_REG_REPCNT_HI_WATERMARKS
`define ENTROPY_SRC_REG_REPCNT_HI_WATERMARKS                                                        (32'h58)
`define ENTROPY_SRC_REG_REPCNT_HI_WATERMARKS_FIPS_WATERMARK_LOW                                     (0)
`define ENTROPY_SRC_REG_REPCNT_HI_WATERMARKS_FIPS_WATERMARK_MASK                                    (32'hffff)
`define ENTROPY_SRC_REG_REPCNT_HI_WATERMARKS_BYPASS_WATERMARK_LOW                                   (16)
`define ENTROPY_SRC_REG_REPCNT_HI_WATERMARKS_BYPASS_WATERMARK_MASK                                  (32'hffff0000)
`endif
`ifndef ENTROPY_SRC_REG_REPCNTS_HI_WATERMARKS
`define ENTROPY_SRC_REG_REPCNTS_HI_WATERMARKS                                                       (32'h5c)
`define ENTROPY_SRC_REG_REPCNTS_HI_WATERMARKS_FIPS_WATERMARK_LOW                                    (0)
`define ENTROPY_SRC_REG_REPCNTS_HI_WATERMARKS_FIPS_WATERMARK_MASK                                   (32'hffff)
`define ENTROPY_SRC_REG_REPCNTS_HI_WATERMARKS_BYPASS_WATERMARK_LOW                                  (16)
`define ENTROPY_SRC_REG_REPCNTS_HI_WATERMARKS_BYPASS_WATERMARK_MASK                                 (32'hffff0000)
`endif
`ifndef ENTROPY_SRC_REG_ADAPTP_HI_WATERMARKS
`define ENTROPY_SRC_REG_ADAPTP_HI_WATERMARKS                                                        (32'h60)
`define ENTROPY_SRC_REG_ADAPTP_HI_WATERMARKS_FIPS_WATERMARK_LOW                                     (0)
`define ENTROPY_SRC_REG_ADAPTP_HI_WATERMARKS_FIPS_WATERMARK_MASK                                    (32'hffff)
`define ENTROPY_SRC_REG_ADAPTP_HI_WATERMARKS_BYPASS_WATERMARK_LOW                                   (16)
`define ENTROPY_SRC_REG_ADAPTP_HI_WATERMARKS_BYPASS_WATERMARK_MASK                                  (32'hffff0000)
`endif
`ifndef ENTROPY_SRC_REG_ADAPTP_LO_WATERMARKS
`define ENTROPY_SRC_REG_ADAPTP_LO_WATERMARKS                                                        (32'h64)
`define ENTROPY_SRC_REG_ADAPTP_LO_WATERMARKS_FIPS_WATERMARK_LOW                                     (0)
`define ENTROPY_SRC_REG_ADAPTP_LO_WATERMARKS_FIPS_WATERMARK_MASK                                    (32'hffff)
`define ENTROPY_SRC_REG_ADAPTP_LO_WATERMARKS_BYPASS_WATERMARK_LOW                                   (16)
`define ENTROPY_SRC_REG_ADAPTP_LO_WATERMARKS_BYPASS_WATERMARK_MASK                                  (32'hffff0000)
`endif
`ifndef ENTROPY_SRC_REG_EXTHT_HI_WATERMARKS
`define ENTROPY_SRC_REG_EXTHT_HI_WATERMARKS                                                         (32'h68)
`define ENTROPY_SRC_REG_EXTHT_HI_WATERMARKS_FIPS_WATERMARK_LOW                                      (0)
`define ENTROPY_SRC_REG_EXTHT_HI_WATERMARKS_FIPS_WATERMARK_MASK                                     (32'hffff)
`define ENTROPY_SRC_REG_EXTHT_HI_WATERMARKS_BYPASS_WATERMARK_LOW                                    (16)
`define ENTROPY_SRC_REG_EXTHT_HI_WATERMARKS_BYPASS_WATERMARK_MASK                                   (32'hffff0000)
`endif
`ifndef ENTROPY_SRC_REG_EXTHT_LO_WATERMARKS
`define ENTROPY_SRC_REG_EXTHT_LO_WATERMARKS                                                         (32'h6c)
`define ENTROPY_SRC_REG_EXTHT_LO_WATERMARKS_FIPS_WATERMARK_LOW                                      (0)
`define ENTROPY_SRC_REG_EXTHT_LO_WATERMARKS_FIPS_WATERMARK_MASK                                     (32'hffff)
`define ENTROPY_SRC_REG_EXTHT_LO_WATERMARKS_BYPASS_WATERMARK_LOW                                    (16)
`define ENTROPY_SRC_REG_EXTHT_LO_WATERMARKS_BYPASS_WATERMARK_MASK                                   (32'hffff0000)
`endif
`ifndef ENTROPY_SRC_REG_BUCKET_HI_WATERMARKS
`define ENTROPY_SRC_REG_BUCKET_HI_WATERMARKS                                                        (32'h70)
`define ENTROPY_SRC_REG_BUCKET_HI_WATERMARKS_FIPS_WATERMARK_LOW                                     (0)
`define ENTROPY_SRC_REG_BUCKET_HI_WATERMARKS_FIPS_WATERMARK_MASK                                    (32'hffff)
`define ENTROPY_SRC_REG_BUCKET_HI_WATERMARKS_BYPASS_WATERMARK_LOW                                   (16)
`define ENTROPY_SRC_REG_BUCKET_HI_WATERMARKS_BYPASS_WATERMARK_MASK                                  (32'hffff0000)
`endif
`ifndef ENTROPY_SRC_REG_MARKOV_HI_WATERMARKS
`define ENTROPY_SRC_REG_MARKOV_HI_WATERMARKS                                                        (32'h74)
`define ENTROPY_SRC_REG_MARKOV_HI_WATERMARKS_FIPS_WATERMARK_LOW                                     (0)
`define ENTROPY_SRC_REG_MARKOV_HI_WATERMARKS_FIPS_WATERMARK_MASK                                    (32'hffff)
`define ENTROPY_SRC_REG_MARKOV_HI_WATERMARKS_BYPASS_WATERMARK_LOW                                   (16)
`define ENTROPY_SRC_REG_MARKOV_HI_WATERMARKS_BYPASS_WATERMARK_MASK                                  (32'hffff0000)
`endif
`ifndef ENTROPY_SRC_REG_MARKOV_LO_WATERMARKS
`define ENTROPY_SRC_REG_MARKOV_LO_WATERMARKS                                                        (32'h78)
`define ENTROPY_SRC_REG_MARKOV_LO_WATERMARKS_FIPS_WATERMARK_LOW                                     (0)
`define ENTROPY_SRC_REG_MARKOV_LO_WATERMARKS_FIPS_WATERMARK_MASK                                    (32'hffff)
`define ENTROPY_SRC_REG_MARKOV_LO_WATERMARKS_BYPASS_WATERMARK_LOW                                   (16)
`define ENTROPY_SRC_REG_MARKOV_LO_WATERMARKS_BYPASS_WATERMARK_MASK                                  (32'hffff0000)
`endif
`ifndef ENTROPY_SRC_REG_REPCNT_TOTAL_FAILS
`define ENTROPY_SRC_REG_REPCNT_TOTAL_FAILS                                                          (32'h7c)
`endif
`ifndef ENTROPY_SRC_REG_REPCNTS_TOTAL_FAILS
`define ENTROPY_SRC_REG_REPCNTS_TOTAL_FAILS                                                         (32'h80)
`endif
`ifndef ENTROPY_SRC_REG_ADAPTP_HI_TOTAL_FAILS
`define ENTROPY_SRC_REG_ADAPTP_HI_TOTAL_FAILS                                                       (32'h84)
`endif
`ifndef ENTROPY_SRC_REG_ADAPTP_LO_TOTAL_FAILS
`define ENTROPY_SRC_REG_ADAPTP_LO_TOTAL_FAILS                                                       (32'h88)
`endif
`ifndef ENTROPY_SRC_REG_BUCKET_TOTAL_FAILS
`define ENTROPY_SRC_REG_BUCKET_TOTAL_FAILS                                                          (32'h8c)
`endif
`ifndef ENTROPY_SRC_REG_MARKOV_HI_TOTAL_FAILS
`define ENTROPY_SRC_REG_MARKOV_HI_TOTAL_FAILS                                                       (32'h90)
`endif
`ifndef ENTROPY_SRC_REG_MARKOV_LO_TOTAL_FAILS
`define ENTROPY_SRC_REG_MARKOV_LO_TOTAL_FAILS                                                       (32'h94)
`endif
`ifndef ENTROPY_SRC_REG_EXTHT_HI_TOTAL_FAILS
`define ENTROPY_SRC_REG_EXTHT_HI_TOTAL_FAILS                                                        (32'h98)
`endif
`ifndef ENTROPY_SRC_REG_EXTHT_LO_TOTAL_FAILS
`define ENTROPY_SRC_REG_EXTHT_LO_TOTAL_FAILS                                                        (32'h9c)
`endif
`ifndef ENTROPY_SRC_REG_ALERT_THRESHOLD
`define ENTROPY_SRC_REG_ALERT_THRESHOLD                                                             (32'ha0)
`define ENTROPY_SRC_REG_ALERT_THRESHOLD_ALERT_THRESHOLD_LOW                                         (0)
`define ENTROPY_SRC_REG_ALERT_THRESHOLD_ALERT_THRESHOLD_MASK                                        (32'hffff)
`define ENTROPY_SRC_REG_ALERT_THRESHOLD_ALERT_THRESHOLD_INV_LOW                                     (16)
`define ENTROPY_SRC_REG_ALERT_THRESHOLD_ALERT_THRESHOLD_INV_MASK                                    (32'hffff0000)
`endif
`ifndef ENTROPY_SRC_REG_ALERT_SUMMARY_FAIL_COUNTS
`define ENTROPY_SRC_REG_ALERT_SUMMARY_FAIL_COUNTS                                                   (32'ha4)
`define ENTROPY_SRC_REG_ALERT_SUMMARY_FAIL_COUNTS_ANY_FAIL_COUNT_LOW                                (0)
`define ENTROPY_SRC_REG_ALERT_SUMMARY_FAIL_COUNTS_ANY_FAIL_COUNT_MASK                               (32'hffff)
`endif
`ifndef ENTROPY_SRC_REG_ALERT_FAIL_COUNTS
`define ENTROPY_SRC_REG_ALERT_FAIL_COUNTS                                                           (32'ha8)
`define ENTROPY_SRC_REG_ALERT_FAIL_COUNTS_REPCNT_FAIL_COUNT_LOW                                     (4)
`define ENTROPY_SRC_REG_ALERT_FAIL_COUNTS_REPCNT_FAIL_COUNT_MASK                                    (32'hf0)
`define ENTROPY_SRC_REG_ALERT_FAIL_COUNTS_ADAPTP_HI_FAIL_COUNT_LOW                                  (8)
`define ENTROPY_SRC_REG_ALERT_FAIL_COUNTS_ADAPTP_HI_FAIL_COUNT_MASK                                 (32'hf00)
`define ENTROPY_SRC_REG_ALERT_FAIL_COUNTS_ADAPTP_LO_FAIL_COUNT_LOW                                  (12)
`define ENTROPY_SRC_REG_ALERT_FAIL_COUNTS_ADAPTP_LO_FAIL_COUNT_MASK                                 (32'hf000)
`define ENTROPY_SRC_REG_ALERT_FAIL_COUNTS_BUCKET_FAIL_COUNT_LOW                                     (16)
`define ENTROPY_SRC_REG_ALERT_FAIL_COUNTS_BUCKET_FAIL_COUNT_MASK                                    (32'hf0000)
`define ENTROPY_SRC_REG_ALERT_FAIL_COUNTS_MARKOV_HI_FAIL_COUNT_LOW                                  (20)
`define ENTROPY_SRC_REG_ALERT_FAIL_COUNTS_MARKOV_HI_FAIL_COUNT_MASK                                 (32'hf00000)
`define ENTROPY_SRC_REG_ALERT_FAIL_COUNTS_MARKOV_LO_FAIL_COUNT_LOW                                  (24)
`define ENTROPY_SRC_REG_ALERT_FAIL_COUNTS_MARKOV_LO_FAIL_COUNT_MASK                                 (32'hf000000)
`define ENTROPY_SRC_REG_ALERT_FAIL_COUNTS_REPCNTS_FAIL_COUNT_LOW                                    (28)
`define ENTROPY_SRC_REG_ALERT_FAIL_COUNTS_REPCNTS_FAIL_COUNT_MASK                                   (32'hf0000000)
`endif
`ifndef ENTROPY_SRC_REG_EXTHT_FAIL_COUNTS
`define ENTROPY_SRC_REG_EXTHT_FAIL_COUNTS                                                           (32'hac)
`define ENTROPY_SRC_REG_EXTHT_FAIL_COUNTS_EXTHT_HI_FAIL_COUNT_LOW                                   (0)
`define ENTROPY_SRC_REG_EXTHT_FAIL_COUNTS_EXTHT_HI_FAIL_COUNT_MASK                                  (32'hf)
`define ENTROPY_SRC_REG_EXTHT_FAIL_COUNTS_EXTHT_LO_FAIL_COUNT_LOW                                   (4)
`define ENTROPY_SRC_REG_EXTHT_FAIL_COUNTS_EXTHT_LO_FAIL_COUNT_MASK                                  (32'hf0)
`endif
`ifndef ENTROPY_SRC_REG_FW_OV_CONTROL
`define ENTROPY_SRC_REG_FW_OV_CONTROL                                                               (32'hb0)
`define ENTROPY_SRC_REG_FW_OV_CONTROL_FW_OV_MODE_LOW                                                (0)
`define ENTROPY_SRC_REG_FW_OV_CONTROL_FW_OV_MODE_MASK                                               (32'hf)
`define ENTROPY_SRC_REG_FW_OV_CONTROL_FW_OV_ENTROPY_INSERT_LOW                                      (4)
`define ENTROPY_SRC_REG_FW_OV_CONTROL_FW_OV_ENTROPY_INSERT_MASK                                     (32'hf0)
`endif
`ifndef ENTROPY_SRC_REG_FW_OV_SHA3_START
`define ENTROPY_SRC_REG_FW_OV_SHA3_START                                                            (32'hb4)
`define ENTROPY_SRC_REG_FW_OV_SHA3_START_FW_OV_INSERT_START_LOW                                     (0)
`define ENTROPY_SRC_REG_FW_OV_SHA3_START_FW_OV_INSERT_START_MASK                                    (32'hf)
`endif
`ifndef ENTROPY_SRC_REG_FW_OV_WR_FIFO_FULL
`define ENTROPY_SRC_REG_FW_OV_WR_FIFO_FULL                                                          (32'hb8)
`define ENTROPY_SRC_REG_FW_OV_WR_FIFO_FULL_FW_OV_WR_FIFO_FULL_LOW                                   (0)
`define ENTROPY_SRC_REG_FW_OV_WR_FIFO_FULL_FW_OV_WR_FIFO_FULL_MASK                                  (32'h1)
`endif
`ifndef ENTROPY_SRC_REG_FW_OV_RD_FIFO_OVERFLOW
`define ENTROPY_SRC_REG_FW_OV_RD_FIFO_OVERFLOW                                                      (32'hbc)
`define ENTROPY_SRC_REG_FW_OV_RD_FIFO_OVERFLOW_FW_OV_RD_FIFO_OVERFLOW_LOW                           (0)
`define ENTROPY_SRC_REG_FW_OV_RD_FIFO_OVERFLOW_FW_OV_RD_FIFO_OVERFLOW_MASK                          (32'h1)
`endif
`ifndef ENTROPY_SRC_REG_FW_OV_RD_DATA
`define ENTROPY_SRC_REG_FW_OV_RD_DATA                                                               (32'hc0)
`endif
`ifndef ENTROPY_SRC_REG_FW_OV_WR_DATA
`define ENTROPY_SRC_REG_FW_OV_WR_DATA                                                               (32'hc4)
`endif
`ifndef ENTROPY_SRC_REG_OBSERVE_FIFO_THRESH
`define ENTROPY_SRC_REG_OBSERVE_FIFO_THRESH                                                         (32'hc8)
`define ENTROPY_SRC_REG_OBSERVE_FIFO_THRESH_OBSERVE_FIFO_THRESH_LOW                                 (0)
`define ENTROPY_SRC_REG_OBSERVE_FIFO_THRESH_OBSERVE_FIFO_THRESH_MASK                                (32'h3f)
`endif
`ifndef ENTROPY_SRC_REG_OBSERVE_FIFO_DEPTH
`define ENTROPY_SRC_REG_OBSERVE_FIFO_DEPTH                                                          (32'hcc)
`define ENTROPY_SRC_REG_OBSERVE_FIFO_DEPTH_OBSERVE_FIFO_DEPTH_LOW                                   (0)
`define ENTROPY_SRC_REG_OBSERVE_FIFO_DEPTH_OBSERVE_FIFO_DEPTH_MASK                                  (32'h3f)
`endif
`ifndef ENTROPY_SRC_REG_DEBUG_STATUS
`define ENTROPY_SRC_REG_DEBUG_STATUS                                                                (32'hd0)
`define ENTROPY_SRC_REG_DEBUG_STATUS_ENTROPY_FIFO_DEPTH_LOW                                         (0)
`define ENTROPY_SRC_REG_DEBUG_STATUS_ENTROPY_FIFO_DEPTH_MASK                                        (32'h3)
`define ENTROPY_SRC_REG_DEBUG_STATUS_SHA3_FSM_LOW                                                   (3)
`define ENTROPY_SRC_REG_DEBUG_STATUS_SHA3_FSM_MASK                                                  (32'h38)
`define ENTROPY_SRC_REG_DEBUG_STATUS_SHA3_BLOCK_PR_LOW                                              (6)
`define ENTROPY_SRC_REG_DEBUG_STATUS_SHA3_BLOCK_PR_MASK                                             (32'h40)
`define ENTROPY_SRC_REG_DEBUG_STATUS_SHA3_SQUEEZING_LOW                                             (7)
`define ENTROPY_SRC_REG_DEBUG_STATUS_SHA3_SQUEEZING_MASK                                            (32'h80)
`define ENTROPY_SRC_REG_DEBUG_STATUS_SHA3_ABSORBED_LOW                                              (8)
`define ENTROPY_SRC_REG_DEBUG_STATUS_SHA3_ABSORBED_MASK                                             (32'h100)
`define ENTROPY_SRC_REG_DEBUG_STATUS_SHA3_ERR_LOW                                                   (9)
`define ENTROPY_SRC_REG_DEBUG_STATUS_SHA3_ERR_MASK                                                  (32'h200)
`define ENTROPY_SRC_REG_DEBUG_STATUS_MAIN_SM_IDLE_LOW                                               (16)
`define ENTROPY_SRC_REG_DEBUG_STATUS_MAIN_SM_IDLE_MASK                                              (32'h10000)
`define ENTROPY_SRC_REG_DEBUG_STATUS_MAIN_SM_BOOT_DONE_LOW                                          (17)
`define ENTROPY_SRC_REG_DEBUG_STATUS_MAIN_SM_BOOT_DONE_MASK                                         (32'h20000)
`endif
`ifndef ENTROPY_SRC_REG_RECOV_ALERT_STS
`define ENTROPY_SRC_REG_RECOV_ALERT_STS                                                             (32'hd4)
`define ENTROPY_SRC_REG_RECOV_ALERT_STS_FIPS_ENABLE_FIELD_ALERT_LOW                                 (0)
`define ENTROPY_SRC_REG_RECOV_ALERT_STS_FIPS_ENABLE_FIELD_ALERT_MASK                                (32'h1)
`define ENTROPY_SRC_REG_RECOV_ALERT_STS_ENTROPY_DATA_REG_EN_FIELD_ALERT_LOW                         (1)
`define ENTROPY_SRC_REG_RECOV_ALERT_STS_ENTROPY_DATA_REG_EN_FIELD_ALERT_MASK                        (32'h2)
`define ENTROPY_SRC_REG_RECOV_ALERT_STS_MODULE_ENABLE_FIELD_ALERT_LOW                               (2)
`define ENTROPY_SRC_REG_RECOV_ALERT_STS_MODULE_ENABLE_FIELD_ALERT_MASK                              (32'h4)
`define ENTROPY_SRC_REG_RECOV_ALERT_STS_THRESHOLD_SCOPE_FIELD_ALERT_LOW                             (3)
`define ENTROPY_SRC_REG_RECOV_ALERT_STS_THRESHOLD_SCOPE_FIELD_ALERT_MASK                            (32'h8)
`define ENTROPY_SRC_REG_RECOV_ALERT_STS_RNG_BIT_ENABLE_FIELD_ALERT_LOW                              (5)
`define ENTROPY_SRC_REG_RECOV_ALERT_STS_RNG_BIT_ENABLE_FIELD_ALERT_MASK                             (32'h20)
`define ENTROPY_SRC_REG_RECOV_ALERT_STS_FW_OV_SHA3_START_FIELD_ALERT_LOW                            (7)
`define ENTROPY_SRC_REG_RECOV_ALERT_STS_FW_OV_SHA3_START_FIELD_ALERT_MASK                           (32'h80)
`define ENTROPY_SRC_REG_RECOV_ALERT_STS_FW_OV_MODE_FIELD_ALERT_LOW                                  (8)
`define ENTROPY_SRC_REG_RECOV_ALERT_STS_FW_OV_MODE_FIELD_ALERT_MASK                                 (32'h100)
`define ENTROPY_SRC_REG_RECOV_ALERT_STS_FW_OV_ENTROPY_INSERT_FIELD_ALERT_LOW                        (9)
`define ENTROPY_SRC_REG_RECOV_ALERT_STS_FW_OV_ENTROPY_INSERT_FIELD_ALERT_MASK                       (32'h200)
`define ENTROPY_SRC_REG_RECOV_ALERT_STS_ES_ROUTE_FIELD_ALERT_LOW                                    (10)
`define ENTROPY_SRC_REG_RECOV_ALERT_STS_ES_ROUTE_FIELD_ALERT_MASK                                   (32'h400)
`define ENTROPY_SRC_REG_RECOV_ALERT_STS_ES_TYPE_FIELD_ALERT_LOW                                     (11)
`define ENTROPY_SRC_REG_RECOV_ALERT_STS_ES_TYPE_FIELD_ALERT_MASK                                    (32'h800)
`define ENTROPY_SRC_REG_RECOV_ALERT_STS_ES_MAIN_SM_ALERT_LOW                                        (12)
`define ENTROPY_SRC_REG_RECOV_ALERT_STS_ES_MAIN_SM_ALERT_MASK                                       (32'h1000)
`define ENTROPY_SRC_REG_RECOV_ALERT_STS_ES_BUS_CMP_ALERT_LOW                                        (13)
`define ENTROPY_SRC_REG_RECOV_ALERT_STS_ES_BUS_CMP_ALERT_MASK                                       (32'h2000)
`define ENTROPY_SRC_REG_RECOV_ALERT_STS_ES_THRESH_CFG_ALERT_LOW                                     (14)
`define ENTROPY_SRC_REG_RECOV_ALERT_STS_ES_THRESH_CFG_ALERT_MASK                                    (32'h4000)
`define ENTROPY_SRC_REG_RECOV_ALERT_STS_ES_FW_OV_WR_ALERT_LOW                                       (15)
`define ENTROPY_SRC_REG_RECOV_ALERT_STS_ES_FW_OV_WR_ALERT_MASK                                      (32'h8000)
`define ENTROPY_SRC_REG_RECOV_ALERT_STS_ES_FW_OV_DISABLE_ALERT_LOW                                  (16)
`define ENTROPY_SRC_REG_RECOV_ALERT_STS_ES_FW_OV_DISABLE_ALERT_MASK                                 (32'h10000)
`define ENTROPY_SRC_REG_RECOV_ALERT_STS_FIPS_FLAG_FIELD_ALERT_LOW                                   (17)
`define ENTROPY_SRC_REG_RECOV_ALERT_STS_FIPS_FLAG_FIELD_ALERT_MASK                                  (32'h20000)
`define ENTROPY_SRC_REG_RECOV_ALERT_STS_RNG_FIPS_FIELD_ALERT_LOW                                    (18)
`define ENTROPY_SRC_REG_RECOV_ALERT_STS_RNG_FIPS_FIELD_ALERT_MASK                                   (32'h40000)
`define ENTROPY_SRC_REG_RECOV_ALERT_STS_POSTHT_ENTROPY_DROP_ALERT_LOW                               (31)
`define ENTROPY_SRC_REG_RECOV_ALERT_STS_POSTHT_ENTROPY_DROP_ALERT_MASK                              (32'h80000000)
`endif
`ifndef ENTROPY_SRC_REG_ERR_CODE
`define ENTROPY_SRC_REG_ERR_CODE                                                                    (32'hd8)
`define ENTROPY_SRC_REG_ERR_CODE_SFIFO_ESRNG_ERR_LOW                                                (0)
`define ENTROPY_SRC_REG_ERR_CODE_SFIFO_ESRNG_ERR_MASK                                               (32'h1)
`define ENTROPY_SRC_REG_ERR_CODE_SFIFO_DISTR_ERR_LOW                                                (1)
`define ENTROPY_SRC_REG_ERR_CODE_SFIFO_DISTR_ERR_MASK                                               (32'h2)
`define ENTROPY_SRC_REG_ERR_CODE_SFIFO_OBSERVE_ERR_LOW                                              (2)
`define ENTROPY_SRC_REG_ERR_CODE_SFIFO_OBSERVE_ERR_MASK                                             (32'h4)
`define ENTROPY_SRC_REG_ERR_CODE_SFIFO_ESFINAL_ERR_LOW                                              (3)
`define ENTROPY_SRC_REG_ERR_CODE_SFIFO_ESFINAL_ERR_MASK                                             (32'h8)
`define ENTROPY_SRC_REG_ERR_CODE_ES_ACK_SM_ERR_LOW                                                  (20)
`define ENTROPY_SRC_REG_ERR_CODE_ES_ACK_SM_ERR_MASK                                                 (32'h100000)
`define ENTROPY_SRC_REG_ERR_CODE_ES_MAIN_SM_ERR_LOW                                                 (21)
`define ENTROPY_SRC_REG_ERR_CODE_ES_MAIN_SM_ERR_MASK                                                (32'h200000)
`define ENTROPY_SRC_REG_ERR_CODE_ES_CNTR_ERR_LOW                                                    (22)
`define ENTROPY_SRC_REG_ERR_CODE_ES_CNTR_ERR_MASK                                                   (32'h400000)
`define ENTROPY_SRC_REG_ERR_CODE_SHA3_STATE_ERR_LOW                                                 (23)
`define ENTROPY_SRC_REG_ERR_CODE_SHA3_STATE_ERR_MASK                                                (32'h800000)
`define ENTROPY_SRC_REG_ERR_CODE_SHA3_RST_STORAGE_ERR_LOW                                           (24)
`define ENTROPY_SRC_REG_ERR_CODE_SHA3_RST_STORAGE_ERR_MASK                                          (32'h1000000)
`define ENTROPY_SRC_REG_ERR_CODE_FIFO_WRITE_ERR_LOW                                                 (28)
`define ENTROPY_SRC_REG_ERR_CODE_FIFO_WRITE_ERR_MASK                                                (32'h10000000)
`define ENTROPY_SRC_REG_ERR_CODE_FIFO_READ_ERR_LOW                                                  (29)
`define ENTROPY_SRC_REG_ERR_CODE_FIFO_READ_ERR_MASK                                                 (32'h20000000)
`define ENTROPY_SRC_REG_ERR_CODE_FIFO_STATE_ERR_LOW                                                 (30)
`define ENTROPY_SRC_REG_ERR_CODE_FIFO_STATE_ERR_MASK                                                (32'h40000000)
`endif
`ifndef ENTROPY_SRC_REG_ERR_CODE_TEST
`define ENTROPY_SRC_REG_ERR_CODE_TEST                                                               (32'hdc)
`define ENTROPY_SRC_REG_ERR_CODE_TEST_ERR_CODE_TEST_LOW                                             (0)
`define ENTROPY_SRC_REG_ERR_CODE_TEST_ERR_CODE_TEST_MASK                                            (32'h1f)
`endif
`ifndef ENTROPY_SRC_REG_MAIN_SM_STATE
`define ENTROPY_SRC_REG_MAIN_SM_STATE                                                               (32'he0)
`define ENTROPY_SRC_REG_MAIN_SM_STATE_MAIN_SM_STATE_LOW                                             (0)
`define ENTROPY_SRC_REG_MAIN_SM_STATE_MAIN_SM_STATE_MASK                                            (32'h1ff)
`endif
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
`ifndef SHA512_ACC_CSR_LOCK
`define SHA512_ACC_CSR_LOCK                                                                         (32'h0)
`define SHA512_ACC_CSR_LOCK_LOCK_LOW                                                                (0)
`define SHA512_ACC_CSR_LOCK_LOCK_MASK                                                               (32'h1)
`endif
`ifndef SHA512_ACC_CSR_USER
`define SHA512_ACC_CSR_USER                                                                         (32'h4)
`endif
`ifndef SHA512_ACC_CSR_MODE
`define SHA512_ACC_CSR_MODE                                                                         (32'h8)
`define SHA512_ACC_CSR_MODE_MODE_LOW                                                                (0)
`define SHA512_ACC_CSR_MODE_MODE_MASK                                                               (32'h3)
`define SHA512_ACC_CSR_MODE_ENDIAN_TOGGLE_LOW                                                       (2)
`define SHA512_ACC_CSR_MODE_ENDIAN_TOGGLE_MASK                                                      (32'h4)
`endif
`ifndef SHA512_ACC_CSR_START_ADDRESS
`define SHA512_ACC_CSR_START_ADDRESS                                                                (32'hc)
`endif
`ifndef SHA512_ACC_CSR_DLEN
`define SHA512_ACC_CSR_DLEN                                                                         (32'h10)
`endif
`ifndef SHA512_ACC_CSR_DATAIN
`define SHA512_ACC_CSR_DATAIN                                                                       (32'h14)
`endif
`ifndef SHA512_ACC_CSR_EXECUTE
`define SHA512_ACC_CSR_EXECUTE                                                                      (32'h18)
`define SHA512_ACC_CSR_EXECUTE_EXECUTE_LOW                                                          (0)
`define SHA512_ACC_CSR_EXECUTE_EXECUTE_MASK                                                         (32'h1)
`endif
`ifndef SHA512_ACC_CSR_STATUS
`define SHA512_ACC_CSR_STATUS                                                                       (32'h1c)
`define SHA512_ACC_CSR_STATUS_VALID_LOW                                                             (0)
`define SHA512_ACC_CSR_STATUS_VALID_MASK                                                            (32'h1)
`define SHA512_ACC_CSR_STATUS_SOC_HAS_LOCK_LOW                                                      (1)
`define SHA512_ACC_CSR_STATUS_SOC_HAS_LOCK_MASK                                                     (32'h2)
`endif
`ifndef SHA512_ACC_CSR_DIGEST_0
`define SHA512_ACC_CSR_DIGEST_0                                                                     (32'h20)
`endif
`ifndef SHA512_ACC_CSR_DIGEST_1
`define SHA512_ACC_CSR_DIGEST_1                                                                     (32'h24)
`endif
`ifndef SHA512_ACC_CSR_DIGEST_2
`define SHA512_ACC_CSR_DIGEST_2                                                                     (32'h28)
`endif
`ifndef SHA512_ACC_CSR_DIGEST_3
`define SHA512_ACC_CSR_DIGEST_3                                                                     (32'h2c)
`endif
`ifndef SHA512_ACC_CSR_DIGEST_4
`define SHA512_ACC_CSR_DIGEST_4                                                                     (32'h30)
`endif
`ifndef SHA512_ACC_CSR_DIGEST_5
`define SHA512_ACC_CSR_DIGEST_5                                                                     (32'h34)
`endif
`ifndef SHA512_ACC_CSR_DIGEST_6
`define SHA512_ACC_CSR_DIGEST_6                                                                     (32'h38)
`endif
`ifndef SHA512_ACC_CSR_DIGEST_7
`define SHA512_ACC_CSR_DIGEST_7                                                                     (32'h3c)
`endif
`ifndef SHA512_ACC_CSR_DIGEST_8
`define SHA512_ACC_CSR_DIGEST_8                                                                     (32'h40)
`endif
`ifndef SHA512_ACC_CSR_DIGEST_9
`define SHA512_ACC_CSR_DIGEST_9                                                                     (32'h44)
`endif
`ifndef SHA512_ACC_CSR_DIGEST_10
`define SHA512_ACC_CSR_DIGEST_10                                                                    (32'h48)
`endif
`ifndef SHA512_ACC_CSR_DIGEST_11
`define SHA512_ACC_CSR_DIGEST_11                                                                    (32'h4c)
`endif
`ifndef SHA512_ACC_CSR_DIGEST_12
`define SHA512_ACC_CSR_DIGEST_12                                                                    (32'h50)
`endif
`ifndef SHA512_ACC_CSR_DIGEST_13
`define SHA512_ACC_CSR_DIGEST_13                                                                    (32'h54)
`endif
`ifndef SHA512_ACC_CSR_DIGEST_14
`define SHA512_ACC_CSR_DIGEST_14                                                                    (32'h58)
`endif
`ifndef SHA512_ACC_CSR_DIGEST_15
`define SHA512_ACC_CSR_DIGEST_15                                                                    (32'h5c)
`endif
`ifndef SHA512_ACC_CSR_CONTROL
`define SHA512_ACC_CSR_CONTROL                                                                      (32'h60)
`define SHA512_ACC_CSR_CONTROL_ZEROIZE_LOW                                                          (0)
`define SHA512_ACC_CSR_CONTROL_ZEROIZE_MASK                                                         (32'h1)
`endif
`ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_GLOBAL_INTR_EN_R
`define SHA512_ACC_CSR_INTR_BLOCK_RF_GLOBAL_INTR_EN_R                                               (32'h800)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_LOW                                  (0)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_MASK                                 (32'h1)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_LOW                                  (1)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_MASK                                 (32'h2)
`endif
`ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_EN_R
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_EN_R                                                (32'h804)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR0_EN_LOW                                  (0)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR0_EN_MASK                                 (32'h1)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR1_EN_LOW                                  (1)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR1_EN_MASK                                 (32'h2)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR2_EN_LOW                                  (2)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR2_EN_MASK                                 (32'h4)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR3_EN_LOW                                  (3)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR3_EN_MASK                                 (32'h8)
`endif
`ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTR_EN_R
`define SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTR_EN_R                                                (32'h808)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_CMD_DONE_EN_LOW                          (0)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_CMD_DONE_EN_MASK                         (32'h1)
`endif
`ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R                                            (32'h80c)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS_LOW                                (0)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS_MASK                               (32'h1)
`endif
`ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R
`define SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R                                            (32'h810)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS_LOW                                (0)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS_MASK                               (32'h1)
`endif
`ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R                                          (32'h814)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR0_STS_LOW                           (0)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR0_STS_MASK                          (32'h1)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR1_STS_LOW                           (1)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR1_STS_MASK                          (32'h2)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR2_STS_LOW                           (2)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR2_STS_MASK                          (32'h4)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR3_STS_LOW                           (3)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR3_STS_MASK                          (32'h8)
`endif
`ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R
`define SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R                                          (32'h818)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_LOW                   (0)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK                  (32'h1)
`endif
`ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_TRIG_R
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_TRIG_R                                              (32'h81c)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR0_TRIG_LOW                              (0)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR0_TRIG_MASK                             (32'h1)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR1_TRIG_LOW                              (1)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR1_TRIG_MASK                             (32'h2)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR2_TRIG_LOW                              (2)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR2_TRIG_MASK                             (32'h4)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR3_TRIG_LOW                              (3)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR3_TRIG_MASK                             (32'h8)
`endif
`ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R
`define SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R                                              (32'h820)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_DONE_TRIG_LOW                      (0)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_DONE_TRIG_MASK                     (32'h1)
`endif
`ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR0_INTR_COUNT_R
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR0_INTR_COUNT_R                                            (32'h900)
`endif
`ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR1_INTR_COUNT_R
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR1_INTR_COUNT_R                                            (32'h904)
`endif
`ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR2_INTR_COUNT_R
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR2_INTR_COUNT_R                                            (32'h908)
`endif
`ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR3_INTR_COUNT_R
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR3_INTR_COUNT_R                                            (32'h90c)
`endif
`ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R
`define SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R                                    (32'h980)
`endif
`ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR0_INTR_COUNT_INCR_R
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR0_INTR_COUNT_INCR_R                                       (32'ha00)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR0_INTR_COUNT_INCR_R_PULSE_LOW                             (0)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR0_INTR_COUNT_INCR_R_PULSE_MASK                            (32'h1)
`endif
`ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR1_INTR_COUNT_INCR_R
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR1_INTR_COUNT_INCR_R                                       (32'ha04)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR1_INTR_COUNT_INCR_R_PULSE_LOW                             (0)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR1_INTR_COUNT_INCR_R_PULSE_MASK                            (32'h1)
`endif
`ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R                                       (32'ha08)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R_PULSE_LOW                             (0)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R_PULSE_MASK                            (32'h1)
`endif
`ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R                                       (32'ha0c)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R_PULSE_LOW                             (0)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R_PULSE_MASK                            (32'h1)
`endif
`ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R
`define SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R                               (32'ha10)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R_PULSE_LOW                     (0)
`define SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R_PULSE_MASK                    (32'h1)
`endif
`ifndef AXI_DMA_REG_ID
`define AXI_DMA_REG_ID                                                                              (32'h0)
`endif
`ifndef AXI_DMA_REG_CAP
`define AXI_DMA_REG_CAP                                                                             (32'h4)
`define AXI_DMA_REG_CAP_FIFO_MAX_DEPTH_LOW                                                          (0)
`define AXI_DMA_REG_CAP_FIFO_MAX_DEPTH_MASK                                                         (32'hfff)
`define AXI_DMA_REG_CAP_RSVD_LOW                                                                    (12)
`define AXI_DMA_REG_CAP_RSVD_MASK                                                                   (32'hfffff000)
`endif
`ifndef AXI_DMA_REG_CTRL
`define AXI_DMA_REG_CTRL                                                                            (32'h8)
`define AXI_DMA_REG_CTRL_GO_LOW                                                                     (0)
`define AXI_DMA_REG_CTRL_GO_MASK                                                                    (32'h1)
`define AXI_DMA_REG_CTRL_FLUSH_LOW                                                                  (1)
`define AXI_DMA_REG_CTRL_FLUSH_MASK                                                                 (32'h2)
`define AXI_DMA_REG_CTRL_AES_MODE_EN_LOW                                                            (2)
`define AXI_DMA_REG_CTRL_AES_MODE_EN_MASK                                                           (32'h4)
`define AXI_DMA_REG_CTRL_AES_GCM_MODE_LOW                                                           (3)
`define AXI_DMA_REG_CTRL_AES_GCM_MODE_MASK                                                          (32'h8)
`define AXI_DMA_REG_CTRL_RSVD0_LOW                                                                  (4)
`define AXI_DMA_REG_CTRL_RSVD0_MASK                                                                 (32'hfff0)
`define AXI_DMA_REG_CTRL_RD_ROUTE_LOW                                                               (16)
`define AXI_DMA_REG_CTRL_RD_ROUTE_MASK                                                              (32'h30000)
`define AXI_DMA_REG_CTRL_RSVD1_LOW                                                                  (18)
`define AXI_DMA_REG_CTRL_RSVD1_MASK                                                                 (32'hc0000)
`define AXI_DMA_REG_CTRL_RD_FIXED_LOW                                                               (20)
`define AXI_DMA_REG_CTRL_RD_FIXED_MASK                                                              (32'h100000)
`define AXI_DMA_REG_CTRL_RSVD2_LOW                                                                  (21)
`define AXI_DMA_REG_CTRL_RSVD2_MASK                                                                 (32'he00000)
`define AXI_DMA_REG_CTRL_WR_ROUTE_LOW                                                               (24)
`define AXI_DMA_REG_CTRL_WR_ROUTE_MASK                                                              (32'h7000000)
`define AXI_DMA_REG_CTRL_RSVD3_LOW                                                                  (27)
`define AXI_DMA_REG_CTRL_RSVD3_MASK                                                                 (32'h8000000)
`define AXI_DMA_REG_CTRL_WR_FIXED_LOW                                                               (28)
`define AXI_DMA_REG_CTRL_WR_FIXED_MASK                                                              (32'h10000000)
`define AXI_DMA_REG_CTRL_RSVD4_LOW                                                                  (29)
`define AXI_DMA_REG_CTRL_RSVD4_MASK                                                                 (32'he0000000)
`endif
`ifndef AXI_DMA_REG_STATUS0
`define AXI_DMA_REG_STATUS0                                                                         (32'hc)
`define AXI_DMA_REG_STATUS0_BUSY_LOW                                                                (0)
`define AXI_DMA_REG_STATUS0_BUSY_MASK                                                               (32'h1)
`define AXI_DMA_REG_STATUS0_ERROR_LOW                                                               (1)
`define AXI_DMA_REG_STATUS0_ERROR_MASK                                                              (32'h2)
`define AXI_DMA_REG_STATUS0_RSVD0_LOW                                                               (2)
`define AXI_DMA_REG_STATUS0_RSVD0_MASK                                                              (32'hc)
`define AXI_DMA_REG_STATUS0_FIFO_DEPTH_LOW                                                          (4)
`define AXI_DMA_REG_STATUS0_FIFO_DEPTH_MASK                                                         (32'hfff0)
`define AXI_DMA_REG_STATUS0_AXI_DMA_FSM_PS_LOW                                                      (16)
`define AXI_DMA_REG_STATUS0_AXI_DMA_FSM_PS_MASK                                                     (32'h30000)
`define AXI_DMA_REG_STATUS0_PAYLOAD_AVAILABLE_LOW                                                   (18)
`define AXI_DMA_REG_STATUS0_PAYLOAD_AVAILABLE_MASK                                                  (32'h40000)
`define AXI_DMA_REG_STATUS0_IMAGE_ACTIVATED_LOW                                                     (19)
`define AXI_DMA_REG_STATUS0_IMAGE_ACTIVATED_MASK                                                    (32'h80000)
`define AXI_DMA_REG_STATUS0_AXI_DMA_AES_FSM_PS_LOW                                                  (20)
`define AXI_DMA_REG_STATUS0_AXI_DMA_AES_FSM_PS_MASK                                                 (32'hf00000)
`define AXI_DMA_REG_STATUS0_RSVD1_LOW                                                               (24)
`define AXI_DMA_REG_STATUS0_RSVD1_MASK                                                              (32'hff000000)
`endif
`ifndef AXI_DMA_REG_STATUS1
`define AXI_DMA_REG_STATUS1                                                                         (32'h10)
`endif
`ifndef AXI_DMA_REG_SRC_ADDR_L
`define AXI_DMA_REG_SRC_ADDR_L                                                                      (32'h14)
`endif
`ifndef AXI_DMA_REG_SRC_ADDR_H
`define AXI_DMA_REG_SRC_ADDR_H                                                                      (32'h18)
`endif
`ifndef AXI_DMA_REG_DST_ADDR_L
`define AXI_DMA_REG_DST_ADDR_L                                                                      (32'h1c)
`endif
`ifndef AXI_DMA_REG_DST_ADDR_H
`define AXI_DMA_REG_DST_ADDR_H                                                                      (32'h20)
`endif
`ifndef AXI_DMA_REG_BYTE_COUNT
`define AXI_DMA_REG_BYTE_COUNT                                                                      (32'h24)
`endif
`ifndef AXI_DMA_REG_BLOCK_SIZE
`define AXI_DMA_REG_BLOCK_SIZE                                                                      (32'h28)
`define AXI_DMA_REG_BLOCK_SIZE_SIZE_LOW                                                             (0)
`define AXI_DMA_REG_BLOCK_SIZE_SIZE_MASK                                                            (32'hfff)
`define AXI_DMA_REG_BLOCK_SIZE_RSVD_LOW                                                             (12)
`define AXI_DMA_REG_BLOCK_SIZE_RSVD_MASK                                                            (32'hfffff000)
`endif
`ifndef AXI_DMA_REG_WRITE_DATA
`define AXI_DMA_REG_WRITE_DATA                                                                      (32'h2c)
`endif
`ifndef AXI_DMA_REG_READ_DATA
`define AXI_DMA_REG_READ_DATA                                                                       (32'h30)
`endif
`ifndef AXI_DMA_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R
`define AXI_DMA_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R                                                  (32'h800)
`define AXI_DMA_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_LOW                                     (0)
`define AXI_DMA_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_MASK                                    (32'h1)
`define AXI_DMA_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_LOW                                     (1)
`define AXI_DMA_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_MASK                                    (32'h2)
`endif
`ifndef AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R                                                   (32'h804)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_CMD_DEC_EN_LOW                              (0)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_CMD_DEC_EN_MASK                             (32'h1)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_AXI_RD_EN_LOW                               (1)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_AXI_RD_EN_MASK                              (32'h2)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_AXI_WR_EN_LOW                               (2)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_AXI_WR_EN_MASK                              (32'h4)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_MBOX_LOCK_EN_LOW                            (3)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_MBOX_LOCK_EN_MASK                           (32'h8)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_SHA_LOCK_EN_LOW                             (4)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_SHA_LOCK_EN_MASK                            (32'h10)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_FIFO_OFLOW_EN_LOW                           (5)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_FIFO_OFLOW_EN_MASK                          (32'h20)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_FIFO_UFLOW_EN_LOW                           (6)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_FIFO_UFLOW_EN_MASK                          (32'h40)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_AES_CIF_EN_LOW                              (7)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_AES_CIF_EN_MASK                             (32'h80)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_KV_RD_EN_LOW                                (8)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_KV_RD_EN_MASK                               (32'h100)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_KV_RD_LARGE_EN_LOW                          (9)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_KV_RD_LARGE_EN_MASK                         (32'h200)
`endif
`ifndef AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R
`define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R                                                   (32'h808)
`define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_TXN_DONE_EN_LOW                             (0)
`define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_TXN_DONE_EN_MASK                            (32'h1)
`define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_FIFO_EMPTY_EN_LOW                           (1)
`define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_FIFO_EMPTY_EN_MASK                          (32'h2)
`define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_FIFO_NOT_EMPTY_EN_LOW                       (2)
`define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_FIFO_NOT_EMPTY_EN_MASK                      (32'h4)
`define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_FIFO_FULL_EN_LOW                            (3)
`define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_FIFO_FULL_EN_MASK                           (32'h8)
`define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_FIFO_NOT_FULL_EN_LOW                        (4)
`define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_FIFO_NOT_FULL_EN_MASK                       (32'h10)
`endif
`ifndef AXI_DMA_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R                                               (32'h80c)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS_LOW                                   (0)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS_MASK                                  (32'h1)
`endif
`ifndef AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R
`define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R                                               (32'h810)
`define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS_LOW                                   (0)
`define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS_MASK                                  (32'h1)
`endif
`ifndef AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R                                             (32'h814)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_CMD_DEC_STS_LOW                       (0)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_CMD_DEC_STS_MASK                      (32'h1)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_AXI_RD_STS_LOW                        (1)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_AXI_RD_STS_MASK                       (32'h2)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_AXI_WR_STS_LOW                        (2)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_AXI_WR_STS_MASK                       (32'h4)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_MBOX_LOCK_STS_LOW                     (3)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_MBOX_LOCK_STS_MASK                    (32'h8)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_SHA_LOCK_STS_LOW                      (4)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_SHA_LOCK_STS_MASK                     (32'h10)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_FIFO_OFLOW_STS_LOW                    (5)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_FIFO_OFLOW_STS_MASK                   (32'h20)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_FIFO_UFLOW_STS_LOW                    (6)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_FIFO_UFLOW_STS_MASK                   (32'h40)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_AES_CIF_STS_LOW                       (7)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_AES_CIF_STS_MASK                      (32'h80)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_KV_RD_STS_LOW                         (8)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_KV_RD_STS_MASK                        (32'h100)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_KV_RD_LARGE_STS_LOW                   (9)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_KV_RD_LARGE_STS_MASK                  (32'h200)
`endif
`ifndef AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R
`define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R                                             (32'h818)
`define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_TXN_DONE_STS_LOW                      (0)
`define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_TXN_DONE_STS_MASK                     (32'h1)
`define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_FIFO_EMPTY_STS_LOW                    (1)
`define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_FIFO_EMPTY_STS_MASK                   (32'h2)
`define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_FIFO_NOT_EMPTY_STS_LOW                (2)
`define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_FIFO_NOT_EMPTY_STS_MASK               (32'h4)
`define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_FIFO_FULL_STS_LOW                     (3)
`define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_FIFO_FULL_STS_MASK                    (32'h8)
`define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_FIFO_NOT_FULL_STS_LOW                 (4)
`define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_FIFO_NOT_FULL_STS_MASK                (32'h10)
`endif
`ifndef AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R                                                 (32'h81c)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_CMD_DEC_TRIG_LOW                          (0)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_CMD_DEC_TRIG_MASK                         (32'h1)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_AXI_RD_TRIG_LOW                           (1)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_AXI_RD_TRIG_MASK                          (32'h2)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_AXI_WR_TRIG_LOW                           (2)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_AXI_WR_TRIG_MASK                          (32'h4)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_MBOX_LOCK_TRIG_LOW                        (3)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_MBOX_LOCK_TRIG_MASK                       (32'h8)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_SHA_LOCK_TRIG_LOW                         (4)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_SHA_LOCK_TRIG_MASK                        (32'h10)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_FIFO_OFLOW_TRIG_LOW                       (5)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_FIFO_OFLOW_TRIG_MASK                      (32'h20)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_FIFO_UFLOW_TRIG_LOW                       (6)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_FIFO_UFLOW_TRIG_MASK                      (32'h40)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_AES_CIF_TRIG_LOW                          (7)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_AES_CIF_TRIG_MASK                         (32'h80)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_KV_RD_TRIG_LOW                            (8)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_KV_RD_TRIG_MASK                           (32'h100)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_KV_RD_LARGE_TRIG_LOW                      (9)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_KV_RD_LARGE_TRIG_MASK                     (32'h200)
`endif
`ifndef AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R
`define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R                                                 (32'h820)
`define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_TXN_DONE_TRIG_LOW                         (0)
`define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_TXN_DONE_TRIG_MASK                        (32'h1)
`define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_FIFO_EMPTY_TRIG_LOW                       (1)
`define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_FIFO_EMPTY_TRIG_MASK                      (32'h2)
`define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_FIFO_NOT_EMPTY_TRIG_LOW                   (2)
`define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_FIFO_NOT_EMPTY_TRIG_MASK                  (32'h4)
`define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_FIFO_FULL_TRIG_LOW                        (3)
`define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_FIFO_FULL_TRIG_MASK                       (32'h8)
`define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_FIFO_NOT_FULL_TRIG_LOW                    (4)
`define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_FIFO_NOT_FULL_TRIG_MASK                   (32'h10)
`endif
`ifndef AXI_DMA_REG_INTR_BLOCK_RF_ERROR_CMD_DEC_INTR_COUNT_R
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_CMD_DEC_INTR_COUNT_R                                        (32'h900)
`endif
`ifndef AXI_DMA_REG_INTR_BLOCK_RF_ERROR_AXI_RD_INTR_COUNT_R
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_AXI_RD_INTR_COUNT_R                                         (32'h904)
`endif
`ifndef AXI_DMA_REG_INTR_BLOCK_RF_ERROR_AXI_WR_INTR_COUNT_R
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_AXI_WR_INTR_COUNT_R                                         (32'h908)
`endif
`ifndef AXI_DMA_REG_INTR_BLOCK_RF_ERROR_MBOX_LOCK_INTR_COUNT_R
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_MBOX_LOCK_INTR_COUNT_R                                      (32'h90c)
`endif
`ifndef AXI_DMA_REG_INTR_BLOCK_RF_ERROR_SHA_LOCK_INTR_COUNT_R
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_SHA_LOCK_INTR_COUNT_R                                       (32'h910)
`endif
`ifndef AXI_DMA_REG_INTR_BLOCK_RF_ERROR_FIFO_OFLOW_INTR_COUNT_R
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_FIFO_OFLOW_INTR_COUNT_R                                     (32'h914)
`endif
`ifndef AXI_DMA_REG_INTR_BLOCK_RF_ERROR_FIFO_UFLOW_INTR_COUNT_R
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_FIFO_UFLOW_INTR_COUNT_R                                     (32'h918)
`endif
`ifndef AXI_DMA_REG_INTR_BLOCK_RF_ERROR_AES_CIF_INTR_COUNT_R
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_AES_CIF_INTR_COUNT_R                                        (32'h91c)
`endif
`ifndef AXI_DMA_REG_INTR_BLOCK_RF_ERROR_KV_RD_INTR_COUNT_R
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_KV_RD_INTR_COUNT_R                                          (32'h920)
`endif
`ifndef AXI_DMA_REG_INTR_BLOCK_RF_ERROR_KV_RD_LARGE_INTR_COUNT_R
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_KV_RD_LARGE_INTR_COUNT_R                                    (32'h924)
`endif
`ifndef AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_TXN_DONE_INTR_COUNT_R
`define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_TXN_DONE_INTR_COUNT_R                                       (32'h980)
`endif
`ifndef AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_FIFO_EMPTY_INTR_COUNT_R
`define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_FIFO_EMPTY_INTR_COUNT_R                                     (32'h984)
`endif
`ifndef AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_FIFO_NOT_EMPTY_INTR_COUNT_R
`define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_FIFO_NOT_EMPTY_INTR_COUNT_R                                 (32'h988)
`endif
`ifndef AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_FIFO_FULL_INTR_COUNT_R
`define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_FIFO_FULL_INTR_COUNT_R                                      (32'h98c)
`endif
`ifndef AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_FIFO_NOT_FULL_INTR_COUNT_R
`define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_FIFO_NOT_FULL_INTR_COUNT_R                                  (32'h990)
`endif
`ifndef AXI_DMA_REG_INTR_BLOCK_RF_ERROR_CMD_DEC_INTR_COUNT_INCR_R
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_CMD_DEC_INTR_COUNT_INCR_R                                   (32'ha00)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_CMD_DEC_INTR_COUNT_INCR_R_PULSE_LOW                         (0)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_CMD_DEC_INTR_COUNT_INCR_R_PULSE_MASK                        (32'h1)
`endif
`ifndef AXI_DMA_REG_INTR_BLOCK_RF_ERROR_AXI_RD_INTR_COUNT_INCR_R
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_AXI_RD_INTR_COUNT_INCR_R                                    (32'ha04)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_AXI_RD_INTR_COUNT_INCR_R_PULSE_LOW                          (0)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_AXI_RD_INTR_COUNT_INCR_R_PULSE_MASK                         (32'h1)
`endif
`ifndef AXI_DMA_REG_INTR_BLOCK_RF_ERROR_AXI_WR_INTR_COUNT_INCR_R
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_AXI_WR_INTR_COUNT_INCR_R                                    (32'ha08)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_AXI_WR_INTR_COUNT_INCR_R_PULSE_LOW                          (0)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_AXI_WR_INTR_COUNT_INCR_R_PULSE_MASK                         (32'h1)
`endif
`ifndef AXI_DMA_REG_INTR_BLOCK_RF_ERROR_MBOX_LOCK_INTR_COUNT_INCR_R
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_MBOX_LOCK_INTR_COUNT_INCR_R                                 (32'ha0c)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_MBOX_LOCK_INTR_COUNT_INCR_R_PULSE_LOW                       (0)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_MBOX_LOCK_INTR_COUNT_INCR_R_PULSE_MASK                      (32'h1)
`endif
`ifndef AXI_DMA_REG_INTR_BLOCK_RF_ERROR_SHA_LOCK_INTR_COUNT_INCR_R
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_SHA_LOCK_INTR_COUNT_INCR_R                                  (32'ha10)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_SHA_LOCK_INTR_COUNT_INCR_R_PULSE_LOW                        (0)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_SHA_LOCK_INTR_COUNT_INCR_R_PULSE_MASK                       (32'h1)
`endif
`ifndef AXI_DMA_REG_INTR_BLOCK_RF_ERROR_FIFO_OFLOW_INTR_COUNT_INCR_R
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_FIFO_OFLOW_INTR_COUNT_INCR_R                                (32'ha14)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_FIFO_OFLOW_INTR_COUNT_INCR_R_PULSE_LOW                      (0)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_FIFO_OFLOW_INTR_COUNT_INCR_R_PULSE_MASK                     (32'h1)
`endif
`ifndef AXI_DMA_REG_INTR_BLOCK_RF_ERROR_FIFO_UFLOW_INTR_COUNT_INCR_R
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_FIFO_UFLOW_INTR_COUNT_INCR_R                                (32'ha18)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_FIFO_UFLOW_INTR_COUNT_INCR_R_PULSE_LOW                      (0)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_FIFO_UFLOW_INTR_COUNT_INCR_R_PULSE_MASK                     (32'h1)
`endif
`ifndef AXI_DMA_REG_INTR_BLOCK_RF_ERROR_AES_CIF_INTR_COUNT_INCR_R
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_AES_CIF_INTR_COUNT_INCR_R                                   (32'ha1c)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_AES_CIF_INTR_COUNT_INCR_R_PULSE_LOW                         (0)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_AES_CIF_INTR_COUNT_INCR_R_PULSE_MASK                        (32'h1)
`endif
`ifndef AXI_DMA_REG_INTR_BLOCK_RF_ERROR_KV_RD_INTR_COUNT_INCR_R
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_KV_RD_INTR_COUNT_INCR_R                                     (32'ha20)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_KV_RD_INTR_COUNT_INCR_R_PULSE_LOW                           (0)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_KV_RD_INTR_COUNT_INCR_R_PULSE_MASK                          (32'h1)
`endif
`ifndef AXI_DMA_REG_INTR_BLOCK_RF_ERROR_KV_RD_LARGE_INTR_COUNT_INCR_R
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_KV_RD_LARGE_INTR_COUNT_INCR_R                               (32'ha24)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_KV_RD_LARGE_INTR_COUNT_INCR_R_PULSE_LOW                     (0)
`define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_KV_RD_LARGE_INTR_COUNT_INCR_R_PULSE_MASK                    (32'h1)
`endif
`ifndef AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_TXN_DONE_INTR_COUNT_INCR_R
`define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_TXN_DONE_INTR_COUNT_INCR_R                                  (32'ha28)
`define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_TXN_DONE_INTR_COUNT_INCR_R_PULSE_LOW                        (0)
`define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_TXN_DONE_INTR_COUNT_INCR_R_PULSE_MASK                       (32'h1)
`endif
`ifndef AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_FIFO_EMPTY_INTR_COUNT_INCR_R
`define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_FIFO_EMPTY_INTR_COUNT_INCR_R                                (32'ha2c)
`define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_FIFO_EMPTY_INTR_COUNT_INCR_R_PULSE_LOW                      (0)
`define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_FIFO_EMPTY_INTR_COUNT_INCR_R_PULSE_MASK                     (32'h1)
`endif
`ifndef AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_FIFO_NOT_EMPTY_INTR_COUNT_INCR_R
`define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_FIFO_NOT_EMPTY_INTR_COUNT_INCR_R                            (32'ha30)
`define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_FIFO_NOT_EMPTY_INTR_COUNT_INCR_R_PULSE_LOW                  (0)
`define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_FIFO_NOT_EMPTY_INTR_COUNT_INCR_R_PULSE_MASK                 (32'h1)
`endif
`ifndef AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_FIFO_FULL_INTR_COUNT_INCR_R
`define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_FIFO_FULL_INTR_COUNT_INCR_R                                 (32'ha34)
`define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_FIFO_FULL_INTR_COUNT_INCR_R_PULSE_LOW                       (0)
`define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_FIFO_FULL_INTR_COUNT_INCR_R_PULSE_MASK                      (32'h1)
`endif
`ifndef AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_FIFO_NOT_FULL_INTR_COUNT_INCR_R
`define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_FIFO_NOT_FULL_INTR_COUNT_INCR_R                             (32'ha38)
`define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_FIFO_NOT_FULL_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
`define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_FIFO_NOT_FULL_INTR_COUNT_INCR_R_PULSE_MASK                  (32'h1)
`endif
`ifndef SOC_IFC_REG_CPTRA_HW_ERROR_FATAL
`define SOC_IFC_REG_CPTRA_HW_ERROR_FATAL                                                            (32'h0)
`define SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_ICCM_ECC_UNC_LOW                                           (0)
`define SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_ICCM_ECC_UNC_MASK                                          (32'h1)
`define SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_DCCM_ECC_UNC_LOW                                           (1)
`define SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_DCCM_ECC_UNC_MASK                                          (32'h2)
`define SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_NMI_PIN_LOW                                                (2)
`define SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_NMI_PIN_MASK                                               (32'h4)
`define SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_CRYPTO_ERR_LOW                                             (3)
`define SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_CRYPTO_ERR_MASK                                            (32'h8)
`define SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_RSVD_LOW                                                   (4)
`define SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_RSVD_MASK                                                  (32'hfffffff0)
`endif
`ifndef SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL
`define SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL                                                        (32'h4)
`define SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL_MBOX_PROT_NO_LOCK_LOW                                  (0)
`define SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL_MBOX_PROT_NO_LOCK_MASK                                 (32'h1)
`define SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL_MBOX_PROT_OOO_LOW                                      (1)
`define SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL_MBOX_PROT_OOO_MASK                                     (32'h2)
`define SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL_MBOX_ECC_UNC_LOW                                       (2)
`define SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL_MBOX_ECC_UNC_MASK                                      (32'h4)
`define SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL_RSVD_LOW                                               (3)
`define SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL_RSVD_MASK                                              (32'hfffffff8)
`endif
`ifndef SOC_IFC_REG_CPTRA_FW_ERROR_FATAL
`define SOC_IFC_REG_CPTRA_FW_ERROR_FATAL                                                            (32'h8)
`endif
`ifndef SOC_IFC_REG_CPTRA_FW_ERROR_NON_FATAL
`define SOC_IFC_REG_CPTRA_FW_ERROR_NON_FATAL                                                        (32'hc)
`endif
`ifndef SOC_IFC_REG_CPTRA_HW_ERROR_ENC
`define SOC_IFC_REG_CPTRA_HW_ERROR_ENC                                                              (32'h10)
`endif
`ifndef SOC_IFC_REG_CPTRA_FW_ERROR_ENC
`define SOC_IFC_REG_CPTRA_FW_ERROR_ENC                                                              (32'h14)
`endif
`ifndef SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_0
`define SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_0                                                  (32'h18)
`endif
`ifndef SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_1
`define SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_1                                                  (32'h1c)
`endif
`ifndef SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_2
`define SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_2                                                  (32'h20)
`endif
`ifndef SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_3
`define SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_3                                                  (32'h24)
`endif
`ifndef SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_4
`define SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_4                                                  (32'h28)
`endif
`ifndef SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_5
`define SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_5                                                  (32'h2c)
`endif
`ifndef SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_6
`define SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_6                                                  (32'h30)
`endif
`ifndef SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_7
`define SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_7                                                  (32'h34)
`endif
`ifndef SOC_IFC_REG_CPTRA_BOOT_STATUS
`define SOC_IFC_REG_CPTRA_BOOT_STATUS                                                               (32'h38)
`endif
`ifndef SOC_IFC_REG_CPTRA_FLOW_STATUS
`define SOC_IFC_REG_CPTRA_FLOW_STATUS                                                               (32'h3c)
`define SOC_IFC_REG_CPTRA_FLOW_STATUS_STATUS_LOW                                                    (0)
`define SOC_IFC_REG_CPTRA_FLOW_STATUS_STATUS_MASK                                                   (32'hffffff)
`define SOC_IFC_REG_CPTRA_FLOW_STATUS_IDEVID_CSR_READY_LOW                                          (24)
`define SOC_IFC_REG_CPTRA_FLOW_STATUS_IDEVID_CSR_READY_MASK                                         (32'h1000000)
`define SOC_IFC_REG_CPTRA_FLOW_STATUS_BOOT_FSM_PS_LOW                                               (25)
`define SOC_IFC_REG_CPTRA_FLOW_STATUS_BOOT_FSM_PS_MASK                                              (32'he000000)
`define SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_MB_PROCESSING_LOW                                   (28)
`define SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_MB_PROCESSING_MASK                                  (32'h10000000)
`define SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_RUNTIME_LOW                                         (29)
`define SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_RUNTIME_MASK                                        (32'h20000000)
`define SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_FUSES_LOW                                           (30)
`define SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_FUSES_MASK                                          (32'h40000000)
`define SOC_IFC_REG_CPTRA_FLOW_STATUS_MAILBOX_FLOW_DONE_LOW                                         (31)
`define SOC_IFC_REG_CPTRA_FLOW_STATUS_MAILBOX_FLOW_DONE_MASK                                        (32'h80000000)
`endif
`ifndef SOC_IFC_REG_CPTRA_RESET_REASON
`define SOC_IFC_REG_CPTRA_RESET_REASON                                                              (32'h40)
`define SOC_IFC_REG_CPTRA_RESET_REASON_FW_UPD_RESET_LOW                                             (0)
`define SOC_IFC_REG_CPTRA_RESET_REASON_FW_UPD_RESET_MASK                                            (32'h1)
`define SOC_IFC_REG_CPTRA_RESET_REASON_WARM_RESET_LOW                                               (1)
`define SOC_IFC_REG_CPTRA_RESET_REASON_WARM_RESET_MASK                                              (32'h2)
`endif
`ifndef SOC_IFC_REG_CPTRA_SECURITY_STATE
`define SOC_IFC_REG_CPTRA_SECURITY_STATE                                                            (32'h44)
`define SOC_IFC_REG_CPTRA_SECURITY_STATE_DEVICE_LIFECYCLE_LOW                                       (0)
`define SOC_IFC_REG_CPTRA_SECURITY_STATE_DEVICE_LIFECYCLE_MASK                                      (32'h3)
`define SOC_IFC_REG_CPTRA_SECURITY_STATE_DEBUG_LOCKED_LOW                                           (2)
`define SOC_IFC_REG_CPTRA_SECURITY_STATE_DEBUG_LOCKED_MASK                                          (32'h4)
`define SOC_IFC_REG_CPTRA_SECURITY_STATE_SCAN_MODE_LOW                                              (3)
`define SOC_IFC_REG_CPTRA_SECURITY_STATE_SCAN_MODE_MASK                                             (32'h8)
`define SOC_IFC_REG_CPTRA_SECURITY_STATE_RSVD_LOW                                                   (4)
`define SOC_IFC_REG_CPTRA_SECURITY_STATE_RSVD_MASK                                                  (32'hfffffff0)
`endif
`ifndef SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_0
`define SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_0                                                     (32'h48)
`endif
`ifndef SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_1
`define SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_1                                                     (32'h4c)
`endif
`ifndef SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_2
`define SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_2                                                     (32'h50)
`endif
`ifndef SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_3
`define SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_3                                                     (32'h54)
`endif
`ifndef SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_4
`define SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_4                                                     (32'h58)
`endif
`ifndef SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_0
`define SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_0                                                      (32'h5c)
`define SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_0_LOCK_LOW                                             (0)
`define SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_0_LOCK_MASK                                            (32'h1)
`endif
`ifndef SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_1
`define SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_1                                                      (32'h60)
`define SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_1_LOCK_LOW                                             (0)
`define SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_1_LOCK_MASK                                            (32'h1)
`endif
`ifndef SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_2
`define SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_2                                                      (32'h64)
`define SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_2_LOCK_LOW                                             (0)
`define SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_2_LOCK_MASK                                            (32'h1)
`endif
`ifndef SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_3
`define SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_3                                                      (32'h68)
`define SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_3_LOCK_LOW                                             (0)
`define SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_3_LOCK_MASK                                            (32'h1)
`endif
`ifndef SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_4
`define SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_4                                                      (32'h6c)
`define SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_4_LOCK_LOW                                             (0)
`define SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_4_LOCK_MASK                                            (32'h1)
`endif
`ifndef SOC_IFC_REG_CPTRA_TRNG_VALID_AXI_USER
`define SOC_IFC_REG_CPTRA_TRNG_VALID_AXI_USER                                                       (32'h70)
`endif
`ifndef SOC_IFC_REG_CPTRA_TRNG_AXI_USER_LOCK
`define SOC_IFC_REG_CPTRA_TRNG_AXI_USER_LOCK                                                        (32'h74)
`define SOC_IFC_REG_CPTRA_TRNG_AXI_USER_LOCK_LOCK_LOW                                               (0)
`define SOC_IFC_REG_CPTRA_TRNG_AXI_USER_LOCK_LOCK_MASK                                              (32'h1)
`endif
`ifndef SOC_IFC_REG_CPTRA_TRNG_DATA_0
`define SOC_IFC_REG_CPTRA_TRNG_DATA_0                                                               (32'h78)
`endif
`ifndef SOC_IFC_REG_CPTRA_TRNG_DATA_1
`define SOC_IFC_REG_CPTRA_TRNG_DATA_1                                                               (32'h7c)
`endif
`ifndef SOC_IFC_REG_CPTRA_TRNG_DATA_2
`define SOC_IFC_REG_CPTRA_TRNG_DATA_2                                                               (32'h80)
`endif
`ifndef SOC_IFC_REG_CPTRA_TRNG_DATA_3
`define SOC_IFC_REG_CPTRA_TRNG_DATA_3                                                               (32'h84)
`endif
`ifndef SOC_IFC_REG_CPTRA_TRNG_DATA_4
`define SOC_IFC_REG_CPTRA_TRNG_DATA_4                                                               (32'h88)
`endif
`ifndef SOC_IFC_REG_CPTRA_TRNG_DATA_5
`define SOC_IFC_REG_CPTRA_TRNG_DATA_5                                                               (32'h8c)
`endif
`ifndef SOC_IFC_REG_CPTRA_TRNG_DATA_6
`define SOC_IFC_REG_CPTRA_TRNG_DATA_6                                                               (32'h90)
`endif
`ifndef SOC_IFC_REG_CPTRA_TRNG_DATA_7
`define SOC_IFC_REG_CPTRA_TRNG_DATA_7                                                               (32'h94)
`endif
`ifndef SOC_IFC_REG_CPTRA_TRNG_DATA_8
`define SOC_IFC_REG_CPTRA_TRNG_DATA_8                                                               (32'h98)
`endif
`ifndef SOC_IFC_REG_CPTRA_TRNG_DATA_9
`define SOC_IFC_REG_CPTRA_TRNG_DATA_9                                                               (32'h9c)
`endif
`ifndef SOC_IFC_REG_CPTRA_TRNG_DATA_10
`define SOC_IFC_REG_CPTRA_TRNG_DATA_10                                                              (32'ha0)
`endif
`ifndef SOC_IFC_REG_CPTRA_TRNG_DATA_11
`define SOC_IFC_REG_CPTRA_TRNG_DATA_11                                                              (32'ha4)
`endif
`ifndef SOC_IFC_REG_CPTRA_TRNG_CTRL
`define SOC_IFC_REG_CPTRA_TRNG_CTRL                                                                 (32'ha8)
`define SOC_IFC_REG_CPTRA_TRNG_CTRL_CLEAR_LOW                                                       (0)
`define SOC_IFC_REG_CPTRA_TRNG_CTRL_CLEAR_MASK                                                      (32'h1)
`endif
`ifndef SOC_IFC_REG_CPTRA_TRNG_STATUS
`define SOC_IFC_REG_CPTRA_TRNG_STATUS                                                               (32'hac)
`define SOC_IFC_REG_CPTRA_TRNG_STATUS_DATA_REQ_LOW                                                  (0)
`define SOC_IFC_REG_CPTRA_TRNG_STATUS_DATA_REQ_MASK                                                 (32'h1)
`define SOC_IFC_REG_CPTRA_TRNG_STATUS_DATA_WR_DONE_LOW                                              (1)
`define SOC_IFC_REG_CPTRA_TRNG_STATUS_DATA_WR_DONE_MASK                                             (32'h2)
`endif
`ifndef SOC_IFC_REG_CPTRA_FUSE_WR_DONE
`define SOC_IFC_REG_CPTRA_FUSE_WR_DONE                                                              (32'hb0)
`define SOC_IFC_REG_CPTRA_FUSE_WR_DONE_DONE_LOW                                                     (0)
`define SOC_IFC_REG_CPTRA_FUSE_WR_DONE_DONE_MASK                                                    (32'h1)
`endif
`ifndef SOC_IFC_REG_CPTRA_TIMER_CONFIG
`define SOC_IFC_REG_CPTRA_TIMER_CONFIG                                                              (32'hb4)
`endif
`ifndef SOC_IFC_REG_CPTRA_BOOTFSM_GO
`define SOC_IFC_REG_CPTRA_BOOTFSM_GO                                                                (32'hb8)
`define SOC_IFC_REG_CPTRA_BOOTFSM_GO_GO_LOW                                                         (0)
`define SOC_IFC_REG_CPTRA_BOOTFSM_GO_GO_MASK                                                        (32'h1)
`endif
`ifndef SOC_IFC_REG_CPTRA_DBG_MANUF_SERVICE_REG
`define SOC_IFC_REG_CPTRA_DBG_MANUF_SERVICE_REG                                                     (32'hbc)
`endif
`ifndef SOC_IFC_REG_CPTRA_CLK_GATING_EN
`define SOC_IFC_REG_CPTRA_CLK_GATING_EN                                                             (32'hc0)
`define SOC_IFC_REG_CPTRA_CLK_GATING_EN_CLK_GATING_EN_LOW                                           (0)
`define SOC_IFC_REG_CPTRA_CLK_GATING_EN_CLK_GATING_EN_MASK                                          (32'h1)
`endif
`ifndef SOC_IFC_REG_CPTRA_GENERIC_INPUT_WIRES_0
`define SOC_IFC_REG_CPTRA_GENERIC_INPUT_WIRES_0                                                     (32'hc4)
`endif
`ifndef SOC_IFC_REG_CPTRA_GENERIC_INPUT_WIRES_1
`define SOC_IFC_REG_CPTRA_GENERIC_INPUT_WIRES_1                                                     (32'hc8)
`endif
`ifndef SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0
`define SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0                                                    (32'hcc)
`endif
`ifndef SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_1
`define SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_1                                                    (32'hd0)
`endif
`ifndef SOC_IFC_REG_CPTRA_HW_REV_ID
`define SOC_IFC_REG_CPTRA_HW_REV_ID                                                                 (32'hd4)
`define SOC_IFC_REG_CPTRA_HW_REV_ID_CPTRA_GENERATION_LOW                                            (0)
`define SOC_IFC_REG_CPTRA_HW_REV_ID_CPTRA_GENERATION_MASK                                           (32'hffff)
`define SOC_IFC_REG_CPTRA_HW_REV_ID_SOC_STEPPING_ID_LOW                                             (16)
`define SOC_IFC_REG_CPTRA_HW_REV_ID_SOC_STEPPING_ID_MASK                                            (32'hffff0000)
`endif
`ifndef SOC_IFC_REG_CPTRA_FW_REV_ID_0
`define SOC_IFC_REG_CPTRA_FW_REV_ID_0                                                               (32'hd8)
`endif
`ifndef SOC_IFC_REG_CPTRA_FW_REV_ID_1
`define SOC_IFC_REG_CPTRA_FW_REV_ID_1                                                               (32'hdc)
`endif
`ifndef SOC_IFC_REG_CPTRA_HW_CONFIG
`define SOC_IFC_REG_CPTRA_HW_CONFIG                                                                 (32'he0)
`define SOC_IFC_REG_CPTRA_HW_CONFIG_ITRNG_EN_LOW                                                    (0)
`define SOC_IFC_REG_CPTRA_HW_CONFIG_ITRNG_EN_MASK                                                   (32'h1)
`define SOC_IFC_REG_CPTRA_HW_CONFIG_FUSE_GRANULARITY_LOW                                            (1)
`define SOC_IFC_REG_CPTRA_HW_CONFIG_FUSE_GRANULARITY_MASK                                           (32'h2)
`define SOC_IFC_REG_CPTRA_HW_CONFIG_RSVD_EN_LOW                                                     (2)
`define SOC_IFC_REG_CPTRA_HW_CONFIG_RSVD_EN_MASK                                                    (32'hc)
`define SOC_IFC_REG_CPTRA_HW_CONFIG_LMS_ACC_EN_LOW                                                  (4)
`define SOC_IFC_REG_CPTRA_HW_CONFIG_LMS_ACC_EN_MASK                                                 (32'h10)
`define SOC_IFC_REG_CPTRA_HW_CONFIG_SUBSYSTEM_MODE_EN_LOW                                           (5)
`define SOC_IFC_REG_CPTRA_HW_CONFIG_SUBSYSTEM_MODE_EN_MASK                                          (32'h20)
`define SOC_IFC_REG_CPTRA_HW_CONFIG_OCP_LOCK_MODE_EN_LOW                                            (6)
`define SOC_IFC_REG_CPTRA_HW_CONFIG_OCP_LOCK_MODE_EN_MASK                                           (32'h40)
`endif
`ifndef SOC_IFC_REG_CPTRA_WDT_TIMER1_EN
`define SOC_IFC_REG_CPTRA_WDT_TIMER1_EN                                                             (32'he4)
`define SOC_IFC_REG_CPTRA_WDT_TIMER1_EN_TIMER1_EN_LOW                                               (0)
`define SOC_IFC_REG_CPTRA_WDT_TIMER1_EN_TIMER1_EN_MASK                                              (32'h1)
`endif
`ifndef SOC_IFC_REG_CPTRA_WDT_TIMER1_CTRL
`define SOC_IFC_REG_CPTRA_WDT_TIMER1_CTRL                                                           (32'he8)
`define SOC_IFC_REG_CPTRA_WDT_TIMER1_CTRL_TIMER1_RESTART_LOW                                        (0)
`define SOC_IFC_REG_CPTRA_WDT_TIMER1_CTRL_TIMER1_RESTART_MASK                                       (32'h1)
`endif
`ifndef SOC_IFC_REG_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD_0
`define SOC_IFC_REG_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD_0                                               (32'hec)
`endif
`ifndef SOC_IFC_REG_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD_1
`define SOC_IFC_REG_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD_1                                               (32'hf0)
`endif
`ifndef SOC_IFC_REG_CPTRA_WDT_TIMER2_EN
`define SOC_IFC_REG_CPTRA_WDT_TIMER2_EN                                                             (32'hf4)
`define SOC_IFC_REG_CPTRA_WDT_TIMER2_EN_TIMER2_EN_LOW                                               (0)
`define SOC_IFC_REG_CPTRA_WDT_TIMER2_EN_TIMER2_EN_MASK                                              (32'h1)
`endif
`ifndef SOC_IFC_REG_CPTRA_WDT_TIMER2_CTRL
`define SOC_IFC_REG_CPTRA_WDT_TIMER2_CTRL                                                           (32'hf8)
`define SOC_IFC_REG_CPTRA_WDT_TIMER2_CTRL_TIMER2_RESTART_LOW                                        (0)
`define SOC_IFC_REG_CPTRA_WDT_TIMER2_CTRL_TIMER2_RESTART_MASK                                       (32'h1)
`endif
`ifndef SOC_IFC_REG_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD_0
`define SOC_IFC_REG_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD_0                                               (32'hfc)
`endif
`ifndef SOC_IFC_REG_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD_1
`define SOC_IFC_REG_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD_1                                               (32'h100)
`endif
`ifndef SOC_IFC_REG_CPTRA_WDT_STATUS
`define SOC_IFC_REG_CPTRA_WDT_STATUS                                                                (32'h104)
`define SOC_IFC_REG_CPTRA_WDT_STATUS_T1_TIMEOUT_LOW                                                 (0)
`define SOC_IFC_REG_CPTRA_WDT_STATUS_T1_TIMEOUT_MASK                                                (32'h1)
`define SOC_IFC_REG_CPTRA_WDT_STATUS_T2_TIMEOUT_LOW                                                 (1)
`define SOC_IFC_REG_CPTRA_WDT_STATUS_T2_TIMEOUT_MASK                                                (32'h2)
`endif
`ifndef SOC_IFC_REG_CPTRA_FUSE_VALID_AXI_USER
`define SOC_IFC_REG_CPTRA_FUSE_VALID_AXI_USER                                                       (32'h108)
`endif
`ifndef SOC_IFC_REG_CPTRA_FUSE_AXI_USER_LOCK
`define SOC_IFC_REG_CPTRA_FUSE_AXI_USER_LOCK                                                        (32'h10c)
`define SOC_IFC_REG_CPTRA_FUSE_AXI_USER_LOCK_LOCK_LOW                                               (0)
`define SOC_IFC_REG_CPTRA_FUSE_AXI_USER_LOCK_LOCK_MASK                                              (32'h1)
`endif
`ifndef SOC_IFC_REG_CPTRA_WDT_CFG_0
`define SOC_IFC_REG_CPTRA_WDT_CFG_0                                                                 (32'h110)
`endif
`ifndef SOC_IFC_REG_CPTRA_WDT_CFG_1
`define SOC_IFC_REG_CPTRA_WDT_CFG_1                                                                 (32'h114)
`endif
`ifndef SOC_IFC_REG_CPTRA_ITRNG_ENTROPY_CONFIG_0
`define SOC_IFC_REG_CPTRA_ITRNG_ENTROPY_CONFIG_0                                                    (32'h118)
`define SOC_IFC_REG_CPTRA_ITRNG_ENTROPY_CONFIG_0_LOW_THRESHOLD_LOW                                  (0)
`define SOC_IFC_REG_CPTRA_ITRNG_ENTROPY_CONFIG_0_LOW_THRESHOLD_MASK                                 (32'hffff)
`define SOC_IFC_REG_CPTRA_ITRNG_ENTROPY_CONFIG_0_HIGH_THRESHOLD_LOW                                 (16)
`define SOC_IFC_REG_CPTRA_ITRNG_ENTROPY_CONFIG_0_HIGH_THRESHOLD_MASK                                (32'hffff0000)
`endif
`ifndef SOC_IFC_REG_CPTRA_ITRNG_ENTROPY_CONFIG_1
`define SOC_IFC_REG_CPTRA_ITRNG_ENTROPY_CONFIG_1                                                    (32'h11c)
`define SOC_IFC_REG_CPTRA_ITRNG_ENTROPY_CONFIG_1_REPETITION_COUNT_LOW                               (0)
`define SOC_IFC_REG_CPTRA_ITRNG_ENTROPY_CONFIG_1_REPETITION_COUNT_MASK                              (32'hffff)
`define SOC_IFC_REG_CPTRA_ITRNG_ENTROPY_CONFIG_1_RSVD_LOW                                           (16)
`define SOC_IFC_REG_CPTRA_ITRNG_ENTROPY_CONFIG_1_RSVD_MASK                                          (32'hffff0000)
`endif
`ifndef SOC_IFC_REG_CPTRA_RSVD_REG_0
`define SOC_IFC_REG_CPTRA_RSVD_REG_0                                                                (32'h120)
`endif
`ifndef SOC_IFC_REG_CPTRA_RSVD_REG_1
`define SOC_IFC_REG_CPTRA_RSVD_REG_1                                                                (32'h124)
`endif
`ifndef SOC_IFC_REG_CPTRA_HW_CAPABILITIES
`define SOC_IFC_REG_CPTRA_HW_CAPABILITIES                                                           (32'h128)
`endif
`ifndef SOC_IFC_REG_CPTRA_FW_CAPABILITIES
`define SOC_IFC_REG_CPTRA_FW_CAPABILITIES                                                           (32'h12c)
`endif
`ifndef SOC_IFC_REG_CPTRA_CAP_LOCK
`define SOC_IFC_REG_CPTRA_CAP_LOCK                                                                  (32'h130)
`define SOC_IFC_REG_CPTRA_CAP_LOCK_LOCK_LOW                                                         (0)
`define SOC_IFC_REG_CPTRA_CAP_LOCK_LOCK_MASK                                                        (32'h1)
`endif
`ifndef SOC_IFC_REG_CPTRA_OWNER_PK_HASH_0
`define SOC_IFC_REG_CPTRA_OWNER_PK_HASH_0                                                           (32'h140)
`endif
`ifndef SOC_IFC_REG_CPTRA_OWNER_PK_HASH_1
`define SOC_IFC_REG_CPTRA_OWNER_PK_HASH_1                                                           (32'h144)
`endif
`ifndef SOC_IFC_REG_CPTRA_OWNER_PK_HASH_2
`define SOC_IFC_REG_CPTRA_OWNER_PK_HASH_2                                                           (32'h148)
`endif
`ifndef SOC_IFC_REG_CPTRA_OWNER_PK_HASH_3
`define SOC_IFC_REG_CPTRA_OWNER_PK_HASH_3                                                           (32'h14c)
`endif
`ifndef SOC_IFC_REG_CPTRA_OWNER_PK_HASH_4
`define SOC_IFC_REG_CPTRA_OWNER_PK_HASH_4                                                           (32'h150)
`endif
`ifndef SOC_IFC_REG_CPTRA_OWNER_PK_HASH_5
`define SOC_IFC_REG_CPTRA_OWNER_PK_HASH_5                                                           (32'h154)
`endif
`ifndef SOC_IFC_REG_CPTRA_OWNER_PK_HASH_6
`define SOC_IFC_REG_CPTRA_OWNER_PK_HASH_6                                                           (32'h158)
`endif
`ifndef SOC_IFC_REG_CPTRA_OWNER_PK_HASH_7
`define SOC_IFC_REG_CPTRA_OWNER_PK_HASH_7                                                           (32'h15c)
`endif
`ifndef SOC_IFC_REG_CPTRA_OWNER_PK_HASH_8
`define SOC_IFC_REG_CPTRA_OWNER_PK_HASH_8                                                           (32'h160)
`endif
`ifndef SOC_IFC_REG_CPTRA_OWNER_PK_HASH_9
`define SOC_IFC_REG_CPTRA_OWNER_PK_HASH_9                                                           (32'h164)
`endif
`ifndef SOC_IFC_REG_CPTRA_OWNER_PK_HASH_10
`define SOC_IFC_REG_CPTRA_OWNER_PK_HASH_10                                                          (32'h168)
`endif
`ifndef SOC_IFC_REG_CPTRA_OWNER_PK_HASH_11
`define SOC_IFC_REG_CPTRA_OWNER_PK_HASH_11                                                          (32'h16c)
`endif
`ifndef SOC_IFC_REG_CPTRA_OWNER_PK_HASH_LOCK
`define SOC_IFC_REG_CPTRA_OWNER_PK_HASH_LOCK                                                        (32'h170)
`define SOC_IFC_REG_CPTRA_OWNER_PK_HASH_LOCK_LOCK_LOW                                               (0)
`define SOC_IFC_REG_CPTRA_OWNER_PK_HASH_LOCK_LOCK_MASK                                              (32'h1)
`endif
`ifndef SOC_IFC_REG_FUSE_UDS_SEED_0
`define SOC_IFC_REG_FUSE_UDS_SEED_0                                                                 (32'h200)
`endif
`ifndef SOC_IFC_REG_FUSE_UDS_SEED_1
`define SOC_IFC_REG_FUSE_UDS_SEED_1                                                                 (32'h204)
`endif
`ifndef SOC_IFC_REG_FUSE_UDS_SEED_2
`define SOC_IFC_REG_FUSE_UDS_SEED_2                                                                 (32'h208)
`endif
`ifndef SOC_IFC_REG_FUSE_UDS_SEED_3
`define SOC_IFC_REG_FUSE_UDS_SEED_3                                                                 (32'h20c)
`endif
`ifndef SOC_IFC_REG_FUSE_UDS_SEED_4
`define SOC_IFC_REG_FUSE_UDS_SEED_4                                                                 (32'h210)
`endif
`ifndef SOC_IFC_REG_FUSE_UDS_SEED_5
`define SOC_IFC_REG_FUSE_UDS_SEED_5                                                                 (32'h214)
`endif
`ifndef SOC_IFC_REG_FUSE_UDS_SEED_6
`define SOC_IFC_REG_FUSE_UDS_SEED_6                                                                 (32'h218)
`endif
`ifndef SOC_IFC_REG_FUSE_UDS_SEED_7
`define SOC_IFC_REG_FUSE_UDS_SEED_7                                                                 (32'h21c)
`endif
`ifndef SOC_IFC_REG_FUSE_UDS_SEED_8
`define SOC_IFC_REG_FUSE_UDS_SEED_8                                                                 (32'h220)
`endif
`ifndef SOC_IFC_REG_FUSE_UDS_SEED_9
`define SOC_IFC_REG_FUSE_UDS_SEED_9                                                                 (32'h224)
`endif
`ifndef SOC_IFC_REG_FUSE_UDS_SEED_10
`define SOC_IFC_REG_FUSE_UDS_SEED_10                                                                (32'h228)
`endif
`ifndef SOC_IFC_REG_FUSE_UDS_SEED_11
`define SOC_IFC_REG_FUSE_UDS_SEED_11                                                                (32'h22c)
`endif
`ifndef SOC_IFC_REG_FUSE_UDS_SEED_12
`define SOC_IFC_REG_FUSE_UDS_SEED_12                                                                (32'h230)
`endif
`ifndef SOC_IFC_REG_FUSE_UDS_SEED_13
`define SOC_IFC_REG_FUSE_UDS_SEED_13                                                                (32'h234)
`endif
`ifndef SOC_IFC_REG_FUSE_UDS_SEED_14
`define SOC_IFC_REG_FUSE_UDS_SEED_14                                                                (32'h238)
`endif
`ifndef SOC_IFC_REG_FUSE_UDS_SEED_15
`define SOC_IFC_REG_FUSE_UDS_SEED_15                                                                (32'h23c)
`endif
`ifndef SOC_IFC_REG_FUSE_FIELD_ENTROPY_0
`define SOC_IFC_REG_FUSE_FIELD_ENTROPY_0                                                            (32'h240)
`endif
`ifndef SOC_IFC_REG_FUSE_FIELD_ENTROPY_1
`define SOC_IFC_REG_FUSE_FIELD_ENTROPY_1                                                            (32'h244)
`endif
`ifndef SOC_IFC_REG_FUSE_FIELD_ENTROPY_2
`define SOC_IFC_REG_FUSE_FIELD_ENTROPY_2                                                            (32'h248)
`endif
`ifndef SOC_IFC_REG_FUSE_FIELD_ENTROPY_3
`define SOC_IFC_REG_FUSE_FIELD_ENTROPY_3                                                            (32'h24c)
`endif
`ifndef SOC_IFC_REG_FUSE_FIELD_ENTROPY_4
`define SOC_IFC_REG_FUSE_FIELD_ENTROPY_4                                                            (32'h250)
`endif
`ifndef SOC_IFC_REG_FUSE_FIELD_ENTROPY_5
`define SOC_IFC_REG_FUSE_FIELD_ENTROPY_5                                                            (32'h254)
`endif
`ifndef SOC_IFC_REG_FUSE_FIELD_ENTROPY_6
`define SOC_IFC_REG_FUSE_FIELD_ENTROPY_6                                                            (32'h258)
`endif
`ifndef SOC_IFC_REG_FUSE_FIELD_ENTROPY_7
`define SOC_IFC_REG_FUSE_FIELD_ENTROPY_7                                                            (32'h25c)
`endif
`ifndef SOC_IFC_REG_FUSE_VENDOR_PK_HASH_0
`define SOC_IFC_REG_FUSE_VENDOR_PK_HASH_0                                                           (32'h260)
`endif
`ifndef SOC_IFC_REG_FUSE_VENDOR_PK_HASH_1
`define SOC_IFC_REG_FUSE_VENDOR_PK_HASH_1                                                           (32'h264)
`endif
`ifndef SOC_IFC_REG_FUSE_VENDOR_PK_HASH_2
`define SOC_IFC_REG_FUSE_VENDOR_PK_HASH_2                                                           (32'h268)
`endif
`ifndef SOC_IFC_REG_FUSE_VENDOR_PK_HASH_3
`define SOC_IFC_REG_FUSE_VENDOR_PK_HASH_3                                                           (32'h26c)
`endif
`ifndef SOC_IFC_REG_FUSE_VENDOR_PK_HASH_4
`define SOC_IFC_REG_FUSE_VENDOR_PK_HASH_4                                                           (32'h270)
`endif
`ifndef SOC_IFC_REG_FUSE_VENDOR_PK_HASH_5
`define SOC_IFC_REG_FUSE_VENDOR_PK_HASH_5                                                           (32'h274)
`endif
`ifndef SOC_IFC_REG_FUSE_VENDOR_PK_HASH_6
`define SOC_IFC_REG_FUSE_VENDOR_PK_HASH_6                                                           (32'h278)
`endif
`ifndef SOC_IFC_REG_FUSE_VENDOR_PK_HASH_7
`define SOC_IFC_REG_FUSE_VENDOR_PK_HASH_7                                                           (32'h27c)
`endif
`ifndef SOC_IFC_REG_FUSE_VENDOR_PK_HASH_8
`define SOC_IFC_REG_FUSE_VENDOR_PK_HASH_8                                                           (32'h280)
`endif
`ifndef SOC_IFC_REG_FUSE_VENDOR_PK_HASH_9
`define SOC_IFC_REG_FUSE_VENDOR_PK_HASH_9                                                           (32'h284)
`endif
`ifndef SOC_IFC_REG_FUSE_VENDOR_PK_HASH_10
`define SOC_IFC_REG_FUSE_VENDOR_PK_HASH_10                                                          (32'h288)
`endif
`ifndef SOC_IFC_REG_FUSE_VENDOR_PK_HASH_11
`define SOC_IFC_REG_FUSE_VENDOR_PK_HASH_11                                                          (32'h28c)
`endif
`ifndef SOC_IFC_REG_FUSE_ECC_REVOCATION
`define SOC_IFC_REG_FUSE_ECC_REVOCATION                                                             (32'h290)
`define SOC_IFC_REG_FUSE_ECC_REVOCATION_ECC_REVOCATION_LOW                                          (0)
`define SOC_IFC_REG_FUSE_ECC_REVOCATION_ECC_REVOCATION_MASK                                         (32'hf)
`endif
`ifndef SOC_IFC_REG_FUSE_FMC_KEY_MANIFEST_SVN
`define SOC_IFC_REG_FUSE_FMC_KEY_MANIFEST_SVN                                                       (32'h2b4)
`endif
`ifndef SOC_IFC_REG_FUSE_RUNTIME_SVN_0
`define SOC_IFC_REG_FUSE_RUNTIME_SVN_0                                                              (32'h2b8)
`endif
`ifndef SOC_IFC_REG_FUSE_RUNTIME_SVN_1
`define SOC_IFC_REG_FUSE_RUNTIME_SVN_1                                                              (32'h2bc)
`endif
`ifndef SOC_IFC_REG_FUSE_RUNTIME_SVN_2
`define SOC_IFC_REG_FUSE_RUNTIME_SVN_2                                                              (32'h2c0)
`endif
`ifndef SOC_IFC_REG_FUSE_RUNTIME_SVN_3
`define SOC_IFC_REG_FUSE_RUNTIME_SVN_3                                                              (32'h2c4)
`endif
`ifndef SOC_IFC_REG_FUSE_ANTI_ROLLBACK_DISABLE
`define SOC_IFC_REG_FUSE_ANTI_ROLLBACK_DISABLE                                                      (32'h2c8)
`define SOC_IFC_REG_FUSE_ANTI_ROLLBACK_DISABLE_DIS_LOW                                              (0)
`define SOC_IFC_REG_FUSE_ANTI_ROLLBACK_DISABLE_DIS_MASK                                             (32'h1)
`endif
`ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_0
`define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_0                                                         (32'h2cc)
`endif
`ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_1
`define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_1                                                         (32'h2d0)
`endif
`ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_2
`define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_2                                                         (32'h2d4)
`endif
`ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_3
`define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_3                                                         (32'h2d8)
`endif
`ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_4
`define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_4                                                         (32'h2dc)
`endif
`ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_5
`define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_5                                                         (32'h2e0)
`endif
`ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_6
`define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_6                                                         (32'h2e4)
`endif
`ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_7
`define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_7                                                         (32'h2e8)
`endif
`ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_8
`define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_8                                                         (32'h2ec)
`endif
`ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_9
`define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_9                                                         (32'h2f0)
`endif
`ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_10
`define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_10                                                        (32'h2f4)
`endif
`ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_11
`define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_11                                                        (32'h2f8)
`endif
`ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_12
`define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_12                                                        (32'h2fc)
`endif
`ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_13
`define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_13                                                        (32'h300)
`endif
`ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_14
`define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_14                                                        (32'h304)
`endif
`ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_15
`define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_15                                                        (32'h308)
`endif
`ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_16
`define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_16                                                        (32'h30c)
`endif
`ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_17
`define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_17                                                        (32'h310)
`endif
`ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_18
`define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_18                                                        (32'h314)
`endif
`ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_19
`define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_19                                                        (32'h318)
`endif
`ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_20
`define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_20                                                        (32'h31c)
`endif
`ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_21
`define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_21                                                        (32'h320)
`endif
`ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_22
`define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_22                                                        (32'h324)
`endif
`ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_23
`define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_23                                                        (32'h328)
`endif
`ifndef SOC_IFC_REG_FUSE_IDEVID_MANUF_HSM_ID_0
`define SOC_IFC_REG_FUSE_IDEVID_MANUF_HSM_ID_0                                                      (32'h32c)
`endif
`ifndef SOC_IFC_REG_FUSE_IDEVID_MANUF_HSM_ID_1
`define SOC_IFC_REG_FUSE_IDEVID_MANUF_HSM_ID_1                                                      (32'h330)
`endif
`ifndef SOC_IFC_REG_FUSE_IDEVID_MANUF_HSM_ID_2
`define SOC_IFC_REG_FUSE_IDEVID_MANUF_HSM_ID_2                                                      (32'h334)
`endif
`ifndef SOC_IFC_REG_FUSE_IDEVID_MANUF_HSM_ID_3
`define SOC_IFC_REG_FUSE_IDEVID_MANUF_HSM_ID_3                                                      (32'h338)
`endif
`ifndef SOC_IFC_REG_FUSE_LMS_REVOCATION
`define SOC_IFC_REG_FUSE_LMS_REVOCATION                                                             (32'h340)
`endif
`ifndef SOC_IFC_REG_FUSE_MLDSA_REVOCATION
`define SOC_IFC_REG_FUSE_MLDSA_REVOCATION                                                           (32'h344)
`define SOC_IFC_REG_FUSE_MLDSA_REVOCATION_MLDSA_REVOCATION_LOW                                      (0)
`define SOC_IFC_REG_FUSE_MLDSA_REVOCATION_MLDSA_REVOCATION_MASK                                     (32'hf)
`endif
`ifndef SOC_IFC_REG_FUSE_SOC_STEPPING_ID
`define SOC_IFC_REG_FUSE_SOC_STEPPING_ID                                                            (32'h348)
`define SOC_IFC_REG_FUSE_SOC_STEPPING_ID_SOC_STEPPING_ID_LOW                                        (0)
`define SOC_IFC_REG_FUSE_SOC_STEPPING_ID_SOC_STEPPING_ID_MASK                                       (32'hffff)
`endif
`ifndef SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_0
`define SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_0                                                   (32'h34c)
`endif
`ifndef SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_1
`define SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_1                                                   (32'h350)
`endif
`ifndef SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_2
`define SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_2                                                   (32'h354)
`endif
`ifndef SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_3
`define SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_3                                                   (32'h358)
`endif
`ifndef SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_4
`define SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_4                                                   (32'h35c)
`endif
`ifndef SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_5
`define SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_5                                                   (32'h360)
`endif
`ifndef SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_6
`define SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_6                                                   (32'h364)
`endif
`ifndef SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_7
`define SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_7                                                   (32'h368)
`endif
`ifndef SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_8
`define SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_8                                                   (32'h36c)
`endif
`ifndef SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_9
`define SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_9                                                   (32'h370)
`endif
`ifndef SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_10
`define SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_10                                                  (32'h374)
`endif
`ifndef SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_11
`define SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_11                                                  (32'h378)
`endif
`ifndef SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_12
`define SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_12                                                  (32'h37c)
`endif
`ifndef SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_13
`define SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_13                                                  (32'h380)
`endif
`ifndef SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_14
`define SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_14                                                  (32'h384)
`endif
`ifndef SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_15
`define SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_15                                                  (32'h388)
`endif
`ifndef SOC_IFC_REG_FUSE_PQC_KEY_TYPE
`define SOC_IFC_REG_FUSE_PQC_KEY_TYPE                                                               (32'h38c)
`define SOC_IFC_REG_FUSE_PQC_KEY_TYPE_KEY_TYPE_LOW                                                  (0)
`define SOC_IFC_REG_FUSE_PQC_KEY_TYPE_KEY_TYPE_MASK                                                 (32'h3)
`endif
`ifndef SOC_IFC_REG_FUSE_SOC_MANIFEST_SVN_0
`define SOC_IFC_REG_FUSE_SOC_MANIFEST_SVN_0                                                         (32'h390)
`endif
`ifndef SOC_IFC_REG_FUSE_SOC_MANIFEST_SVN_1
`define SOC_IFC_REG_FUSE_SOC_MANIFEST_SVN_1                                                         (32'h394)
`endif
`ifndef SOC_IFC_REG_FUSE_SOC_MANIFEST_SVN_2
`define SOC_IFC_REG_FUSE_SOC_MANIFEST_SVN_2                                                         (32'h398)
`endif
`ifndef SOC_IFC_REG_FUSE_SOC_MANIFEST_SVN_3
`define SOC_IFC_REG_FUSE_SOC_MANIFEST_SVN_3                                                         (32'h39c)
`endif
`ifndef SOC_IFC_REG_FUSE_SOC_MANIFEST_MAX_SVN
`define SOC_IFC_REG_FUSE_SOC_MANIFEST_MAX_SVN                                                       (32'h3a0)
`define SOC_IFC_REG_FUSE_SOC_MANIFEST_MAX_SVN_SVN_LOW                                               (0)
`define SOC_IFC_REG_FUSE_SOC_MANIFEST_MAX_SVN_SVN_MASK                                              (32'hff)
`endif
`ifndef SOC_IFC_REG_FUSE_HEK_SEED_0
`define SOC_IFC_REG_FUSE_HEK_SEED_0                                                                 (32'h3c0)
`endif
`ifndef SOC_IFC_REG_FUSE_HEK_SEED_1
`define SOC_IFC_REG_FUSE_HEK_SEED_1                                                                 (32'h3c4)
`endif
`ifndef SOC_IFC_REG_FUSE_HEK_SEED_2
`define SOC_IFC_REG_FUSE_HEK_SEED_2                                                                 (32'h3c8)
`endif
`ifndef SOC_IFC_REG_FUSE_HEK_SEED_3
`define SOC_IFC_REG_FUSE_HEK_SEED_3                                                                 (32'h3cc)
`endif
`ifndef SOC_IFC_REG_FUSE_HEK_SEED_4
`define SOC_IFC_REG_FUSE_HEK_SEED_4                                                                 (32'h3d0)
`endif
`ifndef SOC_IFC_REG_FUSE_HEK_SEED_5
`define SOC_IFC_REG_FUSE_HEK_SEED_5                                                                 (32'h3d4)
`endif
`ifndef SOC_IFC_REG_FUSE_HEK_SEED_6
`define SOC_IFC_REG_FUSE_HEK_SEED_6                                                                 (32'h3d8)
`endif
`ifndef SOC_IFC_REG_FUSE_HEK_SEED_7
`define SOC_IFC_REG_FUSE_HEK_SEED_7                                                                 (32'h3dc)
`endif
`ifndef SOC_IFC_REG_SS_CALIPTRA_BASE_ADDR_L
`define SOC_IFC_REG_SS_CALIPTRA_BASE_ADDR_L                                                         (32'h500)
`endif
`ifndef SOC_IFC_REG_SS_CALIPTRA_BASE_ADDR_H
`define SOC_IFC_REG_SS_CALIPTRA_BASE_ADDR_H                                                         (32'h504)
`endif
`ifndef SOC_IFC_REG_SS_MCI_BASE_ADDR_L
`define SOC_IFC_REG_SS_MCI_BASE_ADDR_L                                                              (32'h508)
`endif
`ifndef SOC_IFC_REG_SS_MCI_BASE_ADDR_H
`define SOC_IFC_REG_SS_MCI_BASE_ADDR_H                                                              (32'h50c)
`endif
`ifndef SOC_IFC_REG_SS_RECOVERY_IFC_BASE_ADDR_L
`define SOC_IFC_REG_SS_RECOVERY_IFC_BASE_ADDR_L                                                     (32'h510)
`endif
`ifndef SOC_IFC_REG_SS_RECOVERY_IFC_BASE_ADDR_H
`define SOC_IFC_REG_SS_RECOVERY_IFC_BASE_ADDR_H                                                     (32'h514)
`endif
`ifndef SOC_IFC_REG_SS_OTP_FC_BASE_ADDR_L
`define SOC_IFC_REG_SS_OTP_FC_BASE_ADDR_L                                                           (32'h518)
`endif
`ifndef SOC_IFC_REG_SS_OTP_FC_BASE_ADDR_H
`define SOC_IFC_REG_SS_OTP_FC_BASE_ADDR_H                                                           (32'h51c)
`endif
`ifndef SOC_IFC_REG_SS_UDS_SEED_BASE_ADDR_L
`define SOC_IFC_REG_SS_UDS_SEED_BASE_ADDR_L                                                         (32'h520)
`endif
`ifndef SOC_IFC_REG_SS_UDS_SEED_BASE_ADDR_H
`define SOC_IFC_REG_SS_UDS_SEED_BASE_ADDR_H                                                         (32'h524)
`endif
`ifndef SOC_IFC_REG_SS_PROD_DEBUG_UNLOCK_AUTH_PK_HASH_REG_BANK_OFFSET
`define SOC_IFC_REG_SS_PROD_DEBUG_UNLOCK_AUTH_PK_HASH_REG_BANK_OFFSET                               (32'h528)
`endif
`ifndef SOC_IFC_REG_SS_NUM_OF_PROD_DEBUG_UNLOCK_AUTH_PK_HASHES
`define SOC_IFC_REG_SS_NUM_OF_PROD_DEBUG_UNLOCK_AUTH_PK_HASHES                                      (32'h52c)
`endif
`ifndef SOC_IFC_REG_SS_DEBUG_INTENT
`define SOC_IFC_REG_SS_DEBUG_INTENT                                                                 (32'h530)
`define SOC_IFC_REG_SS_DEBUG_INTENT_DEBUG_INTENT_LOW                                                (0)
`define SOC_IFC_REG_SS_DEBUG_INTENT_DEBUG_INTENT_MASK                                               (32'h1)
`endif
`ifndef SOC_IFC_REG_SS_CALIPTRA_DMA_AXI_USER
`define SOC_IFC_REG_SS_CALIPTRA_DMA_AXI_USER                                                        (32'h534)
`endif
`ifndef SOC_IFC_REG_SS_EXTERNAL_STAGING_AREA_BASE_ADDR_L
`define SOC_IFC_REG_SS_EXTERNAL_STAGING_AREA_BASE_ADDR_L                                            (32'h538)
`endif
`ifndef SOC_IFC_REG_SS_EXTERNAL_STAGING_AREA_BASE_ADDR_H
`define SOC_IFC_REG_SS_EXTERNAL_STAGING_AREA_BASE_ADDR_H                                            (32'h53c)
`endif
`ifndef SOC_IFC_REG_SS_KEY_RELEASE_BASE_ADDR_L
`define SOC_IFC_REG_SS_KEY_RELEASE_BASE_ADDR_L                                                      (32'h540)
`endif
`ifndef SOC_IFC_REG_SS_KEY_RELEASE_BASE_ADDR_H
`define SOC_IFC_REG_SS_KEY_RELEASE_BASE_ADDR_H                                                      (32'h544)
`endif
`ifndef SOC_IFC_REG_SS_KEY_RELEASE_SIZE
`define SOC_IFC_REG_SS_KEY_RELEASE_SIZE                                                             (32'h548)
`define SOC_IFC_REG_SS_KEY_RELEASE_SIZE_SIZE_LOW                                                    (0)
`define SOC_IFC_REG_SS_KEY_RELEASE_SIZE_SIZE_MASK                                                   (32'hffff)
`endif
`ifndef SOC_IFC_REG_SS_OCP_LOCK_CTRL
`define SOC_IFC_REG_SS_OCP_LOCK_CTRL                                                                (32'h54c)
`define SOC_IFC_REG_SS_OCP_LOCK_CTRL_LOCK_IN_PROGRESS_LOW                                           (0)
`define SOC_IFC_REG_SS_OCP_LOCK_CTRL_LOCK_IN_PROGRESS_MASK                                          (32'h1)
`endif
`ifndef SOC_IFC_REG_SS_STRAP_GENERIC_0
`define SOC_IFC_REG_SS_STRAP_GENERIC_0                                                              (32'h5a0)
`endif
`ifndef SOC_IFC_REG_SS_STRAP_GENERIC_1
`define SOC_IFC_REG_SS_STRAP_GENERIC_1                                                              (32'h5a4)
`endif
`ifndef SOC_IFC_REG_SS_STRAP_GENERIC_2
`define SOC_IFC_REG_SS_STRAP_GENERIC_2                                                              (32'h5a8)
`endif
`ifndef SOC_IFC_REG_SS_STRAP_GENERIC_3
`define SOC_IFC_REG_SS_STRAP_GENERIC_3                                                              (32'h5ac)
`endif
`ifndef SOC_IFC_REG_SS_DBG_SERVICE_REG_REQ
`define SOC_IFC_REG_SS_DBG_SERVICE_REG_REQ                                                          (32'h5c0)
`define SOC_IFC_REG_SS_DBG_SERVICE_REG_REQ_MANUF_DBG_UNLOCK_REQ_LOW                                 (0)
`define SOC_IFC_REG_SS_DBG_SERVICE_REG_REQ_MANUF_DBG_UNLOCK_REQ_MASK                                (32'h1)
`define SOC_IFC_REG_SS_DBG_SERVICE_REG_REQ_PROD_DBG_UNLOCK_REQ_LOW                                  (1)
`define SOC_IFC_REG_SS_DBG_SERVICE_REG_REQ_PROD_DBG_UNLOCK_REQ_MASK                                 (32'h2)
`define SOC_IFC_REG_SS_DBG_SERVICE_REG_REQ_UDS_PROGRAM_REQ_LOW                                      (2)
`define SOC_IFC_REG_SS_DBG_SERVICE_REG_REQ_UDS_PROGRAM_REQ_MASK                                     (32'h4)
`define SOC_IFC_REG_SS_DBG_SERVICE_REG_REQ_RSVD_LOW                                                 (3)
`define SOC_IFC_REG_SS_DBG_SERVICE_REG_REQ_RSVD_MASK                                                (32'hfffffff8)
`endif
`ifndef SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP
`define SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP                                                          (32'h5c4)
`define SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_MANUF_DBG_UNLOCK_SUCCESS_LOW                             (0)
`define SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_MANUF_DBG_UNLOCK_SUCCESS_MASK                            (32'h1)
`define SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_MANUF_DBG_UNLOCK_FAIL_LOW                                (1)
`define SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_MANUF_DBG_UNLOCK_FAIL_MASK                               (32'h2)
`define SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_MANUF_DBG_UNLOCK_IN_PROGRESS_LOW                         (2)
`define SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_MANUF_DBG_UNLOCK_IN_PROGRESS_MASK                        (32'h4)
`define SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_PROD_DBG_UNLOCK_SUCCESS_LOW                              (3)
`define SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_PROD_DBG_UNLOCK_SUCCESS_MASK                             (32'h8)
`define SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_PROD_DBG_UNLOCK_FAIL_LOW                                 (4)
`define SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_PROD_DBG_UNLOCK_FAIL_MASK                                (32'h10)
`define SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_PROD_DBG_UNLOCK_IN_PROGRESS_LOW                          (5)
`define SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_PROD_DBG_UNLOCK_IN_PROGRESS_MASK                         (32'h20)
`define SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_UDS_PROGRAM_SUCCESS_LOW                                  (6)
`define SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_UDS_PROGRAM_SUCCESS_MASK                                 (32'h40)
`define SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_UDS_PROGRAM_FAIL_LOW                                     (7)
`define SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_UDS_PROGRAM_FAIL_MASK                                    (32'h80)
`define SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_UDS_PROGRAM_IN_PROGRESS_LOW                              (8)
`define SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_UDS_PROGRAM_IN_PROGRESS_MASK                             (32'h100)
`define SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_TAP_MAILBOX_AVAILABLE_LOW                                (9)
`define SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_TAP_MAILBOX_AVAILABLE_MASK                               (32'h200)
`define SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_RSVD_LOW                                                 (10)
`define SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_RSVD_MASK                                                (32'hfffffc00)
`endif
`ifndef SOC_IFC_REG_SS_SOC_DBG_UNLOCK_LEVEL_0
`define SOC_IFC_REG_SS_SOC_DBG_UNLOCK_LEVEL_0                                                       (32'h5c8)
`endif
`ifndef SOC_IFC_REG_SS_SOC_DBG_UNLOCK_LEVEL_1
`define SOC_IFC_REG_SS_SOC_DBG_UNLOCK_LEVEL_1                                                       (32'h5cc)
`endif
`ifndef SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_0
`define SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_0                                                       (32'h5d0)
`endif
`ifndef SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_1
`define SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_1                                                       (32'h5d4)
`endif
`ifndef SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_2
`define SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_2                                                       (32'h5d8)
`endif
`ifndef SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_3
`define SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_3                                                       (32'h5dc)
`endif
`ifndef SOC_IFC_REG_INTERNAL_OBF_KEY_0
`define SOC_IFC_REG_INTERNAL_OBF_KEY_0                                                              (32'h600)
`endif
`ifndef SOC_IFC_REG_INTERNAL_OBF_KEY_1
`define SOC_IFC_REG_INTERNAL_OBF_KEY_1                                                              (32'h604)
`endif
`ifndef SOC_IFC_REG_INTERNAL_OBF_KEY_2
`define SOC_IFC_REG_INTERNAL_OBF_KEY_2                                                              (32'h608)
`endif
`ifndef SOC_IFC_REG_INTERNAL_OBF_KEY_3
`define SOC_IFC_REG_INTERNAL_OBF_KEY_3                                                              (32'h60c)
`endif
`ifndef SOC_IFC_REG_INTERNAL_OBF_KEY_4
`define SOC_IFC_REG_INTERNAL_OBF_KEY_4                                                              (32'h610)
`endif
`ifndef SOC_IFC_REG_INTERNAL_OBF_KEY_5
`define SOC_IFC_REG_INTERNAL_OBF_KEY_5                                                              (32'h614)
`endif
`ifndef SOC_IFC_REG_INTERNAL_OBF_KEY_6
`define SOC_IFC_REG_INTERNAL_OBF_KEY_6                                                              (32'h618)
`endif
`ifndef SOC_IFC_REG_INTERNAL_OBF_KEY_7
`define SOC_IFC_REG_INTERNAL_OBF_KEY_7                                                              (32'h61c)
`endif
`ifndef SOC_IFC_REG_INTERNAL_ICCM_LOCK
`define SOC_IFC_REG_INTERNAL_ICCM_LOCK                                                              (32'h620)
`define SOC_IFC_REG_INTERNAL_ICCM_LOCK_LOCK_LOW                                                     (0)
`define SOC_IFC_REG_INTERNAL_ICCM_LOCK_LOCK_MASK                                                    (32'h1)
`endif
`ifndef SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET
`define SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET                                                        (32'h624)
`define SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET_CORE_RST_LOW                                           (0)
`define SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET_CORE_RST_MASK                                          (32'h1)
`endif
`ifndef SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET_WAIT_CYCLES
`define SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET_WAIT_CYCLES                                            (32'h628)
`define SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET_WAIT_CYCLES_WAIT_CYCLES_LOW                            (0)
`define SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET_WAIT_CYCLES_WAIT_CYCLES_MASK                           (32'hff)
`endif
`ifndef SOC_IFC_REG_INTERNAL_NMI_VECTOR
`define SOC_IFC_REG_INTERNAL_NMI_VECTOR                                                             (32'h62c)
`endif
`ifndef SOC_IFC_REG_INTERNAL_HW_ERROR_FATAL_MASK
`define SOC_IFC_REG_INTERNAL_HW_ERROR_FATAL_MASK                                                    (32'h630)
`define SOC_IFC_REG_INTERNAL_HW_ERROR_FATAL_MASK_MASK_ICCM_ECC_UNC_LOW                              (0)
`define SOC_IFC_REG_INTERNAL_HW_ERROR_FATAL_MASK_MASK_ICCM_ECC_UNC_MASK                             (32'h1)
`define SOC_IFC_REG_INTERNAL_HW_ERROR_FATAL_MASK_MASK_DCCM_ECC_UNC_LOW                              (1)
`define SOC_IFC_REG_INTERNAL_HW_ERROR_FATAL_MASK_MASK_DCCM_ECC_UNC_MASK                             (32'h2)
`define SOC_IFC_REG_INTERNAL_HW_ERROR_FATAL_MASK_MASK_NMI_PIN_LOW                                   (2)
`define SOC_IFC_REG_INTERNAL_HW_ERROR_FATAL_MASK_MASK_NMI_PIN_MASK                                  (32'h4)
`define SOC_IFC_REG_INTERNAL_HW_ERROR_FATAL_MASK_MASK_CRYPTO_ERR_LOW                                (3)
`define SOC_IFC_REG_INTERNAL_HW_ERROR_FATAL_MASK_MASK_CRYPTO_ERR_MASK                               (32'h8)
`endif
`ifndef SOC_IFC_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK
`define SOC_IFC_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK                                                (32'h634)
`define SOC_IFC_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK_MASK_MBOX_PROT_NO_LOCK_LOW                     (0)
`define SOC_IFC_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK_MASK_MBOX_PROT_NO_LOCK_MASK                    (32'h1)
`define SOC_IFC_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK_MASK_MBOX_PROT_OOO_LOW                         (1)
`define SOC_IFC_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK_MASK_MBOX_PROT_OOO_MASK                        (32'h2)
`define SOC_IFC_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK_MASK_MBOX_ECC_UNC_LOW                          (2)
`define SOC_IFC_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK_MASK_MBOX_ECC_UNC_MASK                         (32'h4)
`endif
`ifndef SOC_IFC_REG_INTERNAL_FW_ERROR_FATAL_MASK
`define SOC_IFC_REG_INTERNAL_FW_ERROR_FATAL_MASK                                                    (32'h638)
`endif
`ifndef SOC_IFC_REG_INTERNAL_FW_ERROR_NON_FATAL_MASK
`define SOC_IFC_REG_INTERNAL_FW_ERROR_NON_FATAL_MASK                                                (32'h63c)
`endif
`ifndef SOC_IFC_REG_INTERNAL_RV_MTIME_L
`define SOC_IFC_REG_INTERNAL_RV_MTIME_L                                                             (32'h640)
`endif
`ifndef SOC_IFC_REG_INTERNAL_RV_MTIME_H
`define SOC_IFC_REG_INTERNAL_RV_MTIME_H                                                             (32'h644)
`endif
`ifndef SOC_IFC_REG_INTERNAL_RV_MTIMECMP_L
`define SOC_IFC_REG_INTERNAL_RV_MTIMECMP_L                                                          (32'h648)
`endif
`ifndef SOC_IFC_REG_INTERNAL_RV_MTIMECMP_H
`define SOC_IFC_REG_INTERNAL_RV_MTIMECMP_H                                                          (32'h64c)
`endif
`ifndef SOC_IFC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R
`define SOC_IFC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R                                                  (32'h800)
`define SOC_IFC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_LOW                                     (0)
`define SOC_IFC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_MASK                                    (32'h1)
`define SOC_IFC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_LOW                                     (1)
`define SOC_IFC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_MASK                                    (32'h2)
`endif
`ifndef SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R                                                   (32'h804)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_INTERNAL_EN_LOW                             (0)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_INTERNAL_EN_MASK                            (32'h1)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_INV_DEV_EN_LOW                              (1)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_INV_DEV_EN_MASK                             (32'h2)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_CMD_FAIL_EN_LOW                             (2)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_CMD_FAIL_EN_MASK                            (32'h4)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_BAD_FUSE_EN_LOW                             (3)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_BAD_FUSE_EN_MASK                            (32'h8)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_ICCM_BLOCKED_EN_LOW                         (4)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_ICCM_BLOCKED_EN_MASK                        (32'h10)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_MBOX_ECC_UNC_EN_LOW                         (5)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_MBOX_ECC_UNC_EN_MASK                        (32'h20)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_WDT_TIMER1_TIMEOUT_EN_LOW                   (6)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_WDT_TIMER1_TIMEOUT_EN_MASK                  (32'h40)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_WDT_TIMER2_TIMEOUT_EN_LOW                   (7)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_WDT_TIMER2_TIMEOUT_EN_MASK                  (32'h80)
`endif
`ifndef SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R                                                   (32'h808)
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_CMD_AVAIL_EN_LOW                            (0)
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_CMD_AVAIL_EN_MASK                           (32'h1)
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_MBOX_ECC_COR_EN_LOW                         (1)
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_MBOX_ECC_COR_EN_MASK                        (32'h2)
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_DEBUG_LOCKED_EN_LOW                         (2)
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_DEBUG_LOCKED_EN_MASK                        (32'h4)
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_SCAN_MODE_EN_LOW                            (3)
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_SCAN_MODE_EN_MASK                           (32'h8)
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_SOC_REQ_LOCK_EN_LOW                         (4)
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_SOC_REQ_LOCK_EN_MASK                        (32'h10)
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_GEN_IN_TOGGLE_EN_LOW                        (5)
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_GEN_IN_TOGGLE_EN_MASK                       (32'h20)
`endif
`ifndef SOC_IFC_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R                                               (32'h80c)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS_LOW                                   (0)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS_MASK                                  (32'h1)
`endif
`ifndef SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R                                               (32'h810)
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS_LOW                                   (0)
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS_MASK                                  (32'h1)
`endif
`ifndef SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R                                             (32'h814)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_INTERNAL_STS_LOW                      (0)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_INTERNAL_STS_MASK                     (32'h1)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_INV_DEV_STS_LOW                       (1)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_INV_DEV_STS_MASK                      (32'h2)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_CMD_FAIL_STS_LOW                      (2)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_CMD_FAIL_STS_MASK                     (32'h4)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_BAD_FUSE_STS_LOW                      (3)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_BAD_FUSE_STS_MASK                     (32'h8)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_ICCM_BLOCKED_STS_LOW                  (4)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_ICCM_BLOCKED_STS_MASK                 (32'h10)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_MBOX_ECC_UNC_STS_LOW                  (5)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_MBOX_ECC_UNC_STS_MASK                 (32'h20)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_WDT_TIMER1_TIMEOUT_STS_LOW            (6)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_WDT_TIMER1_TIMEOUT_STS_MASK           (32'h40)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_WDT_TIMER2_TIMEOUT_STS_LOW            (7)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_WDT_TIMER2_TIMEOUT_STS_MASK           (32'h80)
`endif
`ifndef SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R                                             (32'h818)
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_AVAIL_STS_LOW                     (0)
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_AVAIL_STS_MASK                    (32'h1)
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_MBOX_ECC_COR_STS_LOW                  (1)
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_MBOX_ECC_COR_STS_MASK                 (32'h2)
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_DEBUG_LOCKED_STS_LOW                  (2)
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_DEBUG_LOCKED_STS_MASK                 (32'h4)
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_SCAN_MODE_STS_LOW                     (3)
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_SCAN_MODE_STS_MASK                    (32'h8)
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_SOC_REQ_LOCK_STS_LOW                  (4)
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_SOC_REQ_LOCK_STS_MASK                 (32'h10)
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_GEN_IN_TOGGLE_STS_LOW                 (5)
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_GEN_IN_TOGGLE_STS_MASK                (32'h20)
`endif
`ifndef SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R                                                 (32'h81c)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_INTERNAL_TRIG_LOW                         (0)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_INTERNAL_TRIG_MASK                        (32'h1)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_INV_DEV_TRIG_LOW                          (1)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_INV_DEV_TRIG_MASK                         (32'h2)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_CMD_FAIL_TRIG_LOW                         (2)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_CMD_FAIL_TRIG_MASK                        (32'h4)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_BAD_FUSE_TRIG_LOW                         (3)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_BAD_FUSE_TRIG_MASK                        (32'h8)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_ICCM_BLOCKED_TRIG_LOW                     (4)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_ICCM_BLOCKED_TRIG_MASK                    (32'h10)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_MBOX_ECC_UNC_TRIG_LOW                     (5)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_MBOX_ECC_UNC_TRIG_MASK                    (32'h20)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_WDT_TIMER1_TIMEOUT_TRIG_LOW               (6)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_WDT_TIMER1_TIMEOUT_TRIG_MASK              (32'h40)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_WDT_TIMER2_TIMEOUT_TRIG_LOW               (7)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_WDT_TIMER2_TIMEOUT_TRIG_MASK              (32'h80)
`endif
`ifndef SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R                                                 (32'h820)
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_AVAIL_TRIG_LOW                        (0)
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_AVAIL_TRIG_MASK                       (32'h1)
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_MBOX_ECC_COR_TRIG_LOW                     (1)
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_MBOX_ECC_COR_TRIG_MASK                    (32'h2)
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_DEBUG_LOCKED_TRIG_LOW                     (2)
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_DEBUG_LOCKED_TRIG_MASK                    (32'h4)
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_SCAN_MODE_TRIG_LOW                        (3)
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_SCAN_MODE_TRIG_MASK                       (32'h8)
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_SOC_REQ_LOCK_TRIG_LOW                     (4)
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_SOC_REQ_LOCK_TRIG_MASK                    (32'h10)
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_GEN_IN_TOGGLE_TRIG_LOW                    (5)
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_GEN_IN_TOGGLE_TRIG_MASK                   (32'h20)
`endif
`ifndef SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_R
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_R                                       (32'h900)
`endif
`ifndef SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INV_DEV_INTR_COUNT_R
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INV_DEV_INTR_COUNT_R                                        (32'h904)
`endif
`ifndef SOC_IFC_REG_INTR_BLOCK_RF_ERROR_CMD_FAIL_INTR_COUNT_R
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_CMD_FAIL_INTR_COUNT_R                                       (32'h908)
`endif
`ifndef SOC_IFC_REG_INTR_BLOCK_RF_ERROR_BAD_FUSE_INTR_COUNT_R
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_BAD_FUSE_INTR_COUNT_R                                       (32'h90c)
`endif
`ifndef SOC_IFC_REG_INTR_BLOCK_RF_ERROR_ICCM_BLOCKED_INTR_COUNT_R
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_ICCM_BLOCKED_INTR_COUNT_R                                   (32'h910)
`endif
`ifndef SOC_IFC_REG_INTR_BLOCK_RF_ERROR_MBOX_ECC_UNC_INTR_COUNT_R
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_MBOX_ECC_UNC_INTR_COUNT_R                                   (32'h914)
`endif
`ifndef SOC_IFC_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_R
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_R                             (32'h918)
`endif
`ifndef SOC_IFC_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_R
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_R                             (32'h91c)
`endif
`ifndef SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_CMD_AVAIL_INTR_COUNT_R
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_CMD_AVAIL_INTR_COUNT_R                                      (32'h980)
`endif
`ifndef SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_MBOX_ECC_COR_INTR_COUNT_R
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_MBOX_ECC_COR_INTR_COUNT_R                                   (32'h984)
`endif
`ifndef SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_R
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_R                                   (32'h988)
`endif
`ifndef SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_R
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_R                                      (32'h98c)
`endif
`ifndef SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_SOC_REQ_LOCK_INTR_COUNT_R
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_SOC_REQ_LOCK_INTR_COUNT_R                                   (32'h990)
`endif
`ifndef SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_R
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_R                                  (32'h994)
`endif
`ifndef SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R                                  (32'ha00)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R_PULSE_LOW                        (0)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R_PULSE_MASK                       (32'h1)
`endif
`ifndef SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INV_DEV_INTR_COUNT_INCR_R
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INV_DEV_INTR_COUNT_INCR_R                                   (32'ha04)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INV_DEV_INTR_COUNT_INCR_R_PULSE_LOW                         (0)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INV_DEV_INTR_COUNT_INCR_R_PULSE_MASK                        (32'h1)
`endif
`ifndef SOC_IFC_REG_INTR_BLOCK_RF_ERROR_CMD_FAIL_INTR_COUNT_INCR_R
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_CMD_FAIL_INTR_COUNT_INCR_R                                  (32'ha08)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_CMD_FAIL_INTR_COUNT_INCR_R_PULSE_LOW                        (0)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_CMD_FAIL_INTR_COUNT_INCR_R_PULSE_MASK                       (32'h1)
`endif
`ifndef SOC_IFC_REG_INTR_BLOCK_RF_ERROR_BAD_FUSE_INTR_COUNT_INCR_R
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_BAD_FUSE_INTR_COUNT_INCR_R                                  (32'ha0c)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_BAD_FUSE_INTR_COUNT_INCR_R_PULSE_LOW                        (0)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_BAD_FUSE_INTR_COUNT_INCR_R_PULSE_MASK                       (32'h1)
`endif
`ifndef SOC_IFC_REG_INTR_BLOCK_RF_ERROR_ICCM_BLOCKED_INTR_COUNT_INCR_R
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_ICCM_BLOCKED_INTR_COUNT_INCR_R                              (32'ha10)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_ICCM_BLOCKED_INTR_COUNT_INCR_R_PULSE_LOW                    (0)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_ICCM_BLOCKED_INTR_COUNT_INCR_R_PULSE_MASK                   (32'h1)
`endif
`ifndef SOC_IFC_REG_INTR_BLOCK_RF_ERROR_MBOX_ECC_UNC_INTR_COUNT_INCR_R
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_MBOX_ECC_UNC_INTR_COUNT_INCR_R                              (32'ha14)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_MBOX_ECC_UNC_INTR_COUNT_INCR_R_PULSE_LOW                    (0)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_MBOX_ECC_UNC_INTR_COUNT_INCR_R_PULSE_MASK                   (32'h1)
`endif
`ifndef SOC_IFC_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_INCR_R
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_INCR_R                        (32'ha18)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_INCR_R_PULSE_LOW              (0)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_INCR_R_PULSE_MASK             (32'h1)
`endif
`ifndef SOC_IFC_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_INCR_R
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_INCR_R                        (32'ha1c)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_INCR_R_PULSE_LOW              (0)
`define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_INCR_R_PULSE_MASK             (32'h1)
`endif
`ifndef SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_CMD_AVAIL_INTR_COUNT_INCR_R
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_CMD_AVAIL_INTR_COUNT_INCR_R                                 (32'ha20)
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_CMD_AVAIL_INTR_COUNT_INCR_R_PULSE_LOW                       (0)
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_CMD_AVAIL_INTR_COUNT_INCR_R_PULSE_MASK                      (32'h1)
`endif
`ifndef SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_MBOX_ECC_COR_INTR_COUNT_INCR_R
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_MBOX_ECC_COR_INTR_COUNT_INCR_R                              (32'ha24)
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_MBOX_ECC_COR_INTR_COUNT_INCR_R_PULSE_LOW                    (0)
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_MBOX_ECC_COR_INTR_COUNT_INCR_R_PULSE_MASK                   (32'h1)
`endif
`ifndef SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_INCR_R
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_INCR_R                              (32'ha28)
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_INCR_R_PULSE_LOW                    (0)
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_INCR_R_PULSE_MASK                   (32'h1)
`endif
`ifndef SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_INCR_R
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_INCR_R                                 (32'ha2c)
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_INCR_R_PULSE_LOW                       (0)
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_INCR_R_PULSE_MASK                      (32'h1)
`endif
`ifndef SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_SOC_REQ_LOCK_INTR_COUNT_INCR_R
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_SOC_REQ_LOCK_INTR_COUNT_INCR_R                              (32'ha30)
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_SOC_REQ_LOCK_INTR_COUNT_INCR_R_PULSE_LOW                    (0)
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_SOC_REQ_LOCK_INTR_COUNT_INCR_R_PULSE_MASK                   (32'h1)
`endif
`ifndef SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_INCR_R
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_INCR_R                             (32'ha34)
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
`define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_INCR_R_PULSE_MASK                  (32'h1)
`endif


`endif