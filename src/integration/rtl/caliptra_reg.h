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
#ifndef CALIPTRA_REG_HEADER
#define CALIPTRA_REG_HEADER


#define CLP_BASE_ADDR                                                                               (0x0)
#define CLP_DOE_REG_BASE_ADDR                                                                       (0x10000000)
#define CLP_DOE_REG_DOE_IV_0                                                                        (0x10000000)
#ifndef DOE_REG_DOE_IV_0
#define DOE_REG_DOE_IV_0                                                                            (0x0)
#endif
#define CLP_DOE_REG_DOE_IV_1                                                                        (0x10000004)
#ifndef DOE_REG_DOE_IV_1
#define DOE_REG_DOE_IV_1                                                                            (0x4)
#endif
#define CLP_DOE_REG_DOE_IV_2                                                                        (0x10000008)
#ifndef DOE_REG_DOE_IV_2
#define DOE_REG_DOE_IV_2                                                                            (0x8)
#endif
#define CLP_DOE_REG_DOE_IV_3                                                                        (0x1000000c)
#ifndef DOE_REG_DOE_IV_3
#define DOE_REG_DOE_IV_3                                                                            (0xc)
#endif
#define CLP_DOE_REG_DOE_CTRL                                                                        (0x10000010)
#ifndef DOE_REG_DOE_CTRL
#define DOE_REG_DOE_CTRL                                                                            (0x10)
#define DOE_REG_DOE_CTRL_CMD_LOW                                                                    (0)
#define DOE_REG_DOE_CTRL_CMD_MASK                                                                   (0x3)
#define DOE_REG_DOE_CTRL_DEST_LOW                                                                   (2)
#define DOE_REG_DOE_CTRL_DEST_MASK                                                                  (0x7c)
#endif
#define CLP_DOE_REG_DOE_STATUS                                                                      (0x10000014)
#ifndef DOE_REG_DOE_STATUS
#define DOE_REG_DOE_STATUS                                                                          (0x14)
#define DOE_REG_DOE_STATUS_READY_LOW                                                                (0)
#define DOE_REG_DOE_STATUS_READY_MASK                                                               (0x1)
#define DOE_REG_DOE_STATUS_VALID_LOW                                                                (1)
#define DOE_REG_DOE_STATUS_VALID_MASK                                                               (0x2)
#define DOE_REG_DOE_STATUS_UDS_FLOW_DONE_LOW                                                        (2)
#define DOE_REG_DOE_STATUS_UDS_FLOW_DONE_MASK                                                       (0x4)
#define DOE_REG_DOE_STATUS_FE_FLOW_DONE_LOW                                                         (3)
#define DOE_REG_DOE_STATUS_FE_FLOW_DONE_MASK                                                        (0x8)
#define DOE_REG_DOE_STATUS_DEOBF_SECRETS_CLEARED_LOW                                                (4)
#define DOE_REG_DOE_STATUS_DEOBF_SECRETS_CLEARED_MASK                                               (0x10)
#endif
#define CLP_DOE_REG_INTR_BLOCK_RF_START                                                             (0x10000800)
#define CLP_DOE_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R                                                  (0x10000800)
#ifndef DOE_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R
#define DOE_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R                                                      (0x800)
#define DOE_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_LOW                                         (0)
#define DOE_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_MASK                                        (0x1)
#define DOE_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_LOW                                         (1)
#define DOE_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_MASK                                        (0x2)
#endif
#define CLP_DOE_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R                                                   (0x10000804)
#ifndef DOE_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R
#define DOE_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R                                                       (0x804)
#define DOE_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR0_EN_LOW                                         (0)
#define DOE_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR0_EN_MASK                                        (0x1)
#define DOE_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR1_EN_LOW                                         (1)
#define DOE_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR1_EN_MASK                                        (0x2)
#define DOE_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR2_EN_LOW                                         (2)
#define DOE_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR2_EN_MASK                                        (0x4)
#define DOE_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR3_EN_LOW                                         (3)
#define DOE_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR3_EN_MASK                                        (0x8)
#endif
#define CLP_DOE_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R                                                   (0x10000808)
#ifndef DOE_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R
#define DOE_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R                                                       (0x808)
#define DOE_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_CMD_DONE_EN_LOW                                 (0)
#define DOE_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_CMD_DONE_EN_MASK                                (0x1)
#endif
#define CLP_DOE_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R                                               (0x1000080c)
#ifndef DOE_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R
#define DOE_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R                                                   (0x80c)
#define DOE_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS_LOW                                       (0)
#define DOE_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS_MASK                                      (0x1)
#endif
#define CLP_DOE_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R                                               (0x10000810)
#ifndef DOE_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R
#define DOE_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R                                                   (0x810)
#define DOE_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS_LOW                                       (0)
#define DOE_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS_MASK                                      (0x1)
#endif
#define CLP_DOE_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R                                             (0x10000814)
#ifndef DOE_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R
#define DOE_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R                                                 (0x814)
#define DOE_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR0_STS_LOW                                  (0)
#define DOE_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR0_STS_MASK                                 (0x1)
#define DOE_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR1_STS_LOW                                  (1)
#define DOE_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR1_STS_MASK                                 (0x2)
#define DOE_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR2_STS_LOW                                  (2)
#define DOE_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR2_STS_MASK                                 (0x4)
#define DOE_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR3_STS_LOW                                  (3)
#define DOE_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR3_STS_MASK                                 (0x8)
#endif
#define CLP_DOE_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R                                             (0x10000818)
#ifndef DOE_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R
#define DOE_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R                                                 (0x818)
#define DOE_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_LOW                          (0)
#define DOE_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK                         (0x1)
#endif
#define CLP_DOE_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R                                                 (0x1000081c)
#ifndef DOE_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R
#define DOE_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R                                                     (0x81c)
#define DOE_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR0_TRIG_LOW                                     (0)
#define DOE_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR0_TRIG_MASK                                    (0x1)
#define DOE_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR1_TRIG_LOW                                     (1)
#define DOE_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR1_TRIG_MASK                                    (0x2)
#define DOE_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR2_TRIG_LOW                                     (2)
#define DOE_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR2_TRIG_MASK                                    (0x4)
#define DOE_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR3_TRIG_LOW                                     (3)
#define DOE_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR3_TRIG_MASK                                    (0x8)
#endif
#define CLP_DOE_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R                                                 (0x10000820)
#ifndef DOE_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R
#define DOE_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R                                                     (0x820)
#define DOE_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_DONE_TRIG_LOW                             (0)
#define DOE_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_DONE_TRIG_MASK                            (0x1)
#endif
#define CLP_DOE_REG_INTR_BLOCK_RF_ERROR0_INTR_COUNT_R                                               (0x10000900)
#ifndef DOE_REG_INTR_BLOCK_RF_ERROR0_INTR_COUNT_R
#define DOE_REG_INTR_BLOCK_RF_ERROR0_INTR_COUNT_R                                                   (0x900)
#endif
#define CLP_DOE_REG_INTR_BLOCK_RF_ERROR1_INTR_COUNT_R                                               (0x10000904)
#ifndef DOE_REG_INTR_BLOCK_RF_ERROR1_INTR_COUNT_R
#define DOE_REG_INTR_BLOCK_RF_ERROR1_INTR_COUNT_R                                                   (0x904)
#endif
#define CLP_DOE_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_R                                               (0x10000908)
#ifndef DOE_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_R
#define DOE_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_R                                                   (0x908)
#endif
#define CLP_DOE_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_R                                               (0x1000090c)
#ifndef DOE_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_R
#define DOE_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_R                                                   (0x90c)
#endif
#define CLP_DOE_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R                                       (0x10000980)
#ifndef DOE_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R
#define DOE_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R                                           (0x980)
#endif
#define CLP_DOE_REG_INTR_BLOCK_RF_ERROR0_INTR_COUNT_INCR_R                                          (0x10000a00)
#ifndef DOE_REG_INTR_BLOCK_RF_ERROR0_INTR_COUNT_INCR_R
#define DOE_REG_INTR_BLOCK_RF_ERROR0_INTR_COUNT_INCR_R                                              (0xa00)
#define DOE_REG_INTR_BLOCK_RF_ERROR0_INTR_COUNT_INCR_R_PULSE_LOW                                    (0)
#define DOE_REG_INTR_BLOCK_RF_ERROR0_INTR_COUNT_INCR_R_PULSE_MASK                                   (0x1)
#endif
#define CLP_DOE_REG_INTR_BLOCK_RF_ERROR1_INTR_COUNT_INCR_R                                          (0x10000a04)
#ifndef DOE_REG_INTR_BLOCK_RF_ERROR1_INTR_COUNT_INCR_R
#define DOE_REG_INTR_BLOCK_RF_ERROR1_INTR_COUNT_INCR_R                                              (0xa04)
#define DOE_REG_INTR_BLOCK_RF_ERROR1_INTR_COUNT_INCR_R_PULSE_LOW                                    (0)
#define DOE_REG_INTR_BLOCK_RF_ERROR1_INTR_COUNT_INCR_R_PULSE_MASK                                   (0x1)
#endif
#define CLP_DOE_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R                                          (0x10000a08)
#ifndef DOE_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R
#define DOE_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R                                              (0xa08)
#define DOE_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R_PULSE_LOW                                    (0)
#define DOE_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R_PULSE_MASK                                   (0x1)
#endif
#define CLP_DOE_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R                                          (0x10000a0c)
#ifndef DOE_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R
#define DOE_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R                                              (0xa0c)
#define DOE_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R_PULSE_LOW                                    (0)
#define DOE_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R_PULSE_MASK                                   (0x1)
#endif
#define CLP_DOE_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R                                  (0x10000a10)
#ifndef DOE_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R
#define DOE_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R                                      (0xa10)
#define DOE_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R_PULSE_LOW                            (0)
#define DOE_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R_PULSE_MASK                           (0x1)
#endif
#define CLP_ECC_REG_BASE_ADDR                                                                       (0x10008000)
#define CLP_ECC_REG_ECC_NAME_0                                                                      (0x10008000)
#ifndef ECC_REG_ECC_NAME_0
#define ECC_REG_ECC_NAME_0                                                                          (0x0)
#endif
#define CLP_ECC_REG_ECC_NAME_1                                                                      (0x10008004)
#ifndef ECC_REG_ECC_NAME_1
#define ECC_REG_ECC_NAME_1                                                                          (0x4)
#endif
#define CLP_ECC_REG_ECC_VERSION_0                                                                   (0x10008008)
#ifndef ECC_REG_ECC_VERSION_0
#define ECC_REG_ECC_VERSION_0                                                                       (0x8)
#endif
#define CLP_ECC_REG_ECC_VERSION_1                                                                   (0x1000800c)
#ifndef ECC_REG_ECC_VERSION_1
#define ECC_REG_ECC_VERSION_1                                                                       (0xc)
#endif
#define CLP_ECC_REG_ECC_CTRL                                                                        (0x10008010)
#ifndef ECC_REG_ECC_CTRL
#define ECC_REG_ECC_CTRL                                                                            (0x10)
#define ECC_REG_ECC_CTRL_CTRL_LOW                                                                   (0)
#define ECC_REG_ECC_CTRL_CTRL_MASK                                                                  (0x3)
#define ECC_REG_ECC_CTRL_ZEROIZE_LOW                                                                (2)
#define ECC_REG_ECC_CTRL_ZEROIZE_MASK                                                               (0x4)
#define ECC_REG_ECC_CTRL_PCR_SIGN_LOW                                                               (3)
#define ECC_REG_ECC_CTRL_PCR_SIGN_MASK                                                              (0x8)
#define ECC_REG_ECC_CTRL_DH_SHAREDKEY_LOW                                                           (4)
#define ECC_REG_ECC_CTRL_DH_SHAREDKEY_MASK                                                          (0x10)
#endif
#define CLP_ECC_REG_ECC_STATUS                                                                      (0x10008018)
#ifndef ECC_REG_ECC_STATUS
#define ECC_REG_ECC_STATUS                                                                          (0x18)
#define ECC_REG_ECC_STATUS_READY_LOW                                                                (0)
#define ECC_REG_ECC_STATUS_READY_MASK                                                               (0x1)
#define ECC_REG_ECC_STATUS_VALID_LOW                                                                (1)
#define ECC_REG_ECC_STATUS_VALID_MASK                                                               (0x2)
#endif
#define CLP_ECC_REG_ECC_SEED_0                                                                      (0x10008080)
#ifndef ECC_REG_ECC_SEED_0
#define ECC_REG_ECC_SEED_0                                                                          (0x80)
#endif
#define CLP_ECC_REG_ECC_SEED_1                                                                      (0x10008084)
#ifndef ECC_REG_ECC_SEED_1
#define ECC_REG_ECC_SEED_1                                                                          (0x84)
#endif
#define CLP_ECC_REG_ECC_SEED_2                                                                      (0x10008088)
#ifndef ECC_REG_ECC_SEED_2
#define ECC_REG_ECC_SEED_2                                                                          (0x88)
#endif
#define CLP_ECC_REG_ECC_SEED_3                                                                      (0x1000808c)
#ifndef ECC_REG_ECC_SEED_3
#define ECC_REG_ECC_SEED_3                                                                          (0x8c)
#endif
#define CLP_ECC_REG_ECC_SEED_4                                                                      (0x10008090)
#ifndef ECC_REG_ECC_SEED_4
#define ECC_REG_ECC_SEED_4                                                                          (0x90)
#endif
#define CLP_ECC_REG_ECC_SEED_5                                                                      (0x10008094)
#ifndef ECC_REG_ECC_SEED_5
#define ECC_REG_ECC_SEED_5                                                                          (0x94)
#endif
#define CLP_ECC_REG_ECC_SEED_6                                                                      (0x10008098)
#ifndef ECC_REG_ECC_SEED_6
#define ECC_REG_ECC_SEED_6                                                                          (0x98)
#endif
#define CLP_ECC_REG_ECC_SEED_7                                                                      (0x1000809c)
#ifndef ECC_REG_ECC_SEED_7
#define ECC_REG_ECC_SEED_7                                                                          (0x9c)
#endif
#define CLP_ECC_REG_ECC_SEED_8                                                                      (0x100080a0)
#ifndef ECC_REG_ECC_SEED_8
#define ECC_REG_ECC_SEED_8                                                                          (0xa0)
#endif
#define CLP_ECC_REG_ECC_SEED_9                                                                      (0x100080a4)
#ifndef ECC_REG_ECC_SEED_9
#define ECC_REG_ECC_SEED_9                                                                          (0xa4)
#endif
#define CLP_ECC_REG_ECC_SEED_10                                                                     (0x100080a8)
#ifndef ECC_REG_ECC_SEED_10
#define ECC_REG_ECC_SEED_10                                                                         (0xa8)
#endif
#define CLP_ECC_REG_ECC_SEED_11                                                                     (0x100080ac)
#ifndef ECC_REG_ECC_SEED_11
#define ECC_REG_ECC_SEED_11                                                                         (0xac)
#endif
#define CLP_ECC_REG_ECC_MSG_0                                                                       (0x10008100)
#ifndef ECC_REG_ECC_MSG_0
#define ECC_REG_ECC_MSG_0                                                                           (0x100)
#endif
#define CLP_ECC_REG_ECC_MSG_1                                                                       (0x10008104)
#ifndef ECC_REG_ECC_MSG_1
#define ECC_REG_ECC_MSG_1                                                                           (0x104)
#endif
#define CLP_ECC_REG_ECC_MSG_2                                                                       (0x10008108)
#ifndef ECC_REG_ECC_MSG_2
#define ECC_REG_ECC_MSG_2                                                                           (0x108)
#endif
#define CLP_ECC_REG_ECC_MSG_3                                                                       (0x1000810c)
#ifndef ECC_REG_ECC_MSG_3
#define ECC_REG_ECC_MSG_3                                                                           (0x10c)
#endif
#define CLP_ECC_REG_ECC_MSG_4                                                                       (0x10008110)
#ifndef ECC_REG_ECC_MSG_4
#define ECC_REG_ECC_MSG_4                                                                           (0x110)
#endif
#define CLP_ECC_REG_ECC_MSG_5                                                                       (0x10008114)
#ifndef ECC_REG_ECC_MSG_5
#define ECC_REG_ECC_MSG_5                                                                           (0x114)
#endif
#define CLP_ECC_REG_ECC_MSG_6                                                                       (0x10008118)
#ifndef ECC_REG_ECC_MSG_6
#define ECC_REG_ECC_MSG_6                                                                           (0x118)
#endif
#define CLP_ECC_REG_ECC_MSG_7                                                                       (0x1000811c)
#ifndef ECC_REG_ECC_MSG_7
#define ECC_REG_ECC_MSG_7                                                                           (0x11c)
#endif
#define CLP_ECC_REG_ECC_MSG_8                                                                       (0x10008120)
#ifndef ECC_REG_ECC_MSG_8
#define ECC_REG_ECC_MSG_8                                                                           (0x120)
#endif
#define CLP_ECC_REG_ECC_MSG_9                                                                       (0x10008124)
#ifndef ECC_REG_ECC_MSG_9
#define ECC_REG_ECC_MSG_9                                                                           (0x124)
#endif
#define CLP_ECC_REG_ECC_MSG_10                                                                      (0x10008128)
#ifndef ECC_REG_ECC_MSG_10
#define ECC_REG_ECC_MSG_10                                                                          (0x128)
#endif
#define CLP_ECC_REG_ECC_MSG_11                                                                      (0x1000812c)
#ifndef ECC_REG_ECC_MSG_11
#define ECC_REG_ECC_MSG_11                                                                          (0x12c)
#endif
#define CLP_ECC_REG_ECC_PRIVKEY_OUT_0                                                               (0x10008180)
#ifndef ECC_REG_ECC_PRIVKEY_OUT_0
#define ECC_REG_ECC_PRIVKEY_OUT_0                                                                   (0x180)
#endif
#define CLP_ECC_REG_ECC_PRIVKEY_OUT_1                                                               (0x10008184)
#ifndef ECC_REG_ECC_PRIVKEY_OUT_1
#define ECC_REG_ECC_PRIVKEY_OUT_1                                                                   (0x184)
#endif
#define CLP_ECC_REG_ECC_PRIVKEY_OUT_2                                                               (0x10008188)
#ifndef ECC_REG_ECC_PRIVKEY_OUT_2
#define ECC_REG_ECC_PRIVKEY_OUT_2                                                                   (0x188)
#endif
#define CLP_ECC_REG_ECC_PRIVKEY_OUT_3                                                               (0x1000818c)
#ifndef ECC_REG_ECC_PRIVKEY_OUT_3
#define ECC_REG_ECC_PRIVKEY_OUT_3                                                                   (0x18c)
#endif
#define CLP_ECC_REG_ECC_PRIVKEY_OUT_4                                                               (0x10008190)
#ifndef ECC_REG_ECC_PRIVKEY_OUT_4
#define ECC_REG_ECC_PRIVKEY_OUT_4                                                                   (0x190)
#endif
#define CLP_ECC_REG_ECC_PRIVKEY_OUT_5                                                               (0x10008194)
#ifndef ECC_REG_ECC_PRIVKEY_OUT_5
#define ECC_REG_ECC_PRIVKEY_OUT_5                                                                   (0x194)
#endif
#define CLP_ECC_REG_ECC_PRIVKEY_OUT_6                                                               (0x10008198)
#ifndef ECC_REG_ECC_PRIVKEY_OUT_6
#define ECC_REG_ECC_PRIVKEY_OUT_6                                                                   (0x198)
#endif
#define CLP_ECC_REG_ECC_PRIVKEY_OUT_7                                                               (0x1000819c)
#ifndef ECC_REG_ECC_PRIVKEY_OUT_7
#define ECC_REG_ECC_PRIVKEY_OUT_7                                                                   (0x19c)
#endif
#define CLP_ECC_REG_ECC_PRIVKEY_OUT_8                                                               (0x100081a0)
#ifndef ECC_REG_ECC_PRIVKEY_OUT_8
#define ECC_REG_ECC_PRIVKEY_OUT_8                                                                   (0x1a0)
#endif
#define CLP_ECC_REG_ECC_PRIVKEY_OUT_9                                                               (0x100081a4)
#ifndef ECC_REG_ECC_PRIVKEY_OUT_9
#define ECC_REG_ECC_PRIVKEY_OUT_9                                                                   (0x1a4)
#endif
#define CLP_ECC_REG_ECC_PRIVKEY_OUT_10                                                              (0x100081a8)
#ifndef ECC_REG_ECC_PRIVKEY_OUT_10
#define ECC_REG_ECC_PRIVKEY_OUT_10                                                                  (0x1a8)
#endif
#define CLP_ECC_REG_ECC_PRIVKEY_OUT_11                                                              (0x100081ac)
#ifndef ECC_REG_ECC_PRIVKEY_OUT_11
#define ECC_REG_ECC_PRIVKEY_OUT_11                                                                  (0x1ac)
#endif
#define CLP_ECC_REG_ECC_PUBKEY_X_0                                                                  (0x10008200)
#ifndef ECC_REG_ECC_PUBKEY_X_0
#define ECC_REG_ECC_PUBKEY_X_0                                                                      (0x200)
#endif
#define CLP_ECC_REG_ECC_PUBKEY_X_1                                                                  (0x10008204)
#ifndef ECC_REG_ECC_PUBKEY_X_1
#define ECC_REG_ECC_PUBKEY_X_1                                                                      (0x204)
#endif
#define CLP_ECC_REG_ECC_PUBKEY_X_2                                                                  (0x10008208)
#ifndef ECC_REG_ECC_PUBKEY_X_2
#define ECC_REG_ECC_PUBKEY_X_2                                                                      (0x208)
#endif
#define CLP_ECC_REG_ECC_PUBKEY_X_3                                                                  (0x1000820c)
#ifndef ECC_REG_ECC_PUBKEY_X_3
#define ECC_REG_ECC_PUBKEY_X_3                                                                      (0x20c)
#endif
#define CLP_ECC_REG_ECC_PUBKEY_X_4                                                                  (0x10008210)
#ifndef ECC_REG_ECC_PUBKEY_X_4
#define ECC_REG_ECC_PUBKEY_X_4                                                                      (0x210)
#endif
#define CLP_ECC_REG_ECC_PUBKEY_X_5                                                                  (0x10008214)
#ifndef ECC_REG_ECC_PUBKEY_X_5
#define ECC_REG_ECC_PUBKEY_X_5                                                                      (0x214)
#endif
#define CLP_ECC_REG_ECC_PUBKEY_X_6                                                                  (0x10008218)
#ifndef ECC_REG_ECC_PUBKEY_X_6
#define ECC_REG_ECC_PUBKEY_X_6                                                                      (0x218)
#endif
#define CLP_ECC_REG_ECC_PUBKEY_X_7                                                                  (0x1000821c)
#ifndef ECC_REG_ECC_PUBKEY_X_7
#define ECC_REG_ECC_PUBKEY_X_7                                                                      (0x21c)
#endif
#define CLP_ECC_REG_ECC_PUBKEY_X_8                                                                  (0x10008220)
#ifndef ECC_REG_ECC_PUBKEY_X_8
#define ECC_REG_ECC_PUBKEY_X_8                                                                      (0x220)
#endif
#define CLP_ECC_REG_ECC_PUBKEY_X_9                                                                  (0x10008224)
#ifndef ECC_REG_ECC_PUBKEY_X_9
#define ECC_REG_ECC_PUBKEY_X_9                                                                      (0x224)
#endif
#define CLP_ECC_REG_ECC_PUBKEY_X_10                                                                 (0x10008228)
#ifndef ECC_REG_ECC_PUBKEY_X_10
#define ECC_REG_ECC_PUBKEY_X_10                                                                     (0x228)
#endif
#define CLP_ECC_REG_ECC_PUBKEY_X_11                                                                 (0x1000822c)
#ifndef ECC_REG_ECC_PUBKEY_X_11
#define ECC_REG_ECC_PUBKEY_X_11                                                                     (0x22c)
#endif
#define CLP_ECC_REG_ECC_PUBKEY_Y_0                                                                  (0x10008280)
#ifndef ECC_REG_ECC_PUBKEY_Y_0
#define ECC_REG_ECC_PUBKEY_Y_0                                                                      (0x280)
#endif
#define CLP_ECC_REG_ECC_PUBKEY_Y_1                                                                  (0x10008284)
#ifndef ECC_REG_ECC_PUBKEY_Y_1
#define ECC_REG_ECC_PUBKEY_Y_1                                                                      (0x284)
#endif
#define CLP_ECC_REG_ECC_PUBKEY_Y_2                                                                  (0x10008288)
#ifndef ECC_REG_ECC_PUBKEY_Y_2
#define ECC_REG_ECC_PUBKEY_Y_2                                                                      (0x288)
#endif
#define CLP_ECC_REG_ECC_PUBKEY_Y_3                                                                  (0x1000828c)
#ifndef ECC_REG_ECC_PUBKEY_Y_3
#define ECC_REG_ECC_PUBKEY_Y_3                                                                      (0x28c)
#endif
#define CLP_ECC_REG_ECC_PUBKEY_Y_4                                                                  (0x10008290)
#ifndef ECC_REG_ECC_PUBKEY_Y_4
#define ECC_REG_ECC_PUBKEY_Y_4                                                                      (0x290)
#endif
#define CLP_ECC_REG_ECC_PUBKEY_Y_5                                                                  (0x10008294)
#ifndef ECC_REG_ECC_PUBKEY_Y_5
#define ECC_REG_ECC_PUBKEY_Y_5                                                                      (0x294)
#endif
#define CLP_ECC_REG_ECC_PUBKEY_Y_6                                                                  (0x10008298)
#ifndef ECC_REG_ECC_PUBKEY_Y_6
#define ECC_REG_ECC_PUBKEY_Y_6                                                                      (0x298)
#endif
#define CLP_ECC_REG_ECC_PUBKEY_Y_7                                                                  (0x1000829c)
#ifndef ECC_REG_ECC_PUBKEY_Y_7
#define ECC_REG_ECC_PUBKEY_Y_7                                                                      (0x29c)
#endif
#define CLP_ECC_REG_ECC_PUBKEY_Y_8                                                                  (0x100082a0)
#ifndef ECC_REG_ECC_PUBKEY_Y_8
#define ECC_REG_ECC_PUBKEY_Y_8                                                                      (0x2a0)
#endif
#define CLP_ECC_REG_ECC_PUBKEY_Y_9                                                                  (0x100082a4)
#ifndef ECC_REG_ECC_PUBKEY_Y_9
#define ECC_REG_ECC_PUBKEY_Y_9                                                                      (0x2a4)
#endif
#define CLP_ECC_REG_ECC_PUBKEY_Y_10                                                                 (0x100082a8)
#ifndef ECC_REG_ECC_PUBKEY_Y_10
#define ECC_REG_ECC_PUBKEY_Y_10                                                                     (0x2a8)
#endif
#define CLP_ECC_REG_ECC_PUBKEY_Y_11                                                                 (0x100082ac)
#ifndef ECC_REG_ECC_PUBKEY_Y_11
#define ECC_REG_ECC_PUBKEY_Y_11                                                                     (0x2ac)
#endif
#define CLP_ECC_REG_ECC_SIGN_R_0                                                                    (0x10008300)
#ifndef ECC_REG_ECC_SIGN_R_0
#define ECC_REG_ECC_SIGN_R_0                                                                        (0x300)
#endif
#define CLP_ECC_REG_ECC_SIGN_R_1                                                                    (0x10008304)
#ifndef ECC_REG_ECC_SIGN_R_1
#define ECC_REG_ECC_SIGN_R_1                                                                        (0x304)
#endif
#define CLP_ECC_REG_ECC_SIGN_R_2                                                                    (0x10008308)
#ifndef ECC_REG_ECC_SIGN_R_2
#define ECC_REG_ECC_SIGN_R_2                                                                        (0x308)
#endif
#define CLP_ECC_REG_ECC_SIGN_R_3                                                                    (0x1000830c)
#ifndef ECC_REG_ECC_SIGN_R_3
#define ECC_REG_ECC_SIGN_R_3                                                                        (0x30c)
#endif
#define CLP_ECC_REG_ECC_SIGN_R_4                                                                    (0x10008310)
#ifndef ECC_REG_ECC_SIGN_R_4
#define ECC_REG_ECC_SIGN_R_4                                                                        (0x310)
#endif
#define CLP_ECC_REG_ECC_SIGN_R_5                                                                    (0x10008314)
#ifndef ECC_REG_ECC_SIGN_R_5
#define ECC_REG_ECC_SIGN_R_5                                                                        (0x314)
#endif
#define CLP_ECC_REG_ECC_SIGN_R_6                                                                    (0x10008318)
#ifndef ECC_REG_ECC_SIGN_R_6
#define ECC_REG_ECC_SIGN_R_6                                                                        (0x318)
#endif
#define CLP_ECC_REG_ECC_SIGN_R_7                                                                    (0x1000831c)
#ifndef ECC_REG_ECC_SIGN_R_7
#define ECC_REG_ECC_SIGN_R_7                                                                        (0x31c)
#endif
#define CLP_ECC_REG_ECC_SIGN_R_8                                                                    (0x10008320)
#ifndef ECC_REG_ECC_SIGN_R_8
#define ECC_REG_ECC_SIGN_R_8                                                                        (0x320)
#endif
#define CLP_ECC_REG_ECC_SIGN_R_9                                                                    (0x10008324)
#ifndef ECC_REG_ECC_SIGN_R_9
#define ECC_REG_ECC_SIGN_R_9                                                                        (0x324)
#endif
#define CLP_ECC_REG_ECC_SIGN_R_10                                                                   (0x10008328)
#ifndef ECC_REG_ECC_SIGN_R_10
#define ECC_REG_ECC_SIGN_R_10                                                                       (0x328)
#endif
#define CLP_ECC_REG_ECC_SIGN_R_11                                                                   (0x1000832c)
#ifndef ECC_REG_ECC_SIGN_R_11
#define ECC_REG_ECC_SIGN_R_11                                                                       (0x32c)
#endif
#define CLP_ECC_REG_ECC_SIGN_S_0                                                                    (0x10008380)
#ifndef ECC_REG_ECC_SIGN_S_0
#define ECC_REG_ECC_SIGN_S_0                                                                        (0x380)
#endif
#define CLP_ECC_REG_ECC_SIGN_S_1                                                                    (0x10008384)
#ifndef ECC_REG_ECC_SIGN_S_1
#define ECC_REG_ECC_SIGN_S_1                                                                        (0x384)
#endif
#define CLP_ECC_REG_ECC_SIGN_S_2                                                                    (0x10008388)
#ifndef ECC_REG_ECC_SIGN_S_2
#define ECC_REG_ECC_SIGN_S_2                                                                        (0x388)
#endif
#define CLP_ECC_REG_ECC_SIGN_S_3                                                                    (0x1000838c)
#ifndef ECC_REG_ECC_SIGN_S_3
#define ECC_REG_ECC_SIGN_S_3                                                                        (0x38c)
#endif
#define CLP_ECC_REG_ECC_SIGN_S_4                                                                    (0x10008390)
#ifndef ECC_REG_ECC_SIGN_S_4
#define ECC_REG_ECC_SIGN_S_4                                                                        (0x390)
#endif
#define CLP_ECC_REG_ECC_SIGN_S_5                                                                    (0x10008394)
#ifndef ECC_REG_ECC_SIGN_S_5
#define ECC_REG_ECC_SIGN_S_5                                                                        (0x394)
#endif
#define CLP_ECC_REG_ECC_SIGN_S_6                                                                    (0x10008398)
#ifndef ECC_REG_ECC_SIGN_S_6
#define ECC_REG_ECC_SIGN_S_6                                                                        (0x398)
#endif
#define CLP_ECC_REG_ECC_SIGN_S_7                                                                    (0x1000839c)
#ifndef ECC_REG_ECC_SIGN_S_7
#define ECC_REG_ECC_SIGN_S_7                                                                        (0x39c)
#endif
#define CLP_ECC_REG_ECC_SIGN_S_8                                                                    (0x100083a0)
#ifndef ECC_REG_ECC_SIGN_S_8
#define ECC_REG_ECC_SIGN_S_8                                                                        (0x3a0)
#endif
#define CLP_ECC_REG_ECC_SIGN_S_9                                                                    (0x100083a4)
#ifndef ECC_REG_ECC_SIGN_S_9
#define ECC_REG_ECC_SIGN_S_9                                                                        (0x3a4)
#endif
#define CLP_ECC_REG_ECC_SIGN_S_10                                                                   (0x100083a8)
#ifndef ECC_REG_ECC_SIGN_S_10
#define ECC_REG_ECC_SIGN_S_10                                                                       (0x3a8)
#endif
#define CLP_ECC_REG_ECC_SIGN_S_11                                                                   (0x100083ac)
#ifndef ECC_REG_ECC_SIGN_S_11
#define ECC_REG_ECC_SIGN_S_11                                                                       (0x3ac)
#endif
#define CLP_ECC_REG_ECC_VERIFY_R_0                                                                  (0x10008400)
#ifndef ECC_REG_ECC_VERIFY_R_0
#define ECC_REG_ECC_VERIFY_R_0                                                                      (0x400)
#endif
#define CLP_ECC_REG_ECC_VERIFY_R_1                                                                  (0x10008404)
#ifndef ECC_REG_ECC_VERIFY_R_1
#define ECC_REG_ECC_VERIFY_R_1                                                                      (0x404)
#endif
#define CLP_ECC_REG_ECC_VERIFY_R_2                                                                  (0x10008408)
#ifndef ECC_REG_ECC_VERIFY_R_2
#define ECC_REG_ECC_VERIFY_R_2                                                                      (0x408)
#endif
#define CLP_ECC_REG_ECC_VERIFY_R_3                                                                  (0x1000840c)
#ifndef ECC_REG_ECC_VERIFY_R_3
#define ECC_REG_ECC_VERIFY_R_3                                                                      (0x40c)
#endif
#define CLP_ECC_REG_ECC_VERIFY_R_4                                                                  (0x10008410)
#ifndef ECC_REG_ECC_VERIFY_R_4
#define ECC_REG_ECC_VERIFY_R_4                                                                      (0x410)
#endif
#define CLP_ECC_REG_ECC_VERIFY_R_5                                                                  (0x10008414)
#ifndef ECC_REG_ECC_VERIFY_R_5
#define ECC_REG_ECC_VERIFY_R_5                                                                      (0x414)
#endif
#define CLP_ECC_REG_ECC_VERIFY_R_6                                                                  (0x10008418)
#ifndef ECC_REG_ECC_VERIFY_R_6
#define ECC_REG_ECC_VERIFY_R_6                                                                      (0x418)
#endif
#define CLP_ECC_REG_ECC_VERIFY_R_7                                                                  (0x1000841c)
#ifndef ECC_REG_ECC_VERIFY_R_7
#define ECC_REG_ECC_VERIFY_R_7                                                                      (0x41c)
#endif
#define CLP_ECC_REG_ECC_VERIFY_R_8                                                                  (0x10008420)
#ifndef ECC_REG_ECC_VERIFY_R_8
#define ECC_REG_ECC_VERIFY_R_8                                                                      (0x420)
#endif
#define CLP_ECC_REG_ECC_VERIFY_R_9                                                                  (0x10008424)
#ifndef ECC_REG_ECC_VERIFY_R_9
#define ECC_REG_ECC_VERIFY_R_9                                                                      (0x424)
#endif
#define CLP_ECC_REG_ECC_VERIFY_R_10                                                                 (0x10008428)
#ifndef ECC_REG_ECC_VERIFY_R_10
#define ECC_REG_ECC_VERIFY_R_10                                                                     (0x428)
#endif
#define CLP_ECC_REG_ECC_VERIFY_R_11                                                                 (0x1000842c)
#ifndef ECC_REG_ECC_VERIFY_R_11
#define ECC_REG_ECC_VERIFY_R_11                                                                     (0x42c)
#endif
#define CLP_ECC_REG_ECC_IV_0                                                                        (0x10008480)
#ifndef ECC_REG_ECC_IV_0
#define ECC_REG_ECC_IV_0                                                                            (0x480)
#endif
#define CLP_ECC_REG_ECC_IV_1                                                                        (0x10008484)
#ifndef ECC_REG_ECC_IV_1
#define ECC_REG_ECC_IV_1                                                                            (0x484)
#endif
#define CLP_ECC_REG_ECC_IV_2                                                                        (0x10008488)
#ifndef ECC_REG_ECC_IV_2
#define ECC_REG_ECC_IV_2                                                                            (0x488)
#endif
#define CLP_ECC_REG_ECC_IV_3                                                                        (0x1000848c)
#ifndef ECC_REG_ECC_IV_3
#define ECC_REG_ECC_IV_3                                                                            (0x48c)
#endif
#define CLP_ECC_REG_ECC_IV_4                                                                        (0x10008490)
#ifndef ECC_REG_ECC_IV_4
#define ECC_REG_ECC_IV_4                                                                            (0x490)
#endif
#define CLP_ECC_REG_ECC_IV_5                                                                        (0x10008494)
#ifndef ECC_REG_ECC_IV_5
#define ECC_REG_ECC_IV_5                                                                            (0x494)
#endif
#define CLP_ECC_REG_ECC_IV_6                                                                        (0x10008498)
#ifndef ECC_REG_ECC_IV_6
#define ECC_REG_ECC_IV_6                                                                            (0x498)
#endif
#define CLP_ECC_REG_ECC_IV_7                                                                        (0x1000849c)
#ifndef ECC_REG_ECC_IV_7
#define ECC_REG_ECC_IV_7                                                                            (0x49c)
#endif
#define CLP_ECC_REG_ECC_IV_8                                                                        (0x100084a0)
#ifndef ECC_REG_ECC_IV_8
#define ECC_REG_ECC_IV_8                                                                            (0x4a0)
#endif
#define CLP_ECC_REG_ECC_IV_9                                                                        (0x100084a4)
#ifndef ECC_REG_ECC_IV_9
#define ECC_REG_ECC_IV_9                                                                            (0x4a4)
#endif
#define CLP_ECC_REG_ECC_IV_10                                                                       (0x100084a8)
#ifndef ECC_REG_ECC_IV_10
#define ECC_REG_ECC_IV_10                                                                           (0x4a8)
#endif
#define CLP_ECC_REG_ECC_IV_11                                                                       (0x100084ac)
#ifndef ECC_REG_ECC_IV_11
#define ECC_REG_ECC_IV_11                                                                           (0x4ac)
#endif
#define CLP_ECC_REG_ECC_NONCE_0                                                                     (0x10008500)
#ifndef ECC_REG_ECC_NONCE_0
#define ECC_REG_ECC_NONCE_0                                                                         (0x500)
#endif
#define CLP_ECC_REG_ECC_NONCE_1                                                                     (0x10008504)
#ifndef ECC_REG_ECC_NONCE_1
#define ECC_REG_ECC_NONCE_1                                                                         (0x504)
#endif
#define CLP_ECC_REG_ECC_NONCE_2                                                                     (0x10008508)
#ifndef ECC_REG_ECC_NONCE_2
#define ECC_REG_ECC_NONCE_2                                                                         (0x508)
#endif
#define CLP_ECC_REG_ECC_NONCE_3                                                                     (0x1000850c)
#ifndef ECC_REG_ECC_NONCE_3
#define ECC_REG_ECC_NONCE_3                                                                         (0x50c)
#endif
#define CLP_ECC_REG_ECC_NONCE_4                                                                     (0x10008510)
#ifndef ECC_REG_ECC_NONCE_4
#define ECC_REG_ECC_NONCE_4                                                                         (0x510)
#endif
#define CLP_ECC_REG_ECC_NONCE_5                                                                     (0x10008514)
#ifndef ECC_REG_ECC_NONCE_5
#define ECC_REG_ECC_NONCE_5                                                                         (0x514)
#endif
#define CLP_ECC_REG_ECC_NONCE_6                                                                     (0x10008518)
#ifndef ECC_REG_ECC_NONCE_6
#define ECC_REG_ECC_NONCE_6                                                                         (0x518)
#endif
#define CLP_ECC_REG_ECC_NONCE_7                                                                     (0x1000851c)
#ifndef ECC_REG_ECC_NONCE_7
#define ECC_REG_ECC_NONCE_7                                                                         (0x51c)
#endif
#define CLP_ECC_REG_ECC_NONCE_8                                                                     (0x10008520)
#ifndef ECC_REG_ECC_NONCE_8
#define ECC_REG_ECC_NONCE_8                                                                         (0x520)
#endif
#define CLP_ECC_REG_ECC_NONCE_9                                                                     (0x10008524)
#ifndef ECC_REG_ECC_NONCE_9
#define ECC_REG_ECC_NONCE_9                                                                         (0x524)
#endif
#define CLP_ECC_REG_ECC_NONCE_10                                                                    (0x10008528)
#ifndef ECC_REG_ECC_NONCE_10
#define ECC_REG_ECC_NONCE_10                                                                        (0x528)
#endif
#define CLP_ECC_REG_ECC_NONCE_11                                                                    (0x1000852c)
#ifndef ECC_REG_ECC_NONCE_11
#define ECC_REG_ECC_NONCE_11                                                                        (0x52c)
#endif
#define CLP_ECC_REG_ECC_PRIVKEY_IN_0                                                                (0x10008580)
#ifndef ECC_REG_ECC_PRIVKEY_IN_0
#define ECC_REG_ECC_PRIVKEY_IN_0                                                                    (0x580)
#endif
#define CLP_ECC_REG_ECC_PRIVKEY_IN_1                                                                (0x10008584)
#ifndef ECC_REG_ECC_PRIVKEY_IN_1
#define ECC_REG_ECC_PRIVKEY_IN_1                                                                    (0x584)
#endif
#define CLP_ECC_REG_ECC_PRIVKEY_IN_2                                                                (0x10008588)
#ifndef ECC_REG_ECC_PRIVKEY_IN_2
#define ECC_REG_ECC_PRIVKEY_IN_2                                                                    (0x588)
#endif
#define CLP_ECC_REG_ECC_PRIVKEY_IN_3                                                                (0x1000858c)
#ifndef ECC_REG_ECC_PRIVKEY_IN_3
#define ECC_REG_ECC_PRIVKEY_IN_3                                                                    (0x58c)
#endif
#define CLP_ECC_REG_ECC_PRIVKEY_IN_4                                                                (0x10008590)
#ifndef ECC_REG_ECC_PRIVKEY_IN_4
#define ECC_REG_ECC_PRIVKEY_IN_4                                                                    (0x590)
#endif
#define CLP_ECC_REG_ECC_PRIVKEY_IN_5                                                                (0x10008594)
#ifndef ECC_REG_ECC_PRIVKEY_IN_5
#define ECC_REG_ECC_PRIVKEY_IN_5                                                                    (0x594)
#endif
#define CLP_ECC_REG_ECC_PRIVKEY_IN_6                                                                (0x10008598)
#ifndef ECC_REG_ECC_PRIVKEY_IN_6
#define ECC_REG_ECC_PRIVKEY_IN_6                                                                    (0x598)
#endif
#define CLP_ECC_REG_ECC_PRIVKEY_IN_7                                                                (0x1000859c)
#ifndef ECC_REG_ECC_PRIVKEY_IN_7
#define ECC_REG_ECC_PRIVKEY_IN_7                                                                    (0x59c)
#endif
#define CLP_ECC_REG_ECC_PRIVKEY_IN_8                                                                (0x100085a0)
#ifndef ECC_REG_ECC_PRIVKEY_IN_8
#define ECC_REG_ECC_PRIVKEY_IN_8                                                                    (0x5a0)
#endif
#define CLP_ECC_REG_ECC_PRIVKEY_IN_9                                                                (0x100085a4)
#ifndef ECC_REG_ECC_PRIVKEY_IN_9
#define ECC_REG_ECC_PRIVKEY_IN_9                                                                    (0x5a4)
#endif
#define CLP_ECC_REG_ECC_PRIVKEY_IN_10                                                               (0x100085a8)
#ifndef ECC_REG_ECC_PRIVKEY_IN_10
#define ECC_REG_ECC_PRIVKEY_IN_10                                                                   (0x5a8)
#endif
#define CLP_ECC_REG_ECC_PRIVKEY_IN_11                                                               (0x100085ac)
#ifndef ECC_REG_ECC_PRIVKEY_IN_11
#define ECC_REG_ECC_PRIVKEY_IN_11                                                                   (0x5ac)
#endif
#define CLP_ECC_REG_ECC_DH_SHARED_KEY_0                                                             (0x100085c0)
#ifndef ECC_REG_ECC_DH_SHARED_KEY_0
#define ECC_REG_ECC_DH_SHARED_KEY_0                                                                 (0x5c0)
#endif
#define CLP_ECC_REG_ECC_DH_SHARED_KEY_1                                                             (0x100085c4)
#ifndef ECC_REG_ECC_DH_SHARED_KEY_1
#define ECC_REG_ECC_DH_SHARED_KEY_1                                                                 (0x5c4)
#endif
#define CLP_ECC_REG_ECC_DH_SHARED_KEY_2                                                             (0x100085c8)
#ifndef ECC_REG_ECC_DH_SHARED_KEY_2
#define ECC_REG_ECC_DH_SHARED_KEY_2                                                                 (0x5c8)
#endif
#define CLP_ECC_REG_ECC_DH_SHARED_KEY_3                                                             (0x100085cc)
#ifndef ECC_REG_ECC_DH_SHARED_KEY_3
#define ECC_REG_ECC_DH_SHARED_KEY_3                                                                 (0x5cc)
#endif
#define CLP_ECC_REG_ECC_DH_SHARED_KEY_4                                                             (0x100085d0)
#ifndef ECC_REG_ECC_DH_SHARED_KEY_4
#define ECC_REG_ECC_DH_SHARED_KEY_4                                                                 (0x5d0)
#endif
#define CLP_ECC_REG_ECC_DH_SHARED_KEY_5                                                             (0x100085d4)
#ifndef ECC_REG_ECC_DH_SHARED_KEY_5
#define ECC_REG_ECC_DH_SHARED_KEY_5                                                                 (0x5d4)
#endif
#define CLP_ECC_REG_ECC_DH_SHARED_KEY_6                                                             (0x100085d8)
#ifndef ECC_REG_ECC_DH_SHARED_KEY_6
#define ECC_REG_ECC_DH_SHARED_KEY_6                                                                 (0x5d8)
#endif
#define CLP_ECC_REG_ECC_DH_SHARED_KEY_7                                                             (0x100085dc)
#ifndef ECC_REG_ECC_DH_SHARED_KEY_7
#define ECC_REG_ECC_DH_SHARED_KEY_7                                                                 (0x5dc)
#endif
#define CLP_ECC_REG_ECC_DH_SHARED_KEY_8                                                             (0x100085e0)
#ifndef ECC_REG_ECC_DH_SHARED_KEY_8
#define ECC_REG_ECC_DH_SHARED_KEY_8                                                                 (0x5e0)
#endif
#define CLP_ECC_REG_ECC_DH_SHARED_KEY_9                                                             (0x100085e4)
#ifndef ECC_REG_ECC_DH_SHARED_KEY_9
#define ECC_REG_ECC_DH_SHARED_KEY_9                                                                 (0x5e4)
#endif
#define CLP_ECC_REG_ECC_DH_SHARED_KEY_10                                                            (0x100085e8)
#ifndef ECC_REG_ECC_DH_SHARED_KEY_10
#define ECC_REG_ECC_DH_SHARED_KEY_10                                                                (0x5e8)
#endif
#define CLP_ECC_REG_ECC_DH_SHARED_KEY_11                                                            (0x100085ec)
#ifndef ECC_REG_ECC_DH_SHARED_KEY_11
#define ECC_REG_ECC_DH_SHARED_KEY_11                                                                (0x5ec)
#endif
#define CLP_ECC_REG_ECC_KV_RD_PKEY_CTRL                                                             (0x10008600)
#ifndef ECC_REG_ECC_KV_RD_PKEY_CTRL
#define ECC_REG_ECC_KV_RD_PKEY_CTRL                                                                 (0x600)
#define ECC_REG_ECC_KV_RD_PKEY_CTRL_READ_EN_LOW                                                     (0)
#define ECC_REG_ECC_KV_RD_PKEY_CTRL_READ_EN_MASK                                                    (0x1)
#define ECC_REG_ECC_KV_RD_PKEY_CTRL_READ_ENTRY_LOW                                                  (1)
#define ECC_REG_ECC_KV_RD_PKEY_CTRL_READ_ENTRY_MASK                                                 (0x3e)
#define ECC_REG_ECC_KV_RD_PKEY_CTRL_PCR_HASH_EXTEND_LOW                                             (6)
#define ECC_REG_ECC_KV_RD_PKEY_CTRL_PCR_HASH_EXTEND_MASK                                            (0x40)
#define ECC_REG_ECC_KV_RD_PKEY_CTRL_RSVD_LOW                                                        (7)
#define ECC_REG_ECC_KV_RD_PKEY_CTRL_RSVD_MASK                                                       (0xffffff80)
#endif
#define CLP_ECC_REG_ECC_KV_RD_PKEY_STATUS                                                           (0x10008604)
#ifndef ECC_REG_ECC_KV_RD_PKEY_STATUS
#define ECC_REG_ECC_KV_RD_PKEY_STATUS                                                               (0x604)
#define ECC_REG_ECC_KV_RD_PKEY_STATUS_READY_LOW                                                     (0)
#define ECC_REG_ECC_KV_RD_PKEY_STATUS_READY_MASK                                                    (0x1)
#define ECC_REG_ECC_KV_RD_PKEY_STATUS_VALID_LOW                                                     (1)
#define ECC_REG_ECC_KV_RD_PKEY_STATUS_VALID_MASK                                                    (0x2)
#define ECC_REG_ECC_KV_RD_PKEY_STATUS_ERROR_LOW                                                     (2)
#define ECC_REG_ECC_KV_RD_PKEY_STATUS_ERROR_MASK                                                    (0x3fc)
#endif
#define CLP_ECC_REG_ECC_KV_RD_SEED_CTRL                                                             (0x10008608)
#ifndef ECC_REG_ECC_KV_RD_SEED_CTRL
#define ECC_REG_ECC_KV_RD_SEED_CTRL                                                                 (0x608)
#define ECC_REG_ECC_KV_RD_SEED_CTRL_READ_EN_LOW                                                     (0)
#define ECC_REG_ECC_KV_RD_SEED_CTRL_READ_EN_MASK                                                    (0x1)
#define ECC_REG_ECC_KV_RD_SEED_CTRL_READ_ENTRY_LOW                                                  (1)
#define ECC_REG_ECC_KV_RD_SEED_CTRL_READ_ENTRY_MASK                                                 (0x3e)
#define ECC_REG_ECC_KV_RD_SEED_CTRL_PCR_HASH_EXTEND_LOW                                             (6)
#define ECC_REG_ECC_KV_RD_SEED_CTRL_PCR_HASH_EXTEND_MASK                                            (0x40)
#define ECC_REG_ECC_KV_RD_SEED_CTRL_RSVD_LOW                                                        (7)
#define ECC_REG_ECC_KV_RD_SEED_CTRL_RSVD_MASK                                                       (0xffffff80)
#endif
#define CLP_ECC_REG_ECC_KV_RD_SEED_STATUS                                                           (0x1000860c)
#ifndef ECC_REG_ECC_KV_RD_SEED_STATUS
#define ECC_REG_ECC_KV_RD_SEED_STATUS                                                               (0x60c)
#define ECC_REG_ECC_KV_RD_SEED_STATUS_READY_LOW                                                     (0)
#define ECC_REG_ECC_KV_RD_SEED_STATUS_READY_MASK                                                    (0x1)
#define ECC_REG_ECC_KV_RD_SEED_STATUS_VALID_LOW                                                     (1)
#define ECC_REG_ECC_KV_RD_SEED_STATUS_VALID_MASK                                                    (0x2)
#define ECC_REG_ECC_KV_RD_SEED_STATUS_ERROR_LOW                                                     (2)
#define ECC_REG_ECC_KV_RD_SEED_STATUS_ERROR_MASK                                                    (0x3fc)
#endif
#define CLP_ECC_REG_ECC_KV_WR_PKEY_CTRL                                                             (0x10008610)
#ifndef ECC_REG_ECC_KV_WR_PKEY_CTRL
#define ECC_REG_ECC_KV_WR_PKEY_CTRL                                                                 (0x610)
#define ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_EN_LOW                                                    (0)
#define ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_EN_MASK                                                   (0x1)
#define ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_ENTRY_LOW                                                 (1)
#define ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_ENTRY_MASK                                                (0x3e)
#define ECC_REG_ECC_KV_WR_PKEY_CTRL_HMAC_KEY_DEST_VALID_LOW                                         (6)
#define ECC_REG_ECC_KV_WR_PKEY_CTRL_HMAC_KEY_DEST_VALID_MASK                                        (0x40)
#define ECC_REG_ECC_KV_WR_PKEY_CTRL_HMAC_BLOCK_DEST_VALID_LOW                                       (7)
#define ECC_REG_ECC_KV_WR_PKEY_CTRL_HMAC_BLOCK_DEST_VALID_MASK                                      (0x80)
#define ECC_REG_ECC_KV_WR_PKEY_CTRL_MLDSA_SEED_DEST_VALID_LOW                                       (8)
#define ECC_REG_ECC_KV_WR_PKEY_CTRL_MLDSA_SEED_DEST_VALID_MASK                                      (0x100)
#define ECC_REG_ECC_KV_WR_PKEY_CTRL_ECC_PKEY_DEST_VALID_LOW                                         (9)
#define ECC_REG_ECC_KV_WR_PKEY_CTRL_ECC_PKEY_DEST_VALID_MASK                                        (0x200)
#define ECC_REG_ECC_KV_WR_PKEY_CTRL_ECC_SEED_DEST_VALID_LOW                                         (10)
#define ECC_REG_ECC_KV_WR_PKEY_CTRL_ECC_SEED_DEST_VALID_MASK                                        (0x400)
#define ECC_REG_ECC_KV_WR_PKEY_CTRL_AES_KEY_DEST_VALID_LOW                                          (11)
#define ECC_REG_ECC_KV_WR_PKEY_CTRL_AES_KEY_DEST_VALID_MASK                                         (0x800)
#define ECC_REG_ECC_KV_WR_PKEY_CTRL_MLKEM_SEED_DEST_VALID_LOW                                       (12)
#define ECC_REG_ECC_KV_WR_PKEY_CTRL_MLKEM_SEED_DEST_VALID_MASK                                      (0x1000)
#define ECC_REG_ECC_KV_WR_PKEY_CTRL_MLKEM_MSG_DEST_VALID_LOW                                        (13)
#define ECC_REG_ECC_KV_WR_PKEY_CTRL_MLKEM_MSG_DEST_VALID_MASK                                       (0x2000)
#define ECC_REG_ECC_KV_WR_PKEY_CTRL_RSVD_LOW                                                        (14)
#define ECC_REG_ECC_KV_WR_PKEY_CTRL_RSVD_MASK                                                       (0xffffc000)
#endif
#define CLP_ECC_REG_ECC_KV_WR_PKEY_STATUS                                                           (0x10008614)
#ifndef ECC_REG_ECC_KV_WR_PKEY_STATUS
#define ECC_REG_ECC_KV_WR_PKEY_STATUS                                                               (0x614)
#define ECC_REG_ECC_KV_WR_PKEY_STATUS_READY_LOW                                                     (0)
#define ECC_REG_ECC_KV_WR_PKEY_STATUS_READY_MASK                                                    (0x1)
#define ECC_REG_ECC_KV_WR_PKEY_STATUS_VALID_LOW                                                     (1)
#define ECC_REG_ECC_KV_WR_PKEY_STATUS_VALID_MASK                                                    (0x2)
#define ECC_REG_ECC_KV_WR_PKEY_STATUS_ERROR_LOW                                                     (2)
#define ECC_REG_ECC_KV_WR_PKEY_STATUS_ERROR_MASK                                                    (0x3fc)
#endif
#define CLP_ECC_REG_INTR_BLOCK_RF_START                                                             (0x10008800)
#define CLP_ECC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R                                                  (0x10008800)
#ifndef ECC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R
#define ECC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R                                                      (0x800)
#define ECC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_LOW                                         (0)
#define ECC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_MASK                                        (0x1)
#define ECC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_LOW                                         (1)
#define ECC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_MASK                                        (0x2)
#endif
#define CLP_ECC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R                                                   (0x10008804)
#ifndef ECC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R
#define ECC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R                                                       (0x804)
#define ECC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_INTERNAL_EN_LOW                                 (0)
#define ECC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_INTERNAL_EN_MASK                                (0x1)
#endif
#define CLP_ECC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R                                                   (0x10008808)
#ifndef ECC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R
#define ECC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R                                                       (0x808)
#define ECC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_CMD_DONE_EN_LOW                                 (0)
#define ECC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_CMD_DONE_EN_MASK                                (0x1)
#endif
#define CLP_ECC_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R                                               (0x1000880c)
#ifndef ECC_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R
#define ECC_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R                                                   (0x80c)
#define ECC_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS_LOW                                       (0)
#define ECC_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS_MASK                                      (0x1)
#endif
#define CLP_ECC_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R                                               (0x10008810)
#ifndef ECC_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R
#define ECC_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R                                                   (0x810)
#define ECC_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS_LOW                                       (0)
#define ECC_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS_MASK                                      (0x1)
#endif
#define CLP_ECC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R                                             (0x10008814)
#ifndef ECC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R
#define ECC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R                                                 (0x814)
#define ECC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_INTERNAL_STS_LOW                          (0)
#define ECC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_INTERNAL_STS_MASK                         (0x1)
#endif
#define CLP_ECC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R                                             (0x10008818)
#ifndef ECC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R
#define ECC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R                                                 (0x818)
#define ECC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_LOW                          (0)
#define ECC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK                         (0x1)
#endif
#define CLP_ECC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R                                                 (0x1000881c)
#ifndef ECC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R
#define ECC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R                                                     (0x81c)
#define ECC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_INTERNAL_TRIG_LOW                             (0)
#define ECC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_INTERNAL_TRIG_MASK                            (0x1)
#endif
#define CLP_ECC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R                                                 (0x10008820)
#ifndef ECC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R
#define ECC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R                                                     (0x820)
#define ECC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_DONE_TRIG_LOW                             (0)
#define ECC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_DONE_TRIG_MASK                            (0x1)
#endif
#define CLP_ECC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_R                                       (0x10008900)
#ifndef ECC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_R
#define ECC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_R                                           (0x900)
#endif
#define CLP_ECC_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R                                       (0x10008980)
#ifndef ECC_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R
#define ECC_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R                                           (0x980)
#endif
#define CLP_ECC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R                                  (0x10008a00)
#ifndef ECC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R
#define ECC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R                                      (0xa00)
#define ECC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R_PULSE_LOW                            (0)
#define ECC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R_PULSE_MASK                           (0x1)
#endif
#define CLP_ECC_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R                                  (0x10008a04)
#ifndef ECC_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R
#define ECC_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R                                      (0xa04)
#define ECC_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R_PULSE_LOW                            (0)
#define ECC_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R_PULSE_MASK                           (0x1)
#endif
#define CLP_HMAC_REG_BASE_ADDR                                                                      (0x10010000)
#define CLP_HMAC_REG_HMAC512_NAME_0                                                                 (0x10010000)
#ifndef HMAC_REG_HMAC512_NAME_0
#define HMAC_REG_HMAC512_NAME_0                                                                     (0x0)
#endif
#define CLP_HMAC_REG_HMAC512_NAME_1                                                                 (0x10010004)
#ifndef HMAC_REG_HMAC512_NAME_1
#define HMAC_REG_HMAC512_NAME_1                                                                     (0x4)
#endif
#define CLP_HMAC_REG_HMAC512_VERSION_0                                                              (0x10010008)
#ifndef HMAC_REG_HMAC512_VERSION_0
#define HMAC_REG_HMAC512_VERSION_0                                                                  (0x8)
#endif
#define CLP_HMAC_REG_HMAC512_VERSION_1                                                              (0x1001000c)
#ifndef HMAC_REG_HMAC512_VERSION_1
#define HMAC_REG_HMAC512_VERSION_1                                                                  (0xc)
#endif
#define CLP_HMAC_REG_HMAC512_CTRL                                                                   (0x10010010)
#ifndef HMAC_REG_HMAC512_CTRL
#define HMAC_REG_HMAC512_CTRL                                                                       (0x10)
#define HMAC_REG_HMAC512_CTRL_INIT_LOW                                                              (0)
#define HMAC_REG_HMAC512_CTRL_INIT_MASK                                                             (0x1)
#define HMAC_REG_HMAC512_CTRL_NEXT_LOW                                                              (1)
#define HMAC_REG_HMAC512_CTRL_NEXT_MASK                                                             (0x2)
#define HMAC_REG_HMAC512_CTRL_ZEROIZE_LOW                                                           (2)
#define HMAC_REG_HMAC512_CTRL_ZEROIZE_MASK                                                          (0x4)
#define HMAC_REG_HMAC512_CTRL_MODE_LOW                                                              (3)
#define HMAC_REG_HMAC512_CTRL_MODE_MASK                                                             (0x8)
#define HMAC_REG_HMAC512_CTRL_CSR_MODE_LOW                                                          (4)
#define HMAC_REG_HMAC512_CTRL_CSR_MODE_MASK                                                         (0x10)
#define HMAC_REG_HMAC512_CTRL_RESERVED_LOW                                                          (5)
#define HMAC_REG_HMAC512_CTRL_RESERVED_MASK                                                         (0x20)
#endif
#define CLP_HMAC_REG_HMAC512_STATUS                                                                 (0x10010018)
#ifndef HMAC_REG_HMAC512_STATUS
#define HMAC_REG_HMAC512_STATUS                                                                     (0x18)
#define HMAC_REG_HMAC512_STATUS_READY_LOW                                                           (0)
#define HMAC_REG_HMAC512_STATUS_READY_MASK                                                          (0x1)
#define HMAC_REG_HMAC512_STATUS_VALID_LOW                                                           (1)
#define HMAC_REG_HMAC512_STATUS_VALID_MASK                                                          (0x2)
#endif
#define CLP_HMAC_REG_HMAC512_KEY_0                                                                  (0x10010040)
#ifndef HMAC_REG_HMAC512_KEY_0
#define HMAC_REG_HMAC512_KEY_0                                                                      (0x40)
#endif
#define CLP_HMAC_REG_HMAC512_KEY_1                                                                  (0x10010044)
#ifndef HMAC_REG_HMAC512_KEY_1
#define HMAC_REG_HMAC512_KEY_1                                                                      (0x44)
#endif
#define CLP_HMAC_REG_HMAC512_KEY_2                                                                  (0x10010048)
#ifndef HMAC_REG_HMAC512_KEY_2
#define HMAC_REG_HMAC512_KEY_2                                                                      (0x48)
#endif
#define CLP_HMAC_REG_HMAC512_KEY_3                                                                  (0x1001004c)
#ifndef HMAC_REG_HMAC512_KEY_3
#define HMAC_REG_HMAC512_KEY_3                                                                      (0x4c)
#endif
#define CLP_HMAC_REG_HMAC512_KEY_4                                                                  (0x10010050)
#ifndef HMAC_REG_HMAC512_KEY_4
#define HMAC_REG_HMAC512_KEY_4                                                                      (0x50)
#endif
#define CLP_HMAC_REG_HMAC512_KEY_5                                                                  (0x10010054)
#ifndef HMAC_REG_HMAC512_KEY_5
#define HMAC_REG_HMAC512_KEY_5                                                                      (0x54)
#endif
#define CLP_HMAC_REG_HMAC512_KEY_6                                                                  (0x10010058)
#ifndef HMAC_REG_HMAC512_KEY_6
#define HMAC_REG_HMAC512_KEY_6                                                                      (0x58)
#endif
#define CLP_HMAC_REG_HMAC512_KEY_7                                                                  (0x1001005c)
#ifndef HMAC_REG_HMAC512_KEY_7
#define HMAC_REG_HMAC512_KEY_7                                                                      (0x5c)
#endif
#define CLP_HMAC_REG_HMAC512_KEY_8                                                                  (0x10010060)
#ifndef HMAC_REG_HMAC512_KEY_8
#define HMAC_REG_HMAC512_KEY_8                                                                      (0x60)
#endif
#define CLP_HMAC_REG_HMAC512_KEY_9                                                                  (0x10010064)
#ifndef HMAC_REG_HMAC512_KEY_9
#define HMAC_REG_HMAC512_KEY_9                                                                      (0x64)
#endif
#define CLP_HMAC_REG_HMAC512_KEY_10                                                                 (0x10010068)
#ifndef HMAC_REG_HMAC512_KEY_10
#define HMAC_REG_HMAC512_KEY_10                                                                     (0x68)
#endif
#define CLP_HMAC_REG_HMAC512_KEY_11                                                                 (0x1001006c)
#ifndef HMAC_REG_HMAC512_KEY_11
#define HMAC_REG_HMAC512_KEY_11                                                                     (0x6c)
#endif
#define CLP_HMAC_REG_HMAC512_KEY_12                                                                 (0x10010070)
#ifndef HMAC_REG_HMAC512_KEY_12
#define HMAC_REG_HMAC512_KEY_12                                                                     (0x70)
#endif
#define CLP_HMAC_REG_HMAC512_KEY_13                                                                 (0x10010074)
#ifndef HMAC_REG_HMAC512_KEY_13
#define HMAC_REG_HMAC512_KEY_13                                                                     (0x74)
#endif
#define CLP_HMAC_REG_HMAC512_KEY_14                                                                 (0x10010078)
#ifndef HMAC_REG_HMAC512_KEY_14
#define HMAC_REG_HMAC512_KEY_14                                                                     (0x78)
#endif
#define CLP_HMAC_REG_HMAC512_KEY_15                                                                 (0x1001007c)
#ifndef HMAC_REG_HMAC512_KEY_15
#define HMAC_REG_HMAC512_KEY_15                                                                     (0x7c)
#endif
#define CLP_HMAC_REG_HMAC512_BLOCK_0                                                                (0x10010080)
#ifndef HMAC_REG_HMAC512_BLOCK_0
#define HMAC_REG_HMAC512_BLOCK_0                                                                    (0x80)
#endif
#define CLP_HMAC_REG_HMAC512_BLOCK_1                                                                (0x10010084)
#ifndef HMAC_REG_HMAC512_BLOCK_1
#define HMAC_REG_HMAC512_BLOCK_1                                                                    (0x84)
#endif
#define CLP_HMAC_REG_HMAC512_BLOCK_2                                                                (0x10010088)
#ifndef HMAC_REG_HMAC512_BLOCK_2
#define HMAC_REG_HMAC512_BLOCK_2                                                                    (0x88)
#endif
#define CLP_HMAC_REG_HMAC512_BLOCK_3                                                                (0x1001008c)
#ifndef HMAC_REG_HMAC512_BLOCK_3
#define HMAC_REG_HMAC512_BLOCK_3                                                                    (0x8c)
#endif
#define CLP_HMAC_REG_HMAC512_BLOCK_4                                                                (0x10010090)
#ifndef HMAC_REG_HMAC512_BLOCK_4
#define HMAC_REG_HMAC512_BLOCK_4                                                                    (0x90)
#endif
#define CLP_HMAC_REG_HMAC512_BLOCK_5                                                                (0x10010094)
#ifndef HMAC_REG_HMAC512_BLOCK_5
#define HMAC_REG_HMAC512_BLOCK_5                                                                    (0x94)
#endif
#define CLP_HMAC_REG_HMAC512_BLOCK_6                                                                (0x10010098)
#ifndef HMAC_REG_HMAC512_BLOCK_6
#define HMAC_REG_HMAC512_BLOCK_6                                                                    (0x98)
#endif
#define CLP_HMAC_REG_HMAC512_BLOCK_7                                                                (0x1001009c)
#ifndef HMAC_REG_HMAC512_BLOCK_7
#define HMAC_REG_HMAC512_BLOCK_7                                                                    (0x9c)
#endif
#define CLP_HMAC_REG_HMAC512_BLOCK_8                                                                (0x100100a0)
#ifndef HMAC_REG_HMAC512_BLOCK_8
#define HMAC_REG_HMAC512_BLOCK_8                                                                    (0xa0)
#endif
#define CLP_HMAC_REG_HMAC512_BLOCK_9                                                                (0x100100a4)
#ifndef HMAC_REG_HMAC512_BLOCK_9
#define HMAC_REG_HMAC512_BLOCK_9                                                                    (0xa4)
#endif
#define CLP_HMAC_REG_HMAC512_BLOCK_10                                                               (0x100100a8)
#ifndef HMAC_REG_HMAC512_BLOCK_10
#define HMAC_REG_HMAC512_BLOCK_10                                                                   (0xa8)
#endif
#define CLP_HMAC_REG_HMAC512_BLOCK_11                                                               (0x100100ac)
#ifndef HMAC_REG_HMAC512_BLOCK_11
#define HMAC_REG_HMAC512_BLOCK_11                                                                   (0xac)
#endif
#define CLP_HMAC_REG_HMAC512_BLOCK_12                                                               (0x100100b0)
#ifndef HMAC_REG_HMAC512_BLOCK_12
#define HMAC_REG_HMAC512_BLOCK_12                                                                   (0xb0)
#endif
#define CLP_HMAC_REG_HMAC512_BLOCK_13                                                               (0x100100b4)
#ifndef HMAC_REG_HMAC512_BLOCK_13
#define HMAC_REG_HMAC512_BLOCK_13                                                                   (0xb4)
#endif
#define CLP_HMAC_REG_HMAC512_BLOCK_14                                                               (0x100100b8)
#ifndef HMAC_REG_HMAC512_BLOCK_14
#define HMAC_REG_HMAC512_BLOCK_14                                                                   (0xb8)
#endif
#define CLP_HMAC_REG_HMAC512_BLOCK_15                                                               (0x100100bc)
#ifndef HMAC_REG_HMAC512_BLOCK_15
#define HMAC_REG_HMAC512_BLOCK_15                                                                   (0xbc)
#endif
#define CLP_HMAC_REG_HMAC512_BLOCK_16                                                               (0x100100c0)
#ifndef HMAC_REG_HMAC512_BLOCK_16
#define HMAC_REG_HMAC512_BLOCK_16                                                                   (0xc0)
#endif
#define CLP_HMAC_REG_HMAC512_BLOCK_17                                                               (0x100100c4)
#ifndef HMAC_REG_HMAC512_BLOCK_17
#define HMAC_REG_HMAC512_BLOCK_17                                                                   (0xc4)
#endif
#define CLP_HMAC_REG_HMAC512_BLOCK_18                                                               (0x100100c8)
#ifndef HMAC_REG_HMAC512_BLOCK_18
#define HMAC_REG_HMAC512_BLOCK_18                                                                   (0xc8)
#endif
#define CLP_HMAC_REG_HMAC512_BLOCK_19                                                               (0x100100cc)
#ifndef HMAC_REG_HMAC512_BLOCK_19
#define HMAC_REG_HMAC512_BLOCK_19                                                                   (0xcc)
#endif
#define CLP_HMAC_REG_HMAC512_BLOCK_20                                                               (0x100100d0)
#ifndef HMAC_REG_HMAC512_BLOCK_20
#define HMAC_REG_HMAC512_BLOCK_20                                                                   (0xd0)
#endif
#define CLP_HMAC_REG_HMAC512_BLOCK_21                                                               (0x100100d4)
#ifndef HMAC_REG_HMAC512_BLOCK_21
#define HMAC_REG_HMAC512_BLOCK_21                                                                   (0xd4)
#endif
#define CLP_HMAC_REG_HMAC512_BLOCK_22                                                               (0x100100d8)
#ifndef HMAC_REG_HMAC512_BLOCK_22
#define HMAC_REG_HMAC512_BLOCK_22                                                                   (0xd8)
#endif
#define CLP_HMAC_REG_HMAC512_BLOCK_23                                                               (0x100100dc)
#ifndef HMAC_REG_HMAC512_BLOCK_23
#define HMAC_REG_HMAC512_BLOCK_23                                                                   (0xdc)
#endif
#define CLP_HMAC_REG_HMAC512_BLOCK_24                                                               (0x100100e0)
#ifndef HMAC_REG_HMAC512_BLOCK_24
#define HMAC_REG_HMAC512_BLOCK_24                                                                   (0xe0)
#endif
#define CLP_HMAC_REG_HMAC512_BLOCK_25                                                               (0x100100e4)
#ifndef HMAC_REG_HMAC512_BLOCK_25
#define HMAC_REG_HMAC512_BLOCK_25                                                                   (0xe4)
#endif
#define CLP_HMAC_REG_HMAC512_BLOCK_26                                                               (0x100100e8)
#ifndef HMAC_REG_HMAC512_BLOCK_26
#define HMAC_REG_HMAC512_BLOCK_26                                                                   (0xe8)
#endif
#define CLP_HMAC_REG_HMAC512_BLOCK_27                                                               (0x100100ec)
#ifndef HMAC_REG_HMAC512_BLOCK_27
#define HMAC_REG_HMAC512_BLOCK_27                                                                   (0xec)
#endif
#define CLP_HMAC_REG_HMAC512_BLOCK_28                                                               (0x100100f0)
#ifndef HMAC_REG_HMAC512_BLOCK_28
#define HMAC_REG_HMAC512_BLOCK_28                                                                   (0xf0)
#endif
#define CLP_HMAC_REG_HMAC512_BLOCK_29                                                               (0x100100f4)
#ifndef HMAC_REG_HMAC512_BLOCK_29
#define HMAC_REG_HMAC512_BLOCK_29                                                                   (0xf4)
#endif
#define CLP_HMAC_REG_HMAC512_BLOCK_30                                                               (0x100100f8)
#ifndef HMAC_REG_HMAC512_BLOCK_30
#define HMAC_REG_HMAC512_BLOCK_30                                                                   (0xf8)
#endif
#define CLP_HMAC_REG_HMAC512_BLOCK_31                                                               (0x100100fc)
#ifndef HMAC_REG_HMAC512_BLOCK_31
#define HMAC_REG_HMAC512_BLOCK_31                                                                   (0xfc)
#endif
#define CLP_HMAC_REG_HMAC512_TAG_0                                                                  (0x10010100)
#ifndef HMAC_REG_HMAC512_TAG_0
#define HMAC_REG_HMAC512_TAG_0                                                                      (0x100)
#endif
#define CLP_HMAC_REG_HMAC512_TAG_1                                                                  (0x10010104)
#ifndef HMAC_REG_HMAC512_TAG_1
#define HMAC_REG_HMAC512_TAG_1                                                                      (0x104)
#endif
#define CLP_HMAC_REG_HMAC512_TAG_2                                                                  (0x10010108)
#ifndef HMAC_REG_HMAC512_TAG_2
#define HMAC_REG_HMAC512_TAG_2                                                                      (0x108)
#endif
#define CLP_HMAC_REG_HMAC512_TAG_3                                                                  (0x1001010c)
#ifndef HMAC_REG_HMAC512_TAG_3
#define HMAC_REG_HMAC512_TAG_3                                                                      (0x10c)
#endif
#define CLP_HMAC_REG_HMAC512_TAG_4                                                                  (0x10010110)
#ifndef HMAC_REG_HMAC512_TAG_4
#define HMAC_REG_HMAC512_TAG_4                                                                      (0x110)
#endif
#define CLP_HMAC_REG_HMAC512_TAG_5                                                                  (0x10010114)
#ifndef HMAC_REG_HMAC512_TAG_5
#define HMAC_REG_HMAC512_TAG_5                                                                      (0x114)
#endif
#define CLP_HMAC_REG_HMAC512_TAG_6                                                                  (0x10010118)
#ifndef HMAC_REG_HMAC512_TAG_6
#define HMAC_REG_HMAC512_TAG_6                                                                      (0x118)
#endif
#define CLP_HMAC_REG_HMAC512_TAG_7                                                                  (0x1001011c)
#ifndef HMAC_REG_HMAC512_TAG_7
#define HMAC_REG_HMAC512_TAG_7                                                                      (0x11c)
#endif
#define CLP_HMAC_REG_HMAC512_TAG_8                                                                  (0x10010120)
#ifndef HMAC_REG_HMAC512_TAG_8
#define HMAC_REG_HMAC512_TAG_8                                                                      (0x120)
#endif
#define CLP_HMAC_REG_HMAC512_TAG_9                                                                  (0x10010124)
#ifndef HMAC_REG_HMAC512_TAG_9
#define HMAC_REG_HMAC512_TAG_9                                                                      (0x124)
#endif
#define CLP_HMAC_REG_HMAC512_TAG_10                                                                 (0x10010128)
#ifndef HMAC_REG_HMAC512_TAG_10
#define HMAC_REG_HMAC512_TAG_10                                                                     (0x128)
#endif
#define CLP_HMAC_REG_HMAC512_TAG_11                                                                 (0x1001012c)
#ifndef HMAC_REG_HMAC512_TAG_11
#define HMAC_REG_HMAC512_TAG_11                                                                     (0x12c)
#endif
#define CLP_HMAC_REG_HMAC512_TAG_12                                                                 (0x10010130)
#ifndef HMAC_REG_HMAC512_TAG_12
#define HMAC_REG_HMAC512_TAG_12                                                                     (0x130)
#endif
#define CLP_HMAC_REG_HMAC512_TAG_13                                                                 (0x10010134)
#ifndef HMAC_REG_HMAC512_TAG_13
#define HMAC_REG_HMAC512_TAG_13                                                                     (0x134)
#endif
#define CLP_HMAC_REG_HMAC512_TAG_14                                                                 (0x10010138)
#ifndef HMAC_REG_HMAC512_TAG_14
#define HMAC_REG_HMAC512_TAG_14                                                                     (0x138)
#endif
#define CLP_HMAC_REG_HMAC512_TAG_15                                                                 (0x1001013c)
#ifndef HMAC_REG_HMAC512_TAG_15
#define HMAC_REG_HMAC512_TAG_15                                                                     (0x13c)
#endif
#define CLP_HMAC_REG_HMAC512_LFSR_SEED_0                                                            (0x10010140)
#ifndef HMAC_REG_HMAC512_LFSR_SEED_0
#define HMAC_REG_HMAC512_LFSR_SEED_0                                                                (0x140)
#endif
#define CLP_HMAC_REG_HMAC512_LFSR_SEED_1                                                            (0x10010144)
#ifndef HMAC_REG_HMAC512_LFSR_SEED_1
#define HMAC_REG_HMAC512_LFSR_SEED_1                                                                (0x144)
#endif
#define CLP_HMAC_REG_HMAC512_LFSR_SEED_2                                                            (0x10010148)
#ifndef HMAC_REG_HMAC512_LFSR_SEED_2
#define HMAC_REG_HMAC512_LFSR_SEED_2                                                                (0x148)
#endif
#define CLP_HMAC_REG_HMAC512_LFSR_SEED_3                                                            (0x1001014c)
#ifndef HMAC_REG_HMAC512_LFSR_SEED_3
#define HMAC_REG_HMAC512_LFSR_SEED_3                                                                (0x14c)
#endif
#define CLP_HMAC_REG_HMAC512_LFSR_SEED_4                                                            (0x10010150)
#ifndef HMAC_REG_HMAC512_LFSR_SEED_4
#define HMAC_REG_HMAC512_LFSR_SEED_4                                                                (0x150)
#endif
#define CLP_HMAC_REG_HMAC512_LFSR_SEED_5                                                            (0x10010154)
#ifndef HMAC_REG_HMAC512_LFSR_SEED_5
#define HMAC_REG_HMAC512_LFSR_SEED_5                                                                (0x154)
#endif
#define CLP_HMAC_REG_HMAC512_LFSR_SEED_6                                                            (0x10010158)
#ifndef HMAC_REG_HMAC512_LFSR_SEED_6
#define HMAC_REG_HMAC512_LFSR_SEED_6                                                                (0x158)
#endif
#define CLP_HMAC_REG_HMAC512_LFSR_SEED_7                                                            (0x1001015c)
#ifndef HMAC_REG_HMAC512_LFSR_SEED_7
#define HMAC_REG_HMAC512_LFSR_SEED_7                                                                (0x15c)
#endif
#define CLP_HMAC_REG_HMAC512_LFSR_SEED_8                                                            (0x10010160)
#ifndef HMAC_REG_HMAC512_LFSR_SEED_8
#define HMAC_REG_HMAC512_LFSR_SEED_8                                                                (0x160)
#endif
#define CLP_HMAC_REG_HMAC512_LFSR_SEED_9                                                            (0x10010164)
#ifndef HMAC_REG_HMAC512_LFSR_SEED_9
#define HMAC_REG_HMAC512_LFSR_SEED_9                                                                (0x164)
#endif
#define CLP_HMAC_REG_HMAC512_LFSR_SEED_10                                                           (0x10010168)
#ifndef HMAC_REG_HMAC512_LFSR_SEED_10
#define HMAC_REG_HMAC512_LFSR_SEED_10                                                               (0x168)
#endif
#define CLP_HMAC_REG_HMAC512_LFSR_SEED_11                                                           (0x1001016c)
#ifndef HMAC_REG_HMAC512_LFSR_SEED_11
#define HMAC_REG_HMAC512_LFSR_SEED_11                                                               (0x16c)
#endif
#define CLP_HMAC_REG_HMAC512_KV_RD_KEY_CTRL                                                         (0x10010600)
#ifndef HMAC_REG_HMAC512_KV_RD_KEY_CTRL
#define HMAC_REG_HMAC512_KV_RD_KEY_CTRL                                                             (0x600)
#define HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_EN_LOW                                                 (0)
#define HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_EN_MASK                                                (0x1)
#define HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_ENTRY_LOW                                              (1)
#define HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_ENTRY_MASK                                             (0x3e)
#define HMAC_REG_HMAC512_KV_RD_KEY_CTRL_PCR_HASH_EXTEND_LOW                                         (6)
#define HMAC_REG_HMAC512_KV_RD_KEY_CTRL_PCR_HASH_EXTEND_MASK                                        (0x40)
#define HMAC_REG_HMAC512_KV_RD_KEY_CTRL_RSVD_LOW                                                    (7)
#define HMAC_REG_HMAC512_KV_RD_KEY_CTRL_RSVD_MASK                                                   (0xffffff80)
#endif
#define CLP_HMAC_REG_HMAC512_KV_RD_KEY_STATUS                                                       (0x10010604)
#ifndef HMAC_REG_HMAC512_KV_RD_KEY_STATUS
#define HMAC_REG_HMAC512_KV_RD_KEY_STATUS                                                           (0x604)
#define HMAC_REG_HMAC512_KV_RD_KEY_STATUS_READY_LOW                                                 (0)
#define HMAC_REG_HMAC512_KV_RD_KEY_STATUS_READY_MASK                                                (0x1)
#define HMAC_REG_HMAC512_KV_RD_KEY_STATUS_VALID_LOW                                                 (1)
#define HMAC_REG_HMAC512_KV_RD_KEY_STATUS_VALID_MASK                                                (0x2)
#define HMAC_REG_HMAC512_KV_RD_KEY_STATUS_ERROR_LOW                                                 (2)
#define HMAC_REG_HMAC512_KV_RD_KEY_STATUS_ERROR_MASK                                                (0x3fc)
#endif
#define CLP_HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL                                                       (0x10010608)
#ifndef HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL
#define HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL                                                           (0x608)
#define HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL_READ_EN_LOW                                               (0)
#define HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL_READ_EN_MASK                                              (0x1)
#define HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL_READ_ENTRY_LOW                                            (1)
#define HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL_READ_ENTRY_MASK                                           (0x3e)
#define HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL_PCR_HASH_EXTEND_LOW                                       (6)
#define HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL_PCR_HASH_EXTEND_MASK                                      (0x40)
#define HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL_RSVD_LOW                                                  (7)
#define HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL_RSVD_MASK                                                 (0xffffff80)
#endif
#define CLP_HMAC_REG_HMAC512_KV_RD_BLOCK_STATUS                                                     (0x1001060c)
#ifndef HMAC_REG_HMAC512_KV_RD_BLOCK_STATUS
#define HMAC_REG_HMAC512_KV_RD_BLOCK_STATUS                                                         (0x60c)
#define HMAC_REG_HMAC512_KV_RD_BLOCK_STATUS_READY_LOW                                               (0)
#define HMAC_REG_HMAC512_KV_RD_BLOCK_STATUS_READY_MASK                                              (0x1)
#define HMAC_REG_HMAC512_KV_RD_BLOCK_STATUS_VALID_LOW                                               (1)
#define HMAC_REG_HMAC512_KV_RD_BLOCK_STATUS_VALID_MASK                                              (0x2)
#define HMAC_REG_HMAC512_KV_RD_BLOCK_STATUS_ERROR_LOW                                               (2)
#define HMAC_REG_HMAC512_KV_RD_BLOCK_STATUS_ERROR_MASK                                              (0x3fc)
#endif
#define CLP_HMAC_REG_HMAC512_KV_WR_CTRL                                                             (0x10010610)
#ifndef HMAC_REG_HMAC512_KV_WR_CTRL
#define HMAC_REG_HMAC512_KV_WR_CTRL                                                                 (0x610)
#define HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_EN_LOW                                                    (0)
#define HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_EN_MASK                                                   (0x1)
#define HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_ENTRY_LOW                                                 (1)
#define HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_ENTRY_MASK                                                (0x3e)
#define HMAC_REG_HMAC512_KV_WR_CTRL_HMAC_KEY_DEST_VALID_LOW                                         (6)
#define HMAC_REG_HMAC512_KV_WR_CTRL_HMAC_KEY_DEST_VALID_MASK                                        (0x40)
#define HMAC_REG_HMAC512_KV_WR_CTRL_HMAC_BLOCK_DEST_VALID_LOW                                       (7)
#define HMAC_REG_HMAC512_KV_WR_CTRL_HMAC_BLOCK_DEST_VALID_MASK                                      (0x80)
#define HMAC_REG_HMAC512_KV_WR_CTRL_MLDSA_SEED_DEST_VALID_LOW                                       (8)
#define HMAC_REG_HMAC512_KV_WR_CTRL_MLDSA_SEED_DEST_VALID_MASK                                      (0x100)
#define HMAC_REG_HMAC512_KV_WR_CTRL_ECC_PKEY_DEST_VALID_LOW                                         (9)
#define HMAC_REG_HMAC512_KV_WR_CTRL_ECC_PKEY_DEST_VALID_MASK                                        (0x200)
#define HMAC_REG_HMAC512_KV_WR_CTRL_ECC_SEED_DEST_VALID_LOW                                         (10)
#define HMAC_REG_HMAC512_KV_WR_CTRL_ECC_SEED_DEST_VALID_MASK                                        (0x400)
#define HMAC_REG_HMAC512_KV_WR_CTRL_AES_KEY_DEST_VALID_LOW                                          (11)
#define HMAC_REG_HMAC512_KV_WR_CTRL_AES_KEY_DEST_VALID_MASK                                         (0x800)
#define HMAC_REG_HMAC512_KV_WR_CTRL_MLKEM_SEED_DEST_VALID_LOW                                       (12)
#define HMAC_REG_HMAC512_KV_WR_CTRL_MLKEM_SEED_DEST_VALID_MASK                                      (0x1000)
#define HMAC_REG_HMAC512_KV_WR_CTRL_MLKEM_MSG_DEST_VALID_LOW                                        (13)
#define HMAC_REG_HMAC512_KV_WR_CTRL_MLKEM_MSG_DEST_VALID_MASK                                       (0x2000)
#define HMAC_REG_HMAC512_KV_WR_CTRL_RSVD_LOW                                                        (14)
#define HMAC_REG_HMAC512_KV_WR_CTRL_RSVD_MASK                                                       (0xffffc000)
#endif
#define CLP_HMAC_REG_HMAC512_KV_WR_STATUS                                                           (0x10010614)
#ifndef HMAC_REG_HMAC512_KV_WR_STATUS
#define HMAC_REG_HMAC512_KV_WR_STATUS                                                               (0x614)
#define HMAC_REG_HMAC512_KV_WR_STATUS_READY_LOW                                                     (0)
#define HMAC_REG_HMAC512_KV_WR_STATUS_READY_MASK                                                    (0x1)
#define HMAC_REG_HMAC512_KV_WR_STATUS_VALID_LOW                                                     (1)
#define HMAC_REG_HMAC512_KV_WR_STATUS_VALID_MASK                                                    (0x2)
#define HMAC_REG_HMAC512_KV_WR_STATUS_ERROR_LOW                                                     (2)
#define HMAC_REG_HMAC512_KV_WR_STATUS_ERROR_MASK                                                    (0x3fc)
#endif
#define CLP_HMAC_REG_INTR_BLOCK_RF_START                                                            (0x10010800)
#define CLP_HMAC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R                                                 (0x10010800)
#ifndef HMAC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R
#define HMAC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R                                                     (0x800)
#define HMAC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_LOW                                        (0)
#define HMAC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_MASK                                       (0x1)
#define HMAC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_LOW                                        (1)
#define HMAC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_MASK                                       (0x2)
#endif
#define CLP_HMAC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R                                                  (0x10010804)
#ifndef HMAC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R
#define HMAC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R                                                      (0x804)
#define HMAC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_KEY_MODE_ERROR_EN_LOW                                (0)
#define HMAC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_KEY_MODE_ERROR_EN_MASK                               (0x1)
#define HMAC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_KEY_ZERO_ERROR_EN_LOW                                (1)
#define HMAC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_KEY_ZERO_ERROR_EN_MASK                               (0x2)
#define HMAC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR2_EN_LOW                                        (2)
#define HMAC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR2_EN_MASK                                       (0x4)
#define HMAC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR3_EN_LOW                                        (3)
#define HMAC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR3_EN_MASK                                       (0x8)
#endif
#define CLP_HMAC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R                                                  (0x10010808)
#ifndef HMAC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R
#define HMAC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R                                                      (0x808)
#define HMAC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_CMD_DONE_EN_LOW                                (0)
#define HMAC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_CMD_DONE_EN_MASK                               (0x1)
#endif
#define CLP_HMAC_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R                                              (0x1001080c)
#ifndef HMAC_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R
#define HMAC_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R                                                  (0x80c)
#define HMAC_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS_LOW                                      (0)
#define HMAC_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS_MASK                                     (0x1)
#endif
#define CLP_HMAC_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R                                              (0x10010810)
#ifndef HMAC_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R
#define HMAC_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R                                                  (0x810)
#define HMAC_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS_LOW                                      (0)
#define HMAC_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS_MASK                                     (0x1)
#endif
#define CLP_HMAC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R                                            (0x10010814)
#ifndef HMAC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R
#define HMAC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R                                                (0x814)
#define HMAC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_KEY_MODE_ERROR_STS_LOW                         (0)
#define HMAC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_KEY_MODE_ERROR_STS_MASK                        (0x1)
#define HMAC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_KEY_ZERO_ERROR_STS_LOW                         (1)
#define HMAC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_KEY_ZERO_ERROR_STS_MASK                        (0x2)
#define HMAC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR2_STS_LOW                                 (2)
#define HMAC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR2_STS_MASK                                (0x4)
#define HMAC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR3_STS_LOW                                 (3)
#define HMAC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR3_STS_MASK                                (0x8)
#endif
#define CLP_HMAC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R                                            (0x10010818)
#ifndef HMAC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R
#define HMAC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R                                                (0x818)
#define HMAC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_LOW                         (0)
#define HMAC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK                        (0x1)
#endif
#define CLP_HMAC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R                                                (0x1001081c)
#ifndef HMAC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R
#define HMAC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R                                                    (0x81c)
#define HMAC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_KEY_MODE_ERROR_TRIG_LOW                            (0)
#define HMAC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_KEY_MODE_ERROR_TRIG_MASK                           (0x1)
#define HMAC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_KEY_ZERO_ERROR_TRIG_LOW                            (1)
#define HMAC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_KEY_ZERO_ERROR_TRIG_MASK                           (0x2)
#define HMAC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR2_TRIG_LOW                                    (2)
#define HMAC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR2_TRIG_MASK                                   (0x4)
#define HMAC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR3_TRIG_LOW                                    (3)
#define HMAC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR3_TRIG_MASK                                   (0x8)
#endif
#define CLP_HMAC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R                                                (0x10010820)
#ifndef HMAC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R
#define HMAC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R                                                    (0x820)
#define HMAC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_DONE_TRIG_LOW                            (0)
#define HMAC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_DONE_TRIG_MASK                           (0x1)
#endif
#define CLP_HMAC_REG_INTR_BLOCK_RF_KEY_MODE_ERROR_INTR_COUNT_R                                      (0x10010900)
#ifndef HMAC_REG_INTR_BLOCK_RF_KEY_MODE_ERROR_INTR_COUNT_R
#define HMAC_REG_INTR_BLOCK_RF_KEY_MODE_ERROR_INTR_COUNT_R                                          (0x900)
#endif
#define CLP_HMAC_REG_INTR_BLOCK_RF_KEY_ZERO_ERROR_INTR_COUNT_R                                      (0x10010904)
#ifndef HMAC_REG_INTR_BLOCK_RF_KEY_ZERO_ERROR_INTR_COUNT_R
#define HMAC_REG_INTR_BLOCK_RF_KEY_ZERO_ERROR_INTR_COUNT_R                                          (0x904)
#endif
#define CLP_HMAC_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_R                                              (0x10010908)
#ifndef HMAC_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_R
#define HMAC_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_R                                                  (0x908)
#endif
#define CLP_HMAC_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_R                                              (0x1001090c)
#ifndef HMAC_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_R
#define HMAC_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_R                                                  (0x90c)
#endif
#define CLP_HMAC_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R                                      (0x10010980)
#ifndef HMAC_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R
#define HMAC_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R                                          (0x980)
#endif
#define CLP_HMAC_REG_INTR_BLOCK_RF_KEY_MODE_ERROR_INTR_COUNT_INCR_R                                 (0x10010a00)
#ifndef HMAC_REG_INTR_BLOCK_RF_KEY_MODE_ERROR_INTR_COUNT_INCR_R
#define HMAC_REG_INTR_BLOCK_RF_KEY_MODE_ERROR_INTR_COUNT_INCR_R                                     (0xa00)
#define HMAC_REG_INTR_BLOCK_RF_KEY_MODE_ERROR_INTR_COUNT_INCR_R_PULSE_LOW                           (0)
#define HMAC_REG_INTR_BLOCK_RF_KEY_MODE_ERROR_INTR_COUNT_INCR_R_PULSE_MASK                          (0x1)
#endif
#define CLP_HMAC_REG_INTR_BLOCK_RF_KEY_ZERO_ERROR_INTR_COUNT_INCR_R                                 (0x10010a04)
#ifndef HMAC_REG_INTR_BLOCK_RF_KEY_ZERO_ERROR_INTR_COUNT_INCR_R
#define HMAC_REG_INTR_BLOCK_RF_KEY_ZERO_ERROR_INTR_COUNT_INCR_R                                     (0xa04)
#define HMAC_REG_INTR_BLOCK_RF_KEY_ZERO_ERROR_INTR_COUNT_INCR_R_PULSE_LOW                           (0)
#define HMAC_REG_INTR_BLOCK_RF_KEY_ZERO_ERROR_INTR_COUNT_INCR_R_PULSE_MASK                          (0x1)
#endif
#define CLP_HMAC_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R                                         (0x10010a08)
#ifndef HMAC_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R
#define HMAC_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R                                             (0xa08)
#define HMAC_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R_PULSE_LOW                                   (0)
#define HMAC_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R_PULSE_MASK                                  (0x1)
#endif
#define CLP_HMAC_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R                                         (0x10010a0c)
#ifndef HMAC_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R
#define HMAC_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R                                             (0xa0c)
#define HMAC_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R_PULSE_LOW                                   (0)
#define HMAC_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R_PULSE_MASK                                  (0x1)
#endif
#define CLP_HMAC_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R                                 (0x10010a10)
#ifndef HMAC_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R
#define HMAC_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R                                     (0xa10)
#define HMAC_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R_PULSE_LOW                           (0)
#define HMAC_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R_PULSE_MASK                          (0x1)
#endif
#define CLP_AES_REG_BASE_ADDR                                                                       (0x10011000)
#define CLP_AES_REG_KEY_SHARE0_0                                                                    (0x10011004)
#ifndef AES_REG_KEY_SHARE0_0
#define AES_REG_KEY_SHARE0_0                                                                        (0x4)
#endif
#define CLP_AES_REG_KEY_SHARE0_1                                                                    (0x10011008)
#ifndef AES_REG_KEY_SHARE0_1
#define AES_REG_KEY_SHARE0_1                                                                        (0x8)
#endif
#define CLP_AES_REG_KEY_SHARE0_2                                                                    (0x1001100c)
#ifndef AES_REG_KEY_SHARE0_2
#define AES_REG_KEY_SHARE0_2                                                                        (0xc)
#endif
#define CLP_AES_REG_KEY_SHARE0_3                                                                    (0x10011010)
#ifndef AES_REG_KEY_SHARE0_3
#define AES_REG_KEY_SHARE0_3                                                                        (0x10)
#endif
#define CLP_AES_REG_KEY_SHARE0_4                                                                    (0x10011014)
#ifndef AES_REG_KEY_SHARE0_4
#define AES_REG_KEY_SHARE0_4                                                                        (0x14)
#endif
#define CLP_AES_REG_KEY_SHARE0_5                                                                    (0x10011018)
#ifndef AES_REG_KEY_SHARE0_5
#define AES_REG_KEY_SHARE0_5                                                                        (0x18)
#endif
#define CLP_AES_REG_KEY_SHARE0_6                                                                    (0x1001101c)
#ifndef AES_REG_KEY_SHARE0_6
#define AES_REG_KEY_SHARE0_6                                                                        (0x1c)
#endif
#define CLP_AES_REG_KEY_SHARE0_7                                                                    (0x10011020)
#ifndef AES_REG_KEY_SHARE0_7
#define AES_REG_KEY_SHARE0_7                                                                        (0x20)
#endif
#define CLP_AES_REG_KEY_SHARE1_0                                                                    (0x10011024)
#ifndef AES_REG_KEY_SHARE1_0
#define AES_REG_KEY_SHARE1_0                                                                        (0x24)
#endif
#define CLP_AES_REG_KEY_SHARE1_1                                                                    (0x10011028)
#ifndef AES_REG_KEY_SHARE1_1
#define AES_REG_KEY_SHARE1_1                                                                        (0x28)
#endif
#define CLP_AES_REG_KEY_SHARE1_2                                                                    (0x1001102c)
#ifndef AES_REG_KEY_SHARE1_2
#define AES_REG_KEY_SHARE1_2                                                                        (0x2c)
#endif
#define CLP_AES_REG_KEY_SHARE1_3                                                                    (0x10011030)
#ifndef AES_REG_KEY_SHARE1_3
#define AES_REG_KEY_SHARE1_3                                                                        (0x30)
#endif
#define CLP_AES_REG_KEY_SHARE1_4                                                                    (0x10011034)
#ifndef AES_REG_KEY_SHARE1_4
#define AES_REG_KEY_SHARE1_4                                                                        (0x34)
#endif
#define CLP_AES_REG_KEY_SHARE1_5                                                                    (0x10011038)
#ifndef AES_REG_KEY_SHARE1_5
#define AES_REG_KEY_SHARE1_5                                                                        (0x38)
#endif
#define CLP_AES_REG_KEY_SHARE1_6                                                                    (0x1001103c)
#ifndef AES_REG_KEY_SHARE1_6
#define AES_REG_KEY_SHARE1_6                                                                        (0x3c)
#endif
#define CLP_AES_REG_KEY_SHARE1_7                                                                    (0x10011040)
#ifndef AES_REG_KEY_SHARE1_7
#define AES_REG_KEY_SHARE1_7                                                                        (0x40)
#endif
#define CLP_AES_REG_IV_0                                                                            (0x10011044)
#ifndef AES_REG_IV_0
#define AES_REG_IV_0                                                                                (0x44)
#endif
#define CLP_AES_REG_IV_1                                                                            (0x10011048)
#ifndef AES_REG_IV_1
#define AES_REG_IV_1                                                                                (0x48)
#endif
#define CLP_AES_REG_IV_2                                                                            (0x1001104c)
#ifndef AES_REG_IV_2
#define AES_REG_IV_2                                                                                (0x4c)
#endif
#define CLP_AES_REG_IV_3                                                                            (0x10011050)
#ifndef AES_REG_IV_3
#define AES_REG_IV_3                                                                                (0x50)
#endif
#define CLP_AES_REG_DATA_IN_0                                                                       (0x10011054)
#ifndef AES_REG_DATA_IN_0
#define AES_REG_DATA_IN_0                                                                           (0x54)
#endif
#define CLP_AES_REG_DATA_IN_1                                                                       (0x10011058)
#ifndef AES_REG_DATA_IN_1
#define AES_REG_DATA_IN_1                                                                           (0x58)
#endif
#define CLP_AES_REG_DATA_IN_2                                                                       (0x1001105c)
#ifndef AES_REG_DATA_IN_2
#define AES_REG_DATA_IN_2                                                                           (0x5c)
#endif
#define CLP_AES_REG_DATA_IN_3                                                                       (0x10011060)
#ifndef AES_REG_DATA_IN_3
#define AES_REG_DATA_IN_3                                                                           (0x60)
#endif
#define CLP_AES_REG_DATA_OUT_0                                                                      (0x10011064)
#ifndef AES_REG_DATA_OUT_0
#define AES_REG_DATA_OUT_0                                                                          (0x64)
#endif
#define CLP_AES_REG_DATA_OUT_1                                                                      (0x10011068)
#ifndef AES_REG_DATA_OUT_1
#define AES_REG_DATA_OUT_1                                                                          (0x68)
#endif
#define CLP_AES_REG_DATA_OUT_2                                                                      (0x1001106c)
#ifndef AES_REG_DATA_OUT_2
#define AES_REG_DATA_OUT_2                                                                          (0x6c)
#endif
#define CLP_AES_REG_DATA_OUT_3                                                                      (0x10011070)
#ifndef AES_REG_DATA_OUT_3
#define AES_REG_DATA_OUT_3                                                                          (0x70)
#endif
#define CLP_AES_REG_CTRL_SHADOWED                                                                   (0x10011074)
#ifndef AES_REG_CTRL_SHADOWED
#define AES_REG_CTRL_SHADOWED                                                                       (0x74)
#define AES_REG_CTRL_SHADOWED_OPERATION_LOW                                                         (0)
#define AES_REG_CTRL_SHADOWED_OPERATION_MASK                                                        (0x3)
#define AES_REG_CTRL_SHADOWED_MODE_LOW                                                              (2)
#define AES_REG_CTRL_SHADOWED_MODE_MASK                                                             (0xfc)
#define AES_REG_CTRL_SHADOWED_KEY_LEN_LOW                                                           (8)
#define AES_REG_CTRL_SHADOWED_KEY_LEN_MASK                                                          (0x700)
#define AES_REG_CTRL_SHADOWED_SIDELOAD_LOW                                                          (11)
#define AES_REG_CTRL_SHADOWED_SIDELOAD_MASK                                                         (0x800)
#define AES_REG_CTRL_SHADOWED_PRNG_RESEED_RATE_LOW                                                  (12)
#define AES_REG_CTRL_SHADOWED_PRNG_RESEED_RATE_MASK                                                 (0x7000)
#define AES_REG_CTRL_SHADOWED_MANUAL_OPERATION_LOW                                                  (15)
#define AES_REG_CTRL_SHADOWED_MANUAL_OPERATION_MASK                                                 (0x8000)
#endif
#define CLP_AES_REG_CTRL_AUX_SHADOWED                                                               (0x10011078)
#ifndef AES_REG_CTRL_AUX_SHADOWED
#define AES_REG_CTRL_AUX_SHADOWED                                                                   (0x78)
#define AES_REG_CTRL_AUX_SHADOWED_KEY_TOUCH_FORCES_RESEED_LOW                                       (0)
#define AES_REG_CTRL_AUX_SHADOWED_KEY_TOUCH_FORCES_RESEED_MASK                                      (0x1)
#define AES_REG_CTRL_AUX_SHADOWED_FORCE_MASKS_LOW                                                   (1)
#define AES_REG_CTRL_AUX_SHADOWED_FORCE_MASKS_MASK                                                  (0x2)
#endif
#define CLP_AES_REG_CTRL_AUX_REGWEN                                                                 (0x1001107c)
#ifndef AES_REG_CTRL_AUX_REGWEN
#define AES_REG_CTRL_AUX_REGWEN                                                                     (0x7c)
#define AES_REG_CTRL_AUX_REGWEN_CTRL_AUX_REGWEN_LOW                                                 (0)
#define AES_REG_CTRL_AUX_REGWEN_CTRL_AUX_REGWEN_MASK                                                (0x1)
#endif
#define CLP_AES_REG_TRIGGER                                                                         (0x10011080)
#ifndef AES_REG_TRIGGER
#define AES_REG_TRIGGER                                                                             (0x80)
#define AES_REG_TRIGGER_START_LOW                                                                   (0)
#define AES_REG_TRIGGER_START_MASK                                                                  (0x1)
#define AES_REG_TRIGGER_KEY_IV_DATA_IN_CLEAR_LOW                                                    (1)
#define AES_REG_TRIGGER_KEY_IV_DATA_IN_CLEAR_MASK                                                   (0x2)
#define AES_REG_TRIGGER_DATA_OUT_CLEAR_LOW                                                          (2)
#define AES_REG_TRIGGER_DATA_OUT_CLEAR_MASK                                                         (0x4)
#define AES_REG_TRIGGER_PRNG_RESEED_LOW                                                             (3)
#define AES_REG_TRIGGER_PRNG_RESEED_MASK                                                            (0x8)
#endif
#define CLP_AES_REG_STATUS                                                                          (0x10011084)
#ifndef AES_REG_STATUS
#define AES_REG_STATUS                                                                              (0x84)
#define AES_REG_STATUS_IDLE_LOW                                                                     (0)
#define AES_REG_STATUS_IDLE_MASK                                                                    (0x1)
#define AES_REG_STATUS_STALL_LOW                                                                    (1)
#define AES_REG_STATUS_STALL_MASK                                                                   (0x2)
#define AES_REG_STATUS_OUTPUT_LOST_LOW                                                              (2)
#define AES_REG_STATUS_OUTPUT_LOST_MASK                                                             (0x4)
#define AES_REG_STATUS_OUTPUT_VALID_LOW                                                             (3)
#define AES_REG_STATUS_OUTPUT_VALID_MASK                                                            (0x8)
#define AES_REG_STATUS_INPUT_READY_LOW                                                              (4)
#define AES_REG_STATUS_INPUT_READY_MASK                                                             (0x10)
#define AES_REG_STATUS_ALERT_RECOV_CTRL_UPDATE_ERR_LOW                                              (5)
#define AES_REG_STATUS_ALERT_RECOV_CTRL_UPDATE_ERR_MASK                                             (0x20)
#define AES_REG_STATUS_ALERT_FATAL_FAULT_LOW                                                        (6)
#define AES_REG_STATUS_ALERT_FATAL_FAULT_MASK                                                       (0x40)
#endif
#define CLP_AES_REG_CTRL_GCM_SHADOWED                                                               (0x10011088)
#ifndef AES_REG_CTRL_GCM_SHADOWED
#define AES_REG_CTRL_GCM_SHADOWED                                                                   (0x88)
#define AES_REG_CTRL_GCM_SHADOWED_PHASE_LOW                                                         (0)
#define AES_REG_CTRL_GCM_SHADOWED_PHASE_MASK                                                        (0x3f)
#define AES_REG_CTRL_GCM_SHADOWED_NUM_VALID_BYTES_LOW                                               (6)
#define AES_REG_CTRL_GCM_SHADOWED_NUM_VALID_BYTES_MASK                                              (0x7c0)
#endif
#define CLP_AES_CLP_REG_BASE_ADDR                                                                   (0x10011800)
#define CLP_AES_CLP_REG_AES_NAME_0                                                                  (0x10011800)
#ifndef AES_CLP_REG_AES_NAME_0
#define AES_CLP_REG_AES_NAME_0                                                                      (0x0)
#endif
#define CLP_AES_CLP_REG_AES_NAME_1                                                                  (0x10011804)
#ifndef AES_CLP_REG_AES_NAME_1
#define AES_CLP_REG_AES_NAME_1                                                                      (0x4)
#endif
#define CLP_AES_CLP_REG_AES_VERSION_0                                                               (0x10011808)
#ifndef AES_CLP_REG_AES_VERSION_0
#define AES_CLP_REG_AES_VERSION_0                                                                   (0x8)
#endif
#define CLP_AES_CLP_REG_AES_VERSION_1                                                               (0x1001180c)
#ifndef AES_CLP_REG_AES_VERSION_1
#define AES_CLP_REG_AES_VERSION_1                                                                   (0xc)
#endif
#define CLP_AES_CLP_REG_ENTROPY_IF_SEED_0                                                           (0x10011910)
#ifndef AES_CLP_REG_ENTROPY_IF_SEED_0
#define AES_CLP_REG_ENTROPY_IF_SEED_0                                                               (0x110)
#endif
#define CLP_AES_CLP_REG_ENTROPY_IF_SEED_1                                                           (0x10011914)
#ifndef AES_CLP_REG_ENTROPY_IF_SEED_1
#define AES_CLP_REG_ENTROPY_IF_SEED_1                                                               (0x114)
#endif
#define CLP_AES_CLP_REG_ENTROPY_IF_SEED_2                                                           (0x10011918)
#ifndef AES_CLP_REG_ENTROPY_IF_SEED_2
#define AES_CLP_REG_ENTROPY_IF_SEED_2                                                               (0x118)
#endif
#define CLP_AES_CLP_REG_ENTROPY_IF_SEED_3                                                           (0x1001191c)
#ifndef AES_CLP_REG_ENTROPY_IF_SEED_3
#define AES_CLP_REG_ENTROPY_IF_SEED_3                                                               (0x11c)
#endif
#define CLP_AES_CLP_REG_ENTROPY_IF_SEED_4                                                           (0x10011920)
#ifndef AES_CLP_REG_ENTROPY_IF_SEED_4
#define AES_CLP_REG_ENTROPY_IF_SEED_4                                                               (0x120)
#endif
#define CLP_AES_CLP_REG_ENTROPY_IF_SEED_5                                                           (0x10011924)
#ifndef AES_CLP_REG_ENTROPY_IF_SEED_5
#define AES_CLP_REG_ENTROPY_IF_SEED_5                                                               (0x124)
#endif
#define CLP_AES_CLP_REG_ENTROPY_IF_SEED_6                                                           (0x10011928)
#ifndef AES_CLP_REG_ENTROPY_IF_SEED_6
#define AES_CLP_REG_ENTROPY_IF_SEED_6                                                               (0x128)
#endif
#define CLP_AES_CLP_REG_ENTROPY_IF_SEED_7                                                           (0x1001192c)
#ifndef AES_CLP_REG_ENTROPY_IF_SEED_7
#define AES_CLP_REG_ENTROPY_IF_SEED_7                                                               (0x12c)
#endif
#define CLP_AES_CLP_REG_ENTROPY_IF_SEED_8                                                           (0x10011930)
#ifndef AES_CLP_REG_ENTROPY_IF_SEED_8
#define AES_CLP_REG_ENTROPY_IF_SEED_8                                                               (0x130)
#endif
#define CLP_AES_CLP_REG_CTRL0                                                                       (0x10011934)
#ifndef AES_CLP_REG_CTRL0
#define AES_CLP_REG_CTRL0                                                                           (0x134)
#define AES_CLP_REG_CTRL0_ENDIAN_SWAP_LOW                                                           (0)
#define AES_CLP_REG_CTRL0_ENDIAN_SWAP_MASK                                                          (0x1)
#endif
#define CLP_AES_CLP_REG_AES_KV_RD_KEY_CTRL                                                          (0x10011a00)
#ifndef AES_CLP_REG_AES_KV_RD_KEY_CTRL
#define AES_CLP_REG_AES_KV_RD_KEY_CTRL                                                              (0x200)
#define AES_CLP_REG_AES_KV_RD_KEY_CTRL_READ_EN_LOW                                                  (0)
#define AES_CLP_REG_AES_KV_RD_KEY_CTRL_READ_EN_MASK                                                 (0x1)
#define AES_CLP_REG_AES_KV_RD_KEY_CTRL_READ_ENTRY_LOW                                               (1)
#define AES_CLP_REG_AES_KV_RD_KEY_CTRL_READ_ENTRY_MASK                                              (0x3e)
#define AES_CLP_REG_AES_KV_RD_KEY_CTRL_PCR_HASH_EXTEND_LOW                                          (6)
#define AES_CLP_REG_AES_KV_RD_KEY_CTRL_PCR_HASH_EXTEND_MASK                                         (0x40)
#define AES_CLP_REG_AES_KV_RD_KEY_CTRL_RSVD_LOW                                                     (7)
#define AES_CLP_REG_AES_KV_RD_KEY_CTRL_RSVD_MASK                                                    (0xffffff80)
#endif
#define CLP_AES_CLP_REG_AES_KV_RD_KEY_STATUS                                                        (0x10011a04)
#ifndef AES_CLP_REG_AES_KV_RD_KEY_STATUS
#define AES_CLP_REG_AES_KV_RD_KEY_STATUS                                                            (0x204)
#define AES_CLP_REG_AES_KV_RD_KEY_STATUS_READY_LOW                                                  (0)
#define AES_CLP_REG_AES_KV_RD_KEY_STATUS_READY_MASK                                                 (0x1)
#define AES_CLP_REG_AES_KV_RD_KEY_STATUS_VALID_LOW                                                  (1)
#define AES_CLP_REG_AES_KV_RD_KEY_STATUS_VALID_MASK                                                 (0x2)
#define AES_CLP_REG_AES_KV_RD_KEY_STATUS_ERROR_LOW                                                  (2)
#define AES_CLP_REG_AES_KV_RD_KEY_STATUS_ERROR_MASK                                                 (0x3fc)
#endif
#define CLP_AES_CLP_REG_INTR_BLOCK_RF_START                                                         (0x10011c00)
#define CLP_AES_CLP_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R                                              (0x10011c00)
#ifndef AES_CLP_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R
#define AES_CLP_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R                                                  (0x400)
#define AES_CLP_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_LOW                                     (0)
#define AES_CLP_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_MASK                                    (0x1)
#define AES_CLP_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_LOW                                     (1)
#define AES_CLP_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_MASK                                    (0x2)
#endif
#define CLP_AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R                                               (0x10011c04)
#ifndef AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R
#define AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R                                                   (0x404)
#define AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR0_EN_LOW                                     (0)
#define AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR0_EN_MASK                                    (0x1)
#define AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR1_EN_LOW                                     (1)
#define AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR1_EN_MASK                                    (0x2)
#define AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR2_EN_LOW                                     (2)
#define AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR2_EN_MASK                                    (0x4)
#define AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR3_EN_LOW                                     (3)
#define AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR3_EN_MASK                                    (0x8)
#endif
#define CLP_AES_CLP_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R                                               (0x10011c08)
#ifndef AES_CLP_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R
#define AES_CLP_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R                                                   (0x408)
#define AES_CLP_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_CMD_DONE_EN_LOW                             (0)
#define AES_CLP_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_CMD_DONE_EN_MASK                            (0x1)
#endif
#define CLP_AES_CLP_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R                                           (0x10011c0c)
#ifndef AES_CLP_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R
#define AES_CLP_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R                                               (0x40c)
#define AES_CLP_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS_LOW                                   (0)
#define AES_CLP_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS_MASK                                  (0x1)
#endif
#define CLP_AES_CLP_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R                                           (0x10011c10)
#ifndef AES_CLP_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R
#define AES_CLP_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R                                               (0x410)
#define AES_CLP_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS_LOW                                   (0)
#define AES_CLP_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS_MASK                                  (0x1)
#endif
#define CLP_AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R                                         (0x10011c14)
#ifndef AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R
#define AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R                                             (0x414)
#define AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR0_STS_LOW                              (0)
#define AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR0_STS_MASK                             (0x1)
#define AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR1_STS_LOW                              (1)
#define AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR1_STS_MASK                             (0x2)
#define AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR2_STS_LOW                              (2)
#define AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR2_STS_MASK                             (0x4)
#define AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR3_STS_LOW                              (3)
#define AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR3_STS_MASK                             (0x8)
#endif
#define CLP_AES_CLP_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R                                         (0x10011c18)
#ifndef AES_CLP_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R
#define AES_CLP_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R                                             (0x418)
#define AES_CLP_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_LOW                      (0)
#define AES_CLP_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK                     (0x1)
#endif
#define CLP_AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R                                             (0x10011c1c)
#ifndef AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R
#define AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R                                                 (0x41c)
#define AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR0_TRIG_LOW                                 (0)
#define AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR0_TRIG_MASK                                (0x1)
#define AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR1_TRIG_LOW                                 (1)
#define AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR1_TRIG_MASK                                (0x2)
#define AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR2_TRIG_LOW                                 (2)
#define AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR2_TRIG_MASK                                (0x4)
#define AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR3_TRIG_LOW                                 (3)
#define AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR3_TRIG_MASK                                (0x8)
#endif
#define CLP_AES_CLP_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R                                             (0x10011c20)
#ifndef AES_CLP_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R
#define AES_CLP_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R                                                 (0x420)
#define AES_CLP_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_DONE_TRIG_LOW                         (0)
#define AES_CLP_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_DONE_TRIG_MASK                        (0x1)
#endif
#define CLP_AES_CLP_REG_INTR_BLOCK_RF_ERROR0_INTR_COUNT_R                                           (0x10011d00)
#ifndef AES_CLP_REG_INTR_BLOCK_RF_ERROR0_INTR_COUNT_R
#define AES_CLP_REG_INTR_BLOCK_RF_ERROR0_INTR_COUNT_R                                               (0x500)
#endif
#define CLP_AES_CLP_REG_INTR_BLOCK_RF_ERROR1_INTR_COUNT_R                                           (0x10011d04)
#ifndef AES_CLP_REG_INTR_BLOCK_RF_ERROR1_INTR_COUNT_R
#define AES_CLP_REG_INTR_BLOCK_RF_ERROR1_INTR_COUNT_R                                               (0x504)
#endif
#define CLP_AES_CLP_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_R                                           (0x10011d08)
#ifndef AES_CLP_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_R
#define AES_CLP_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_R                                               (0x508)
#endif
#define CLP_AES_CLP_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_R                                           (0x10011d0c)
#ifndef AES_CLP_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_R
#define AES_CLP_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_R                                               (0x50c)
#endif
#define CLP_AES_CLP_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R                                   (0x10011d80)
#ifndef AES_CLP_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R
#define AES_CLP_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R                                       (0x580)
#endif
#define CLP_AES_CLP_REG_INTR_BLOCK_RF_ERROR0_INTR_COUNT_INCR_R                                      (0x10011e00)
#ifndef AES_CLP_REG_INTR_BLOCK_RF_ERROR0_INTR_COUNT_INCR_R
#define AES_CLP_REG_INTR_BLOCK_RF_ERROR0_INTR_COUNT_INCR_R                                          (0x600)
#define AES_CLP_REG_INTR_BLOCK_RF_ERROR0_INTR_COUNT_INCR_R_PULSE_LOW                                (0)
#define AES_CLP_REG_INTR_BLOCK_RF_ERROR0_INTR_COUNT_INCR_R_PULSE_MASK                               (0x1)
#endif
#define CLP_AES_CLP_REG_INTR_BLOCK_RF_ERROR1_INTR_COUNT_INCR_R                                      (0x10011e04)
#ifndef AES_CLP_REG_INTR_BLOCK_RF_ERROR1_INTR_COUNT_INCR_R
#define AES_CLP_REG_INTR_BLOCK_RF_ERROR1_INTR_COUNT_INCR_R                                          (0x604)
#define AES_CLP_REG_INTR_BLOCK_RF_ERROR1_INTR_COUNT_INCR_R_PULSE_LOW                                (0)
#define AES_CLP_REG_INTR_BLOCK_RF_ERROR1_INTR_COUNT_INCR_R_PULSE_MASK                               (0x1)
#endif
#define CLP_AES_CLP_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R                                      (0x10011e08)
#ifndef AES_CLP_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R
#define AES_CLP_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R                                          (0x608)
#define AES_CLP_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R_PULSE_LOW                                (0)
#define AES_CLP_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R_PULSE_MASK                               (0x1)
#endif
#define CLP_AES_CLP_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R                                      (0x10011e0c)
#ifndef AES_CLP_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R
#define AES_CLP_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R                                          (0x60c)
#define AES_CLP_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R_PULSE_LOW                                (0)
#define AES_CLP_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R_PULSE_MASK                               (0x1)
#endif
#define CLP_AES_CLP_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R                              (0x10011e10)
#ifndef AES_CLP_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R
#define AES_CLP_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R                                  (0x610)
#define AES_CLP_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R_PULSE_LOW                        (0)
#define AES_CLP_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R_PULSE_MASK                       (0x1)
#endif
#define CLP_KV_REG_BASE_ADDR                                                                        (0x10018000)
#define CLP_KV_REG_KEY_CTRL_0                                                                       (0x10018000)
#ifndef KV_REG_KEY_CTRL_0
#define KV_REG_KEY_CTRL_0                                                                           (0x0)
#define KV_REG_KEY_CTRL_0_LOCK_WR_LOW                                                               (0)
#define KV_REG_KEY_CTRL_0_LOCK_WR_MASK                                                              (0x1)
#define KV_REG_KEY_CTRL_0_LOCK_USE_LOW                                                              (1)
#define KV_REG_KEY_CTRL_0_LOCK_USE_MASK                                                             (0x2)
#define KV_REG_KEY_CTRL_0_CLEAR_LOW                                                                 (2)
#define KV_REG_KEY_CTRL_0_CLEAR_MASK                                                                (0x4)
#define KV_REG_KEY_CTRL_0_RSVD0_LOW                                                                 (3)
#define KV_REG_KEY_CTRL_0_RSVD0_MASK                                                                (0x8)
#define KV_REG_KEY_CTRL_0_RSVD1_LOW                                                                 (4)
#define KV_REG_KEY_CTRL_0_RSVD1_MASK                                                                (0x1f0)
#define KV_REG_KEY_CTRL_0_DEST_VALID_LOW                                                            (9)
#define KV_REG_KEY_CTRL_0_DEST_VALID_MASK                                                           (0x1fe00)
#define KV_REG_KEY_CTRL_0_LAST_DWORD_LOW                                                            (17)
#define KV_REG_KEY_CTRL_0_LAST_DWORD_MASK                                                           (0x1e0000)
#endif
#define CLP_KV_REG_KEY_CTRL_1                                                                       (0x10018004)
#ifndef KV_REG_KEY_CTRL_1
#define KV_REG_KEY_CTRL_1                                                                           (0x4)
#define KV_REG_KEY_CTRL_1_LOCK_WR_LOW                                                               (0)
#define KV_REG_KEY_CTRL_1_LOCK_WR_MASK                                                              (0x1)
#define KV_REG_KEY_CTRL_1_LOCK_USE_LOW                                                              (1)
#define KV_REG_KEY_CTRL_1_LOCK_USE_MASK                                                             (0x2)
#define KV_REG_KEY_CTRL_1_CLEAR_LOW                                                                 (2)
#define KV_REG_KEY_CTRL_1_CLEAR_MASK                                                                (0x4)
#define KV_REG_KEY_CTRL_1_RSVD0_LOW                                                                 (3)
#define KV_REG_KEY_CTRL_1_RSVD0_MASK                                                                (0x8)
#define KV_REG_KEY_CTRL_1_RSVD1_LOW                                                                 (4)
#define KV_REG_KEY_CTRL_1_RSVD1_MASK                                                                (0x1f0)
#define KV_REG_KEY_CTRL_1_DEST_VALID_LOW                                                            (9)
#define KV_REG_KEY_CTRL_1_DEST_VALID_MASK                                                           (0x1fe00)
#define KV_REG_KEY_CTRL_1_LAST_DWORD_LOW                                                            (17)
#define KV_REG_KEY_CTRL_1_LAST_DWORD_MASK                                                           (0x1e0000)
#endif
#define CLP_KV_REG_KEY_CTRL_2                                                                       (0x10018008)
#ifndef KV_REG_KEY_CTRL_2
#define KV_REG_KEY_CTRL_2                                                                           (0x8)
#define KV_REG_KEY_CTRL_2_LOCK_WR_LOW                                                               (0)
#define KV_REG_KEY_CTRL_2_LOCK_WR_MASK                                                              (0x1)
#define KV_REG_KEY_CTRL_2_LOCK_USE_LOW                                                              (1)
#define KV_REG_KEY_CTRL_2_LOCK_USE_MASK                                                             (0x2)
#define KV_REG_KEY_CTRL_2_CLEAR_LOW                                                                 (2)
#define KV_REG_KEY_CTRL_2_CLEAR_MASK                                                                (0x4)
#define KV_REG_KEY_CTRL_2_RSVD0_LOW                                                                 (3)
#define KV_REG_KEY_CTRL_2_RSVD0_MASK                                                                (0x8)
#define KV_REG_KEY_CTRL_2_RSVD1_LOW                                                                 (4)
#define KV_REG_KEY_CTRL_2_RSVD1_MASK                                                                (0x1f0)
#define KV_REG_KEY_CTRL_2_DEST_VALID_LOW                                                            (9)
#define KV_REG_KEY_CTRL_2_DEST_VALID_MASK                                                           (0x1fe00)
#define KV_REG_KEY_CTRL_2_LAST_DWORD_LOW                                                            (17)
#define KV_REG_KEY_CTRL_2_LAST_DWORD_MASK                                                           (0x1e0000)
#endif
#define CLP_KV_REG_KEY_CTRL_3                                                                       (0x1001800c)
#ifndef KV_REG_KEY_CTRL_3
#define KV_REG_KEY_CTRL_3                                                                           (0xc)
#define KV_REG_KEY_CTRL_3_LOCK_WR_LOW                                                               (0)
#define KV_REG_KEY_CTRL_3_LOCK_WR_MASK                                                              (0x1)
#define KV_REG_KEY_CTRL_3_LOCK_USE_LOW                                                              (1)
#define KV_REG_KEY_CTRL_3_LOCK_USE_MASK                                                             (0x2)
#define KV_REG_KEY_CTRL_3_CLEAR_LOW                                                                 (2)
#define KV_REG_KEY_CTRL_3_CLEAR_MASK                                                                (0x4)
#define KV_REG_KEY_CTRL_3_RSVD0_LOW                                                                 (3)
#define KV_REG_KEY_CTRL_3_RSVD0_MASK                                                                (0x8)
#define KV_REG_KEY_CTRL_3_RSVD1_LOW                                                                 (4)
#define KV_REG_KEY_CTRL_3_RSVD1_MASK                                                                (0x1f0)
#define KV_REG_KEY_CTRL_3_DEST_VALID_LOW                                                            (9)
#define KV_REG_KEY_CTRL_3_DEST_VALID_MASK                                                           (0x1fe00)
#define KV_REG_KEY_CTRL_3_LAST_DWORD_LOW                                                            (17)
#define KV_REG_KEY_CTRL_3_LAST_DWORD_MASK                                                           (0x1e0000)
#endif
#define CLP_KV_REG_KEY_CTRL_4                                                                       (0x10018010)
#ifndef KV_REG_KEY_CTRL_4
#define KV_REG_KEY_CTRL_4                                                                           (0x10)
#define KV_REG_KEY_CTRL_4_LOCK_WR_LOW                                                               (0)
#define KV_REG_KEY_CTRL_4_LOCK_WR_MASK                                                              (0x1)
#define KV_REG_KEY_CTRL_4_LOCK_USE_LOW                                                              (1)
#define KV_REG_KEY_CTRL_4_LOCK_USE_MASK                                                             (0x2)
#define KV_REG_KEY_CTRL_4_CLEAR_LOW                                                                 (2)
#define KV_REG_KEY_CTRL_4_CLEAR_MASK                                                                (0x4)
#define KV_REG_KEY_CTRL_4_RSVD0_LOW                                                                 (3)
#define KV_REG_KEY_CTRL_4_RSVD0_MASK                                                                (0x8)
#define KV_REG_KEY_CTRL_4_RSVD1_LOW                                                                 (4)
#define KV_REG_KEY_CTRL_4_RSVD1_MASK                                                                (0x1f0)
#define KV_REG_KEY_CTRL_4_DEST_VALID_LOW                                                            (9)
#define KV_REG_KEY_CTRL_4_DEST_VALID_MASK                                                           (0x1fe00)
#define KV_REG_KEY_CTRL_4_LAST_DWORD_LOW                                                            (17)
#define KV_REG_KEY_CTRL_4_LAST_DWORD_MASK                                                           (0x1e0000)
#endif
#define CLP_KV_REG_KEY_CTRL_5                                                                       (0x10018014)
#ifndef KV_REG_KEY_CTRL_5
#define KV_REG_KEY_CTRL_5                                                                           (0x14)
#define KV_REG_KEY_CTRL_5_LOCK_WR_LOW                                                               (0)
#define KV_REG_KEY_CTRL_5_LOCK_WR_MASK                                                              (0x1)
#define KV_REG_KEY_CTRL_5_LOCK_USE_LOW                                                              (1)
#define KV_REG_KEY_CTRL_5_LOCK_USE_MASK                                                             (0x2)
#define KV_REG_KEY_CTRL_5_CLEAR_LOW                                                                 (2)
#define KV_REG_KEY_CTRL_5_CLEAR_MASK                                                                (0x4)
#define KV_REG_KEY_CTRL_5_RSVD0_LOW                                                                 (3)
#define KV_REG_KEY_CTRL_5_RSVD0_MASK                                                                (0x8)
#define KV_REG_KEY_CTRL_5_RSVD1_LOW                                                                 (4)
#define KV_REG_KEY_CTRL_5_RSVD1_MASK                                                                (0x1f0)
#define KV_REG_KEY_CTRL_5_DEST_VALID_LOW                                                            (9)
#define KV_REG_KEY_CTRL_5_DEST_VALID_MASK                                                           (0x1fe00)
#define KV_REG_KEY_CTRL_5_LAST_DWORD_LOW                                                            (17)
#define KV_REG_KEY_CTRL_5_LAST_DWORD_MASK                                                           (0x1e0000)
#endif
#define CLP_KV_REG_KEY_CTRL_6                                                                       (0x10018018)
#ifndef KV_REG_KEY_CTRL_6
#define KV_REG_KEY_CTRL_6                                                                           (0x18)
#define KV_REG_KEY_CTRL_6_LOCK_WR_LOW                                                               (0)
#define KV_REG_KEY_CTRL_6_LOCK_WR_MASK                                                              (0x1)
#define KV_REG_KEY_CTRL_6_LOCK_USE_LOW                                                              (1)
#define KV_REG_KEY_CTRL_6_LOCK_USE_MASK                                                             (0x2)
#define KV_REG_KEY_CTRL_6_CLEAR_LOW                                                                 (2)
#define KV_REG_KEY_CTRL_6_CLEAR_MASK                                                                (0x4)
#define KV_REG_KEY_CTRL_6_RSVD0_LOW                                                                 (3)
#define KV_REG_KEY_CTRL_6_RSVD0_MASK                                                                (0x8)
#define KV_REG_KEY_CTRL_6_RSVD1_LOW                                                                 (4)
#define KV_REG_KEY_CTRL_6_RSVD1_MASK                                                                (0x1f0)
#define KV_REG_KEY_CTRL_6_DEST_VALID_LOW                                                            (9)
#define KV_REG_KEY_CTRL_6_DEST_VALID_MASK                                                           (0x1fe00)
#define KV_REG_KEY_CTRL_6_LAST_DWORD_LOW                                                            (17)
#define KV_REG_KEY_CTRL_6_LAST_DWORD_MASK                                                           (0x1e0000)
#endif
#define CLP_KV_REG_KEY_CTRL_7                                                                       (0x1001801c)
#ifndef KV_REG_KEY_CTRL_7
#define KV_REG_KEY_CTRL_7                                                                           (0x1c)
#define KV_REG_KEY_CTRL_7_LOCK_WR_LOW                                                               (0)
#define KV_REG_KEY_CTRL_7_LOCK_WR_MASK                                                              (0x1)
#define KV_REG_KEY_CTRL_7_LOCK_USE_LOW                                                              (1)
#define KV_REG_KEY_CTRL_7_LOCK_USE_MASK                                                             (0x2)
#define KV_REG_KEY_CTRL_7_CLEAR_LOW                                                                 (2)
#define KV_REG_KEY_CTRL_7_CLEAR_MASK                                                                (0x4)
#define KV_REG_KEY_CTRL_7_RSVD0_LOW                                                                 (3)
#define KV_REG_KEY_CTRL_7_RSVD0_MASK                                                                (0x8)
#define KV_REG_KEY_CTRL_7_RSVD1_LOW                                                                 (4)
#define KV_REG_KEY_CTRL_7_RSVD1_MASK                                                                (0x1f0)
#define KV_REG_KEY_CTRL_7_DEST_VALID_LOW                                                            (9)
#define KV_REG_KEY_CTRL_7_DEST_VALID_MASK                                                           (0x1fe00)
#define KV_REG_KEY_CTRL_7_LAST_DWORD_LOW                                                            (17)
#define KV_REG_KEY_CTRL_7_LAST_DWORD_MASK                                                           (0x1e0000)
#endif
#define CLP_KV_REG_KEY_CTRL_8                                                                       (0x10018020)
#ifndef KV_REG_KEY_CTRL_8
#define KV_REG_KEY_CTRL_8                                                                           (0x20)
#define KV_REG_KEY_CTRL_8_LOCK_WR_LOW                                                               (0)
#define KV_REG_KEY_CTRL_8_LOCK_WR_MASK                                                              (0x1)
#define KV_REG_KEY_CTRL_8_LOCK_USE_LOW                                                              (1)
#define KV_REG_KEY_CTRL_8_LOCK_USE_MASK                                                             (0x2)
#define KV_REG_KEY_CTRL_8_CLEAR_LOW                                                                 (2)
#define KV_REG_KEY_CTRL_8_CLEAR_MASK                                                                (0x4)
#define KV_REG_KEY_CTRL_8_RSVD0_LOW                                                                 (3)
#define KV_REG_KEY_CTRL_8_RSVD0_MASK                                                                (0x8)
#define KV_REG_KEY_CTRL_8_RSVD1_LOW                                                                 (4)
#define KV_REG_KEY_CTRL_8_RSVD1_MASK                                                                (0x1f0)
#define KV_REG_KEY_CTRL_8_DEST_VALID_LOW                                                            (9)
#define KV_REG_KEY_CTRL_8_DEST_VALID_MASK                                                           (0x1fe00)
#define KV_REG_KEY_CTRL_8_LAST_DWORD_LOW                                                            (17)
#define KV_REG_KEY_CTRL_8_LAST_DWORD_MASK                                                           (0x1e0000)
#endif
#define CLP_KV_REG_KEY_CTRL_9                                                                       (0x10018024)
#ifndef KV_REG_KEY_CTRL_9
#define KV_REG_KEY_CTRL_9                                                                           (0x24)
#define KV_REG_KEY_CTRL_9_LOCK_WR_LOW                                                               (0)
#define KV_REG_KEY_CTRL_9_LOCK_WR_MASK                                                              (0x1)
#define KV_REG_KEY_CTRL_9_LOCK_USE_LOW                                                              (1)
#define KV_REG_KEY_CTRL_9_LOCK_USE_MASK                                                             (0x2)
#define KV_REG_KEY_CTRL_9_CLEAR_LOW                                                                 (2)
#define KV_REG_KEY_CTRL_9_CLEAR_MASK                                                                (0x4)
#define KV_REG_KEY_CTRL_9_RSVD0_LOW                                                                 (3)
#define KV_REG_KEY_CTRL_9_RSVD0_MASK                                                                (0x8)
#define KV_REG_KEY_CTRL_9_RSVD1_LOW                                                                 (4)
#define KV_REG_KEY_CTRL_9_RSVD1_MASK                                                                (0x1f0)
#define KV_REG_KEY_CTRL_9_DEST_VALID_LOW                                                            (9)
#define KV_REG_KEY_CTRL_9_DEST_VALID_MASK                                                           (0x1fe00)
#define KV_REG_KEY_CTRL_9_LAST_DWORD_LOW                                                            (17)
#define KV_REG_KEY_CTRL_9_LAST_DWORD_MASK                                                           (0x1e0000)
#endif
#define CLP_KV_REG_KEY_CTRL_10                                                                      (0x10018028)
#ifndef KV_REG_KEY_CTRL_10
#define KV_REG_KEY_CTRL_10                                                                          (0x28)
#define KV_REG_KEY_CTRL_10_LOCK_WR_LOW                                                              (0)
#define KV_REG_KEY_CTRL_10_LOCK_WR_MASK                                                             (0x1)
#define KV_REG_KEY_CTRL_10_LOCK_USE_LOW                                                             (1)
#define KV_REG_KEY_CTRL_10_LOCK_USE_MASK                                                            (0x2)
#define KV_REG_KEY_CTRL_10_CLEAR_LOW                                                                (2)
#define KV_REG_KEY_CTRL_10_CLEAR_MASK                                                               (0x4)
#define KV_REG_KEY_CTRL_10_RSVD0_LOW                                                                (3)
#define KV_REG_KEY_CTRL_10_RSVD0_MASK                                                               (0x8)
#define KV_REG_KEY_CTRL_10_RSVD1_LOW                                                                (4)
#define KV_REG_KEY_CTRL_10_RSVD1_MASK                                                               (0x1f0)
#define KV_REG_KEY_CTRL_10_DEST_VALID_LOW                                                           (9)
#define KV_REG_KEY_CTRL_10_DEST_VALID_MASK                                                          (0x1fe00)
#define KV_REG_KEY_CTRL_10_LAST_DWORD_LOW                                                           (17)
#define KV_REG_KEY_CTRL_10_LAST_DWORD_MASK                                                          (0x1e0000)
#endif
#define CLP_KV_REG_KEY_CTRL_11                                                                      (0x1001802c)
#ifndef KV_REG_KEY_CTRL_11
#define KV_REG_KEY_CTRL_11                                                                          (0x2c)
#define KV_REG_KEY_CTRL_11_LOCK_WR_LOW                                                              (0)
#define KV_REG_KEY_CTRL_11_LOCK_WR_MASK                                                             (0x1)
#define KV_REG_KEY_CTRL_11_LOCK_USE_LOW                                                             (1)
#define KV_REG_KEY_CTRL_11_LOCK_USE_MASK                                                            (0x2)
#define KV_REG_KEY_CTRL_11_CLEAR_LOW                                                                (2)
#define KV_REG_KEY_CTRL_11_CLEAR_MASK                                                               (0x4)
#define KV_REG_KEY_CTRL_11_RSVD0_LOW                                                                (3)
#define KV_REG_KEY_CTRL_11_RSVD0_MASK                                                               (0x8)
#define KV_REG_KEY_CTRL_11_RSVD1_LOW                                                                (4)
#define KV_REG_KEY_CTRL_11_RSVD1_MASK                                                               (0x1f0)
#define KV_REG_KEY_CTRL_11_DEST_VALID_LOW                                                           (9)
#define KV_REG_KEY_CTRL_11_DEST_VALID_MASK                                                          (0x1fe00)
#define KV_REG_KEY_CTRL_11_LAST_DWORD_LOW                                                           (17)
#define KV_REG_KEY_CTRL_11_LAST_DWORD_MASK                                                          (0x1e0000)
#endif
#define CLP_KV_REG_KEY_CTRL_12                                                                      (0x10018030)
#ifndef KV_REG_KEY_CTRL_12
#define KV_REG_KEY_CTRL_12                                                                          (0x30)
#define KV_REG_KEY_CTRL_12_LOCK_WR_LOW                                                              (0)
#define KV_REG_KEY_CTRL_12_LOCK_WR_MASK                                                             (0x1)
#define KV_REG_KEY_CTRL_12_LOCK_USE_LOW                                                             (1)
#define KV_REG_KEY_CTRL_12_LOCK_USE_MASK                                                            (0x2)
#define KV_REG_KEY_CTRL_12_CLEAR_LOW                                                                (2)
#define KV_REG_KEY_CTRL_12_CLEAR_MASK                                                               (0x4)
#define KV_REG_KEY_CTRL_12_RSVD0_LOW                                                                (3)
#define KV_REG_KEY_CTRL_12_RSVD0_MASK                                                               (0x8)
#define KV_REG_KEY_CTRL_12_RSVD1_LOW                                                                (4)
#define KV_REG_KEY_CTRL_12_RSVD1_MASK                                                               (0x1f0)
#define KV_REG_KEY_CTRL_12_DEST_VALID_LOW                                                           (9)
#define KV_REG_KEY_CTRL_12_DEST_VALID_MASK                                                          (0x1fe00)
#define KV_REG_KEY_CTRL_12_LAST_DWORD_LOW                                                           (17)
#define KV_REG_KEY_CTRL_12_LAST_DWORD_MASK                                                          (0x1e0000)
#endif
#define CLP_KV_REG_KEY_CTRL_13                                                                      (0x10018034)
#ifndef KV_REG_KEY_CTRL_13
#define KV_REG_KEY_CTRL_13                                                                          (0x34)
#define KV_REG_KEY_CTRL_13_LOCK_WR_LOW                                                              (0)
#define KV_REG_KEY_CTRL_13_LOCK_WR_MASK                                                             (0x1)
#define KV_REG_KEY_CTRL_13_LOCK_USE_LOW                                                             (1)
#define KV_REG_KEY_CTRL_13_LOCK_USE_MASK                                                            (0x2)
#define KV_REG_KEY_CTRL_13_CLEAR_LOW                                                                (2)
#define KV_REG_KEY_CTRL_13_CLEAR_MASK                                                               (0x4)
#define KV_REG_KEY_CTRL_13_RSVD0_LOW                                                                (3)
#define KV_REG_KEY_CTRL_13_RSVD0_MASK                                                               (0x8)
#define KV_REG_KEY_CTRL_13_RSVD1_LOW                                                                (4)
#define KV_REG_KEY_CTRL_13_RSVD1_MASK                                                               (0x1f0)
#define KV_REG_KEY_CTRL_13_DEST_VALID_LOW                                                           (9)
#define KV_REG_KEY_CTRL_13_DEST_VALID_MASK                                                          (0x1fe00)
#define KV_REG_KEY_CTRL_13_LAST_DWORD_LOW                                                           (17)
#define KV_REG_KEY_CTRL_13_LAST_DWORD_MASK                                                          (0x1e0000)
#endif
#define CLP_KV_REG_KEY_CTRL_14                                                                      (0x10018038)
#ifndef KV_REG_KEY_CTRL_14
#define KV_REG_KEY_CTRL_14                                                                          (0x38)
#define KV_REG_KEY_CTRL_14_LOCK_WR_LOW                                                              (0)
#define KV_REG_KEY_CTRL_14_LOCK_WR_MASK                                                             (0x1)
#define KV_REG_KEY_CTRL_14_LOCK_USE_LOW                                                             (1)
#define KV_REG_KEY_CTRL_14_LOCK_USE_MASK                                                            (0x2)
#define KV_REG_KEY_CTRL_14_CLEAR_LOW                                                                (2)
#define KV_REG_KEY_CTRL_14_CLEAR_MASK                                                               (0x4)
#define KV_REG_KEY_CTRL_14_RSVD0_LOW                                                                (3)
#define KV_REG_KEY_CTRL_14_RSVD0_MASK                                                               (0x8)
#define KV_REG_KEY_CTRL_14_RSVD1_LOW                                                                (4)
#define KV_REG_KEY_CTRL_14_RSVD1_MASK                                                               (0x1f0)
#define KV_REG_KEY_CTRL_14_DEST_VALID_LOW                                                           (9)
#define KV_REG_KEY_CTRL_14_DEST_VALID_MASK                                                          (0x1fe00)
#define KV_REG_KEY_CTRL_14_LAST_DWORD_LOW                                                           (17)
#define KV_REG_KEY_CTRL_14_LAST_DWORD_MASK                                                          (0x1e0000)
#endif
#define CLP_KV_REG_KEY_CTRL_15                                                                      (0x1001803c)
#ifndef KV_REG_KEY_CTRL_15
#define KV_REG_KEY_CTRL_15                                                                          (0x3c)
#define KV_REG_KEY_CTRL_15_LOCK_WR_LOW                                                              (0)
#define KV_REG_KEY_CTRL_15_LOCK_WR_MASK                                                             (0x1)
#define KV_REG_KEY_CTRL_15_LOCK_USE_LOW                                                             (1)
#define KV_REG_KEY_CTRL_15_LOCK_USE_MASK                                                            (0x2)
#define KV_REG_KEY_CTRL_15_CLEAR_LOW                                                                (2)
#define KV_REG_KEY_CTRL_15_CLEAR_MASK                                                               (0x4)
#define KV_REG_KEY_CTRL_15_RSVD0_LOW                                                                (3)
#define KV_REG_KEY_CTRL_15_RSVD0_MASK                                                               (0x8)
#define KV_REG_KEY_CTRL_15_RSVD1_LOW                                                                (4)
#define KV_REG_KEY_CTRL_15_RSVD1_MASK                                                               (0x1f0)
#define KV_REG_KEY_CTRL_15_DEST_VALID_LOW                                                           (9)
#define KV_REG_KEY_CTRL_15_DEST_VALID_MASK                                                          (0x1fe00)
#define KV_REG_KEY_CTRL_15_LAST_DWORD_LOW                                                           (17)
#define KV_REG_KEY_CTRL_15_LAST_DWORD_MASK                                                          (0x1e0000)
#endif
#define CLP_KV_REG_KEY_CTRL_16                                                                      (0x10018040)
#ifndef KV_REG_KEY_CTRL_16
#define KV_REG_KEY_CTRL_16                                                                          (0x40)
#define KV_REG_KEY_CTRL_16_LOCK_WR_LOW                                                              (0)
#define KV_REG_KEY_CTRL_16_LOCK_WR_MASK                                                             (0x1)
#define KV_REG_KEY_CTRL_16_LOCK_USE_LOW                                                             (1)
#define KV_REG_KEY_CTRL_16_LOCK_USE_MASK                                                            (0x2)
#define KV_REG_KEY_CTRL_16_CLEAR_LOW                                                                (2)
#define KV_REG_KEY_CTRL_16_CLEAR_MASK                                                               (0x4)
#define KV_REG_KEY_CTRL_16_RSVD0_LOW                                                                (3)
#define KV_REG_KEY_CTRL_16_RSVD0_MASK                                                               (0x8)
#define KV_REG_KEY_CTRL_16_RSVD1_LOW                                                                (4)
#define KV_REG_KEY_CTRL_16_RSVD1_MASK                                                               (0x1f0)
#define KV_REG_KEY_CTRL_16_DEST_VALID_LOW                                                           (9)
#define KV_REG_KEY_CTRL_16_DEST_VALID_MASK                                                          (0x1fe00)
#define KV_REG_KEY_CTRL_16_LAST_DWORD_LOW                                                           (17)
#define KV_REG_KEY_CTRL_16_LAST_DWORD_MASK                                                          (0x1e0000)
#endif
#define CLP_KV_REG_KEY_CTRL_17                                                                      (0x10018044)
#ifndef KV_REG_KEY_CTRL_17
#define KV_REG_KEY_CTRL_17                                                                          (0x44)
#define KV_REG_KEY_CTRL_17_LOCK_WR_LOW                                                              (0)
#define KV_REG_KEY_CTRL_17_LOCK_WR_MASK                                                             (0x1)
#define KV_REG_KEY_CTRL_17_LOCK_USE_LOW                                                             (1)
#define KV_REG_KEY_CTRL_17_LOCK_USE_MASK                                                            (0x2)
#define KV_REG_KEY_CTRL_17_CLEAR_LOW                                                                (2)
#define KV_REG_KEY_CTRL_17_CLEAR_MASK                                                               (0x4)
#define KV_REG_KEY_CTRL_17_RSVD0_LOW                                                                (3)
#define KV_REG_KEY_CTRL_17_RSVD0_MASK                                                               (0x8)
#define KV_REG_KEY_CTRL_17_RSVD1_LOW                                                                (4)
#define KV_REG_KEY_CTRL_17_RSVD1_MASK                                                               (0x1f0)
#define KV_REG_KEY_CTRL_17_DEST_VALID_LOW                                                           (9)
#define KV_REG_KEY_CTRL_17_DEST_VALID_MASK                                                          (0x1fe00)
#define KV_REG_KEY_CTRL_17_LAST_DWORD_LOW                                                           (17)
#define KV_REG_KEY_CTRL_17_LAST_DWORD_MASK                                                          (0x1e0000)
#endif
#define CLP_KV_REG_KEY_CTRL_18                                                                      (0x10018048)
#ifndef KV_REG_KEY_CTRL_18
#define KV_REG_KEY_CTRL_18                                                                          (0x48)
#define KV_REG_KEY_CTRL_18_LOCK_WR_LOW                                                              (0)
#define KV_REG_KEY_CTRL_18_LOCK_WR_MASK                                                             (0x1)
#define KV_REG_KEY_CTRL_18_LOCK_USE_LOW                                                             (1)
#define KV_REG_KEY_CTRL_18_LOCK_USE_MASK                                                            (0x2)
#define KV_REG_KEY_CTRL_18_CLEAR_LOW                                                                (2)
#define KV_REG_KEY_CTRL_18_CLEAR_MASK                                                               (0x4)
#define KV_REG_KEY_CTRL_18_RSVD0_LOW                                                                (3)
#define KV_REG_KEY_CTRL_18_RSVD0_MASK                                                               (0x8)
#define KV_REG_KEY_CTRL_18_RSVD1_LOW                                                                (4)
#define KV_REG_KEY_CTRL_18_RSVD1_MASK                                                               (0x1f0)
#define KV_REG_KEY_CTRL_18_DEST_VALID_LOW                                                           (9)
#define KV_REG_KEY_CTRL_18_DEST_VALID_MASK                                                          (0x1fe00)
#define KV_REG_KEY_CTRL_18_LAST_DWORD_LOW                                                           (17)
#define KV_REG_KEY_CTRL_18_LAST_DWORD_MASK                                                          (0x1e0000)
#endif
#define CLP_KV_REG_KEY_CTRL_19                                                                      (0x1001804c)
#ifndef KV_REG_KEY_CTRL_19
#define KV_REG_KEY_CTRL_19                                                                          (0x4c)
#define KV_REG_KEY_CTRL_19_LOCK_WR_LOW                                                              (0)
#define KV_REG_KEY_CTRL_19_LOCK_WR_MASK                                                             (0x1)
#define KV_REG_KEY_CTRL_19_LOCK_USE_LOW                                                             (1)
#define KV_REG_KEY_CTRL_19_LOCK_USE_MASK                                                            (0x2)
#define KV_REG_KEY_CTRL_19_CLEAR_LOW                                                                (2)
#define KV_REG_KEY_CTRL_19_CLEAR_MASK                                                               (0x4)
#define KV_REG_KEY_CTRL_19_RSVD0_LOW                                                                (3)
#define KV_REG_KEY_CTRL_19_RSVD0_MASK                                                               (0x8)
#define KV_REG_KEY_CTRL_19_RSVD1_LOW                                                                (4)
#define KV_REG_KEY_CTRL_19_RSVD1_MASK                                                               (0x1f0)
#define KV_REG_KEY_CTRL_19_DEST_VALID_LOW                                                           (9)
#define KV_REG_KEY_CTRL_19_DEST_VALID_MASK                                                          (0x1fe00)
#define KV_REG_KEY_CTRL_19_LAST_DWORD_LOW                                                           (17)
#define KV_REG_KEY_CTRL_19_LAST_DWORD_MASK                                                          (0x1e0000)
#endif
#define CLP_KV_REG_KEY_CTRL_20                                                                      (0x10018050)
#ifndef KV_REG_KEY_CTRL_20
#define KV_REG_KEY_CTRL_20                                                                          (0x50)
#define KV_REG_KEY_CTRL_20_LOCK_WR_LOW                                                              (0)
#define KV_REG_KEY_CTRL_20_LOCK_WR_MASK                                                             (0x1)
#define KV_REG_KEY_CTRL_20_LOCK_USE_LOW                                                             (1)
#define KV_REG_KEY_CTRL_20_LOCK_USE_MASK                                                            (0x2)
#define KV_REG_KEY_CTRL_20_CLEAR_LOW                                                                (2)
#define KV_REG_KEY_CTRL_20_CLEAR_MASK                                                               (0x4)
#define KV_REG_KEY_CTRL_20_RSVD0_LOW                                                                (3)
#define KV_REG_KEY_CTRL_20_RSVD0_MASK                                                               (0x8)
#define KV_REG_KEY_CTRL_20_RSVD1_LOW                                                                (4)
#define KV_REG_KEY_CTRL_20_RSVD1_MASK                                                               (0x1f0)
#define KV_REG_KEY_CTRL_20_DEST_VALID_LOW                                                           (9)
#define KV_REG_KEY_CTRL_20_DEST_VALID_MASK                                                          (0x1fe00)
#define KV_REG_KEY_CTRL_20_LAST_DWORD_LOW                                                           (17)
#define KV_REG_KEY_CTRL_20_LAST_DWORD_MASK                                                          (0x1e0000)
#endif
#define CLP_KV_REG_KEY_CTRL_21                                                                      (0x10018054)
#ifndef KV_REG_KEY_CTRL_21
#define KV_REG_KEY_CTRL_21                                                                          (0x54)
#define KV_REG_KEY_CTRL_21_LOCK_WR_LOW                                                              (0)
#define KV_REG_KEY_CTRL_21_LOCK_WR_MASK                                                             (0x1)
#define KV_REG_KEY_CTRL_21_LOCK_USE_LOW                                                             (1)
#define KV_REG_KEY_CTRL_21_LOCK_USE_MASK                                                            (0x2)
#define KV_REG_KEY_CTRL_21_CLEAR_LOW                                                                (2)
#define KV_REG_KEY_CTRL_21_CLEAR_MASK                                                               (0x4)
#define KV_REG_KEY_CTRL_21_RSVD0_LOW                                                                (3)
#define KV_REG_KEY_CTRL_21_RSVD0_MASK                                                               (0x8)
#define KV_REG_KEY_CTRL_21_RSVD1_LOW                                                                (4)
#define KV_REG_KEY_CTRL_21_RSVD1_MASK                                                               (0x1f0)
#define KV_REG_KEY_CTRL_21_DEST_VALID_LOW                                                           (9)
#define KV_REG_KEY_CTRL_21_DEST_VALID_MASK                                                          (0x1fe00)
#define KV_REG_KEY_CTRL_21_LAST_DWORD_LOW                                                           (17)
#define KV_REG_KEY_CTRL_21_LAST_DWORD_MASK                                                          (0x1e0000)
#endif
#define CLP_KV_REG_KEY_CTRL_22                                                                      (0x10018058)
#ifndef KV_REG_KEY_CTRL_22
#define KV_REG_KEY_CTRL_22                                                                          (0x58)
#define KV_REG_KEY_CTRL_22_LOCK_WR_LOW                                                              (0)
#define KV_REG_KEY_CTRL_22_LOCK_WR_MASK                                                             (0x1)
#define KV_REG_KEY_CTRL_22_LOCK_USE_LOW                                                             (1)
#define KV_REG_KEY_CTRL_22_LOCK_USE_MASK                                                            (0x2)
#define KV_REG_KEY_CTRL_22_CLEAR_LOW                                                                (2)
#define KV_REG_KEY_CTRL_22_CLEAR_MASK                                                               (0x4)
#define KV_REG_KEY_CTRL_22_RSVD0_LOW                                                                (3)
#define KV_REG_KEY_CTRL_22_RSVD0_MASK                                                               (0x8)
#define KV_REG_KEY_CTRL_22_RSVD1_LOW                                                                (4)
#define KV_REG_KEY_CTRL_22_RSVD1_MASK                                                               (0x1f0)
#define KV_REG_KEY_CTRL_22_DEST_VALID_LOW                                                           (9)
#define KV_REG_KEY_CTRL_22_DEST_VALID_MASK                                                          (0x1fe00)
#define KV_REG_KEY_CTRL_22_LAST_DWORD_LOW                                                           (17)
#define KV_REG_KEY_CTRL_22_LAST_DWORD_MASK                                                          (0x1e0000)
#endif
#define CLP_KV_REG_KEY_CTRL_23                                                                      (0x1001805c)
#ifndef KV_REG_KEY_CTRL_23
#define KV_REG_KEY_CTRL_23                                                                          (0x5c)
#define KV_REG_KEY_CTRL_23_LOCK_WR_LOW                                                              (0)
#define KV_REG_KEY_CTRL_23_LOCK_WR_MASK                                                             (0x1)
#define KV_REG_KEY_CTRL_23_LOCK_USE_LOW                                                             (1)
#define KV_REG_KEY_CTRL_23_LOCK_USE_MASK                                                            (0x2)
#define KV_REG_KEY_CTRL_23_CLEAR_LOW                                                                (2)
#define KV_REG_KEY_CTRL_23_CLEAR_MASK                                                               (0x4)
#define KV_REG_KEY_CTRL_23_RSVD0_LOW                                                                (3)
#define KV_REG_KEY_CTRL_23_RSVD0_MASK                                                               (0x8)
#define KV_REG_KEY_CTRL_23_RSVD1_LOW                                                                (4)
#define KV_REG_KEY_CTRL_23_RSVD1_MASK                                                               (0x1f0)
#define KV_REG_KEY_CTRL_23_DEST_VALID_LOW                                                           (9)
#define KV_REG_KEY_CTRL_23_DEST_VALID_MASK                                                          (0x1fe00)
#define KV_REG_KEY_CTRL_23_LAST_DWORD_LOW                                                           (17)
#define KV_REG_KEY_CTRL_23_LAST_DWORD_MASK                                                          (0x1e0000)
#endif
#define CLP_KV_REG_KEY_ENTRY_0_0                                                                    (0x10018600)
#ifndef KV_REG_KEY_ENTRY_0_0
#define KV_REG_KEY_ENTRY_0_0                                                                        (0x600)
#endif
#define CLP_KV_REG_KEY_ENTRY_0_1                                                                    (0x10018604)
#ifndef KV_REG_KEY_ENTRY_0_1
#define KV_REG_KEY_ENTRY_0_1                                                                        (0x604)
#endif
#define CLP_KV_REG_KEY_ENTRY_0_2                                                                    (0x10018608)
#ifndef KV_REG_KEY_ENTRY_0_2
#define KV_REG_KEY_ENTRY_0_2                                                                        (0x608)
#endif
#define CLP_KV_REG_KEY_ENTRY_0_3                                                                    (0x1001860c)
#ifndef KV_REG_KEY_ENTRY_0_3
#define KV_REG_KEY_ENTRY_0_3                                                                        (0x60c)
#endif
#define CLP_KV_REG_KEY_ENTRY_0_4                                                                    (0x10018610)
#ifndef KV_REG_KEY_ENTRY_0_4
#define KV_REG_KEY_ENTRY_0_4                                                                        (0x610)
#endif
#define CLP_KV_REG_KEY_ENTRY_0_5                                                                    (0x10018614)
#ifndef KV_REG_KEY_ENTRY_0_5
#define KV_REG_KEY_ENTRY_0_5                                                                        (0x614)
#endif
#define CLP_KV_REG_KEY_ENTRY_0_6                                                                    (0x10018618)
#ifndef KV_REG_KEY_ENTRY_0_6
#define KV_REG_KEY_ENTRY_0_6                                                                        (0x618)
#endif
#define CLP_KV_REG_KEY_ENTRY_0_7                                                                    (0x1001861c)
#ifndef KV_REG_KEY_ENTRY_0_7
#define KV_REG_KEY_ENTRY_0_7                                                                        (0x61c)
#endif
#define CLP_KV_REG_KEY_ENTRY_0_8                                                                    (0x10018620)
#ifndef KV_REG_KEY_ENTRY_0_8
#define KV_REG_KEY_ENTRY_0_8                                                                        (0x620)
#endif
#define CLP_KV_REG_KEY_ENTRY_0_9                                                                    (0x10018624)
#ifndef KV_REG_KEY_ENTRY_0_9
#define KV_REG_KEY_ENTRY_0_9                                                                        (0x624)
#endif
#define CLP_KV_REG_KEY_ENTRY_0_10                                                                   (0x10018628)
#ifndef KV_REG_KEY_ENTRY_0_10
#define KV_REG_KEY_ENTRY_0_10                                                                       (0x628)
#endif
#define CLP_KV_REG_KEY_ENTRY_0_11                                                                   (0x1001862c)
#ifndef KV_REG_KEY_ENTRY_0_11
#define KV_REG_KEY_ENTRY_0_11                                                                       (0x62c)
#endif
#define CLP_KV_REG_KEY_ENTRY_0_12                                                                   (0x10018630)
#ifndef KV_REG_KEY_ENTRY_0_12
#define KV_REG_KEY_ENTRY_0_12                                                                       (0x630)
#endif
#define CLP_KV_REG_KEY_ENTRY_0_13                                                                   (0x10018634)
#ifndef KV_REG_KEY_ENTRY_0_13
#define KV_REG_KEY_ENTRY_0_13                                                                       (0x634)
#endif
#define CLP_KV_REG_KEY_ENTRY_0_14                                                                   (0x10018638)
#ifndef KV_REG_KEY_ENTRY_0_14
#define KV_REG_KEY_ENTRY_0_14                                                                       (0x638)
#endif
#define CLP_KV_REG_KEY_ENTRY_0_15                                                                   (0x1001863c)
#ifndef KV_REG_KEY_ENTRY_0_15
#define KV_REG_KEY_ENTRY_0_15                                                                       (0x63c)
#endif
#define CLP_KV_REG_KEY_ENTRY_1_0                                                                    (0x10018640)
#ifndef KV_REG_KEY_ENTRY_1_0
#define KV_REG_KEY_ENTRY_1_0                                                                        (0x640)
#endif
#define CLP_KV_REG_KEY_ENTRY_1_1                                                                    (0x10018644)
#ifndef KV_REG_KEY_ENTRY_1_1
#define KV_REG_KEY_ENTRY_1_1                                                                        (0x644)
#endif
#define CLP_KV_REG_KEY_ENTRY_1_2                                                                    (0x10018648)
#ifndef KV_REG_KEY_ENTRY_1_2
#define KV_REG_KEY_ENTRY_1_2                                                                        (0x648)
#endif
#define CLP_KV_REG_KEY_ENTRY_1_3                                                                    (0x1001864c)
#ifndef KV_REG_KEY_ENTRY_1_3
#define KV_REG_KEY_ENTRY_1_3                                                                        (0x64c)
#endif
#define CLP_KV_REG_KEY_ENTRY_1_4                                                                    (0x10018650)
#ifndef KV_REG_KEY_ENTRY_1_4
#define KV_REG_KEY_ENTRY_1_4                                                                        (0x650)
#endif
#define CLP_KV_REG_KEY_ENTRY_1_5                                                                    (0x10018654)
#ifndef KV_REG_KEY_ENTRY_1_5
#define KV_REG_KEY_ENTRY_1_5                                                                        (0x654)
#endif
#define CLP_KV_REG_KEY_ENTRY_1_6                                                                    (0x10018658)
#ifndef KV_REG_KEY_ENTRY_1_6
#define KV_REG_KEY_ENTRY_1_6                                                                        (0x658)
#endif
#define CLP_KV_REG_KEY_ENTRY_1_7                                                                    (0x1001865c)
#ifndef KV_REG_KEY_ENTRY_1_7
#define KV_REG_KEY_ENTRY_1_7                                                                        (0x65c)
#endif
#define CLP_KV_REG_KEY_ENTRY_1_8                                                                    (0x10018660)
#ifndef KV_REG_KEY_ENTRY_1_8
#define KV_REG_KEY_ENTRY_1_8                                                                        (0x660)
#endif
#define CLP_KV_REG_KEY_ENTRY_1_9                                                                    (0x10018664)
#ifndef KV_REG_KEY_ENTRY_1_9
#define KV_REG_KEY_ENTRY_1_9                                                                        (0x664)
#endif
#define CLP_KV_REG_KEY_ENTRY_1_10                                                                   (0x10018668)
#ifndef KV_REG_KEY_ENTRY_1_10
#define KV_REG_KEY_ENTRY_1_10                                                                       (0x668)
#endif
#define CLP_KV_REG_KEY_ENTRY_1_11                                                                   (0x1001866c)
#ifndef KV_REG_KEY_ENTRY_1_11
#define KV_REG_KEY_ENTRY_1_11                                                                       (0x66c)
#endif
#define CLP_KV_REG_KEY_ENTRY_1_12                                                                   (0x10018670)
#ifndef KV_REG_KEY_ENTRY_1_12
#define KV_REG_KEY_ENTRY_1_12                                                                       (0x670)
#endif
#define CLP_KV_REG_KEY_ENTRY_1_13                                                                   (0x10018674)
#ifndef KV_REG_KEY_ENTRY_1_13
#define KV_REG_KEY_ENTRY_1_13                                                                       (0x674)
#endif
#define CLP_KV_REG_KEY_ENTRY_1_14                                                                   (0x10018678)
#ifndef KV_REG_KEY_ENTRY_1_14
#define KV_REG_KEY_ENTRY_1_14                                                                       (0x678)
#endif
#define CLP_KV_REG_KEY_ENTRY_1_15                                                                   (0x1001867c)
#ifndef KV_REG_KEY_ENTRY_1_15
#define KV_REG_KEY_ENTRY_1_15                                                                       (0x67c)
#endif
#define CLP_KV_REG_KEY_ENTRY_2_0                                                                    (0x10018680)
#ifndef KV_REG_KEY_ENTRY_2_0
#define KV_REG_KEY_ENTRY_2_0                                                                        (0x680)
#endif
#define CLP_KV_REG_KEY_ENTRY_2_1                                                                    (0x10018684)
#ifndef KV_REG_KEY_ENTRY_2_1
#define KV_REG_KEY_ENTRY_2_1                                                                        (0x684)
#endif
#define CLP_KV_REG_KEY_ENTRY_2_2                                                                    (0x10018688)
#ifndef KV_REG_KEY_ENTRY_2_2
#define KV_REG_KEY_ENTRY_2_2                                                                        (0x688)
#endif
#define CLP_KV_REG_KEY_ENTRY_2_3                                                                    (0x1001868c)
#ifndef KV_REG_KEY_ENTRY_2_3
#define KV_REG_KEY_ENTRY_2_3                                                                        (0x68c)
#endif
#define CLP_KV_REG_KEY_ENTRY_2_4                                                                    (0x10018690)
#ifndef KV_REG_KEY_ENTRY_2_4
#define KV_REG_KEY_ENTRY_2_4                                                                        (0x690)
#endif
#define CLP_KV_REG_KEY_ENTRY_2_5                                                                    (0x10018694)
#ifndef KV_REG_KEY_ENTRY_2_5
#define KV_REG_KEY_ENTRY_2_5                                                                        (0x694)
#endif
#define CLP_KV_REG_KEY_ENTRY_2_6                                                                    (0x10018698)
#ifndef KV_REG_KEY_ENTRY_2_6
#define KV_REG_KEY_ENTRY_2_6                                                                        (0x698)
#endif
#define CLP_KV_REG_KEY_ENTRY_2_7                                                                    (0x1001869c)
#ifndef KV_REG_KEY_ENTRY_2_7
#define KV_REG_KEY_ENTRY_2_7                                                                        (0x69c)
#endif
#define CLP_KV_REG_KEY_ENTRY_2_8                                                                    (0x100186a0)
#ifndef KV_REG_KEY_ENTRY_2_8
#define KV_REG_KEY_ENTRY_2_8                                                                        (0x6a0)
#endif
#define CLP_KV_REG_KEY_ENTRY_2_9                                                                    (0x100186a4)
#ifndef KV_REG_KEY_ENTRY_2_9
#define KV_REG_KEY_ENTRY_2_9                                                                        (0x6a4)
#endif
#define CLP_KV_REG_KEY_ENTRY_2_10                                                                   (0x100186a8)
#ifndef KV_REG_KEY_ENTRY_2_10
#define KV_REG_KEY_ENTRY_2_10                                                                       (0x6a8)
#endif
#define CLP_KV_REG_KEY_ENTRY_2_11                                                                   (0x100186ac)
#ifndef KV_REG_KEY_ENTRY_2_11
#define KV_REG_KEY_ENTRY_2_11                                                                       (0x6ac)
#endif
#define CLP_KV_REG_KEY_ENTRY_2_12                                                                   (0x100186b0)
#ifndef KV_REG_KEY_ENTRY_2_12
#define KV_REG_KEY_ENTRY_2_12                                                                       (0x6b0)
#endif
#define CLP_KV_REG_KEY_ENTRY_2_13                                                                   (0x100186b4)
#ifndef KV_REG_KEY_ENTRY_2_13
#define KV_REG_KEY_ENTRY_2_13                                                                       (0x6b4)
#endif
#define CLP_KV_REG_KEY_ENTRY_2_14                                                                   (0x100186b8)
#ifndef KV_REG_KEY_ENTRY_2_14
#define KV_REG_KEY_ENTRY_2_14                                                                       (0x6b8)
#endif
#define CLP_KV_REG_KEY_ENTRY_2_15                                                                   (0x100186bc)
#ifndef KV_REG_KEY_ENTRY_2_15
#define KV_REG_KEY_ENTRY_2_15                                                                       (0x6bc)
#endif
#define CLP_KV_REG_KEY_ENTRY_3_0                                                                    (0x100186c0)
#ifndef KV_REG_KEY_ENTRY_3_0
#define KV_REG_KEY_ENTRY_3_0                                                                        (0x6c0)
#endif
#define CLP_KV_REG_KEY_ENTRY_3_1                                                                    (0x100186c4)
#ifndef KV_REG_KEY_ENTRY_3_1
#define KV_REG_KEY_ENTRY_3_1                                                                        (0x6c4)
#endif
#define CLP_KV_REG_KEY_ENTRY_3_2                                                                    (0x100186c8)
#ifndef KV_REG_KEY_ENTRY_3_2
#define KV_REG_KEY_ENTRY_3_2                                                                        (0x6c8)
#endif
#define CLP_KV_REG_KEY_ENTRY_3_3                                                                    (0x100186cc)
#ifndef KV_REG_KEY_ENTRY_3_3
#define KV_REG_KEY_ENTRY_3_3                                                                        (0x6cc)
#endif
#define CLP_KV_REG_KEY_ENTRY_3_4                                                                    (0x100186d0)
#ifndef KV_REG_KEY_ENTRY_3_4
#define KV_REG_KEY_ENTRY_3_4                                                                        (0x6d0)
#endif
#define CLP_KV_REG_KEY_ENTRY_3_5                                                                    (0x100186d4)
#ifndef KV_REG_KEY_ENTRY_3_5
#define KV_REG_KEY_ENTRY_3_5                                                                        (0x6d4)
#endif
#define CLP_KV_REG_KEY_ENTRY_3_6                                                                    (0x100186d8)
#ifndef KV_REG_KEY_ENTRY_3_6
#define KV_REG_KEY_ENTRY_3_6                                                                        (0x6d8)
#endif
#define CLP_KV_REG_KEY_ENTRY_3_7                                                                    (0x100186dc)
#ifndef KV_REG_KEY_ENTRY_3_7
#define KV_REG_KEY_ENTRY_3_7                                                                        (0x6dc)
#endif
#define CLP_KV_REG_KEY_ENTRY_3_8                                                                    (0x100186e0)
#ifndef KV_REG_KEY_ENTRY_3_8
#define KV_REG_KEY_ENTRY_3_8                                                                        (0x6e0)
#endif
#define CLP_KV_REG_KEY_ENTRY_3_9                                                                    (0x100186e4)
#ifndef KV_REG_KEY_ENTRY_3_9
#define KV_REG_KEY_ENTRY_3_9                                                                        (0x6e4)
#endif
#define CLP_KV_REG_KEY_ENTRY_3_10                                                                   (0x100186e8)
#ifndef KV_REG_KEY_ENTRY_3_10
#define KV_REG_KEY_ENTRY_3_10                                                                       (0x6e8)
#endif
#define CLP_KV_REG_KEY_ENTRY_3_11                                                                   (0x100186ec)
#ifndef KV_REG_KEY_ENTRY_3_11
#define KV_REG_KEY_ENTRY_3_11                                                                       (0x6ec)
#endif
#define CLP_KV_REG_KEY_ENTRY_3_12                                                                   (0x100186f0)
#ifndef KV_REG_KEY_ENTRY_3_12
#define KV_REG_KEY_ENTRY_3_12                                                                       (0x6f0)
#endif
#define CLP_KV_REG_KEY_ENTRY_3_13                                                                   (0x100186f4)
#ifndef KV_REG_KEY_ENTRY_3_13
#define KV_REG_KEY_ENTRY_3_13                                                                       (0x6f4)
#endif
#define CLP_KV_REG_KEY_ENTRY_3_14                                                                   (0x100186f8)
#ifndef KV_REG_KEY_ENTRY_3_14
#define KV_REG_KEY_ENTRY_3_14                                                                       (0x6f8)
#endif
#define CLP_KV_REG_KEY_ENTRY_3_15                                                                   (0x100186fc)
#ifndef KV_REG_KEY_ENTRY_3_15
#define KV_REG_KEY_ENTRY_3_15                                                                       (0x6fc)
#endif
#define CLP_KV_REG_KEY_ENTRY_4_0                                                                    (0x10018700)
#ifndef KV_REG_KEY_ENTRY_4_0
#define KV_REG_KEY_ENTRY_4_0                                                                        (0x700)
#endif
#define CLP_KV_REG_KEY_ENTRY_4_1                                                                    (0x10018704)
#ifndef KV_REG_KEY_ENTRY_4_1
#define KV_REG_KEY_ENTRY_4_1                                                                        (0x704)
#endif
#define CLP_KV_REG_KEY_ENTRY_4_2                                                                    (0x10018708)
#ifndef KV_REG_KEY_ENTRY_4_2
#define KV_REG_KEY_ENTRY_4_2                                                                        (0x708)
#endif
#define CLP_KV_REG_KEY_ENTRY_4_3                                                                    (0x1001870c)
#ifndef KV_REG_KEY_ENTRY_4_3
#define KV_REG_KEY_ENTRY_4_3                                                                        (0x70c)
#endif
#define CLP_KV_REG_KEY_ENTRY_4_4                                                                    (0x10018710)
#ifndef KV_REG_KEY_ENTRY_4_4
#define KV_REG_KEY_ENTRY_4_4                                                                        (0x710)
#endif
#define CLP_KV_REG_KEY_ENTRY_4_5                                                                    (0x10018714)
#ifndef KV_REG_KEY_ENTRY_4_5
#define KV_REG_KEY_ENTRY_4_5                                                                        (0x714)
#endif
#define CLP_KV_REG_KEY_ENTRY_4_6                                                                    (0x10018718)
#ifndef KV_REG_KEY_ENTRY_4_6
#define KV_REG_KEY_ENTRY_4_6                                                                        (0x718)
#endif
#define CLP_KV_REG_KEY_ENTRY_4_7                                                                    (0x1001871c)
#ifndef KV_REG_KEY_ENTRY_4_7
#define KV_REG_KEY_ENTRY_4_7                                                                        (0x71c)
#endif
#define CLP_KV_REG_KEY_ENTRY_4_8                                                                    (0x10018720)
#ifndef KV_REG_KEY_ENTRY_4_8
#define KV_REG_KEY_ENTRY_4_8                                                                        (0x720)
#endif
#define CLP_KV_REG_KEY_ENTRY_4_9                                                                    (0x10018724)
#ifndef KV_REG_KEY_ENTRY_4_9
#define KV_REG_KEY_ENTRY_4_9                                                                        (0x724)
#endif
#define CLP_KV_REG_KEY_ENTRY_4_10                                                                   (0x10018728)
#ifndef KV_REG_KEY_ENTRY_4_10
#define KV_REG_KEY_ENTRY_4_10                                                                       (0x728)
#endif
#define CLP_KV_REG_KEY_ENTRY_4_11                                                                   (0x1001872c)
#ifndef KV_REG_KEY_ENTRY_4_11
#define KV_REG_KEY_ENTRY_4_11                                                                       (0x72c)
#endif
#define CLP_KV_REG_KEY_ENTRY_4_12                                                                   (0x10018730)
#ifndef KV_REG_KEY_ENTRY_4_12
#define KV_REG_KEY_ENTRY_4_12                                                                       (0x730)
#endif
#define CLP_KV_REG_KEY_ENTRY_4_13                                                                   (0x10018734)
#ifndef KV_REG_KEY_ENTRY_4_13
#define KV_REG_KEY_ENTRY_4_13                                                                       (0x734)
#endif
#define CLP_KV_REG_KEY_ENTRY_4_14                                                                   (0x10018738)
#ifndef KV_REG_KEY_ENTRY_4_14
#define KV_REG_KEY_ENTRY_4_14                                                                       (0x738)
#endif
#define CLP_KV_REG_KEY_ENTRY_4_15                                                                   (0x1001873c)
#ifndef KV_REG_KEY_ENTRY_4_15
#define KV_REG_KEY_ENTRY_4_15                                                                       (0x73c)
#endif
#define CLP_KV_REG_KEY_ENTRY_5_0                                                                    (0x10018740)
#ifndef KV_REG_KEY_ENTRY_5_0
#define KV_REG_KEY_ENTRY_5_0                                                                        (0x740)
#endif
#define CLP_KV_REG_KEY_ENTRY_5_1                                                                    (0x10018744)
#ifndef KV_REG_KEY_ENTRY_5_1
#define KV_REG_KEY_ENTRY_5_1                                                                        (0x744)
#endif
#define CLP_KV_REG_KEY_ENTRY_5_2                                                                    (0x10018748)
#ifndef KV_REG_KEY_ENTRY_5_2
#define KV_REG_KEY_ENTRY_5_2                                                                        (0x748)
#endif
#define CLP_KV_REG_KEY_ENTRY_5_3                                                                    (0x1001874c)
#ifndef KV_REG_KEY_ENTRY_5_3
#define KV_REG_KEY_ENTRY_5_3                                                                        (0x74c)
#endif
#define CLP_KV_REG_KEY_ENTRY_5_4                                                                    (0x10018750)
#ifndef KV_REG_KEY_ENTRY_5_4
#define KV_REG_KEY_ENTRY_5_4                                                                        (0x750)
#endif
#define CLP_KV_REG_KEY_ENTRY_5_5                                                                    (0x10018754)
#ifndef KV_REG_KEY_ENTRY_5_5
#define KV_REG_KEY_ENTRY_5_5                                                                        (0x754)
#endif
#define CLP_KV_REG_KEY_ENTRY_5_6                                                                    (0x10018758)
#ifndef KV_REG_KEY_ENTRY_5_6
#define KV_REG_KEY_ENTRY_5_6                                                                        (0x758)
#endif
#define CLP_KV_REG_KEY_ENTRY_5_7                                                                    (0x1001875c)
#ifndef KV_REG_KEY_ENTRY_5_7
#define KV_REG_KEY_ENTRY_5_7                                                                        (0x75c)
#endif
#define CLP_KV_REG_KEY_ENTRY_5_8                                                                    (0x10018760)
#ifndef KV_REG_KEY_ENTRY_5_8
#define KV_REG_KEY_ENTRY_5_8                                                                        (0x760)
#endif
#define CLP_KV_REG_KEY_ENTRY_5_9                                                                    (0x10018764)
#ifndef KV_REG_KEY_ENTRY_5_9
#define KV_REG_KEY_ENTRY_5_9                                                                        (0x764)
#endif
#define CLP_KV_REG_KEY_ENTRY_5_10                                                                   (0x10018768)
#ifndef KV_REG_KEY_ENTRY_5_10
#define KV_REG_KEY_ENTRY_5_10                                                                       (0x768)
#endif
#define CLP_KV_REG_KEY_ENTRY_5_11                                                                   (0x1001876c)
#ifndef KV_REG_KEY_ENTRY_5_11
#define KV_REG_KEY_ENTRY_5_11                                                                       (0x76c)
#endif
#define CLP_KV_REG_KEY_ENTRY_5_12                                                                   (0x10018770)
#ifndef KV_REG_KEY_ENTRY_5_12
#define KV_REG_KEY_ENTRY_5_12                                                                       (0x770)
#endif
#define CLP_KV_REG_KEY_ENTRY_5_13                                                                   (0x10018774)
#ifndef KV_REG_KEY_ENTRY_5_13
#define KV_REG_KEY_ENTRY_5_13                                                                       (0x774)
#endif
#define CLP_KV_REG_KEY_ENTRY_5_14                                                                   (0x10018778)
#ifndef KV_REG_KEY_ENTRY_5_14
#define KV_REG_KEY_ENTRY_5_14                                                                       (0x778)
#endif
#define CLP_KV_REG_KEY_ENTRY_5_15                                                                   (0x1001877c)
#ifndef KV_REG_KEY_ENTRY_5_15
#define KV_REG_KEY_ENTRY_5_15                                                                       (0x77c)
#endif
#define CLP_KV_REG_KEY_ENTRY_6_0                                                                    (0x10018780)
#ifndef KV_REG_KEY_ENTRY_6_0
#define KV_REG_KEY_ENTRY_6_0                                                                        (0x780)
#endif
#define CLP_KV_REG_KEY_ENTRY_6_1                                                                    (0x10018784)
#ifndef KV_REG_KEY_ENTRY_6_1
#define KV_REG_KEY_ENTRY_6_1                                                                        (0x784)
#endif
#define CLP_KV_REG_KEY_ENTRY_6_2                                                                    (0x10018788)
#ifndef KV_REG_KEY_ENTRY_6_2
#define KV_REG_KEY_ENTRY_6_2                                                                        (0x788)
#endif
#define CLP_KV_REG_KEY_ENTRY_6_3                                                                    (0x1001878c)
#ifndef KV_REG_KEY_ENTRY_6_3
#define KV_REG_KEY_ENTRY_6_3                                                                        (0x78c)
#endif
#define CLP_KV_REG_KEY_ENTRY_6_4                                                                    (0x10018790)
#ifndef KV_REG_KEY_ENTRY_6_4
#define KV_REG_KEY_ENTRY_6_4                                                                        (0x790)
#endif
#define CLP_KV_REG_KEY_ENTRY_6_5                                                                    (0x10018794)
#ifndef KV_REG_KEY_ENTRY_6_5
#define KV_REG_KEY_ENTRY_6_5                                                                        (0x794)
#endif
#define CLP_KV_REG_KEY_ENTRY_6_6                                                                    (0x10018798)
#ifndef KV_REG_KEY_ENTRY_6_6
#define KV_REG_KEY_ENTRY_6_6                                                                        (0x798)
#endif
#define CLP_KV_REG_KEY_ENTRY_6_7                                                                    (0x1001879c)
#ifndef KV_REG_KEY_ENTRY_6_7
#define KV_REG_KEY_ENTRY_6_7                                                                        (0x79c)
#endif
#define CLP_KV_REG_KEY_ENTRY_6_8                                                                    (0x100187a0)
#ifndef KV_REG_KEY_ENTRY_6_8
#define KV_REG_KEY_ENTRY_6_8                                                                        (0x7a0)
#endif
#define CLP_KV_REG_KEY_ENTRY_6_9                                                                    (0x100187a4)
#ifndef KV_REG_KEY_ENTRY_6_9
#define KV_REG_KEY_ENTRY_6_9                                                                        (0x7a4)
#endif
#define CLP_KV_REG_KEY_ENTRY_6_10                                                                   (0x100187a8)
#ifndef KV_REG_KEY_ENTRY_6_10
#define KV_REG_KEY_ENTRY_6_10                                                                       (0x7a8)
#endif
#define CLP_KV_REG_KEY_ENTRY_6_11                                                                   (0x100187ac)
#ifndef KV_REG_KEY_ENTRY_6_11
#define KV_REG_KEY_ENTRY_6_11                                                                       (0x7ac)
#endif
#define CLP_KV_REG_KEY_ENTRY_6_12                                                                   (0x100187b0)
#ifndef KV_REG_KEY_ENTRY_6_12
#define KV_REG_KEY_ENTRY_6_12                                                                       (0x7b0)
#endif
#define CLP_KV_REG_KEY_ENTRY_6_13                                                                   (0x100187b4)
#ifndef KV_REG_KEY_ENTRY_6_13
#define KV_REG_KEY_ENTRY_6_13                                                                       (0x7b4)
#endif
#define CLP_KV_REG_KEY_ENTRY_6_14                                                                   (0x100187b8)
#ifndef KV_REG_KEY_ENTRY_6_14
#define KV_REG_KEY_ENTRY_6_14                                                                       (0x7b8)
#endif
#define CLP_KV_REG_KEY_ENTRY_6_15                                                                   (0x100187bc)
#ifndef KV_REG_KEY_ENTRY_6_15
#define KV_REG_KEY_ENTRY_6_15                                                                       (0x7bc)
#endif
#define CLP_KV_REG_KEY_ENTRY_7_0                                                                    (0x100187c0)
#ifndef KV_REG_KEY_ENTRY_7_0
#define KV_REG_KEY_ENTRY_7_0                                                                        (0x7c0)
#endif
#define CLP_KV_REG_KEY_ENTRY_7_1                                                                    (0x100187c4)
#ifndef KV_REG_KEY_ENTRY_7_1
#define KV_REG_KEY_ENTRY_7_1                                                                        (0x7c4)
#endif
#define CLP_KV_REG_KEY_ENTRY_7_2                                                                    (0x100187c8)
#ifndef KV_REG_KEY_ENTRY_7_2
#define KV_REG_KEY_ENTRY_7_2                                                                        (0x7c8)
#endif
#define CLP_KV_REG_KEY_ENTRY_7_3                                                                    (0x100187cc)
#ifndef KV_REG_KEY_ENTRY_7_3
#define KV_REG_KEY_ENTRY_7_3                                                                        (0x7cc)
#endif
#define CLP_KV_REG_KEY_ENTRY_7_4                                                                    (0x100187d0)
#ifndef KV_REG_KEY_ENTRY_7_4
#define KV_REG_KEY_ENTRY_7_4                                                                        (0x7d0)
#endif
#define CLP_KV_REG_KEY_ENTRY_7_5                                                                    (0x100187d4)
#ifndef KV_REG_KEY_ENTRY_7_5
#define KV_REG_KEY_ENTRY_7_5                                                                        (0x7d4)
#endif
#define CLP_KV_REG_KEY_ENTRY_7_6                                                                    (0x100187d8)
#ifndef KV_REG_KEY_ENTRY_7_6
#define KV_REG_KEY_ENTRY_7_6                                                                        (0x7d8)
#endif
#define CLP_KV_REG_KEY_ENTRY_7_7                                                                    (0x100187dc)
#ifndef KV_REG_KEY_ENTRY_7_7
#define KV_REG_KEY_ENTRY_7_7                                                                        (0x7dc)
#endif
#define CLP_KV_REG_KEY_ENTRY_7_8                                                                    (0x100187e0)
#ifndef KV_REG_KEY_ENTRY_7_8
#define KV_REG_KEY_ENTRY_7_8                                                                        (0x7e0)
#endif
#define CLP_KV_REG_KEY_ENTRY_7_9                                                                    (0x100187e4)
#ifndef KV_REG_KEY_ENTRY_7_9
#define KV_REG_KEY_ENTRY_7_9                                                                        (0x7e4)
#endif
#define CLP_KV_REG_KEY_ENTRY_7_10                                                                   (0x100187e8)
#ifndef KV_REG_KEY_ENTRY_7_10
#define KV_REG_KEY_ENTRY_7_10                                                                       (0x7e8)
#endif
#define CLP_KV_REG_KEY_ENTRY_7_11                                                                   (0x100187ec)
#ifndef KV_REG_KEY_ENTRY_7_11
#define KV_REG_KEY_ENTRY_7_11                                                                       (0x7ec)
#endif
#define CLP_KV_REG_KEY_ENTRY_7_12                                                                   (0x100187f0)
#ifndef KV_REG_KEY_ENTRY_7_12
#define KV_REG_KEY_ENTRY_7_12                                                                       (0x7f0)
#endif
#define CLP_KV_REG_KEY_ENTRY_7_13                                                                   (0x100187f4)
#ifndef KV_REG_KEY_ENTRY_7_13
#define KV_REG_KEY_ENTRY_7_13                                                                       (0x7f4)
#endif
#define CLP_KV_REG_KEY_ENTRY_7_14                                                                   (0x100187f8)
#ifndef KV_REG_KEY_ENTRY_7_14
#define KV_REG_KEY_ENTRY_7_14                                                                       (0x7f8)
#endif
#define CLP_KV_REG_KEY_ENTRY_7_15                                                                   (0x100187fc)
#ifndef KV_REG_KEY_ENTRY_7_15
#define KV_REG_KEY_ENTRY_7_15                                                                       (0x7fc)
#endif
#define CLP_KV_REG_KEY_ENTRY_8_0                                                                    (0x10018800)
#ifndef KV_REG_KEY_ENTRY_8_0
#define KV_REG_KEY_ENTRY_8_0                                                                        (0x800)
#endif
#define CLP_KV_REG_KEY_ENTRY_8_1                                                                    (0x10018804)
#ifndef KV_REG_KEY_ENTRY_8_1
#define KV_REG_KEY_ENTRY_8_1                                                                        (0x804)
#endif
#define CLP_KV_REG_KEY_ENTRY_8_2                                                                    (0x10018808)
#ifndef KV_REG_KEY_ENTRY_8_2
#define KV_REG_KEY_ENTRY_8_2                                                                        (0x808)
#endif
#define CLP_KV_REG_KEY_ENTRY_8_3                                                                    (0x1001880c)
#ifndef KV_REG_KEY_ENTRY_8_3
#define KV_REG_KEY_ENTRY_8_3                                                                        (0x80c)
#endif
#define CLP_KV_REG_KEY_ENTRY_8_4                                                                    (0x10018810)
#ifndef KV_REG_KEY_ENTRY_8_4
#define KV_REG_KEY_ENTRY_8_4                                                                        (0x810)
#endif
#define CLP_KV_REG_KEY_ENTRY_8_5                                                                    (0x10018814)
#ifndef KV_REG_KEY_ENTRY_8_5
#define KV_REG_KEY_ENTRY_8_5                                                                        (0x814)
#endif
#define CLP_KV_REG_KEY_ENTRY_8_6                                                                    (0x10018818)
#ifndef KV_REG_KEY_ENTRY_8_6
#define KV_REG_KEY_ENTRY_8_6                                                                        (0x818)
#endif
#define CLP_KV_REG_KEY_ENTRY_8_7                                                                    (0x1001881c)
#ifndef KV_REG_KEY_ENTRY_8_7
#define KV_REG_KEY_ENTRY_8_7                                                                        (0x81c)
#endif
#define CLP_KV_REG_KEY_ENTRY_8_8                                                                    (0x10018820)
#ifndef KV_REG_KEY_ENTRY_8_8
#define KV_REG_KEY_ENTRY_8_8                                                                        (0x820)
#endif
#define CLP_KV_REG_KEY_ENTRY_8_9                                                                    (0x10018824)
#ifndef KV_REG_KEY_ENTRY_8_9
#define KV_REG_KEY_ENTRY_8_9                                                                        (0x824)
#endif
#define CLP_KV_REG_KEY_ENTRY_8_10                                                                   (0x10018828)
#ifndef KV_REG_KEY_ENTRY_8_10
#define KV_REG_KEY_ENTRY_8_10                                                                       (0x828)
#endif
#define CLP_KV_REG_KEY_ENTRY_8_11                                                                   (0x1001882c)
#ifndef KV_REG_KEY_ENTRY_8_11
#define KV_REG_KEY_ENTRY_8_11                                                                       (0x82c)
#endif
#define CLP_KV_REG_KEY_ENTRY_8_12                                                                   (0x10018830)
#ifndef KV_REG_KEY_ENTRY_8_12
#define KV_REG_KEY_ENTRY_8_12                                                                       (0x830)
#endif
#define CLP_KV_REG_KEY_ENTRY_8_13                                                                   (0x10018834)
#ifndef KV_REG_KEY_ENTRY_8_13
#define KV_REG_KEY_ENTRY_8_13                                                                       (0x834)
#endif
#define CLP_KV_REG_KEY_ENTRY_8_14                                                                   (0x10018838)
#ifndef KV_REG_KEY_ENTRY_8_14
#define KV_REG_KEY_ENTRY_8_14                                                                       (0x838)
#endif
#define CLP_KV_REG_KEY_ENTRY_8_15                                                                   (0x1001883c)
#ifndef KV_REG_KEY_ENTRY_8_15
#define KV_REG_KEY_ENTRY_8_15                                                                       (0x83c)
#endif
#define CLP_KV_REG_KEY_ENTRY_9_0                                                                    (0x10018840)
#ifndef KV_REG_KEY_ENTRY_9_0
#define KV_REG_KEY_ENTRY_9_0                                                                        (0x840)
#endif
#define CLP_KV_REG_KEY_ENTRY_9_1                                                                    (0x10018844)
#ifndef KV_REG_KEY_ENTRY_9_1
#define KV_REG_KEY_ENTRY_9_1                                                                        (0x844)
#endif
#define CLP_KV_REG_KEY_ENTRY_9_2                                                                    (0x10018848)
#ifndef KV_REG_KEY_ENTRY_9_2
#define KV_REG_KEY_ENTRY_9_2                                                                        (0x848)
#endif
#define CLP_KV_REG_KEY_ENTRY_9_3                                                                    (0x1001884c)
#ifndef KV_REG_KEY_ENTRY_9_3
#define KV_REG_KEY_ENTRY_9_3                                                                        (0x84c)
#endif
#define CLP_KV_REG_KEY_ENTRY_9_4                                                                    (0x10018850)
#ifndef KV_REG_KEY_ENTRY_9_4
#define KV_REG_KEY_ENTRY_9_4                                                                        (0x850)
#endif
#define CLP_KV_REG_KEY_ENTRY_9_5                                                                    (0x10018854)
#ifndef KV_REG_KEY_ENTRY_9_5
#define KV_REG_KEY_ENTRY_9_5                                                                        (0x854)
#endif
#define CLP_KV_REG_KEY_ENTRY_9_6                                                                    (0x10018858)
#ifndef KV_REG_KEY_ENTRY_9_6
#define KV_REG_KEY_ENTRY_9_6                                                                        (0x858)
#endif
#define CLP_KV_REG_KEY_ENTRY_9_7                                                                    (0x1001885c)
#ifndef KV_REG_KEY_ENTRY_9_7
#define KV_REG_KEY_ENTRY_9_7                                                                        (0x85c)
#endif
#define CLP_KV_REG_KEY_ENTRY_9_8                                                                    (0x10018860)
#ifndef KV_REG_KEY_ENTRY_9_8
#define KV_REG_KEY_ENTRY_9_8                                                                        (0x860)
#endif
#define CLP_KV_REG_KEY_ENTRY_9_9                                                                    (0x10018864)
#ifndef KV_REG_KEY_ENTRY_9_9
#define KV_REG_KEY_ENTRY_9_9                                                                        (0x864)
#endif
#define CLP_KV_REG_KEY_ENTRY_9_10                                                                   (0x10018868)
#ifndef KV_REG_KEY_ENTRY_9_10
#define KV_REG_KEY_ENTRY_9_10                                                                       (0x868)
#endif
#define CLP_KV_REG_KEY_ENTRY_9_11                                                                   (0x1001886c)
#ifndef KV_REG_KEY_ENTRY_9_11
#define KV_REG_KEY_ENTRY_9_11                                                                       (0x86c)
#endif
#define CLP_KV_REG_KEY_ENTRY_9_12                                                                   (0x10018870)
#ifndef KV_REG_KEY_ENTRY_9_12
#define KV_REG_KEY_ENTRY_9_12                                                                       (0x870)
#endif
#define CLP_KV_REG_KEY_ENTRY_9_13                                                                   (0x10018874)
#ifndef KV_REG_KEY_ENTRY_9_13
#define KV_REG_KEY_ENTRY_9_13                                                                       (0x874)
#endif
#define CLP_KV_REG_KEY_ENTRY_9_14                                                                   (0x10018878)
#ifndef KV_REG_KEY_ENTRY_9_14
#define KV_REG_KEY_ENTRY_9_14                                                                       (0x878)
#endif
#define CLP_KV_REG_KEY_ENTRY_9_15                                                                   (0x1001887c)
#ifndef KV_REG_KEY_ENTRY_9_15
#define KV_REG_KEY_ENTRY_9_15                                                                       (0x87c)
#endif
#define CLP_KV_REG_KEY_ENTRY_10_0                                                                   (0x10018880)
#ifndef KV_REG_KEY_ENTRY_10_0
#define KV_REG_KEY_ENTRY_10_0                                                                       (0x880)
#endif
#define CLP_KV_REG_KEY_ENTRY_10_1                                                                   (0x10018884)
#ifndef KV_REG_KEY_ENTRY_10_1
#define KV_REG_KEY_ENTRY_10_1                                                                       (0x884)
#endif
#define CLP_KV_REG_KEY_ENTRY_10_2                                                                   (0x10018888)
#ifndef KV_REG_KEY_ENTRY_10_2
#define KV_REG_KEY_ENTRY_10_2                                                                       (0x888)
#endif
#define CLP_KV_REG_KEY_ENTRY_10_3                                                                   (0x1001888c)
#ifndef KV_REG_KEY_ENTRY_10_3
#define KV_REG_KEY_ENTRY_10_3                                                                       (0x88c)
#endif
#define CLP_KV_REG_KEY_ENTRY_10_4                                                                   (0x10018890)
#ifndef KV_REG_KEY_ENTRY_10_4
#define KV_REG_KEY_ENTRY_10_4                                                                       (0x890)
#endif
#define CLP_KV_REG_KEY_ENTRY_10_5                                                                   (0x10018894)
#ifndef KV_REG_KEY_ENTRY_10_5
#define KV_REG_KEY_ENTRY_10_5                                                                       (0x894)
#endif
#define CLP_KV_REG_KEY_ENTRY_10_6                                                                   (0x10018898)
#ifndef KV_REG_KEY_ENTRY_10_6
#define KV_REG_KEY_ENTRY_10_6                                                                       (0x898)
#endif
#define CLP_KV_REG_KEY_ENTRY_10_7                                                                   (0x1001889c)
#ifndef KV_REG_KEY_ENTRY_10_7
#define KV_REG_KEY_ENTRY_10_7                                                                       (0x89c)
#endif
#define CLP_KV_REG_KEY_ENTRY_10_8                                                                   (0x100188a0)
#ifndef KV_REG_KEY_ENTRY_10_8
#define KV_REG_KEY_ENTRY_10_8                                                                       (0x8a0)
#endif
#define CLP_KV_REG_KEY_ENTRY_10_9                                                                   (0x100188a4)
#ifndef KV_REG_KEY_ENTRY_10_9
#define KV_REG_KEY_ENTRY_10_9                                                                       (0x8a4)
#endif
#define CLP_KV_REG_KEY_ENTRY_10_10                                                                  (0x100188a8)
#ifndef KV_REG_KEY_ENTRY_10_10
#define KV_REG_KEY_ENTRY_10_10                                                                      (0x8a8)
#endif
#define CLP_KV_REG_KEY_ENTRY_10_11                                                                  (0x100188ac)
#ifndef KV_REG_KEY_ENTRY_10_11
#define KV_REG_KEY_ENTRY_10_11                                                                      (0x8ac)
#endif
#define CLP_KV_REG_KEY_ENTRY_10_12                                                                  (0x100188b0)
#ifndef KV_REG_KEY_ENTRY_10_12
#define KV_REG_KEY_ENTRY_10_12                                                                      (0x8b0)
#endif
#define CLP_KV_REG_KEY_ENTRY_10_13                                                                  (0x100188b4)
#ifndef KV_REG_KEY_ENTRY_10_13
#define KV_REG_KEY_ENTRY_10_13                                                                      (0x8b4)
#endif
#define CLP_KV_REG_KEY_ENTRY_10_14                                                                  (0x100188b8)
#ifndef KV_REG_KEY_ENTRY_10_14
#define KV_REG_KEY_ENTRY_10_14                                                                      (0x8b8)
#endif
#define CLP_KV_REG_KEY_ENTRY_10_15                                                                  (0x100188bc)
#ifndef KV_REG_KEY_ENTRY_10_15
#define KV_REG_KEY_ENTRY_10_15                                                                      (0x8bc)
#endif
#define CLP_KV_REG_KEY_ENTRY_11_0                                                                   (0x100188c0)
#ifndef KV_REG_KEY_ENTRY_11_0
#define KV_REG_KEY_ENTRY_11_0                                                                       (0x8c0)
#endif
#define CLP_KV_REG_KEY_ENTRY_11_1                                                                   (0x100188c4)
#ifndef KV_REG_KEY_ENTRY_11_1
#define KV_REG_KEY_ENTRY_11_1                                                                       (0x8c4)
#endif
#define CLP_KV_REG_KEY_ENTRY_11_2                                                                   (0x100188c8)
#ifndef KV_REG_KEY_ENTRY_11_2
#define KV_REG_KEY_ENTRY_11_2                                                                       (0x8c8)
#endif
#define CLP_KV_REG_KEY_ENTRY_11_3                                                                   (0x100188cc)
#ifndef KV_REG_KEY_ENTRY_11_3
#define KV_REG_KEY_ENTRY_11_3                                                                       (0x8cc)
#endif
#define CLP_KV_REG_KEY_ENTRY_11_4                                                                   (0x100188d0)
#ifndef KV_REG_KEY_ENTRY_11_4
#define KV_REG_KEY_ENTRY_11_4                                                                       (0x8d0)
#endif
#define CLP_KV_REG_KEY_ENTRY_11_5                                                                   (0x100188d4)
#ifndef KV_REG_KEY_ENTRY_11_5
#define KV_REG_KEY_ENTRY_11_5                                                                       (0x8d4)
#endif
#define CLP_KV_REG_KEY_ENTRY_11_6                                                                   (0x100188d8)
#ifndef KV_REG_KEY_ENTRY_11_6
#define KV_REG_KEY_ENTRY_11_6                                                                       (0x8d8)
#endif
#define CLP_KV_REG_KEY_ENTRY_11_7                                                                   (0x100188dc)
#ifndef KV_REG_KEY_ENTRY_11_7
#define KV_REG_KEY_ENTRY_11_7                                                                       (0x8dc)
#endif
#define CLP_KV_REG_KEY_ENTRY_11_8                                                                   (0x100188e0)
#ifndef KV_REG_KEY_ENTRY_11_8
#define KV_REG_KEY_ENTRY_11_8                                                                       (0x8e0)
#endif
#define CLP_KV_REG_KEY_ENTRY_11_9                                                                   (0x100188e4)
#ifndef KV_REG_KEY_ENTRY_11_9
#define KV_REG_KEY_ENTRY_11_9                                                                       (0x8e4)
#endif
#define CLP_KV_REG_KEY_ENTRY_11_10                                                                  (0x100188e8)
#ifndef KV_REG_KEY_ENTRY_11_10
#define KV_REG_KEY_ENTRY_11_10                                                                      (0x8e8)
#endif
#define CLP_KV_REG_KEY_ENTRY_11_11                                                                  (0x100188ec)
#ifndef KV_REG_KEY_ENTRY_11_11
#define KV_REG_KEY_ENTRY_11_11                                                                      (0x8ec)
#endif
#define CLP_KV_REG_KEY_ENTRY_11_12                                                                  (0x100188f0)
#ifndef KV_REG_KEY_ENTRY_11_12
#define KV_REG_KEY_ENTRY_11_12                                                                      (0x8f0)
#endif
#define CLP_KV_REG_KEY_ENTRY_11_13                                                                  (0x100188f4)
#ifndef KV_REG_KEY_ENTRY_11_13
#define KV_REG_KEY_ENTRY_11_13                                                                      (0x8f4)
#endif
#define CLP_KV_REG_KEY_ENTRY_11_14                                                                  (0x100188f8)
#ifndef KV_REG_KEY_ENTRY_11_14
#define KV_REG_KEY_ENTRY_11_14                                                                      (0x8f8)
#endif
#define CLP_KV_REG_KEY_ENTRY_11_15                                                                  (0x100188fc)
#ifndef KV_REG_KEY_ENTRY_11_15
#define KV_REG_KEY_ENTRY_11_15                                                                      (0x8fc)
#endif
#define CLP_KV_REG_KEY_ENTRY_12_0                                                                   (0x10018900)
#ifndef KV_REG_KEY_ENTRY_12_0
#define KV_REG_KEY_ENTRY_12_0                                                                       (0x900)
#endif
#define CLP_KV_REG_KEY_ENTRY_12_1                                                                   (0x10018904)
#ifndef KV_REG_KEY_ENTRY_12_1
#define KV_REG_KEY_ENTRY_12_1                                                                       (0x904)
#endif
#define CLP_KV_REG_KEY_ENTRY_12_2                                                                   (0x10018908)
#ifndef KV_REG_KEY_ENTRY_12_2
#define KV_REG_KEY_ENTRY_12_2                                                                       (0x908)
#endif
#define CLP_KV_REG_KEY_ENTRY_12_3                                                                   (0x1001890c)
#ifndef KV_REG_KEY_ENTRY_12_3
#define KV_REG_KEY_ENTRY_12_3                                                                       (0x90c)
#endif
#define CLP_KV_REG_KEY_ENTRY_12_4                                                                   (0x10018910)
#ifndef KV_REG_KEY_ENTRY_12_4
#define KV_REG_KEY_ENTRY_12_4                                                                       (0x910)
#endif
#define CLP_KV_REG_KEY_ENTRY_12_5                                                                   (0x10018914)
#ifndef KV_REG_KEY_ENTRY_12_5
#define KV_REG_KEY_ENTRY_12_5                                                                       (0x914)
#endif
#define CLP_KV_REG_KEY_ENTRY_12_6                                                                   (0x10018918)
#ifndef KV_REG_KEY_ENTRY_12_6
#define KV_REG_KEY_ENTRY_12_6                                                                       (0x918)
#endif
#define CLP_KV_REG_KEY_ENTRY_12_7                                                                   (0x1001891c)
#ifndef KV_REG_KEY_ENTRY_12_7
#define KV_REG_KEY_ENTRY_12_7                                                                       (0x91c)
#endif
#define CLP_KV_REG_KEY_ENTRY_12_8                                                                   (0x10018920)
#ifndef KV_REG_KEY_ENTRY_12_8
#define KV_REG_KEY_ENTRY_12_8                                                                       (0x920)
#endif
#define CLP_KV_REG_KEY_ENTRY_12_9                                                                   (0x10018924)
#ifndef KV_REG_KEY_ENTRY_12_9
#define KV_REG_KEY_ENTRY_12_9                                                                       (0x924)
#endif
#define CLP_KV_REG_KEY_ENTRY_12_10                                                                  (0x10018928)
#ifndef KV_REG_KEY_ENTRY_12_10
#define KV_REG_KEY_ENTRY_12_10                                                                      (0x928)
#endif
#define CLP_KV_REG_KEY_ENTRY_12_11                                                                  (0x1001892c)
#ifndef KV_REG_KEY_ENTRY_12_11
#define KV_REG_KEY_ENTRY_12_11                                                                      (0x92c)
#endif
#define CLP_KV_REG_KEY_ENTRY_12_12                                                                  (0x10018930)
#ifndef KV_REG_KEY_ENTRY_12_12
#define KV_REG_KEY_ENTRY_12_12                                                                      (0x930)
#endif
#define CLP_KV_REG_KEY_ENTRY_12_13                                                                  (0x10018934)
#ifndef KV_REG_KEY_ENTRY_12_13
#define KV_REG_KEY_ENTRY_12_13                                                                      (0x934)
#endif
#define CLP_KV_REG_KEY_ENTRY_12_14                                                                  (0x10018938)
#ifndef KV_REG_KEY_ENTRY_12_14
#define KV_REG_KEY_ENTRY_12_14                                                                      (0x938)
#endif
#define CLP_KV_REG_KEY_ENTRY_12_15                                                                  (0x1001893c)
#ifndef KV_REG_KEY_ENTRY_12_15
#define KV_REG_KEY_ENTRY_12_15                                                                      (0x93c)
#endif
#define CLP_KV_REG_KEY_ENTRY_13_0                                                                   (0x10018940)
#ifndef KV_REG_KEY_ENTRY_13_0
#define KV_REG_KEY_ENTRY_13_0                                                                       (0x940)
#endif
#define CLP_KV_REG_KEY_ENTRY_13_1                                                                   (0x10018944)
#ifndef KV_REG_KEY_ENTRY_13_1
#define KV_REG_KEY_ENTRY_13_1                                                                       (0x944)
#endif
#define CLP_KV_REG_KEY_ENTRY_13_2                                                                   (0x10018948)
#ifndef KV_REG_KEY_ENTRY_13_2
#define KV_REG_KEY_ENTRY_13_2                                                                       (0x948)
#endif
#define CLP_KV_REG_KEY_ENTRY_13_3                                                                   (0x1001894c)
#ifndef KV_REG_KEY_ENTRY_13_3
#define KV_REG_KEY_ENTRY_13_3                                                                       (0x94c)
#endif
#define CLP_KV_REG_KEY_ENTRY_13_4                                                                   (0x10018950)
#ifndef KV_REG_KEY_ENTRY_13_4
#define KV_REG_KEY_ENTRY_13_4                                                                       (0x950)
#endif
#define CLP_KV_REG_KEY_ENTRY_13_5                                                                   (0x10018954)
#ifndef KV_REG_KEY_ENTRY_13_5
#define KV_REG_KEY_ENTRY_13_5                                                                       (0x954)
#endif
#define CLP_KV_REG_KEY_ENTRY_13_6                                                                   (0x10018958)
#ifndef KV_REG_KEY_ENTRY_13_6
#define KV_REG_KEY_ENTRY_13_6                                                                       (0x958)
#endif
#define CLP_KV_REG_KEY_ENTRY_13_7                                                                   (0x1001895c)
#ifndef KV_REG_KEY_ENTRY_13_7
#define KV_REG_KEY_ENTRY_13_7                                                                       (0x95c)
#endif
#define CLP_KV_REG_KEY_ENTRY_13_8                                                                   (0x10018960)
#ifndef KV_REG_KEY_ENTRY_13_8
#define KV_REG_KEY_ENTRY_13_8                                                                       (0x960)
#endif
#define CLP_KV_REG_KEY_ENTRY_13_9                                                                   (0x10018964)
#ifndef KV_REG_KEY_ENTRY_13_9
#define KV_REG_KEY_ENTRY_13_9                                                                       (0x964)
#endif
#define CLP_KV_REG_KEY_ENTRY_13_10                                                                  (0x10018968)
#ifndef KV_REG_KEY_ENTRY_13_10
#define KV_REG_KEY_ENTRY_13_10                                                                      (0x968)
#endif
#define CLP_KV_REG_KEY_ENTRY_13_11                                                                  (0x1001896c)
#ifndef KV_REG_KEY_ENTRY_13_11
#define KV_REG_KEY_ENTRY_13_11                                                                      (0x96c)
#endif
#define CLP_KV_REG_KEY_ENTRY_13_12                                                                  (0x10018970)
#ifndef KV_REG_KEY_ENTRY_13_12
#define KV_REG_KEY_ENTRY_13_12                                                                      (0x970)
#endif
#define CLP_KV_REG_KEY_ENTRY_13_13                                                                  (0x10018974)
#ifndef KV_REG_KEY_ENTRY_13_13
#define KV_REG_KEY_ENTRY_13_13                                                                      (0x974)
#endif
#define CLP_KV_REG_KEY_ENTRY_13_14                                                                  (0x10018978)
#ifndef KV_REG_KEY_ENTRY_13_14
#define KV_REG_KEY_ENTRY_13_14                                                                      (0x978)
#endif
#define CLP_KV_REG_KEY_ENTRY_13_15                                                                  (0x1001897c)
#ifndef KV_REG_KEY_ENTRY_13_15
#define KV_REG_KEY_ENTRY_13_15                                                                      (0x97c)
#endif
#define CLP_KV_REG_KEY_ENTRY_14_0                                                                   (0x10018980)
#ifndef KV_REG_KEY_ENTRY_14_0
#define KV_REG_KEY_ENTRY_14_0                                                                       (0x980)
#endif
#define CLP_KV_REG_KEY_ENTRY_14_1                                                                   (0x10018984)
#ifndef KV_REG_KEY_ENTRY_14_1
#define KV_REG_KEY_ENTRY_14_1                                                                       (0x984)
#endif
#define CLP_KV_REG_KEY_ENTRY_14_2                                                                   (0x10018988)
#ifndef KV_REG_KEY_ENTRY_14_2
#define KV_REG_KEY_ENTRY_14_2                                                                       (0x988)
#endif
#define CLP_KV_REG_KEY_ENTRY_14_3                                                                   (0x1001898c)
#ifndef KV_REG_KEY_ENTRY_14_3
#define KV_REG_KEY_ENTRY_14_3                                                                       (0x98c)
#endif
#define CLP_KV_REG_KEY_ENTRY_14_4                                                                   (0x10018990)
#ifndef KV_REG_KEY_ENTRY_14_4
#define KV_REG_KEY_ENTRY_14_4                                                                       (0x990)
#endif
#define CLP_KV_REG_KEY_ENTRY_14_5                                                                   (0x10018994)
#ifndef KV_REG_KEY_ENTRY_14_5
#define KV_REG_KEY_ENTRY_14_5                                                                       (0x994)
#endif
#define CLP_KV_REG_KEY_ENTRY_14_6                                                                   (0x10018998)
#ifndef KV_REG_KEY_ENTRY_14_6
#define KV_REG_KEY_ENTRY_14_6                                                                       (0x998)
#endif
#define CLP_KV_REG_KEY_ENTRY_14_7                                                                   (0x1001899c)
#ifndef KV_REG_KEY_ENTRY_14_7
#define KV_REG_KEY_ENTRY_14_7                                                                       (0x99c)
#endif
#define CLP_KV_REG_KEY_ENTRY_14_8                                                                   (0x100189a0)
#ifndef KV_REG_KEY_ENTRY_14_8
#define KV_REG_KEY_ENTRY_14_8                                                                       (0x9a0)
#endif
#define CLP_KV_REG_KEY_ENTRY_14_9                                                                   (0x100189a4)
#ifndef KV_REG_KEY_ENTRY_14_9
#define KV_REG_KEY_ENTRY_14_9                                                                       (0x9a4)
#endif
#define CLP_KV_REG_KEY_ENTRY_14_10                                                                  (0x100189a8)
#ifndef KV_REG_KEY_ENTRY_14_10
#define KV_REG_KEY_ENTRY_14_10                                                                      (0x9a8)
#endif
#define CLP_KV_REG_KEY_ENTRY_14_11                                                                  (0x100189ac)
#ifndef KV_REG_KEY_ENTRY_14_11
#define KV_REG_KEY_ENTRY_14_11                                                                      (0x9ac)
#endif
#define CLP_KV_REG_KEY_ENTRY_14_12                                                                  (0x100189b0)
#ifndef KV_REG_KEY_ENTRY_14_12
#define KV_REG_KEY_ENTRY_14_12                                                                      (0x9b0)
#endif
#define CLP_KV_REG_KEY_ENTRY_14_13                                                                  (0x100189b4)
#ifndef KV_REG_KEY_ENTRY_14_13
#define KV_REG_KEY_ENTRY_14_13                                                                      (0x9b4)
#endif
#define CLP_KV_REG_KEY_ENTRY_14_14                                                                  (0x100189b8)
#ifndef KV_REG_KEY_ENTRY_14_14
#define KV_REG_KEY_ENTRY_14_14                                                                      (0x9b8)
#endif
#define CLP_KV_REG_KEY_ENTRY_14_15                                                                  (0x100189bc)
#ifndef KV_REG_KEY_ENTRY_14_15
#define KV_REG_KEY_ENTRY_14_15                                                                      (0x9bc)
#endif
#define CLP_KV_REG_KEY_ENTRY_15_0                                                                   (0x100189c0)
#ifndef KV_REG_KEY_ENTRY_15_0
#define KV_REG_KEY_ENTRY_15_0                                                                       (0x9c0)
#endif
#define CLP_KV_REG_KEY_ENTRY_15_1                                                                   (0x100189c4)
#ifndef KV_REG_KEY_ENTRY_15_1
#define KV_REG_KEY_ENTRY_15_1                                                                       (0x9c4)
#endif
#define CLP_KV_REG_KEY_ENTRY_15_2                                                                   (0x100189c8)
#ifndef KV_REG_KEY_ENTRY_15_2
#define KV_REG_KEY_ENTRY_15_2                                                                       (0x9c8)
#endif
#define CLP_KV_REG_KEY_ENTRY_15_3                                                                   (0x100189cc)
#ifndef KV_REG_KEY_ENTRY_15_3
#define KV_REG_KEY_ENTRY_15_3                                                                       (0x9cc)
#endif
#define CLP_KV_REG_KEY_ENTRY_15_4                                                                   (0x100189d0)
#ifndef KV_REG_KEY_ENTRY_15_4
#define KV_REG_KEY_ENTRY_15_4                                                                       (0x9d0)
#endif
#define CLP_KV_REG_KEY_ENTRY_15_5                                                                   (0x100189d4)
#ifndef KV_REG_KEY_ENTRY_15_5
#define KV_REG_KEY_ENTRY_15_5                                                                       (0x9d4)
#endif
#define CLP_KV_REG_KEY_ENTRY_15_6                                                                   (0x100189d8)
#ifndef KV_REG_KEY_ENTRY_15_6
#define KV_REG_KEY_ENTRY_15_6                                                                       (0x9d8)
#endif
#define CLP_KV_REG_KEY_ENTRY_15_7                                                                   (0x100189dc)
#ifndef KV_REG_KEY_ENTRY_15_7
#define KV_REG_KEY_ENTRY_15_7                                                                       (0x9dc)
#endif
#define CLP_KV_REG_KEY_ENTRY_15_8                                                                   (0x100189e0)
#ifndef KV_REG_KEY_ENTRY_15_8
#define KV_REG_KEY_ENTRY_15_8                                                                       (0x9e0)
#endif
#define CLP_KV_REG_KEY_ENTRY_15_9                                                                   (0x100189e4)
#ifndef KV_REG_KEY_ENTRY_15_9
#define KV_REG_KEY_ENTRY_15_9                                                                       (0x9e4)
#endif
#define CLP_KV_REG_KEY_ENTRY_15_10                                                                  (0x100189e8)
#ifndef KV_REG_KEY_ENTRY_15_10
#define KV_REG_KEY_ENTRY_15_10                                                                      (0x9e8)
#endif
#define CLP_KV_REG_KEY_ENTRY_15_11                                                                  (0x100189ec)
#ifndef KV_REG_KEY_ENTRY_15_11
#define KV_REG_KEY_ENTRY_15_11                                                                      (0x9ec)
#endif
#define CLP_KV_REG_KEY_ENTRY_15_12                                                                  (0x100189f0)
#ifndef KV_REG_KEY_ENTRY_15_12
#define KV_REG_KEY_ENTRY_15_12                                                                      (0x9f0)
#endif
#define CLP_KV_REG_KEY_ENTRY_15_13                                                                  (0x100189f4)
#ifndef KV_REG_KEY_ENTRY_15_13
#define KV_REG_KEY_ENTRY_15_13                                                                      (0x9f4)
#endif
#define CLP_KV_REG_KEY_ENTRY_15_14                                                                  (0x100189f8)
#ifndef KV_REG_KEY_ENTRY_15_14
#define KV_REG_KEY_ENTRY_15_14                                                                      (0x9f8)
#endif
#define CLP_KV_REG_KEY_ENTRY_15_15                                                                  (0x100189fc)
#ifndef KV_REG_KEY_ENTRY_15_15
#define KV_REG_KEY_ENTRY_15_15                                                                      (0x9fc)
#endif
#define CLP_KV_REG_KEY_ENTRY_16_0                                                                   (0x10018a00)
#ifndef KV_REG_KEY_ENTRY_16_0
#define KV_REG_KEY_ENTRY_16_0                                                                       (0xa00)
#endif
#define CLP_KV_REG_KEY_ENTRY_16_1                                                                   (0x10018a04)
#ifndef KV_REG_KEY_ENTRY_16_1
#define KV_REG_KEY_ENTRY_16_1                                                                       (0xa04)
#endif
#define CLP_KV_REG_KEY_ENTRY_16_2                                                                   (0x10018a08)
#ifndef KV_REG_KEY_ENTRY_16_2
#define KV_REG_KEY_ENTRY_16_2                                                                       (0xa08)
#endif
#define CLP_KV_REG_KEY_ENTRY_16_3                                                                   (0x10018a0c)
#ifndef KV_REG_KEY_ENTRY_16_3
#define KV_REG_KEY_ENTRY_16_3                                                                       (0xa0c)
#endif
#define CLP_KV_REG_KEY_ENTRY_16_4                                                                   (0x10018a10)
#ifndef KV_REG_KEY_ENTRY_16_4
#define KV_REG_KEY_ENTRY_16_4                                                                       (0xa10)
#endif
#define CLP_KV_REG_KEY_ENTRY_16_5                                                                   (0x10018a14)
#ifndef KV_REG_KEY_ENTRY_16_5
#define KV_REG_KEY_ENTRY_16_5                                                                       (0xa14)
#endif
#define CLP_KV_REG_KEY_ENTRY_16_6                                                                   (0x10018a18)
#ifndef KV_REG_KEY_ENTRY_16_6
#define KV_REG_KEY_ENTRY_16_6                                                                       (0xa18)
#endif
#define CLP_KV_REG_KEY_ENTRY_16_7                                                                   (0x10018a1c)
#ifndef KV_REG_KEY_ENTRY_16_7
#define KV_REG_KEY_ENTRY_16_7                                                                       (0xa1c)
#endif
#define CLP_KV_REG_KEY_ENTRY_16_8                                                                   (0x10018a20)
#ifndef KV_REG_KEY_ENTRY_16_8
#define KV_REG_KEY_ENTRY_16_8                                                                       (0xa20)
#endif
#define CLP_KV_REG_KEY_ENTRY_16_9                                                                   (0x10018a24)
#ifndef KV_REG_KEY_ENTRY_16_9
#define KV_REG_KEY_ENTRY_16_9                                                                       (0xa24)
#endif
#define CLP_KV_REG_KEY_ENTRY_16_10                                                                  (0x10018a28)
#ifndef KV_REG_KEY_ENTRY_16_10
#define KV_REG_KEY_ENTRY_16_10                                                                      (0xa28)
#endif
#define CLP_KV_REG_KEY_ENTRY_16_11                                                                  (0x10018a2c)
#ifndef KV_REG_KEY_ENTRY_16_11
#define KV_REG_KEY_ENTRY_16_11                                                                      (0xa2c)
#endif
#define CLP_KV_REG_KEY_ENTRY_16_12                                                                  (0x10018a30)
#ifndef KV_REG_KEY_ENTRY_16_12
#define KV_REG_KEY_ENTRY_16_12                                                                      (0xa30)
#endif
#define CLP_KV_REG_KEY_ENTRY_16_13                                                                  (0x10018a34)
#ifndef KV_REG_KEY_ENTRY_16_13
#define KV_REG_KEY_ENTRY_16_13                                                                      (0xa34)
#endif
#define CLP_KV_REG_KEY_ENTRY_16_14                                                                  (0x10018a38)
#ifndef KV_REG_KEY_ENTRY_16_14
#define KV_REG_KEY_ENTRY_16_14                                                                      (0xa38)
#endif
#define CLP_KV_REG_KEY_ENTRY_16_15                                                                  (0x10018a3c)
#ifndef KV_REG_KEY_ENTRY_16_15
#define KV_REG_KEY_ENTRY_16_15                                                                      (0xa3c)
#endif
#define CLP_KV_REG_KEY_ENTRY_17_0                                                                   (0x10018a40)
#ifndef KV_REG_KEY_ENTRY_17_0
#define KV_REG_KEY_ENTRY_17_0                                                                       (0xa40)
#endif
#define CLP_KV_REG_KEY_ENTRY_17_1                                                                   (0x10018a44)
#ifndef KV_REG_KEY_ENTRY_17_1
#define KV_REG_KEY_ENTRY_17_1                                                                       (0xa44)
#endif
#define CLP_KV_REG_KEY_ENTRY_17_2                                                                   (0x10018a48)
#ifndef KV_REG_KEY_ENTRY_17_2
#define KV_REG_KEY_ENTRY_17_2                                                                       (0xa48)
#endif
#define CLP_KV_REG_KEY_ENTRY_17_3                                                                   (0x10018a4c)
#ifndef KV_REG_KEY_ENTRY_17_3
#define KV_REG_KEY_ENTRY_17_3                                                                       (0xa4c)
#endif
#define CLP_KV_REG_KEY_ENTRY_17_4                                                                   (0x10018a50)
#ifndef KV_REG_KEY_ENTRY_17_4
#define KV_REG_KEY_ENTRY_17_4                                                                       (0xa50)
#endif
#define CLP_KV_REG_KEY_ENTRY_17_5                                                                   (0x10018a54)
#ifndef KV_REG_KEY_ENTRY_17_5
#define KV_REG_KEY_ENTRY_17_5                                                                       (0xa54)
#endif
#define CLP_KV_REG_KEY_ENTRY_17_6                                                                   (0x10018a58)
#ifndef KV_REG_KEY_ENTRY_17_6
#define KV_REG_KEY_ENTRY_17_6                                                                       (0xa58)
#endif
#define CLP_KV_REG_KEY_ENTRY_17_7                                                                   (0x10018a5c)
#ifndef KV_REG_KEY_ENTRY_17_7
#define KV_REG_KEY_ENTRY_17_7                                                                       (0xa5c)
#endif
#define CLP_KV_REG_KEY_ENTRY_17_8                                                                   (0x10018a60)
#ifndef KV_REG_KEY_ENTRY_17_8
#define KV_REG_KEY_ENTRY_17_8                                                                       (0xa60)
#endif
#define CLP_KV_REG_KEY_ENTRY_17_9                                                                   (0x10018a64)
#ifndef KV_REG_KEY_ENTRY_17_9
#define KV_REG_KEY_ENTRY_17_9                                                                       (0xa64)
#endif
#define CLP_KV_REG_KEY_ENTRY_17_10                                                                  (0x10018a68)
#ifndef KV_REG_KEY_ENTRY_17_10
#define KV_REG_KEY_ENTRY_17_10                                                                      (0xa68)
#endif
#define CLP_KV_REG_KEY_ENTRY_17_11                                                                  (0x10018a6c)
#ifndef KV_REG_KEY_ENTRY_17_11
#define KV_REG_KEY_ENTRY_17_11                                                                      (0xa6c)
#endif
#define CLP_KV_REG_KEY_ENTRY_17_12                                                                  (0x10018a70)
#ifndef KV_REG_KEY_ENTRY_17_12
#define KV_REG_KEY_ENTRY_17_12                                                                      (0xa70)
#endif
#define CLP_KV_REG_KEY_ENTRY_17_13                                                                  (0x10018a74)
#ifndef KV_REG_KEY_ENTRY_17_13
#define KV_REG_KEY_ENTRY_17_13                                                                      (0xa74)
#endif
#define CLP_KV_REG_KEY_ENTRY_17_14                                                                  (0x10018a78)
#ifndef KV_REG_KEY_ENTRY_17_14
#define KV_REG_KEY_ENTRY_17_14                                                                      (0xa78)
#endif
#define CLP_KV_REG_KEY_ENTRY_17_15                                                                  (0x10018a7c)
#ifndef KV_REG_KEY_ENTRY_17_15
#define KV_REG_KEY_ENTRY_17_15                                                                      (0xa7c)
#endif
#define CLP_KV_REG_KEY_ENTRY_18_0                                                                   (0x10018a80)
#ifndef KV_REG_KEY_ENTRY_18_0
#define KV_REG_KEY_ENTRY_18_0                                                                       (0xa80)
#endif
#define CLP_KV_REG_KEY_ENTRY_18_1                                                                   (0x10018a84)
#ifndef KV_REG_KEY_ENTRY_18_1
#define KV_REG_KEY_ENTRY_18_1                                                                       (0xa84)
#endif
#define CLP_KV_REG_KEY_ENTRY_18_2                                                                   (0x10018a88)
#ifndef KV_REG_KEY_ENTRY_18_2
#define KV_REG_KEY_ENTRY_18_2                                                                       (0xa88)
#endif
#define CLP_KV_REG_KEY_ENTRY_18_3                                                                   (0x10018a8c)
#ifndef KV_REG_KEY_ENTRY_18_3
#define KV_REG_KEY_ENTRY_18_3                                                                       (0xa8c)
#endif
#define CLP_KV_REG_KEY_ENTRY_18_4                                                                   (0x10018a90)
#ifndef KV_REG_KEY_ENTRY_18_4
#define KV_REG_KEY_ENTRY_18_4                                                                       (0xa90)
#endif
#define CLP_KV_REG_KEY_ENTRY_18_5                                                                   (0x10018a94)
#ifndef KV_REG_KEY_ENTRY_18_5
#define KV_REG_KEY_ENTRY_18_5                                                                       (0xa94)
#endif
#define CLP_KV_REG_KEY_ENTRY_18_6                                                                   (0x10018a98)
#ifndef KV_REG_KEY_ENTRY_18_6
#define KV_REG_KEY_ENTRY_18_6                                                                       (0xa98)
#endif
#define CLP_KV_REG_KEY_ENTRY_18_7                                                                   (0x10018a9c)
#ifndef KV_REG_KEY_ENTRY_18_7
#define KV_REG_KEY_ENTRY_18_7                                                                       (0xa9c)
#endif
#define CLP_KV_REG_KEY_ENTRY_18_8                                                                   (0x10018aa0)
#ifndef KV_REG_KEY_ENTRY_18_8
#define KV_REG_KEY_ENTRY_18_8                                                                       (0xaa0)
#endif
#define CLP_KV_REG_KEY_ENTRY_18_9                                                                   (0x10018aa4)
#ifndef KV_REG_KEY_ENTRY_18_9
#define KV_REG_KEY_ENTRY_18_9                                                                       (0xaa4)
#endif
#define CLP_KV_REG_KEY_ENTRY_18_10                                                                  (0x10018aa8)
#ifndef KV_REG_KEY_ENTRY_18_10
#define KV_REG_KEY_ENTRY_18_10                                                                      (0xaa8)
#endif
#define CLP_KV_REG_KEY_ENTRY_18_11                                                                  (0x10018aac)
#ifndef KV_REG_KEY_ENTRY_18_11
#define KV_REG_KEY_ENTRY_18_11                                                                      (0xaac)
#endif
#define CLP_KV_REG_KEY_ENTRY_18_12                                                                  (0x10018ab0)
#ifndef KV_REG_KEY_ENTRY_18_12
#define KV_REG_KEY_ENTRY_18_12                                                                      (0xab0)
#endif
#define CLP_KV_REG_KEY_ENTRY_18_13                                                                  (0x10018ab4)
#ifndef KV_REG_KEY_ENTRY_18_13
#define KV_REG_KEY_ENTRY_18_13                                                                      (0xab4)
#endif
#define CLP_KV_REG_KEY_ENTRY_18_14                                                                  (0x10018ab8)
#ifndef KV_REG_KEY_ENTRY_18_14
#define KV_REG_KEY_ENTRY_18_14                                                                      (0xab8)
#endif
#define CLP_KV_REG_KEY_ENTRY_18_15                                                                  (0x10018abc)
#ifndef KV_REG_KEY_ENTRY_18_15
#define KV_REG_KEY_ENTRY_18_15                                                                      (0xabc)
#endif
#define CLP_KV_REG_KEY_ENTRY_19_0                                                                   (0x10018ac0)
#ifndef KV_REG_KEY_ENTRY_19_0
#define KV_REG_KEY_ENTRY_19_0                                                                       (0xac0)
#endif
#define CLP_KV_REG_KEY_ENTRY_19_1                                                                   (0x10018ac4)
#ifndef KV_REG_KEY_ENTRY_19_1
#define KV_REG_KEY_ENTRY_19_1                                                                       (0xac4)
#endif
#define CLP_KV_REG_KEY_ENTRY_19_2                                                                   (0x10018ac8)
#ifndef KV_REG_KEY_ENTRY_19_2
#define KV_REG_KEY_ENTRY_19_2                                                                       (0xac8)
#endif
#define CLP_KV_REG_KEY_ENTRY_19_3                                                                   (0x10018acc)
#ifndef KV_REG_KEY_ENTRY_19_3
#define KV_REG_KEY_ENTRY_19_3                                                                       (0xacc)
#endif
#define CLP_KV_REG_KEY_ENTRY_19_4                                                                   (0x10018ad0)
#ifndef KV_REG_KEY_ENTRY_19_4
#define KV_REG_KEY_ENTRY_19_4                                                                       (0xad0)
#endif
#define CLP_KV_REG_KEY_ENTRY_19_5                                                                   (0x10018ad4)
#ifndef KV_REG_KEY_ENTRY_19_5
#define KV_REG_KEY_ENTRY_19_5                                                                       (0xad4)
#endif
#define CLP_KV_REG_KEY_ENTRY_19_6                                                                   (0x10018ad8)
#ifndef KV_REG_KEY_ENTRY_19_6
#define KV_REG_KEY_ENTRY_19_6                                                                       (0xad8)
#endif
#define CLP_KV_REG_KEY_ENTRY_19_7                                                                   (0x10018adc)
#ifndef KV_REG_KEY_ENTRY_19_7
#define KV_REG_KEY_ENTRY_19_7                                                                       (0xadc)
#endif
#define CLP_KV_REG_KEY_ENTRY_19_8                                                                   (0x10018ae0)
#ifndef KV_REG_KEY_ENTRY_19_8
#define KV_REG_KEY_ENTRY_19_8                                                                       (0xae0)
#endif
#define CLP_KV_REG_KEY_ENTRY_19_9                                                                   (0x10018ae4)
#ifndef KV_REG_KEY_ENTRY_19_9
#define KV_REG_KEY_ENTRY_19_9                                                                       (0xae4)
#endif
#define CLP_KV_REG_KEY_ENTRY_19_10                                                                  (0x10018ae8)
#ifndef KV_REG_KEY_ENTRY_19_10
#define KV_REG_KEY_ENTRY_19_10                                                                      (0xae8)
#endif
#define CLP_KV_REG_KEY_ENTRY_19_11                                                                  (0x10018aec)
#ifndef KV_REG_KEY_ENTRY_19_11
#define KV_REG_KEY_ENTRY_19_11                                                                      (0xaec)
#endif
#define CLP_KV_REG_KEY_ENTRY_19_12                                                                  (0x10018af0)
#ifndef KV_REG_KEY_ENTRY_19_12
#define KV_REG_KEY_ENTRY_19_12                                                                      (0xaf0)
#endif
#define CLP_KV_REG_KEY_ENTRY_19_13                                                                  (0x10018af4)
#ifndef KV_REG_KEY_ENTRY_19_13
#define KV_REG_KEY_ENTRY_19_13                                                                      (0xaf4)
#endif
#define CLP_KV_REG_KEY_ENTRY_19_14                                                                  (0x10018af8)
#ifndef KV_REG_KEY_ENTRY_19_14
#define KV_REG_KEY_ENTRY_19_14                                                                      (0xaf8)
#endif
#define CLP_KV_REG_KEY_ENTRY_19_15                                                                  (0x10018afc)
#ifndef KV_REG_KEY_ENTRY_19_15
#define KV_REG_KEY_ENTRY_19_15                                                                      (0xafc)
#endif
#define CLP_KV_REG_KEY_ENTRY_20_0                                                                   (0x10018b00)
#ifndef KV_REG_KEY_ENTRY_20_0
#define KV_REG_KEY_ENTRY_20_0                                                                       (0xb00)
#endif
#define CLP_KV_REG_KEY_ENTRY_20_1                                                                   (0x10018b04)
#ifndef KV_REG_KEY_ENTRY_20_1
#define KV_REG_KEY_ENTRY_20_1                                                                       (0xb04)
#endif
#define CLP_KV_REG_KEY_ENTRY_20_2                                                                   (0x10018b08)
#ifndef KV_REG_KEY_ENTRY_20_2
#define KV_REG_KEY_ENTRY_20_2                                                                       (0xb08)
#endif
#define CLP_KV_REG_KEY_ENTRY_20_3                                                                   (0x10018b0c)
#ifndef KV_REG_KEY_ENTRY_20_3
#define KV_REG_KEY_ENTRY_20_3                                                                       (0xb0c)
#endif
#define CLP_KV_REG_KEY_ENTRY_20_4                                                                   (0x10018b10)
#ifndef KV_REG_KEY_ENTRY_20_4
#define KV_REG_KEY_ENTRY_20_4                                                                       (0xb10)
#endif
#define CLP_KV_REG_KEY_ENTRY_20_5                                                                   (0x10018b14)
#ifndef KV_REG_KEY_ENTRY_20_5
#define KV_REG_KEY_ENTRY_20_5                                                                       (0xb14)
#endif
#define CLP_KV_REG_KEY_ENTRY_20_6                                                                   (0x10018b18)
#ifndef KV_REG_KEY_ENTRY_20_6
#define KV_REG_KEY_ENTRY_20_6                                                                       (0xb18)
#endif
#define CLP_KV_REG_KEY_ENTRY_20_7                                                                   (0x10018b1c)
#ifndef KV_REG_KEY_ENTRY_20_7
#define KV_REG_KEY_ENTRY_20_7                                                                       (0xb1c)
#endif
#define CLP_KV_REG_KEY_ENTRY_20_8                                                                   (0x10018b20)
#ifndef KV_REG_KEY_ENTRY_20_8
#define KV_REG_KEY_ENTRY_20_8                                                                       (0xb20)
#endif
#define CLP_KV_REG_KEY_ENTRY_20_9                                                                   (0x10018b24)
#ifndef KV_REG_KEY_ENTRY_20_9
#define KV_REG_KEY_ENTRY_20_9                                                                       (0xb24)
#endif
#define CLP_KV_REG_KEY_ENTRY_20_10                                                                  (0x10018b28)
#ifndef KV_REG_KEY_ENTRY_20_10
#define KV_REG_KEY_ENTRY_20_10                                                                      (0xb28)
#endif
#define CLP_KV_REG_KEY_ENTRY_20_11                                                                  (0x10018b2c)
#ifndef KV_REG_KEY_ENTRY_20_11
#define KV_REG_KEY_ENTRY_20_11                                                                      (0xb2c)
#endif
#define CLP_KV_REG_KEY_ENTRY_20_12                                                                  (0x10018b30)
#ifndef KV_REG_KEY_ENTRY_20_12
#define KV_REG_KEY_ENTRY_20_12                                                                      (0xb30)
#endif
#define CLP_KV_REG_KEY_ENTRY_20_13                                                                  (0x10018b34)
#ifndef KV_REG_KEY_ENTRY_20_13
#define KV_REG_KEY_ENTRY_20_13                                                                      (0xb34)
#endif
#define CLP_KV_REG_KEY_ENTRY_20_14                                                                  (0x10018b38)
#ifndef KV_REG_KEY_ENTRY_20_14
#define KV_REG_KEY_ENTRY_20_14                                                                      (0xb38)
#endif
#define CLP_KV_REG_KEY_ENTRY_20_15                                                                  (0x10018b3c)
#ifndef KV_REG_KEY_ENTRY_20_15
#define KV_REG_KEY_ENTRY_20_15                                                                      (0xb3c)
#endif
#define CLP_KV_REG_KEY_ENTRY_21_0                                                                   (0x10018b40)
#ifndef KV_REG_KEY_ENTRY_21_0
#define KV_REG_KEY_ENTRY_21_0                                                                       (0xb40)
#endif
#define CLP_KV_REG_KEY_ENTRY_21_1                                                                   (0x10018b44)
#ifndef KV_REG_KEY_ENTRY_21_1
#define KV_REG_KEY_ENTRY_21_1                                                                       (0xb44)
#endif
#define CLP_KV_REG_KEY_ENTRY_21_2                                                                   (0x10018b48)
#ifndef KV_REG_KEY_ENTRY_21_2
#define KV_REG_KEY_ENTRY_21_2                                                                       (0xb48)
#endif
#define CLP_KV_REG_KEY_ENTRY_21_3                                                                   (0x10018b4c)
#ifndef KV_REG_KEY_ENTRY_21_3
#define KV_REG_KEY_ENTRY_21_3                                                                       (0xb4c)
#endif
#define CLP_KV_REG_KEY_ENTRY_21_4                                                                   (0x10018b50)
#ifndef KV_REG_KEY_ENTRY_21_4
#define KV_REG_KEY_ENTRY_21_4                                                                       (0xb50)
#endif
#define CLP_KV_REG_KEY_ENTRY_21_5                                                                   (0x10018b54)
#ifndef KV_REG_KEY_ENTRY_21_5
#define KV_REG_KEY_ENTRY_21_5                                                                       (0xb54)
#endif
#define CLP_KV_REG_KEY_ENTRY_21_6                                                                   (0x10018b58)
#ifndef KV_REG_KEY_ENTRY_21_6
#define KV_REG_KEY_ENTRY_21_6                                                                       (0xb58)
#endif
#define CLP_KV_REG_KEY_ENTRY_21_7                                                                   (0x10018b5c)
#ifndef KV_REG_KEY_ENTRY_21_7
#define KV_REG_KEY_ENTRY_21_7                                                                       (0xb5c)
#endif
#define CLP_KV_REG_KEY_ENTRY_21_8                                                                   (0x10018b60)
#ifndef KV_REG_KEY_ENTRY_21_8
#define KV_REG_KEY_ENTRY_21_8                                                                       (0xb60)
#endif
#define CLP_KV_REG_KEY_ENTRY_21_9                                                                   (0x10018b64)
#ifndef KV_REG_KEY_ENTRY_21_9
#define KV_REG_KEY_ENTRY_21_9                                                                       (0xb64)
#endif
#define CLP_KV_REG_KEY_ENTRY_21_10                                                                  (0x10018b68)
#ifndef KV_REG_KEY_ENTRY_21_10
#define KV_REG_KEY_ENTRY_21_10                                                                      (0xb68)
#endif
#define CLP_KV_REG_KEY_ENTRY_21_11                                                                  (0x10018b6c)
#ifndef KV_REG_KEY_ENTRY_21_11
#define KV_REG_KEY_ENTRY_21_11                                                                      (0xb6c)
#endif
#define CLP_KV_REG_KEY_ENTRY_21_12                                                                  (0x10018b70)
#ifndef KV_REG_KEY_ENTRY_21_12
#define KV_REG_KEY_ENTRY_21_12                                                                      (0xb70)
#endif
#define CLP_KV_REG_KEY_ENTRY_21_13                                                                  (0x10018b74)
#ifndef KV_REG_KEY_ENTRY_21_13
#define KV_REG_KEY_ENTRY_21_13                                                                      (0xb74)
#endif
#define CLP_KV_REG_KEY_ENTRY_21_14                                                                  (0x10018b78)
#ifndef KV_REG_KEY_ENTRY_21_14
#define KV_REG_KEY_ENTRY_21_14                                                                      (0xb78)
#endif
#define CLP_KV_REG_KEY_ENTRY_21_15                                                                  (0x10018b7c)
#ifndef KV_REG_KEY_ENTRY_21_15
#define KV_REG_KEY_ENTRY_21_15                                                                      (0xb7c)
#endif
#define CLP_KV_REG_KEY_ENTRY_22_0                                                                   (0x10018b80)
#ifndef KV_REG_KEY_ENTRY_22_0
#define KV_REG_KEY_ENTRY_22_0                                                                       (0xb80)
#endif
#define CLP_KV_REG_KEY_ENTRY_22_1                                                                   (0x10018b84)
#ifndef KV_REG_KEY_ENTRY_22_1
#define KV_REG_KEY_ENTRY_22_1                                                                       (0xb84)
#endif
#define CLP_KV_REG_KEY_ENTRY_22_2                                                                   (0x10018b88)
#ifndef KV_REG_KEY_ENTRY_22_2
#define KV_REG_KEY_ENTRY_22_2                                                                       (0xb88)
#endif
#define CLP_KV_REG_KEY_ENTRY_22_3                                                                   (0x10018b8c)
#ifndef KV_REG_KEY_ENTRY_22_3
#define KV_REG_KEY_ENTRY_22_3                                                                       (0xb8c)
#endif
#define CLP_KV_REG_KEY_ENTRY_22_4                                                                   (0x10018b90)
#ifndef KV_REG_KEY_ENTRY_22_4
#define KV_REG_KEY_ENTRY_22_4                                                                       (0xb90)
#endif
#define CLP_KV_REG_KEY_ENTRY_22_5                                                                   (0x10018b94)
#ifndef KV_REG_KEY_ENTRY_22_5
#define KV_REG_KEY_ENTRY_22_5                                                                       (0xb94)
#endif
#define CLP_KV_REG_KEY_ENTRY_22_6                                                                   (0x10018b98)
#ifndef KV_REG_KEY_ENTRY_22_6
#define KV_REG_KEY_ENTRY_22_6                                                                       (0xb98)
#endif
#define CLP_KV_REG_KEY_ENTRY_22_7                                                                   (0x10018b9c)
#ifndef KV_REG_KEY_ENTRY_22_7
#define KV_REG_KEY_ENTRY_22_7                                                                       (0xb9c)
#endif
#define CLP_KV_REG_KEY_ENTRY_22_8                                                                   (0x10018ba0)
#ifndef KV_REG_KEY_ENTRY_22_8
#define KV_REG_KEY_ENTRY_22_8                                                                       (0xba0)
#endif
#define CLP_KV_REG_KEY_ENTRY_22_9                                                                   (0x10018ba4)
#ifndef KV_REG_KEY_ENTRY_22_9
#define KV_REG_KEY_ENTRY_22_9                                                                       (0xba4)
#endif
#define CLP_KV_REG_KEY_ENTRY_22_10                                                                  (0x10018ba8)
#ifndef KV_REG_KEY_ENTRY_22_10
#define KV_REG_KEY_ENTRY_22_10                                                                      (0xba8)
#endif
#define CLP_KV_REG_KEY_ENTRY_22_11                                                                  (0x10018bac)
#ifndef KV_REG_KEY_ENTRY_22_11
#define KV_REG_KEY_ENTRY_22_11                                                                      (0xbac)
#endif
#define CLP_KV_REG_KEY_ENTRY_22_12                                                                  (0x10018bb0)
#ifndef KV_REG_KEY_ENTRY_22_12
#define KV_REG_KEY_ENTRY_22_12                                                                      (0xbb0)
#endif
#define CLP_KV_REG_KEY_ENTRY_22_13                                                                  (0x10018bb4)
#ifndef KV_REG_KEY_ENTRY_22_13
#define KV_REG_KEY_ENTRY_22_13                                                                      (0xbb4)
#endif
#define CLP_KV_REG_KEY_ENTRY_22_14                                                                  (0x10018bb8)
#ifndef KV_REG_KEY_ENTRY_22_14
#define KV_REG_KEY_ENTRY_22_14                                                                      (0xbb8)
#endif
#define CLP_KV_REG_KEY_ENTRY_22_15                                                                  (0x10018bbc)
#ifndef KV_REG_KEY_ENTRY_22_15
#define KV_REG_KEY_ENTRY_22_15                                                                      (0xbbc)
#endif
#define CLP_KV_REG_KEY_ENTRY_23_0                                                                   (0x10018bc0)
#ifndef KV_REG_KEY_ENTRY_23_0
#define KV_REG_KEY_ENTRY_23_0                                                                       (0xbc0)
#endif
#define CLP_KV_REG_KEY_ENTRY_23_1                                                                   (0x10018bc4)
#ifndef KV_REG_KEY_ENTRY_23_1
#define KV_REG_KEY_ENTRY_23_1                                                                       (0xbc4)
#endif
#define CLP_KV_REG_KEY_ENTRY_23_2                                                                   (0x10018bc8)
#ifndef KV_REG_KEY_ENTRY_23_2
#define KV_REG_KEY_ENTRY_23_2                                                                       (0xbc8)
#endif
#define CLP_KV_REG_KEY_ENTRY_23_3                                                                   (0x10018bcc)
#ifndef KV_REG_KEY_ENTRY_23_3
#define KV_REG_KEY_ENTRY_23_3                                                                       (0xbcc)
#endif
#define CLP_KV_REG_KEY_ENTRY_23_4                                                                   (0x10018bd0)
#ifndef KV_REG_KEY_ENTRY_23_4
#define KV_REG_KEY_ENTRY_23_4                                                                       (0xbd0)
#endif
#define CLP_KV_REG_KEY_ENTRY_23_5                                                                   (0x10018bd4)
#ifndef KV_REG_KEY_ENTRY_23_5
#define KV_REG_KEY_ENTRY_23_5                                                                       (0xbd4)
#endif
#define CLP_KV_REG_KEY_ENTRY_23_6                                                                   (0x10018bd8)
#ifndef KV_REG_KEY_ENTRY_23_6
#define KV_REG_KEY_ENTRY_23_6                                                                       (0xbd8)
#endif
#define CLP_KV_REG_KEY_ENTRY_23_7                                                                   (0x10018bdc)
#ifndef KV_REG_KEY_ENTRY_23_7
#define KV_REG_KEY_ENTRY_23_7                                                                       (0xbdc)
#endif
#define CLP_KV_REG_KEY_ENTRY_23_8                                                                   (0x10018be0)
#ifndef KV_REG_KEY_ENTRY_23_8
#define KV_REG_KEY_ENTRY_23_8                                                                       (0xbe0)
#endif
#define CLP_KV_REG_KEY_ENTRY_23_9                                                                   (0x10018be4)
#ifndef KV_REG_KEY_ENTRY_23_9
#define KV_REG_KEY_ENTRY_23_9                                                                       (0xbe4)
#endif
#define CLP_KV_REG_KEY_ENTRY_23_10                                                                  (0x10018be8)
#ifndef KV_REG_KEY_ENTRY_23_10
#define KV_REG_KEY_ENTRY_23_10                                                                      (0xbe8)
#endif
#define CLP_KV_REG_KEY_ENTRY_23_11                                                                  (0x10018bec)
#ifndef KV_REG_KEY_ENTRY_23_11
#define KV_REG_KEY_ENTRY_23_11                                                                      (0xbec)
#endif
#define CLP_KV_REG_KEY_ENTRY_23_12                                                                  (0x10018bf0)
#ifndef KV_REG_KEY_ENTRY_23_12
#define KV_REG_KEY_ENTRY_23_12                                                                      (0xbf0)
#endif
#define CLP_KV_REG_KEY_ENTRY_23_13                                                                  (0x10018bf4)
#ifndef KV_REG_KEY_ENTRY_23_13
#define KV_REG_KEY_ENTRY_23_13                                                                      (0xbf4)
#endif
#define CLP_KV_REG_KEY_ENTRY_23_14                                                                  (0x10018bf8)
#ifndef KV_REG_KEY_ENTRY_23_14
#define KV_REG_KEY_ENTRY_23_14                                                                      (0xbf8)
#endif
#define CLP_KV_REG_KEY_ENTRY_23_15                                                                  (0x10018bfc)
#ifndef KV_REG_KEY_ENTRY_23_15
#define KV_REG_KEY_ENTRY_23_15                                                                      (0xbfc)
#endif
#define CLP_KV_REG_CLEAR_SECRETS                                                                    (0x10018c00)
#ifndef KV_REG_CLEAR_SECRETS
#define KV_REG_CLEAR_SECRETS                                                                        (0xc00)
#define KV_REG_CLEAR_SECRETS_WR_DEBUG_VALUES_LOW                                                    (0)
#define KV_REG_CLEAR_SECRETS_WR_DEBUG_VALUES_MASK                                                   (0x1)
#define KV_REG_CLEAR_SECRETS_SEL_DEBUG_VALUE_LOW                                                    (1)
#define KV_REG_CLEAR_SECRETS_SEL_DEBUG_VALUE_MASK                                                   (0x2)
#endif
#define CLP_PV_REG_BASE_ADDR                                                                        (0x1001a000)
#define CLP_PV_REG_PCR_CTRL_0                                                                       (0x1001a000)
#ifndef PV_REG_PCR_CTRL_0
#define PV_REG_PCR_CTRL_0                                                                           (0x0)
#define PV_REG_PCR_CTRL_0_LOCK_LOW                                                                  (0)
#define PV_REG_PCR_CTRL_0_LOCK_MASK                                                                 (0x1)
#define PV_REG_PCR_CTRL_0_CLEAR_LOW                                                                 (1)
#define PV_REG_PCR_CTRL_0_CLEAR_MASK                                                                (0x2)
#define PV_REG_PCR_CTRL_0_RSVD0_LOW                                                                 (2)
#define PV_REG_PCR_CTRL_0_RSVD0_MASK                                                                (0x4)
#define PV_REG_PCR_CTRL_0_RSVD1_LOW                                                                 (3)
#define PV_REG_PCR_CTRL_0_RSVD1_MASK                                                                (0xf8)
#endif
#define CLP_PV_REG_PCR_CTRL_1                                                                       (0x1001a004)
#ifndef PV_REG_PCR_CTRL_1
#define PV_REG_PCR_CTRL_1                                                                           (0x4)
#define PV_REG_PCR_CTRL_1_LOCK_LOW                                                                  (0)
#define PV_REG_PCR_CTRL_1_LOCK_MASK                                                                 (0x1)
#define PV_REG_PCR_CTRL_1_CLEAR_LOW                                                                 (1)
#define PV_REG_PCR_CTRL_1_CLEAR_MASK                                                                (0x2)
#define PV_REG_PCR_CTRL_1_RSVD0_LOW                                                                 (2)
#define PV_REG_PCR_CTRL_1_RSVD0_MASK                                                                (0x4)
#define PV_REG_PCR_CTRL_1_RSVD1_LOW                                                                 (3)
#define PV_REG_PCR_CTRL_1_RSVD1_MASK                                                                (0xf8)
#endif
#define CLP_PV_REG_PCR_CTRL_2                                                                       (0x1001a008)
#ifndef PV_REG_PCR_CTRL_2
#define PV_REG_PCR_CTRL_2                                                                           (0x8)
#define PV_REG_PCR_CTRL_2_LOCK_LOW                                                                  (0)
#define PV_REG_PCR_CTRL_2_LOCK_MASK                                                                 (0x1)
#define PV_REG_PCR_CTRL_2_CLEAR_LOW                                                                 (1)
#define PV_REG_PCR_CTRL_2_CLEAR_MASK                                                                (0x2)
#define PV_REG_PCR_CTRL_2_RSVD0_LOW                                                                 (2)
#define PV_REG_PCR_CTRL_2_RSVD0_MASK                                                                (0x4)
#define PV_REG_PCR_CTRL_2_RSVD1_LOW                                                                 (3)
#define PV_REG_PCR_CTRL_2_RSVD1_MASK                                                                (0xf8)
#endif
#define CLP_PV_REG_PCR_CTRL_3                                                                       (0x1001a00c)
#ifndef PV_REG_PCR_CTRL_3
#define PV_REG_PCR_CTRL_3                                                                           (0xc)
#define PV_REG_PCR_CTRL_3_LOCK_LOW                                                                  (0)
#define PV_REG_PCR_CTRL_3_LOCK_MASK                                                                 (0x1)
#define PV_REG_PCR_CTRL_3_CLEAR_LOW                                                                 (1)
#define PV_REG_PCR_CTRL_3_CLEAR_MASK                                                                (0x2)
#define PV_REG_PCR_CTRL_3_RSVD0_LOW                                                                 (2)
#define PV_REG_PCR_CTRL_3_RSVD0_MASK                                                                (0x4)
#define PV_REG_PCR_CTRL_3_RSVD1_LOW                                                                 (3)
#define PV_REG_PCR_CTRL_3_RSVD1_MASK                                                                (0xf8)
#endif
#define CLP_PV_REG_PCR_CTRL_4                                                                       (0x1001a010)
#ifndef PV_REG_PCR_CTRL_4
#define PV_REG_PCR_CTRL_4                                                                           (0x10)
#define PV_REG_PCR_CTRL_4_LOCK_LOW                                                                  (0)
#define PV_REG_PCR_CTRL_4_LOCK_MASK                                                                 (0x1)
#define PV_REG_PCR_CTRL_4_CLEAR_LOW                                                                 (1)
#define PV_REG_PCR_CTRL_4_CLEAR_MASK                                                                (0x2)
#define PV_REG_PCR_CTRL_4_RSVD0_LOW                                                                 (2)
#define PV_REG_PCR_CTRL_4_RSVD0_MASK                                                                (0x4)
#define PV_REG_PCR_CTRL_4_RSVD1_LOW                                                                 (3)
#define PV_REG_PCR_CTRL_4_RSVD1_MASK                                                                (0xf8)
#endif
#define CLP_PV_REG_PCR_CTRL_5                                                                       (0x1001a014)
#ifndef PV_REG_PCR_CTRL_5
#define PV_REG_PCR_CTRL_5                                                                           (0x14)
#define PV_REG_PCR_CTRL_5_LOCK_LOW                                                                  (0)
#define PV_REG_PCR_CTRL_5_LOCK_MASK                                                                 (0x1)
#define PV_REG_PCR_CTRL_5_CLEAR_LOW                                                                 (1)
#define PV_REG_PCR_CTRL_5_CLEAR_MASK                                                                (0x2)
#define PV_REG_PCR_CTRL_5_RSVD0_LOW                                                                 (2)
#define PV_REG_PCR_CTRL_5_RSVD0_MASK                                                                (0x4)
#define PV_REG_PCR_CTRL_5_RSVD1_LOW                                                                 (3)
#define PV_REG_PCR_CTRL_5_RSVD1_MASK                                                                (0xf8)
#endif
#define CLP_PV_REG_PCR_CTRL_6                                                                       (0x1001a018)
#ifndef PV_REG_PCR_CTRL_6
#define PV_REG_PCR_CTRL_6                                                                           (0x18)
#define PV_REG_PCR_CTRL_6_LOCK_LOW                                                                  (0)
#define PV_REG_PCR_CTRL_6_LOCK_MASK                                                                 (0x1)
#define PV_REG_PCR_CTRL_6_CLEAR_LOW                                                                 (1)
#define PV_REG_PCR_CTRL_6_CLEAR_MASK                                                                (0x2)
#define PV_REG_PCR_CTRL_6_RSVD0_LOW                                                                 (2)
#define PV_REG_PCR_CTRL_6_RSVD0_MASK                                                                (0x4)
#define PV_REG_PCR_CTRL_6_RSVD1_LOW                                                                 (3)
#define PV_REG_PCR_CTRL_6_RSVD1_MASK                                                                (0xf8)
#endif
#define CLP_PV_REG_PCR_CTRL_7                                                                       (0x1001a01c)
#ifndef PV_REG_PCR_CTRL_7
#define PV_REG_PCR_CTRL_7                                                                           (0x1c)
#define PV_REG_PCR_CTRL_7_LOCK_LOW                                                                  (0)
#define PV_REG_PCR_CTRL_7_LOCK_MASK                                                                 (0x1)
#define PV_REG_PCR_CTRL_7_CLEAR_LOW                                                                 (1)
#define PV_REG_PCR_CTRL_7_CLEAR_MASK                                                                (0x2)
#define PV_REG_PCR_CTRL_7_RSVD0_LOW                                                                 (2)
#define PV_REG_PCR_CTRL_7_RSVD0_MASK                                                                (0x4)
#define PV_REG_PCR_CTRL_7_RSVD1_LOW                                                                 (3)
#define PV_REG_PCR_CTRL_7_RSVD1_MASK                                                                (0xf8)
#endif
#define CLP_PV_REG_PCR_CTRL_8                                                                       (0x1001a020)
#ifndef PV_REG_PCR_CTRL_8
#define PV_REG_PCR_CTRL_8                                                                           (0x20)
#define PV_REG_PCR_CTRL_8_LOCK_LOW                                                                  (0)
#define PV_REG_PCR_CTRL_8_LOCK_MASK                                                                 (0x1)
#define PV_REG_PCR_CTRL_8_CLEAR_LOW                                                                 (1)
#define PV_REG_PCR_CTRL_8_CLEAR_MASK                                                                (0x2)
#define PV_REG_PCR_CTRL_8_RSVD0_LOW                                                                 (2)
#define PV_REG_PCR_CTRL_8_RSVD0_MASK                                                                (0x4)
#define PV_REG_PCR_CTRL_8_RSVD1_LOW                                                                 (3)
#define PV_REG_PCR_CTRL_8_RSVD1_MASK                                                                (0xf8)
#endif
#define CLP_PV_REG_PCR_CTRL_9                                                                       (0x1001a024)
#ifndef PV_REG_PCR_CTRL_9
#define PV_REG_PCR_CTRL_9                                                                           (0x24)
#define PV_REG_PCR_CTRL_9_LOCK_LOW                                                                  (0)
#define PV_REG_PCR_CTRL_9_LOCK_MASK                                                                 (0x1)
#define PV_REG_PCR_CTRL_9_CLEAR_LOW                                                                 (1)
#define PV_REG_PCR_CTRL_9_CLEAR_MASK                                                                (0x2)
#define PV_REG_PCR_CTRL_9_RSVD0_LOW                                                                 (2)
#define PV_REG_PCR_CTRL_9_RSVD0_MASK                                                                (0x4)
#define PV_REG_PCR_CTRL_9_RSVD1_LOW                                                                 (3)
#define PV_REG_PCR_CTRL_9_RSVD1_MASK                                                                (0xf8)
#endif
#define CLP_PV_REG_PCR_CTRL_10                                                                      (0x1001a028)
#ifndef PV_REG_PCR_CTRL_10
#define PV_REG_PCR_CTRL_10                                                                          (0x28)
#define PV_REG_PCR_CTRL_10_LOCK_LOW                                                                 (0)
#define PV_REG_PCR_CTRL_10_LOCK_MASK                                                                (0x1)
#define PV_REG_PCR_CTRL_10_CLEAR_LOW                                                                (1)
#define PV_REG_PCR_CTRL_10_CLEAR_MASK                                                               (0x2)
#define PV_REG_PCR_CTRL_10_RSVD0_LOW                                                                (2)
#define PV_REG_PCR_CTRL_10_RSVD0_MASK                                                               (0x4)
#define PV_REG_PCR_CTRL_10_RSVD1_LOW                                                                (3)
#define PV_REG_PCR_CTRL_10_RSVD1_MASK                                                               (0xf8)
#endif
#define CLP_PV_REG_PCR_CTRL_11                                                                      (0x1001a02c)
#ifndef PV_REG_PCR_CTRL_11
#define PV_REG_PCR_CTRL_11                                                                          (0x2c)
#define PV_REG_PCR_CTRL_11_LOCK_LOW                                                                 (0)
#define PV_REG_PCR_CTRL_11_LOCK_MASK                                                                (0x1)
#define PV_REG_PCR_CTRL_11_CLEAR_LOW                                                                (1)
#define PV_REG_PCR_CTRL_11_CLEAR_MASK                                                               (0x2)
#define PV_REG_PCR_CTRL_11_RSVD0_LOW                                                                (2)
#define PV_REG_PCR_CTRL_11_RSVD0_MASK                                                               (0x4)
#define PV_REG_PCR_CTRL_11_RSVD1_LOW                                                                (3)
#define PV_REG_PCR_CTRL_11_RSVD1_MASK                                                               (0xf8)
#endif
#define CLP_PV_REG_PCR_CTRL_12                                                                      (0x1001a030)
#ifndef PV_REG_PCR_CTRL_12
#define PV_REG_PCR_CTRL_12                                                                          (0x30)
#define PV_REG_PCR_CTRL_12_LOCK_LOW                                                                 (0)
#define PV_REG_PCR_CTRL_12_LOCK_MASK                                                                (0x1)
#define PV_REG_PCR_CTRL_12_CLEAR_LOW                                                                (1)
#define PV_REG_PCR_CTRL_12_CLEAR_MASK                                                               (0x2)
#define PV_REG_PCR_CTRL_12_RSVD0_LOW                                                                (2)
#define PV_REG_PCR_CTRL_12_RSVD0_MASK                                                               (0x4)
#define PV_REG_PCR_CTRL_12_RSVD1_LOW                                                                (3)
#define PV_REG_PCR_CTRL_12_RSVD1_MASK                                                               (0xf8)
#endif
#define CLP_PV_REG_PCR_CTRL_13                                                                      (0x1001a034)
#ifndef PV_REG_PCR_CTRL_13
#define PV_REG_PCR_CTRL_13                                                                          (0x34)
#define PV_REG_PCR_CTRL_13_LOCK_LOW                                                                 (0)
#define PV_REG_PCR_CTRL_13_LOCK_MASK                                                                (0x1)
#define PV_REG_PCR_CTRL_13_CLEAR_LOW                                                                (1)
#define PV_REG_PCR_CTRL_13_CLEAR_MASK                                                               (0x2)
#define PV_REG_PCR_CTRL_13_RSVD0_LOW                                                                (2)
#define PV_REG_PCR_CTRL_13_RSVD0_MASK                                                               (0x4)
#define PV_REG_PCR_CTRL_13_RSVD1_LOW                                                                (3)
#define PV_REG_PCR_CTRL_13_RSVD1_MASK                                                               (0xf8)
#endif
#define CLP_PV_REG_PCR_CTRL_14                                                                      (0x1001a038)
#ifndef PV_REG_PCR_CTRL_14
#define PV_REG_PCR_CTRL_14                                                                          (0x38)
#define PV_REG_PCR_CTRL_14_LOCK_LOW                                                                 (0)
#define PV_REG_PCR_CTRL_14_LOCK_MASK                                                                (0x1)
#define PV_REG_PCR_CTRL_14_CLEAR_LOW                                                                (1)
#define PV_REG_PCR_CTRL_14_CLEAR_MASK                                                               (0x2)
#define PV_REG_PCR_CTRL_14_RSVD0_LOW                                                                (2)
#define PV_REG_PCR_CTRL_14_RSVD0_MASK                                                               (0x4)
#define PV_REG_PCR_CTRL_14_RSVD1_LOW                                                                (3)
#define PV_REG_PCR_CTRL_14_RSVD1_MASK                                                               (0xf8)
#endif
#define CLP_PV_REG_PCR_CTRL_15                                                                      (0x1001a03c)
#ifndef PV_REG_PCR_CTRL_15
#define PV_REG_PCR_CTRL_15                                                                          (0x3c)
#define PV_REG_PCR_CTRL_15_LOCK_LOW                                                                 (0)
#define PV_REG_PCR_CTRL_15_LOCK_MASK                                                                (0x1)
#define PV_REG_PCR_CTRL_15_CLEAR_LOW                                                                (1)
#define PV_REG_PCR_CTRL_15_CLEAR_MASK                                                               (0x2)
#define PV_REG_PCR_CTRL_15_RSVD0_LOW                                                                (2)
#define PV_REG_PCR_CTRL_15_RSVD0_MASK                                                               (0x4)
#define PV_REG_PCR_CTRL_15_RSVD1_LOW                                                                (3)
#define PV_REG_PCR_CTRL_15_RSVD1_MASK                                                               (0xf8)
#endif
#define CLP_PV_REG_PCR_CTRL_16                                                                      (0x1001a040)
#ifndef PV_REG_PCR_CTRL_16
#define PV_REG_PCR_CTRL_16                                                                          (0x40)
#define PV_REG_PCR_CTRL_16_LOCK_LOW                                                                 (0)
#define PV_REG_PCR_CTRL_16_LOCK_MASK                                                                (0x1)
#define PV_REG_PCR_CTRL_16_CLEAR_LOW                                                                (1)
#define PV_REG_PCR_CTRL_16_CLEAR_MASK                                                               (0x2)
#define PV_REG_PCR_CTRL_16_RSVD0_LOW                                                                (2)
#define PV_REG_PCR_CTRL_16_RSVD0_MASK                                                               (0x4)
#define PV_REG_PCR_CTRL_16_RSVD1_LOW                                                                (3)
#define PV_REG_PCR_CTRL_16_RSVD1_MASK                                                               (0xf8)
#endif
#define CLP_PV_REG_PCR_CTRL_17                                                                      (0x1001a044)
#ifndef PV_REG_PCR_CTRL_17
#define PV_REG_PCR_CTRL_17                                                                          (0x44)
#define PV_REG_PCR_CTRL_17_LOCK_LOW                                                                 (0)
#define PV_REG_PCR_CTRL_17_LOCK_MASK                                                                (0x1)
#define PV_REG_PCR_CTRL_17_CLEAR_LOW                                                                (1)
#define PV_REG_PCR_CTRL_17_CLEAR_MASK                                                               (0x2)
#define PV_REG_PCR_CTRL_17_RSVD0_LOW                                                                (2)
#define PV_REG_PCR_CTRL_17_RSVD0_MASK                                                               (0x4)
#define PV_REG_PCR_CTRL_17_RSVD1_LOW                                                                (3)
#define PV_REG_PCR_CTRL_17_RSVD1_MASK                                                               (0xf8)
#endif
#define CLP_PV_REG_PCR_CTRL_18                                                                      (0x1001a048)
#ifndef PV_REG_PCR_CTRL_18
#define PV_REG_PCR_CTRL_18                                                                          (0x48)
#define PV_REG_PCR_CTRL_18_LOCK_LOW                                                                 (0)
#define PV_REG_PCR_CTRL_18_LOCK_MASK                                                                (0x1)
#define PV_REG_PCR_CTRL_18_CLEAR_LOW                                                                (1)
#define PV_REG_PCR_CTRL_18_CLEAR_MASK                                                               (0x2)
#define PV_REG_PCR_CTRL_18_RSVD0_LOW                                                                (2)
#define PV_REG_PCR_CTRL_18_RSVD0_MASK                                                               (0x4)
#define PV_REG_PCR_CTRL_18_RSVD1_LOW                                                                (3)
#define PV_REG_PCR_CTRL_18_RSVD1_MASK                                                               (0xf8)
#endif
#define CLP_PV_REG_PCR_CTRL_19                                                                      (0x1001a04c)
#ifndef PV_REG_PCR_CTRL_19
#define PV_REG_PCR_CTRL_19                                                                          (0x4c)
#define PV_REG_PCR_CTRL_19_LOCK_LOW                                                                 (0)
#define PV_REG_PCR_CTRL_19_LOCK_MASK                                                                (0x1)
#define PV_REG_PCR_CTRL_19_CLEAR_LOW                                                                (1)
#define PV_REG_PCR_CTRL_19_CLEAR_MASK                                                               (0x2)
#define PV_REG_PCR_CTRL_19_RSVD0_LOW                                                                (2)
#define PV_REG_PCR_CTRL_19_RSVD0_MASK                                                               (0x4)
#define PV_REG_PCR_CTRL_19_RSVD1_LOW                                                                (3)
#define PV_REG_PCR_CTRL_19_RSVD1_MASK                                                               (0xf8)
#endif
#define CLP_PV_REG_PCR_CTRL_20                                                                      (0x1001a050)
#ifndef PV_REG_PCR_CTRL_20
#define PV_REG_PCR_CTRL_20                                                                          (0x50)
#define PV_REG_PCR_CTRL_20_LOCK_LOW                                                                 (0)
#define PV_REG_PCR_CTRL_20_LOCK_MASK                                                                (0x1)
#define PV_REG_PCR_CTRL_20_CLEAR_LOW                                                                (1)
#define PV_REG_PCR_CTRL_20_CLEAR_MASK                                                               (0x2)
#define PV_REG_PCR_CTRL_20_RSVD0_LOW                                                                (2)
#define PV_REG_PCR_CTRL_20_RSVD0_MASK                                                               (0x4)
#define PV_REG_PCR_CTRL_20_RSVD1_LOW                                                                (3)
#define PV_REG_PCR_CTRL_20_RSVD1_MASK                                                               (0xf8)
#endif
#define CLP_PV_REG_PCR_CTRL_21                                                                      (0x1001a054)
#ifndef PV_REG_PCR_CTRL_21
#define PV_REG_PCR_CTRL_21                                                                          (0x54)
#define PV_REG_PCR_CTRL_21_LOCK_LOW                                                                 (0)
#define PV_REG_PCR_CTRL_21_LOCK_MASK                                                                (0x1)
#define PV_REG_PCR_CTRL_21_CLEAR_LOW                                                                (1)
#define PV_REG_PCR_CTRL_21_CLEAR_MASK                                                               (0x2)
#define PV_REG_PCR_CTRL_21_RSVD0_LOW                                                                (2)
#define PV_REG_PCR_CTRL_21_RSVD0_MASK                                                               (0x4)
#define PV_REG_PCR_CTRL_21_RSVD1_LOW                                                                (3)
#define PV_REG_PCR_CTRL_21_RSVD1_MASK                                                               (0xf8)
#endif
#define CLP_PV_REG_PCR_CTRL_22                                                                      (0x1001a058)
#ifndef PV_REG_PCR_CTRL_22
#define PV_REG_PCR_CTRL_22                                                                          (0x58)
#define PV_REG_PCR_CTRL_22_LOCK_LOW                                                                 (0)
#define PV_REG_PCR_CTRL_22_LOCK_MASK                                                                (0x1)
#define PV_REG_PCR_CTRL_22_CLEAR_LOW                                                                (1)
#define PV_REG_PCR_CTRL_22_CLEAR_MASK                                                               (0x2)
#define PV_REG_PCR_CTRL_22_RSVD0_LOW                                                                (2)
#define PV_REG_PCR_CTRL_22_RSVD0_MASK                                                               (0x4)
#define PV_REG_PCR_CTRL_22_RSVD1_LOW                                                                (3)
#define PV_REG_PCR_CTRL_22_RSVD1_MASK                                                               (0xf8)
#endif
#define CLP_PV_REG_PCR_CTRL_23                                                                      (0x1001a05c)
#ifndef PV_REG_PCR_CTRL_23
#define PV_REG_PCR_CTRL_23                                                                          (0x5c)
#define PV_REG_PCR_CTRL_23_LOCK_LOW                                                                 (0)
#define PV_REG_PCR_CTRL_23_LOCK_MASK                                                                (0x1)
#define PV_REG_PCR_CTRL_23_CLEAR_LOW                                                                (1)
#define PV_REG_PCR_CTRL_23_CLEAR_MASK                                                               (0x2)
#define PV_REG_PCR_CTRL_23_RSVD0_LOW                                                                (2)
#define PV_REG_PCR_CTRL_23_RSVD0_MASK                                                               (0x4)
#define PV_REG_PCR_CTRL_23_RSVD1_LOW                                                                (3)
#define PV_REG_PCR_CTRL_23_RSVD1_MASK                                                               (0xf8)
#endif
#define CLP_PV_REG_PCR_CTRL_24                                                                      (0x1001a060)
#ifndef PV_REG_PCR_CTRL_24
#define PV_REG_PCR_CTRL_24                                                                          (0x60)
#define PV_REG_PCR_CTRL_24_LOCK_LOW                                                                 (0)
#define PV_REG_PCR_CTRL_24_LOCK_MASK                                                                (0x1)
#define PV_REG_PCR_CTRL_24_CLEAR_LOW                                                                (1)
#define PV_REG_PCR_CTRL_24_CLEAR_MASK                                                               (0x2)
#define PV_REG_PCR_CTRL_24_RSVD0_LOW                                                                (2)
#define PV_REG_PCR_CTRL_24_RSVD0_MASK                                                               (0x4)
#define PV_REG_PCR_CTRL_24_RSVD1_LOW                                                                (3)
#define PV_REG_PCR_CTRL_24_RSVD1_MASK                                                               (0xf8)
#endif
#define CLP_PV_REG_PCR_CTRL_25                                                                      (0x1001a064)
#ifndef PV_REG_PCR_CTRL_25
#define PV_REG_PCR_CTRL_25                                                                          (0x64)
#define PV_REG_PCR_CTRL_25_LOCK_LOW                                                                 (0)
#define PV_REG_PCR_CTRL_25_LOCK_MASK                                                                (0x1)
#define PV_REG_PCR_CTRL_25_CLEAR_LOW                                                                (1)
#define PV_REG_PCR_CTRL_25_CLEAR_MASK                                                               (0x2)
#define PV_REG_PCR_CTRL_25_RSVD0_LOW                                                                (2)
#define PV_REG_PCR_CTRL_25_RSVD0_MASK                                                               (0x4)
#define PV_REG_PCR_CTRL_25_RSVD1_LOW                                                                (3)
#define PV_REG_PCR_CTRL_25_RSVD1_MASK                                                               (0xf8)
#endif
#define CLP_PV_REG_PCR_CTRL_26                                                                      (0x1001a068)
#ifndef PV_REG_PCR_CTRL_26
#define PV_REG_PCR_CTRL_26                                                                          (0x68)
#define PV_REG_PCR_CTRL_26_LOCK_LOW                                                                 (0)
#define PV_REG_PCR_CTRL_26_LOCK_MASK                                                                (0x1)
#define PV_REG_PCR_CTRL_26_CLEAR_LOW                                                                (1)
#define PV_REG_PCR_CTRL_26_CLEAR_MASK                                                               (0x2)
#define PV_REG_PCR_CTRL_26_RSVD0_LOW                                                                (2)
#define PV_REG_PCR_CTRL_26_RSVD0_MASK                                                               (0x4)
#define PV_REG_PCR_CTRL_26_RSVD1_LOW                                                                (3)
#define PV_REG_PCR_CTRL_26_RSVD1_MASK                                                               (0xf8)
#endif
#define CLP_PV_REG_PCR_CTRL_27                                                                      (0x1001a06c)
#ifndef PV_REG_PCR_CTRL_27
#define PV_REG_PCR_CTRL_27                                                                          (0x6c)
#define PV_REG_PCR_CTRL_27_LOCK_LOW                                                                 (0)
#define PV_REG_PCR_CTRL_27_LOCK_MASK                                                                (0x1)
#define PV_REG_PCR_CTRL_27_CLEAR_LOW                                                                (1)
#define PV_REG_PCR_CTRL_27_CLEAR_MASK                                                               (0x2)
#define PV_REG_PCR_CTRL_27_RSVD0_LOW                                                                (2)
#define PV_REG_PCR_CTRL_27_RSVD0_MASK                                                               (0x4)
#define PV_REG_PCR_CTRL_27_RSVD1_LOW                                                                (3)
#define PV_REG_PCR_CTRL_27_RSVD1_MASK                                                               (0xf8)
#endif
#define CLP_PV_REG_PCR_CTRL_28                                                                      (0x1001a070)
#ifndef PV_REG_PCR_CTRL_28
#define PV_REG_PCR_CTRL_28                                                                          (0x70)
#define PV_REG_PCR_CTRL_28_LOCK_LOW                                                                 (0)
#define PV_REG_PCR_CTRL_28_LOCK_MASK                                                                (0x1)
#define PV_REG_PCR_CTRL_28_CLEAR_LOW                                                                (1)
#define PV_REG_PCR_CTRL_28_CLEAR_MASK                                                               (0x2)
#define PV_REG_PCR_CTRL_28_RSVD0_LOW                                                                (2)
#define PV_REG_PCR_CTRL_28_RSVD0_MASK                                                               (0x4)
#define PV_REG_PCR_CTRL_28_RSVD1_LOW                                                                (3)
#define PV_REG_PCR_CTRL_28_RSVD1_MASK                                                               (0xf8)
#endif
#define CLP_PV_REG_PCR_CTRL_29                                                                      (0x1001a074)
#ifndef PV_REG_PCR_CTRL_29
#define PV_REG_PCR_CTRL_29                                                                          (0x74)
#define PV_REG_PCR_CTRL_29_LOCK_LOW                                                                 (0)
#define PV_REG_PCR_CTRL_29_LOCK_MASK                                                                (0x1)
#define PV_REG_PCR_CTRL_29_CLEAR_LOW                                                                (1)
#define PV_REG_PCR_CTRL_29_CLEAR_MASK                                                               (0x2)
#define PV_REG_PCR_CTRL_29_RSVD0_LOW                                                                (2)
#define PV_REG_PCR_CTRL_29_RSVD0_MASK                                                               (0x4)
#define PV_REG_PCR_CTRL_29_RSVD1_LOW                                                                (3)
#define PV_REG_PCR_CTRL_29_RSVD1_MASK                                                               (0xf8)
#endif
#define CLP_PV_REG_PCR_CTRL_30                                                                      (0x1001a078)
#ifndef PV_REG_PCR_CTRL_30
#define PV_REG_PCR_CTRL_30                                                                          (0x78)
#define PV_REG_PCR_CTRL_30_LOCK_LOW                                                                 (0)
#define PV_REG_PCR_CTRL_30_LOCK_MASK                                                                (0x1)
#define PV_REG_PCR_CTRL_30_CLEAR_LOW                                                                (1)
#define PV_REG_PCR_CTRL_30_CLEAR_MASK                                                               (0x2)
#define PV_REG_PCR_CTRL_30_RSVD0_LOW                                                                (2)
#define PV_REG_PCR_CTRL_30_RSVD0_MASK                                                               (0x4)
#define PV_REG_PCR_CTRL_30_RSVD1_LOW                                                                (3)
#define PV_REG_PCR_CTRL_30_RSVD1_MASK                                                               (0xf8)
#endif
#define CLP_PV_REG_PCR_CTRL_31                                                                      (0x1001a07c)
#ifndef PV_REG_PCR_CTRL_31
#define PV_REG_PCR_CTRL_31                                                                          (0x7c)
#define PV_REG_PCR_CTRL_31_LOCK_LOW                                                                 (0)
#define PV_REG_PCR_CTRL_31_LOCK_MASK                                                                (0x1)
#define PV_REG_PCR_CTRL_31_CLEAR_LOW                                                                (1)
#define PV_REG_PCR_CTRL_31_CLEAR_MASK                                                               (0x2)
#define PV_REG_PCR_CTRL_31_RSVD0_LOW                                                                (2)
#define PV_REG_PCR_CTRL_31_RSVD0_MASK                                                               (0x4)
#define PV_REG_PCR_CTRL_31_RSVD1_LOW                                                                (3)
#define PV_REG_PCR_CTRL_31_RSVD1_MASK                                                               (0xf8)
#endif
#define CLP_PV_REG_PCR_ENTRY_0_0                                                                    (0x1001a600)
#ifndef PV_REG_PCR_ENTRY_0_0
#define PV_REG_PCR_ENTRY_0_0                                                                        (0x600)
#endif
#define CLP_PV_REG_PCR_ENTRY_0_1                                                                    (0x1001a604)
#ifndef PV_REG_PCR_ENTRY_0_1
#define PV_REG_PCR_ENTRY_0_1                                                                        (0x604)
#endif
#define CLP_PV_REG_PCR_ENTRY_0_2                                                                    (0x1001a608)
#ifndef PV_REG_PCR_ENTRY_0_2
#define PV_REG_PCR_ENTRY_0_2                                                                        (0x608)
#endif
#define CLP_PV_REG_PCR_ENTRY_0_3                                                                    (0x1001a60c)
#ifndef PV_REG_PCR_ENTRY_0_3
#define PV_REG_PCR_ENTRY_0_3                                                                        (0x60c)
#endif
#define CLP_PV_REG_PCR_ENTRY_0_4                                                                    (0x1001a610)
#ifndef PV_REG_PCR_ENTRY_0_4
#define PV_REG_PCR_ENTRY_0_4                                                                        (0x610)
#endif
#define CLP_PV_REG_PCR_ENTRY_0_5                                                                    (0x1001a614)
#ifndef PV_REG_PCR_ENTRY_0_5
#define PV_REG_PCR_ENTRY_0_5                                                                        (0x614)
#endif
#define CLP_PV_REG_PCR_ENTRY_0_6                                                                    (0x1001a618)
#ifndef PV_REG_PCR_ENTRY_0_6
#define PV_REG_PCR_ENTRY_0_6                                                                        (0x618)
#endif
#define CLP_PV_REG_PCR_ENTRY_0_7                                                                    (0x1001a61c)
#ifndef PV_REG_PCR_ENTRY_0_7
#define PV_REG_PCR_ENTRY_0_7                                                                        (0x61c)
#endif
#define CLP_PV_REG_PCR_ENTRY_0_8                                                                    (0x1001a620)
#ifndef PV_REG_PCR_ENTRY_0_8
#define PV_REG_PCR_ENTRY_0_8                                                                        (0x620)
#endif
#define CLP_PV_REG_PCR_ENTRY_0_9                                                                    (0x1001a624)
#ifndef PV_REG_PCR_ENTRY_0_9
#define PV_REG_PCR_ENTRY_0_9                                                                        (0x624)
#endif
#define CLP_PV_REG_PCR_ENTRY_0_10                                                                   (0x1001a628)
#ifndef PV_REG_PCR_ENTRY_0_10
#define PV_REG_PCR_ENTRY_0_10                                                                       (0x628)
#endif
#define CLP_PV_REG_PCR_ENTRY_0_11                                                                   (0x1001a62c)
#ifndef PV_REG_PCR_ENTRY_0_11
#define PV_REG_PCR_ENTRY_0_11                                                                       (0x62c)
#endif
#define CLP_PV_REG_PCR_ENTRY_1_0                                                                    (0x1001a630)
#ifndef PV_REG_PCR_ENTRY_1_0
#define PV_REG_PCR_ENTRY_1_0                                                                        (0x630)
#endif
#define CLP_PV_REG_PCR_ENTRY_1_1                                                                    (0x1001a634)
#ifndef PV_REG_PCR_ENTRY_1_1
#define PV_REG_PCR_ENTRY_1_1                                                                        (0x634)
#endif
#define CLP_PV_REG_PCR_ENTRY_1_2                                                                    (0x1001a638)
#ifndef PV_REG_PCR_ENTRY_1_2
#define PV_REG_PCR_ENTRY_1_2                                                                        (0x638)
#endif
#define CLP_PV_REG_PCR_ENTRY_1_3                                                                    (0x1001a63c)
#ifndef PV_REG_PCR_ENTRY_1_3
#define PV_REG_PCR_ENTRY_1_3                                                                        (0x63c)
#endif
#define CLP_PV_REG_PCR_ENTRY_1_4                                                                    (0x1001a640)
#ifndef PV_REG_PCR_ENTRY_1_4
#define PV_REG_PCR_ENTRY_1_4                                                                        (0x640)
#endif
#define CLP_PV_REG_PCR_ENTRY_1_5                                                                    (0x1001a644)
#ifndef PV_REG_PCR_ENTRY_1_5
#define PV_REG_PCR_ENTRY_1_5                                                                        (0x644)
#endif
#define CLP_PV_REG_PCR_ENTRY_1_6                                                                    (0x1001a648)
#ifndef PV_REG_PCR_ENTRY_1_6
#define PV_REG_PCR_ENTRY_1_6                                                                        (0x648)
#endif
#define CLP_PV_REG_PCR_ENTRY_1_7                                                                    (0x1001a64c)
#ifndef PV_REG_PCR_ENTRY_1_7
#define PV_REG_PCR_ENTRY_1_7                                                                        (0x64c)
#endif
#define CLP_PV_REG_PCR_ENTRY_1_8                                                                    (0x1001a650)
#ifndef PV_REG_PCR_ENTRY_1_8
#define PV_REG_PCR_ENTRY_1_8                                                                        (0x650)
#endif
#define CLP_PV_REG_PCR_ENTRY_1_9                                                                    (0x1001a654)
#ifndef PV_REG_PCR_ENTRY_1_9
#define PV_REG_PCR_ENTRY_1_9                                                                        (0x654)
#endif
#define CLP_PV_REG_PCR_ENTRY_1_10                                                                   (0x1001a658)
#ifndef PV_REG_PCR_ENTRY_1_10
#define PV_REG_PCR_ENTRY_1_10                                                                       (0x658)
#endif
#define CLP_PV_REG_PCR_ENTRY_1_11                                                                   (0x1001a65c)
#ifndef PV_REG_PCR_ENTRY_1_11
#define PV_REG_PCR_ENTRY_1_11                                                                       (0x65c)
#endif
#define CLP_PV_REG_PCR_ENTRY_2_0                                                                    (0x1001a660)
#ifndef PV_REG_PCR_ENTRY_2_0
#define PV_REG_PCR_ENTRY_2_0                                                                        (0x660)
#endif
#define CLP_PV_REG_PCR_ENTRY_2_1                                                                    (0x1001a664)
#ifndef PV_REG_PCR_ENTRY_2_1
#define PV_REG_PCR_ENTRY_2_1                                                                        (0x664)
#endif
#define CLP_PV_REG_PCR_ENTRY_2_2                                                                    (0x1001a668)
#ifndef PV_REG_PCR_ENTRY_2_2
#define PV_REG_PCR_ENTRY_2_2                                                                        (0x668)
#endif
#define CLP_PV_REG_PCR_ENTRY_2_3                                                                    (0x1001a66c)
#ifndef PV_REG_PCR_ENTRY_2_3
#define PV_REG_PCR_ENTRY_2_3                                                                        (0x66c)
#endif
#define CLP_PV_REG_PCR_ENTRY_2_4                                                                    (0x1001a670)
#ifndef PV_REG_PCR_ENTRY_2_4
#define PV_REG_PCR_ENTRY_2_4                                                                        (0x670)
#endif
#define CLP_PV_REG_PCR_ENTRY_2_5                                                                    (0x1001a674)
#ifndef PV_REG_PCR_ENTRY_2_5
#define PV_REG_PCR_ENTRY_2_5                                                                        (0x674)
#endif
#define CLP_PV_REG_PCR_ENTRY_2_6                                                                    (0x1001a678)
#ifndef PV_REG_PCR_ENTRY_2_6
#define PV_REG_PCR_ENTRY_2_6                                                                        (0x678)
#endif
#define CLP_PV_REG_PCR_ENTRY_2_7                                                                    (0x1001a67c)
#ifndef PV_REG_PCR_ENTRY_2_7
#define PV_REG_PCR_ENTRY_2_7                                                                        (0x67c)
#endif
#define CLP_PV_REG_PCR_ENTRY_2_8                                                                    (0x1001a680)
#ifndef PV_REG_PCR_ENTRY_2_8
#define PV_REG_PCR_ENTRY_2_8                                                                        (0x680)
#endif
#define CLP_PV_REG_PCR_ENTRY_2_9                                                                    (0x1001a684)
#ifndef PV_REG_PCR_ENTRY_2_9
#define PV_REG_PCR_ENTRY_2_9                                                                        (0x684)
#endif
#define CLP_PV_REG_PCR_ENTRY_2_10                                                                   (0x1001a688)
#ifndef PV_REG_PCR_ENTRY_2_10
#define PV_REG_PCR_ENTRY_2_10                                                                       (0x688)
#endif
#define CLP_PV_REG_PCR_ENTRY_2_11                                                                   (0x1001a68c)
#ifndef PV_REG_PCR_ENTRY_2_11
#define PV_REG_PCR_ENTRY_2_11                                                                       (0x68c)
#endif
#define CLP_PV_REG_PCR_ENTRY_3_0                                                                    (0x1001a690)
#ifndef PV_REG_PCR_ENTRY_3_0
#define PV_REG_PCR_ENTRY_3_0                                                                        (0x690)
#endif
#define CLP_PV_REG_PCR_ENTRY_3_1                                                                    (0x1001a694)
#ifndef PV_REG_PCR_ENTRY_3_1
#define PV_REG_PCR_ENTRY_3_1                                                                        (0x694)
#endif
#define CLP_PV_REG_PCR_ENTRY_3_2                                                                    (0x1001a698)
#ifndef PV_REG_PCR_ENTRY_3_2
#define PV_REG_PCR_ENTRY_3_2                                                                        (0x698)
#endif
#define CLP_PV_REG_PCR_ENTRY_3_3                                                                    (0x1001a69c)
#ifndef PV_REG_PCR_ENTRY_3_3
#define PV_REG_PCR_ENTRY_3_3                                                                        (0x69c)
#endif
#define CLP_PV_REG_PCR_ENTRY_3_4                                                                    (0x1001a6a0)
#ifndef PV_REG_PCR_ENTRY_3_4
#define PV_REG_PCR_ENTRY_3_4                                                                        (0x6a0)
#endif
#define CLP_PV_REG_PCR_ENTRY_3_5                                                                    (0x1001a6a4)
#ifndef PV_REG_PCR_ENTRY_3_5
#define PV_REG_PCR_ENTRY_3_5                                                                        (0x6a4)
#endif
#define CLP_PV_REG_PCR_ENTRY_3_6                                                                    (0x1001a6a8)
#ifndef PV_REG_PCR_ENTRY_3_6
#define PV_REG_PCR_ENTRY_3_6                                                                        (0x6a8)
#endif
#define CLP_PV_REG_PCR_ENTRY_3_7                                                                    (0x1001a6ac)
#ifndef PV_REG_PCR_ENTRY_3_7
#define PV_REG_PCR_ENTRY_3_7                                                                        (0x6ac)
#endif
#define CLP_PV_REG_PCR_ENTRY_3_8                                                                    (0x1001a6b0)
#ifndef PV_REG_PCR_ENTRY_3_8
#define PV_REG_PCR_ENTRY_3_8                                                                        (0x6b0)
#endif
#define CLP_PV_REG_PCR_ENTRY_3_9                                                                    (0x1001a6b4)
#ifndef PV_REG_PCR_ENTRY_3_9
#define PV_REG_PCR_ENTRY_3_9                                                                        (0x6b4)
#endif
#define CLP_PV_REG_PCR_ENTRY_3_10                                                                   (0x1001a6b8)
#ifndef PV_REG_PCR_ENTRY_3_10
#define PV_REG_PCR_ENTRY_3_10                                                                       (0x6b8)
#endif
#define CLP_PV_REG_PCR_ENTRY_3_11                                                                   (0x1001a6bc)
#ifndef PV_REG_PCR_ENTRY_3_11
#define PV_REG_PCR_ENTRY_3_11                                                                       (0x6bc)
#endif
#define CLP_PV_REG_PCR_ENTRY_4_0                                                                    (0x1001a6c0)
#ifndef PV_REG_PCR_ENTRY_4_0
#define PV_REG_PCR_ENTRY_4_0                                                                        (0x6c0)
#endif
#define CLP_PV_REG_PCR_ENTRY_4_1                                                                    (0x1001a6c4)
#ifndef PV_REG_PCR_ENTRY_4_1
#define PV_REG_PCR_ENTRY_4_1                                                                        (0x6c4)
#endif
#define CLP_PV_REG_PCR_ENTRY_4_2                                                                    (0x1001a6c8)
#ifndef PV_REG_PCR_ENTRY_4_2
#define PV_REG_PCR_ENTRY_4_2                                                                        (0x6c8)
#endif
#define CLP_PV_REG_PCR_ENTRY_4_3                                                                    (0x1001a6cc)
#ifndef PV_REG_PCR_ENTRY_4_3
#define PV_REG_PCR_ENTRY_4_3                                                                        (0x6cc)
#endif
#define CLP_PV_REG_PCR_ENTRY_4_4                                                                    (0x1001a6d0)
#ifndef PV_REG_PCR_ENTRY_4_4
#define PV_REG_PCR_ENTRY_4_4                                                                        (0x6d0)
#endif
#define CLP_PV_REG_PCR_ENTRY_4_5                                                                    (0x1001a6d4)
#ifndef PV_REG_PCR_ENTRY_4_5
#define PV_REG_PCR_ENTRY_4_5                                                                        (0x6d4)
#endif
#define CLP_PV_REG_PCR_ENTRY_4_6                                                                    (0x1001a6d8)
#ifndef PV_REG_PCR_ENTRY_4_6
#define PV_REG_PCR_ENTRY_4_6                                                                        (0x6d8)
#endif
#define CLP_PV_REG_PCR_ENTRY_4_7                                                                    (0x1001a6dc)
#ifndef PV_REG_PCR_ENTRY_4_7
#define PV_REG_PCR_ENTRY_4_7                                                                        (0x6dc)
#endif
#define CLP_PV_REG_PCR_ENTRY_4_8                                                                    (0x1001a6e0)
#ifndef PV_REG_PCR_ENTRY_4_8
#define PV_REG_PCR_ENTRY_4_8                                                                        (0x6e0)
#endif
#define CLP_PV_REG_PCR_ENTRY_4_9                                                                    (0x1001a6e4)
#ifndef PV_REG_PCR_ENTRY_4_9
#define PV_REG_PCR_ENTRY_4_9                                                                        (0x6e4)
#endif
#define CLP_PV_REG_PCR_ENTRY_4_10                                                                   (0x1001a6e8)
#ifndef PV_REG_PCR_ENTRY_4_10
#define PV_REG_PCR_ENTRY_4_10                                                                       (0x6e8)
#endif
#define CLP_PV_REG_PCR_ENTRY_4_11                                                                   (0x1001a6ec)
#ifndef PV_REG_PCR_ENTRY_4_11
#define PV_REG_PCR_ENTRY_4_11                                                                       (0x6ec)
#endif
#define CLP_PV_REG_PCR_ENTRY_5_0                                                                    (0x1001a6f0)
#ifndef PV_REG_PCR_ENTRY_5_0
#define PV_REG_PCR_ENTRY_5_0                                                                        (0x6f0)
#endif
#define CLP_PV_REG_PCR_ENTRY_5_1                                                                    (0x1001a6f4)
#ifndef PV_REG_PCR_ENTRY_5_1
#define PV_REG_PCR_ENTRY_5_1                                                                        (0x6f4)
#endif
#define CLP_PV_REG_PCR_ENTRY_5_2                                                                    (0x1001a6f8)
#ifndef PV_REG_PCR_ENTRY_5_2
#define PV_REG_PCR_ENTRY_5_2                                                                        (0x6f8)
#endif
#define CLP_PV_REG_PCR_ENTRY_5_3                                                                    (0x1001a6fc)
#ifndef PV_REG_PCR_ENTRY_5_3
#define PV_REG_PCR_ENTRY_5_3                                                                        (0x6fc)
#endif
#define CLP_PV_REG_PCR_ENTRY_5_4                                                                    (0x1001a700)
#ifndef PV_REG_PCR_ENTRY_5_4
#define PV_REG_PCR_ENTRY_5_4                                                                        (0x700)
#endif
#define CLP_PV_REG_PCR_ENTRY_5_5                                                                    (0x1001a704)
#ifndef PV_REG_PCR_ENTRY_5_5
#define PV_REG_PCR_ENTRY_5_5                                                                        (0x704)
#endif
#define CLP_PV_REG_PCR_ENTRY_5_6                                                                    (0x1001a708)
#ifndef PV_REG_PCR_ENTRY_5_6
#define PV_REG_PCR_ENTRY_5_6                                                                        (0x708)
#endif
#define CLP_PV_REG_PCR_ENTRY_5_7                                                                    (0x1001a70c)
#ifndef PV_REG_PCR_ENTRY_5_7
#define PV_REG_PCR_ENTRY_5_7                                                                        (0x70c)
#endif
#define CLP_PV_REG_PCR_ENTRY_5_8                                                                    (0x1001a710)
#ifndef PV_REG_PCR_ENTRY_5_8
#define PV_REG_PCR_ENTRY_5_8                                                                        (0x710)
#endif
#define CLP_PV_REG_PCR_ENTRY_5_9                                                                    (0x1001a714)
#ifndef PV_REG_PCR_ENTRY_5_9
#define PV_REG_PCR_ENTRY_5_9                                                                        (0x714)
#endif
#define CLP_PV_REG_PCR_ENTRY_5_10                                                                   (0x1001a718)
#ifndef PV_REG_PCR_ENTRY_5_10
#define PV_REG_PCR_ENTRY_5_10                                                                       (0x718)
#endif
#define CLP_PV_REG_PCR_ENTRY_5_11                                                                   (0x1001a71c)
#ifndef PV_REG_PCR_ENTRY_5_11
#define PV_REG_PCR_ENTRY_5_11                                                                       (0x71c)
#endif
#define CLP_PV_REG_PCR_ENTRY_6_0                                                                    (0x1001a720)
#ifndef PV_REG_PCR_ENTRY_6_0
#define PV_REG_PCR_ENTRY_6_0                                                                        (0x720)
#endif
#define CLP_PV_REG_PCR_ENTRY_6_1                                                                    (0x1001a724)
#ifndef PV_REG_PCR_ENTRY_6_1
#define PV_REG_PCR_ENTRY_6_1                                                                        (0x724)
#endif
#define CLP_PV_REG_PCR_ENTRY_6_2                                                                    (0x1001a728)
#ifndef PV_REG_PCR_ENTRY_6_2
#define PV_REG_PCR_ENTRY_6_2                                                                        (0x728)
#endif
#define CLP_PV_REG_PCR_ENTRY_6_3                                                                    (0x1001a72c)
#ifndef PV_REG_PCR_ENTRY_6_3
#define PV_REG_PCR_ENTRY_6_3                                                                        (0x72c)
#endif
#define CLP_PV_REG_PCR_ENTRY_6_4                                                                    (0x1001a730)
#ifndef PV_REG_PCR_ENTRY_6_4
#define PV_REG_PCR_ENTRY_6_4                                                                        (0x730)
#endif
#define CLP_PV_REG_PCR_ENTRY_6_5                                                                    (0x1001a734)
#ifndef PV_REG_PCR_ENTRY_6_5
#define PV_REG_PCR_ENTRY_6_5                                                                        (0x734)
#endif
#define CLP_PV_REG_PCR_ENTRY_6_6                                                                    (0x1001a738)
#ifndef PV_REG_PCR_ENTRY_6_6
#define PV_REG_PCR_ENTRY_6_6                                                                        (0x738)
#endif
#define CLP_PV_REG_PCR_ENTRY_6_7                                                                    (0x1001a73c)
#ifndef PV_REG_PCR_ENTRY_6_7
#define PV_REG_PCR_ENTRY_6_7                                                                        (0x73c)
#endif
#define CLP_PV_REG_PCR_ENTRY_6_8                                                                    (0x1001a740)
#ifndef PV_REG_PCR_ENTRY_6_8
#define PV_REG_PCR_ENTRY_6_8                                                                        (0x740)
#endif
#define CLP_PV_REG_PCR_ENTRY_6_9                                                                    (0x1001a744)
#ifndef PV_REG_PCR_ENTRY_6_9
#define PV_REG_PCR_ENTRY_6_9                                                                        (0x744)
#endif
#define CLP_PV_REG_PCR_ENTRY_6_10                                                                   (0x1001a748)
#ifndef PV_REG_PCR_ENTRY_6_10
#define PV_REG_PCR_ENTRY_6_10                                                                       (0x748)
#endif
#define CLP_PV_REG_PCR_ENTRY_6_11                                                                   (0x1001a74c)
#ifndef PV_REG_PCR_ENTRY_6_11
#define PV_REG_PCR_ENTRY_6_11                                                                       (0x74c)
#endif
#define CLP_PV_REG_PCR_ENTRY_7_0                                                                    (0x1001a750)
#ifndef PV_REG_PCR_ENTRY_7_0
#define PV_REG_PCR_ENTRY_7_0                                                                        (0x750)
#endif
#define CLP_PV_REG_PCR_ENTRY_7_1                                                                    (0x1001a754)
#ifndef PV_REG_PCR_ENTRY_7_1
#define PV_REG_PCR_ENTRY_7_1                                                                        (0x754)
#endif
#define CLP_PV_REG_PCR_ENTRY_7_2                                                                    (0x1001a758)
#ifndef PV_REG_PCR_ENTRY_7_2
#define PV_REG_PCR_ENTRY_7_2                                                                        (0x758)
#endif
#define CLP_PV_REG_PCR_ENTRY_7_3                                                                    (0x1001a75c)
#ifndef PV_REG_PCR_ENTRY_7_3
#define PV_REG_PCR_ENTRY_7_3                                                                        (0x75c)
#endif
#define CLP_PV_REG_PCR_ENTRY_7_4                                                                    (0x1001a760)
#ifndef PV_REG_PCR_ENTRY_7_4
#define PV_REG_PCR_ENTRY_7_4                                                                        (0x760)
#endif
#define CLP_PV_REG_PCR_ENTRY_7_5                                                                    (0x1001a764)
#ifndef PV_REG_PCR_ENTRY_7_5
#define PV_REG_PCR_ENTRY_7_5                                                                        (0x764)
#endif
#define CLP_PV_REG_PCR_ENTRY_7_6                                                                    (0x1001a768)
#ifndef PV_REG_PCR_ENTRY_7_6
#define PV_REG_PCR_ENTRY_7_6                                                                        (0x768)
#endif
#define CLP_PV_REG_PCR_ENTRY_7_7                                                                    (0x1001a76c)
#ifndef PV_REG_PCR_ENTRY_7_7
#define PV_REG_PCR_ENTRY_7_7                                                                        (0x76c)
#endif
#define CLP_PV_REG_PCR_ENTRY_7_8                                                                    (0x1001a770)
#ifndef PV_REG_PCR_ENTRY_7_8
#define PV_REG_PCR_ENTRY_7_8                                                                        (0x770)
#endif
#define CLP_PV_REG_PCR_ENTRY_7_9                                                                    (0x1001a774)
#ifndef PV_REG_PCR_ENTRY_7_9
#define PV_REG_PCR_ENTRY_7_9                                                                        (0x774)
#endif
#define CLP_PV_REG_PCR_ENTRY_7_10                                                                   (0x1001a778)
#ifndef PV_REG_PCR_ENTRY_7_10
#define PV_REG_PCR_ENTRY_7_10                                                                       (0x778)
#endif
#define CLP_PV_REG_PCR_ENTRY_7_11                                                                   (0x1001a77c)
#ifndef PV_REG_PCR_ENTRY_7_11
#define PV_REG_PCR_ENTRY_7_11                                                                       (0x77c)
#endif
#define CLP_PV_REG_PCR_ENTRY_8_0                                                                    (0x1001a780)
#ifndef PV_REG_PCR_ENTRY_8_0
#define PV_REG_PCR_ENTRY_8_0                                                                        (0x780)
#endif
#define CLP_PV_REG_PCR_ENTRY_8_1                                                                    (0x1001a784)
#ifndef PV_REG_PCR_ENTRY_8_1
#define PV_REG_PCR_ENTRY_8_1                                                                        (0x784)
#endif
#define CLP_PV_REG_PCR_ENTRY_8_2                                                                    (0x1001a788)
#ifndef PV_REG_PCR_ENTRY_8_2
#define PV_REG_PCR_ENTRY_8_2                                                                        (0x788)
#endif
#define CLP_PV_REG_PCR_ENTRY_8_3                                                                    (0x1001a78c)
#ifndef PV_REG_PCR_ENTRY_8_3
#define PV_REG_PCR_ENTRY_8_3                                                                        (0x78c)
#endif
#define CLP_PV_REG_PCR_ENTRY_8_4                                                                    (0x1001a790)
#ifndef PV_REG_PCR_ENTRY_8_4
#define PV_REG_PCR_ENTRY_8_4                                                                        (0x790)
#endif
#define CLP_PV_REG_PCR_ENTRY_8_5                                                                    (0x1001a794)
#ifndef PV_REG_PCR_ENTRY_8_5
#define PV_REG_PCR_ENTRY_8_5                                                                        (0x794)
#endif
#define CLP_PV_REG_PCR_ENTRY_8_6                                                                    (0x1001a798)
#ifndef PV_REG_PCR_ENTRY_8_6
#define PV_REG_PCR_ENTRY_8_6                                                                        (0x798)
#endif
#define CLP_PV_REG_PCR_ENTRY_8_7                                                                    (0x1001a79c)
#ifndef PV_REG_PCR_ENTRY_8_7
#define PV_REG_PCR_ENTRY_8_7                                                                        (0x79c)
#endif
#define CLP_PV_REG_PCR_ENTRY_8_8                                                                    (0x1001a7a0)
#ifndef PV_REG_PCR_ENTRY_8_8
#define PV_REG_PCR_ENTRY_8_8                                                                        (0x7a0)
#endif
#define CLP_PV_REG_PCR_ENTRY_8_9                                                                    (0x1001a7a4)
#ifndef PV_REG_PCR_ENTRY_8_9
#define PV_REG_PCR_ENTRY_8_9                                                                        (0x7a4)
#endif
#define CLP_PV_REG_PCR_ENTRY_8_10                                                                   (0x1001a7a8)
#ifndef PV_REG_PCR_ENTRY_8_10
#define PV_REG_PCR_ENTRY_8_10                                                                       (0x7a8)
#endif
#define CLP_PV_REG_PCR_ENTRY_8_11                                                                   (0x1001a7ac)
#ifndef PV_REG_PCR_ENTRY_8_11
#define PV_REG_PCR_ENTRY_8_11                                                                       (0x7ac)
#endif
#define CLP_PV_REG_PCR_ENTRY_9_0                                                                    (0x1001a7b0)
#ifndef PV_REG_PCR_ENTRY_9_0
#define PV_REG_PCR_ENTRY_9_0                                                                        (0x7b0)
#endif
#define CLP_PV_REG_PCR_ENTRY_9_1                                                                    (0x1001a7b4)
#ifndef PV_REG_PCR_ENTRY_9_1
#define PV_REG_PCR_ENTRY_9_1                                                                        (0x7b4)
#endif
#define CLP_PV_REG_PCR_ENTRY_9_2                                                                    (0x1001a7b8)
#ifndef PV_REG_PCR_ENTRY_9_2
#define PV_REG_PCR_ENTRY_9_2                                                                        (0x7b8)
#endif
#define CLP_PV_REG_PCR_ENTRY_9_3                                                                    (0x1001a7bc)
#ifndef PV_REG_PCR_ENTRY_9_3
#define PV_REG_PCR_ENTRY_9_3                                                                        (0x7bc)
#endif
#define CLP_PV_REG_PCR_ENTRY_9_4                                                                    (0x1001a7c0)
#ifndef PV_REG_PCR_ENTRY_9_4
#define PV_REG_PCR_ENTRY_9_4                                                                        (0x7c0)
#endif
#define CLP_PV_REG_PCR_ENTRY_9_5                                                                    (0x1001a7c4)
#ifndef PV_REG_PCR_ENTRY_9_5
#define PV_REG_PCR_ENTRY_9_5                                                                        (0x7c4)
#endif
#define CLP_PV_REG_PCR_ENTRY_9_6                                                                    (0x1001a7c8)
#ifndef PV_REG_PCR_ENTRY_9_6
#define PV_REG_PCR_ENTRY_9_6                                                                        (0x7c8)
#endif
#define CLP_PV_REG_PCR_ENTRY_9_7                                                                    (0x1001a7cc)
#ifndef PV_REG_PCR_ENTRY_9_7
#define PV_REG_PCR_ENTRY_9_7                                                                        (0x7cc)
#endif
#define CLP_PV_REG_PCR_ENTRY_9_8                                                                    (0x1001a7d0)
#ifndef PV_REG_PCR_ENTRY_9_8
#define PV_REG_PCR_ENTRY_9_8                                                                        (0x7d0)
#endif
#define CLP_PV_REG_PCR_ENTRY_9_9                                                                    (0x1001a7d4)
#ifndef PV_REG_PCR_ENTRY_9_9
#define PV_REG_PCR_ENTRY_9_9                                                                        (0x7d4)
#endif
#define CLP_PV_REG_PCR_ENTRY_9_10                                                                   (0x1001a7d8)
#ifndef PV_REG_PCR_ENTRY_9_10
#define PV_REG_PCR_ENTRY_9_10                                                                       (0x7d8)
#endif
#define CLP_PV_REG_PCR_ENTRY_9_11                                                                   (0x1001a7dc)
#ifndef PV_REG_PCR_ENTRY_9_11
#define PV_REG_PCR_ENTRY_9_11                                                                       (0x7dc)
#endif
#define CLP_PV_REG_PCR_ENTRY_10_0                                                                   (0x1001a7e0)
#ifndef PV_REG_PCR_ENTRY_10_0
#define PV_REG_PCR_ENTRY_10_0                                                                       (0x7e0)
#endif
#define CLP_PV_REG_PCR_ENTRY_10_1                                                                   (0x1001a7e4)
#ifndef PV_REG_PCR_ENTRY_10_1
#define PV_REG_PCR_ENTRY_10_1                                                                       (0x7e4)
#endif
#define CLP_PV_REG_PCR_ENTRY_10_2                                                                   (0x1001a7e8)
#ifndef PV_REG_PCR_ENTRY_10_2
#define PV_REG_PCR_ENTRY_10_2                                                                       (0x7e8)
#endif
#define CLP_PV_REG_PCR_ENTRY_10_3                                                                   (0x1001a7ec)
#ifndef PV_REG_PCR_ENTRY_10_3
#define PV_REG_PCR_ENTRY_10_3                                                                       (0x7ec)
#endif
#define CLP_PV_REG_PCR_ENTRY_10_4                                                                   (0x1001a7f0)
#ifndef PV_REG_PCR_ENTRY_10_4
#define PV_REG_PCR_ENTRY_10_4                                                                       (0x7f0)
#endif
#define CLP_PV_REG_PCR_ENTRY_10_5                                                                   (0x1001a7f4)
#ifndef PV_REG_PCR_ENTRY_10_5
#define PV_REG_PCR_ENTRY_10_5                                                                       (0x7f4)
#endif
#define CLP_PV_REG_PCR_ENTRY_10_6                                                                   (0x1001a7f8)
#ifndef PV_REG_PCR_ENTRY_10_6
#define PV_REG_PCR_ENTRY_10_6                                                                       (0x7f8)
#endif
#define CLP_PV_REG_PCR_ENTRY_10_7                                                                   (0x1001a7fc)
#ifndef PV_REG_PCR_ENTRY_10_7
#define PV_REG_PCR_ENTRY_10_7                                                                       (0x7fc)
#endif
#define CLP_PV_REG_PCR_ENTRY_10_8                                                                   (0x1001a800)
#ifndef PV_REG_PCR_ENTRY_10_8
#define PV_REG_PCR_ENTRY_10_8                                                                       (0x800)
#endif
#define CLP_PV_REG_PCR_ENTRY_10_9                                                                   (0x1001a804)
#ifndef PV_REG_PCR_ENTRY_10_9
#define PV_REG_PCR_ENTRY_10_9                                                                       (0x804)
#endif
#define CLP_PV_REG_PCR_ENTRY_10_10                                                                  (0x1001a808)
#ifndef PV_REG_PCR_ENTRY_10_10
#define PV_REG_PCR_ENTRY_10_10                                                                      (0x808)
#endif
#define CLP_PV_REG_PCR_ENTRY_10_11                                                                  (0x1001a80c)
#ifndef PV_REG_PCR_ENTRY_10_11
#define PV_REG_PCR_ENTRY_10_11                                                                      (0x80c)
#endif
#define CLP_PV_REG_PCR_ENTRY_11_0                                                                   (0x1001a810)
#ifndef PV_REG_PCR_ENTRY_11_0
#define PV_REG_PCR_ENTRY_11_0                                                                       (0x810)
#endif
#define CLP_PV_REG_PCR_ENTRY_11_1                                                                   (0x1001a814)
#ifndef PV_REG_PCR_ENTRY_11_1
#define PV_REG_PCR_ENTRY_11_1                                                                       (0x814)
#endif
#define CLP_PV_REG_PCR_ENTRY_11_2                                                                   (0x1001a818)
#ifndef PV_REG_PCR_ENTRY_11_2
#define PV_REG_PCR_ENTRY_11_2                                                                       (0x818)
#endif
#define CLP_PV_REG_PCR_ENTRY_11_3                                                                   (0x1001a81c)
#ifndef PV_REG_PCR_ENTRY_11_3
#define PV_REG_PCR_ENTRY_11_3                                                                       (0x81c)
#endif
#define CLP_PV_REG_PCR_ENTRY_11_4                                                                   (0x1001a820)
#ifndef PV_REG_PCR_ENTRY_11_4
#define PV_REG_PCR_ENTRY_11_4                                                                       (0x820)
#endif
#define CLP_PV_REG_PCR_ENTRY_11_5                                                                   (0x1001a824)
#ifndef PV_REG_PCR_ENTRY_11_5
#define PV_REG_PCR_ENTRY_11_5                                                                       (0x824)
#endif
#define CLP_PV_REG_PCR_ENTRY_11_6                                                                   (0x1001a828)
#ifndef PV_REG_PCR_ENTRY_11_6
#define PV_REG_PCR_ENTRY_11_6                                                                       (0x828)
#endif
#define CLP_PV_REG_PCR_ENTRY_11_7                                                                   (0x1001a82c)
#ifndef PV_REG_PCR_ENTRY_11_7
#define PV_REG_PCR_ENTRY_11_7                                                                       (0x82c)
#endif
#define CLP_PV_REG_PCR_ENTRY_11_8                                                                   (0x1001a830)
#ifndef PV_REG_PCR_ENTRY_11_8
#define PV_REG_PCR_ENTRY_11_8                                                                       (0x830)
#endif
#define CLP_PV_REG_PCR_ENTRY_11_9                                                                   (0x1001a834)
#ifndef PV_REG_PCR_ENTRY_11_9
#define PV_REG_PCR_ENTRY_11_9                                                                       (0x834)
#endif
#define CLP_PV_REG_PCR_ENTRY_11_10                                                                  (0x1001a838)
#ifndef PV_REG_PCR_ENTRY_11_10
#define PV_REG_PCR_ENTRY_11_10                                                                      (0x838)
#endif
#define CLP_PV_REG_PCR_ENTRY_11_11                                                                  (0x1001a83c)
#ifndef PV_REG_PCR_ENTRY_11_11
#define PV_REG_PCR_ENTRY_11_11                                                                      (0x83c)
#endif
#define CLP_PV_REG_PCR_ENTRY_12_0                                                                   (0x1001a840)
#ifndef PV_REG_PCR_ENTRY_12_0
#define PV_REG_PCR_ENTRY_12_0                                                                       (0x840)
#endif
#define CLP_PV_REG_PCR_ENTRY_12_1                                                                   (0x1001a844)
#ifndef PV_REG_PCR_ENTRY_12_1
#define PV_REG_PCR_ENTRY_12_1                                                                       (0x844)
#endif
#define CLP_PV_REG_PCR_ENTRY_12_2                                                                   (0x1001a848)
#ifndef PV_REG_PCR_ENTRY_12_2
#define PV_REG_PCR_ENTRY_12_2                                                                       (0x848)
#endif
#define CLP_PV_REG_PCR_ENTRY_12_3                                                                   (0x1001a84c)
#ifndef PV_REG_PCR_ENTRY_12_3
#define PV_REG_PCR_ENTRY_12_3                                                                       (0x84c)
#endif
#define CLP_PV_REG_PCR_ENTRY_12_4                                                                   (0x1001a850)
#ifndef PV_REG_PCR_ENTRY_12_4
#define PV_REG_PCR_ENTRY_12_4                                                                       (0x850)
#endif
#define CLP_PV_REG_PCR_ENTRY_12_5                                                                   (0x1001a854)
#ifndef PV_REG_PCR_ENTRY_12_5
#define PV_REG_PCR_ENTRY_12_5                                                                       (0x854)
#endif
#define CLP_PV_REG_PCR_ENTRY_12_6                                                                   (0x1001a858)
#ifndef PV_REG_PCR_ENTRY_12_6
#define PV_REG_PCR_ENTRY_12_6                                                                       (0x858)
#endif
#define CLP_PV_REG_PCR_ENTRY_12_7                                                                   (0x1001a85c)
#ifndef PV_REG_PCR_ENTRY_12_7
#define PV_REG_PCR_ENTRY_12_7                                                                       (0x85c)
#endif
#define CLP_PV_REG_PCR_ENTRY_12_8                                                                   (0x1001a860)
#ifndef PV_REG_PCR_ENTRY_12_8
#define PV_REG_PCR_ENTRY_12_8                                                                       (0x860)
#endif
#define CLP_PV_REG_PCR_ENTRY_12_9                                                                   (0x1001a864)
#ifndef PV_REG_PCR_ENTRY_12_9
#define PV_REG_PCR_ENTRY_12_9                                                                       (0x864)
#endif
#define CLP_PV_REG_PCR_ENTRY_12_10                                                                  (0x1001a868)
#ifndef PV_REG_PCR_ENTRY_12_10
#define PV_REG_PCR_ENTRY_12_10                                                                      (0x868)
#endif
#define CLP_PV_REG_PCR_ENTRY_12_11                                                                  (0x1001a86c)
#ifndef PV_REG_PCR_ENTRY_12_11
#define PV_REG_PCR_ENTRY_12_11                                                                      (0x86c)
#endif
#define CLP_PV_REG_PCR_ENTRY_13_0                                                                   (0x1001a870)
#ifndef PV_REG_PCR_ENTRY_13_0
#define PV_REG_PCR_ENTRY_13_0                                                                       (0x870)
#endif
#define CLP_PV_REG_PCR_ENTRY_13_1                                                                   (0x1001a874)
#ifndef PV_REG_PCR_ENTRY_13_1
#define PV_REG_PCR_ENTRY_13_1                                                                       (0x874)
#endif
#define CLP_PV_REG_PCR_ENTRY_13_2                                                                   (0x1001a878)
#ifndef PV_REG_PCR_ENTRY_13_2
#define PV_REG_PCR_ENTRY_13_2                                                                       (0x878)
#endif
#define CLP_PV_REG_PCR_ENTRY_13_3                                                                   (0x1001a87c)
#ifndef PV_REG_PCR_ENTRY_13_3
#define PV_REG_PCR_ENTRY_13_3                                                                       (0x87c)
#endif
#define CLP_PV_REG_PCR_ENTRY_13_4                                                                   (0x1001a880)
#ifndef PV_REG_PCR_ENTRY_13_4
#define PV_REG_PCR_ENTRY_13_4                                                                       (0x880)
#endif
#define CLP_PV_REG_PCR_ENTRY_13_5                                                                   (0x1001a884)
#ifndef PV_REG_PCR_ENTRY_13_5
#define PV_REG_PCR_ENTRY_13_5                                                                       (0x884)
#endif
#define CLP_PV_REG_PCR_ENTRY_13_6                                                                   (0x1001a888)
#ifndef PV_REG_PCR_ENTRY_13_6
#define PV_REG_PCR_ENTRY_13_6                                                                       (0x888)
#endif
#define CLP_PV_REG_PCR_ENTRY_13_7                                                                   (0x1001a88c)
#ifndef PV_REG_PCR_ENTRY_13_7
#define PV_REG_PCR_ENTRY_13_7                                                                       (0x88c)
#endif
#define CLP_PV_REG_PCR_ENTRY_13_8                                                                   (0x1001a890)
#ifndef PV_REG_PCR_ENTRY_13_8
#define PV_REG_PCR_ENTRY_13_8                                                                       (0x890)
#endif
#define CLP_PV_REG_PCR_ENTRY_13_9                                                                   (0x1001a894)
#ifndef PV_REG_PCR_ENTRY_13_9
#define PV_REG_PCR_ENTRY_13_9                                                                       (0x894)
#endif
#define CLP_PV_REG_PCR_ENTRY_13_10                                                                  (0x1001a898)
#ifndef PV_REG_PCR_ENTRY_13_10
#define PV_REG_PCR_ENTRY_13_10                                                                      (0x898)
#endif
#define CLP_PV_REG_PCR_ENTRY_13_11                                                                  (0x1001a89c)
#ifndef PV_REG_PCR_ENTRY_13_11
#define PV_REG_PCR_ENTRY_13_11                                                                      (0x89c)
#endif
#define CLP_PV_REG_PCR_ENTRY_14_0                                                                   (0x1001a8a0)
#ifndef PV_REG_PCR_ENTRY_14_0
#define PV_REG_PCR_ENTRY_14_0                                                                       (0x8a0)
#endif
#define CLP_PV_REG_PCR_ENTRY_14_1                                                                   (0x1001a8a4)
#ifndef PV_REG_PCR_ENTRY_14_1
#define PV_REG_PCR_ENTRY_14_1                                                                       (0x8a4)
#endif
#define CLP_PV_REG_PCR_ENTRY_14_2                                                                   (0x1001a8a8)
#ifndef PV_REG_PCR_ENTRY_14_2
#define PV_REG_PCR_ENTRY_14_2                                                                       (0x8a8)
#endif
#define CLP_PV_REG_PCR_ENTRY_14_3                                                                   (0x1001a8ac)
#ifndef PV_REG_PCR_ENTRY_14_3
#define PV_REG_PCR_ENTRY_14_3                                                                       (0x8ac)
#endif
#define CLP_PV_REG_PCR_ENTRY_14_4                                                                   (0x1001a8b0)
#ifndef PV_REG_PCR_ENTRY_14_4
#define PV_REG_PCR_ENTRY_14_4                                                                       (0x8b0)
#endif
#define CLP_PV_REG_PCR_ENTRY_14_5                                                                   (0x1001a8b4)
#ifndef PV_REG_PCR_ENTRY_14_5
#define PV_REG_PCR_ENTRY_14_5                                                                       (0x8b4)
#endif
#define CLP_PV_REG_PCR_ENTRY_14_6                                                                   (0x1001a8b8)
#ifndef PV_REG_PCR_ENTRY_14_6
#define PV_REG_PCR_ENTRY_14_6                                                                       (0x8b8)
#endif
#define CLP_PV_REG_PCR_ENTRY_14_7                                                                   (0x1001a8bc)
#ifndef PV_REG_PCR_ENTRY_14_7
#define PV_REG_PCR_ENTRY_14_7                                                                       (0x8bc)
#endif
#define CLP_PV_REG_PCR_ENTRY_14_8                                                                   (0x1001a8c0)
#ifndef PV_REG_PCR_ENTRY_14_8
#define PV_REG_PCR_ENTRY_14_8                                                                       (0x8c0)
#endif
#define CLP_PV_REG_PCR_ENTRY_14_9                                                                   (0x1001a8c4)
#ifndef PV_REG_PCR_ENTRY_14_9
#define PV_REG_PCR_ENTRY_14_9                                                                       (0x8c4)
#endif
#define CLP_PV_REG_PCR_ENTRY_14_10                                                                  (0x1001a8c8)
#ifndef PV_REG_PCR_ENTRY_14_10
#define PV_REG_PCR_ENTRY_14_10                                                                      (0x8c8)
#endif
#define CLP_PV_REG_PCR_ENTRY_14_11                                                                  (0x1001a8cc)
#ifndef PV_REG_PCR_ENTRY_14_11
#define PV_REG_PCR_ENTRY_14_11                                                                      (0x8cc)
#endif
#define CLP_PV_REG_PCR_ENTRY_15_0                                                                   (0x1001a8d0)
#ifndef PV_REG_PCR_ENTRY_15_0
#define PV_REG_PCR_ENTRY_15_0                                                                       (0x8d0)
#endif
#define CLP_PV_REG_PCR_ENTRY_15_1                                                                   (0x1001a8d4)
#ifndef PV_REG_PCR_ENTRY_15_1
#define PV_REG_PCR_ENTRY_15_1                                                                       (0x8d4)
#endif
#define CLP_PV_REG_PCR_ENTRY_15_2                                                                   (0x1001a8d8)
#ifndef PV_REG_PCR_ENTRY_15_2
#define PV_REG_PCR_ENTRY_15_2                                                                       (0x8d8)
#endif
#define CLP_PV_REG_PCR_ENTRY_15_3                                                                   (0x1001a8dc)
#ifndef PV_REG_PCR_ENTRY_15_3
#define PV_REG_PCR_ENTRY_15_3                                                                       (0x8dc)
#endif
#define CLP_PV_REG_PCR_ENTRY_15_4                                                                   (0x1001a8e0)
#ifndef PV_REG_PCR_ENTRY_15_4
#define PV_REG_PCR_ENTRY_15_4                                                                       (0x8e0)
#endif
#define CLP_PV_REG_PCR_ENTRY_15_5                                                                   (0x1001a8e4)
#ifndef PV_REG_PCR_ENTRY_15_5
#define PV_REG_PCR_ENTRY_15_5                                                                       (0x8e4)
#endif
#define CLP_PV_REG_PCR_ENTRY_15_6                                                                   (0x1001a8e8)
#ifndef PV_REG_PCR_ENTRY_15_6
#define PV_REG_PCR_ENTRY_15_6                                                                       (0x8e8)
#endif
#define CLP_PV_REG_PCR_ENTRY_15_7                                                                   (0x1001a8ec)
#ifndef PV_REG_PCR_ENTRY_15_7
#define PV_REG_PCR_ENTRY_15_7                                                                       (0x8ec)
#endif
#define CLP_PV_REG_PCR_ENTRY_15_8                                                                   (0x1001a8f0)
#ifndef PV_REG_PCR_ENTRY_15_8
#define PV_REG_PCR_ENTRY_15_8                                                                       (0x8f0)
#endif
#define CLP_PV_REG_PCR_ENTRY_15_9                                                                   (0x1001a8f4)
#ifndef PV_REG_PCR_ENTRY_15_9
#define PV_REG_PCR_ENTRY_15_9                                                                       (0x8f4)
#endif
#define CLP_PV_REG_PCR_ENTRY_15_10                                                                  (0x1001a8f8)
#ifndef PV_REG_PCR_ENTRY_15_10
#define PV_REG_PCR_ENTRY_15_10                                                                      (0x8f8)
#endif
#define CLP_PV_REG_PCR_ENTRY_15_11                                                                  (0x1001a8fc)
#ifndef PV_REG_PCR_ENTRY_15_11
#define PV_REG_PCR_ENTRY_15_11                                                                      (0x8fc)
#endif
#define CLP_PV_REG_PCR_ENTRY_16_0                                                                   (0x1001a900)
#ifndef PV_REG_PCR_ENTRY_16_0
#define PV_REG_PCR_ENTRY_16_0                                                                       (0x900)
#endif
#define CLP_PV_REG_PCR_ENTRY_16_1                                                                   (0x1001a904)
#ifndef PV_REG_PCR_ENTRY_16_1
#define PV_REG_PCR_ENTRY_16_1                                                                       (0x904)
#endif
#define CLP_PV_REG_PCR_ENTRY_16_2                                                                   (0x1001a908)
#ifndef PV_REG_PCR_ENTRY_16_2
#define PV_REG_PCR_ENTRY_16_2                                                                       (0x908)
#endif
#define CLP_PV_REG_PCR_ENTRY_16_3                                                                   (0x1001a90c)
#ifndef PV_REG_PCR_ENTRY_16_3
#define PV_REG_PCR_ENTRY_16_3                                                                       (0x90c)
#endif
#define CLP_PV_REG_PCR_ENTRY_16_4                                                                   (0x1001a910)
#ifndef PV_REG_PCR_ENTRY_16_4
#define PV_REG_PCR_ENTRY_16_4                                                                       (0x910)
#endif
#define CLP_PV_REG_PCR_ENTRY_16_5                                                                   (0x1001a914)
#ifndef PV_REG_PCR_ENTRY_16_5
#define PV_REG_PCR_ENTRY_16_5                                                                       (0x914)
#endif
#define CLP_PV_REG_PCR_ENTRY_16_6                                                                   (0x1001a918)
#ifndef PV_REG_PCR_ENTRY_16_6
#define PV_REG_PCR_ENTRY_16_6                                                                       (0x918)
#endif
#define CLP_PV_REG_PCR_ENTRY_16_7                                                                   (0x1001a91c)
#ifndef PV_REG_PCR_ENTRY_16_7
#define PV_REG_PCR_ENTRY_16_7                                                                       (0x91c)
#endif
#define CLP_PV_REG_PCR_ENTRY_16_8                                                                   (0x1001a920)
#ifndef PV_REG_PCR_ENTRY_16_8
#define PV_REG_PCR_ENTRY_16_8                                                                       (0x920)
#endif
#define CLP_PV_REG_PCR_ENTRY_16_9                                                                   (0x1001a924)
#ifndef PV_REG_PCR_ENTRY_16_9
#define PV_REG_PCR_ENTRY_16_9                                                                       (0x924)
#endif
#define CLP_PV_REG_PCR_ENTRY_16_10                                                                  (0x1001a928)
#ifndef PV_REG_PCR_ENTRY_16_10
#define PV_REG_PCR_ENTRY_16_10                                                                      (0x928)
#endif
#define CLP_PV_REG_PCR_ENTRY_16_11                                                                  (0x1001a92c)
#ifndef PV_REG_PCR_ENTRY_16_11
#define PV_REG_PCR_ENTRY_16_11                                                                      (0x92c)
#endif
#define CLP_PV_REG_PCR_ENTRY_17_0                                                                   (0x1001a930)
#ifndef PV_REG_PCR_ENTRY_17_0
#define PV_REG_PCR_ENTRY_17_0                                                                       (0x930)
#endif
#define CLP_PV_REG_PCR_ENTRY_17_1                                                                   (0x1001a934)
#ifndef PV_REG_PCR_ENTRY_17_1
#define PV_REG_PCR_ENTRY_17_1                                                                       (0x934)
#endif
#define CLP_PV_REG_PCR_ENTRY_17_2                                                                   (0x1001a938)
#ifndef PV_REG_PCR_ENTRY_17_2
#define PV_REG_PCR_ENTRY_17_2                                                                       (0x938)
#endif
#define CLP_PV_REG_PCR_ENTRY_17_3                                                                   (0x1001a93c)
#ifndef PV_REG_PCR_ENTRY_17_3
#define PV_REG_PCR_ENTRY_17_3                                                                       (0x93c)
#endif
#define CLP_PV_REG_PCR_ENTRY_17_4                                                                   (0x1001a940)
#ifndef PV_REG_PCR_ENTRY_17_4
#define PV_REG_PCR_ENTRY_17_4                                                                       (0x940)
#endif
#define CLP_PV_REG_PCR_ENTRY_17_5                                                                   (0x1001a944)
#ifndef PV_REG_PCR_ENTRY_17_5
#define PV_REG_PCR_ENTRY_17_5                                                                       (0x944)
#endif
#define CLP_PV_REG_PCR_ENTRY_17_6                                                                   (0x1001a948)
#ifndef PV_REG_PCR_ENTRY_17_6
#define PV_REG_PCR_ENTRY_17_6                                                                       (0x948)
#endif
#define CLP_PV_REG_PCR_ENTRY_17_7                                                                   (0x1001a94c)
#ifndef PV_REG_PCR_ENTRY_17_7
#define PV_REG_PCR_ENTRY_17_7                                                                       (0x94c)
#endif
#define CLP_PV_REG_PCR_ENTRY_17_8                                                                   (0x1001a950)
#ifndef PV_REG_PCR_ENTRY_17_8
#define PV_REG_PCR_ENTRY_17_8                                                                       (0x950)
#endif
#define CLP_PV_REG_PCR_ENTRY_17_9                                                                   (0x1001a954)
#ifndef PV_REG_PCR_ENTRY_17_9
#define PV_REG_PCR_ENTRY_17_9                                                                       (0x954)
#endif
#define CLP_PV_REG_PCR_ENTRY_17_10                                                                  (0x1001a958)
#ifndef PV_REG_PCR_ENTRY_17_10
#define PV_REG_PCR_ENTRY_17_10                                                                      (0x958)
#endif
#define CLP_PV_REG_PCR_ENTRY_17_11                                                                  (0x1001a95c)
#ifndef PV_REG_PCR_ENTRY_17_11
#define PV_REG_PCR_ENTRY_17_11                                                                      (0x95c)
#endif
#define CLP_PV_REG_PCR_ENTRY_18_0                                                                   (0x1001a960)
#ifndef PV_REG_PCR_ENTRY_18_0
#define PV_REG_PCR_ENTRY_18_0                                                                       (0x960)
#endif
#define CLP_PV_REG_PCR_ENTRY_18_1                                                                   (0x1001a964)
#ifndef PV_REG_PCR_ENTRY_18_1
#define PV_REG_PCR_ENTRY_18_1                                                                       (0x964)
#endif
#define CLP_PV_REG_PCR_ENTRY_18_2                                                                   (0x1001a968)
#ifndef PV_REG_PCR_ENTRY_18_2
#define PV_REG_PCR_ENTRY_18_2                                                                       (0x968)
#endif
#define CLP_PV_REG_PCR_ENTRY_18_3                                                                   (0x1001a96c)
#ifndef PV_REG_PCR_ENTRY_18_3
#define PV_REG_PCR_ENTRY_18_3                                                                       (0x96c)
#endif
#define CLP_PV_REG_PCR_ENTRY_18_4                                                                   (0x1001a970)
#ifndef PV_REG_PCR_ENTRY_18_4
#define PV_REG_PCR_ENTRY_18_4                                                                       (0x970)
#endif
#define CLP_PV_REG_PCR_ENTRY_18_5                                                                   (0x1001a974)
#ifndef PV_REG_PCR_ENTRY_18_5
#define PV_REG_PCR_ENTRY_18_5                                                                       (0x974)
#endif
#define CLP_PV_REG_PCR_ENTRY_18_6                                                                   (0x1001a978)
#ifndef PV_REG_PCR_ENTRY_18_6
#define PV_REG_PCR_ENTRY_18_6                                                                       (0x978)
#endif
#define CLP_PV_REG_PCR_ENTRY_18_7                                                                   (0x1001a97c)
#ifndef PV_REG_PCR_ENTRY_18_7
#define PV_REG_PCR_ENTRY_18_7                                                                       (0x97c)
#endif
#define CLP_PV_REG_PCR_ENTRY_18_8                                                                   (0x1001a980)
#ifndef PV_REG_PCR_ENTRY_18_8
#define PV_REG_PCR_ENTRY_18_8                                                                       (0x980)
#endif
#define CLP_PV_REG_PCR_ENTRY_18_9                                                                   (0x1001a984)
#ifndef PV_REG_PCR_ENTRY_18_9
#define PV_REG_PCR_ENTRY_18_9                                                                       (0x984)
#endif
#define CLP_PV_REG_PCR_ENTRY_18_10                                                                  (0x1001a988)
#ifndef PV_REG_PCR_ENTRY_18_10
#define PV_REG_PCR_ENTRY_18_10                                                                      (0x988)
#endif
#define CLP_PV_REG_PCR_ENTRY_18_11                                                                  (0x1001a98c)
#ifndef PV_REG_PCR_ENTRY_18_11
#define PV_REG_PCR_ENTRY_18_11                                                                      (0x98c)
#endif
#define CLP_PV_REG_PCR_ENTRY_19_0                                                                   (0x1001a990)
#ifndef PV_REG_PCR_ENTRY_19_0
#define PV_REG_PCR_ENTRY_19_0                                                                       (0x990)
#endif
#define CLP_PV_REG_PCR_ENTRY_19_1                                                                   (0x1001a994)
#ifndef PV_REG_PCR_ENTRY_19_1
#define PV_REG_PCR_ENTRY_19_1                                                                       (0x994)
#endif
#define CLP_PV_REG_PCR_ENTRY_19_2                                                                   (0x1001a998)
#ifndef PV_REG_PCR_ENTRY_19_2
#define PV_REG_PCR_ENTRY_19_2                                                                       (0x998)
#endif
#define CLP_PV_REG_PCR_ENTRY_19_3                                                                   (0x1001a99c)
#ifndef PV_REG_PCR_ENTRY_19_3
#define PV_REG_PCR_ENTRY_19_3                                                                       (0x99c)
#endif
#define CLP_PV_REG_PCR_ENTRY_19_4                                                                   (0x1001a9a0)
#ifndef PV_REG_PCR_ENTRY_19_4
#define PV_REG_PCR_ENTRY_19_4                                                                       (0x9a0)
#endif
#define CLP_PV_REG_PCR_ENTRY_19_5                                                                   (0x1001a9a4)
#ifndef PV_REG_PCR_ENTRY_19_5
#define PV_REG_PCR_ENTRY_19_5                                                                       (0x9a4)
#endif
#define CLP_PV_REG_PCR_ENTRY_19_6                                                                   (0x1001a9a8)
#ifndef PV_REG_PCR_ENTRY_19_6
#define PV_REG_PCR_ENTRY_19_6                                                                       (0x9a8)
#endif
#define CLP_PV_REG_PCR_ENTRY_19_7                                                                   (0x1001a9ac)
#ifndef PV_REG_PCR_ENTRY_19_7
#define PV_REG_PCR_ENTRY_19_7                                                                       (0x9ac)
#endif
#define CLP_PV_REG_PCR_ENTRY_19_8                                                                   (0x1001a9b0)
#ifndef PV_REG_PCR_ENTRY_19_8
#define PV_REG_PCR_ENTRY_19_8                                                                       (0x9b0)
#endif
#define CLP_PV_REG_PCR_ENTRY_19_9                                                                   (0x1001a9b4)
#ifndef PV_REG_PCR_ENTRY_19_9
#define PV_REG_PCR_ENTRY_19_9                                                                       (0x9b4)
#endif
#define CLP_PV_REG_PCR_ENTRY_19_10                                                                  (0x1001a9b8)
#ifndef PV_REG_PCR_ENTRY_19_10
#define PV_REG_PCR_ENTRY_19_10                                                                      (0x9b8)
#endif
#define CLP_PV_REG_PCR_ENTRY_19_11                                                                  (0x1001a9bc)
#ifndef PV_REG_PCR_ENTRY_19_11
#define PV_REG_PCR_ENTRY_19_11                                                                      (0x9bc)
#endif
#define CLP_PV_REG_PCR_ENTRY_20_0                                                                   (0x1001a9c0)
#ifndef PV_REG_PCR_ENTRY_20_0
#define PV_REG_PCR_ENTRY_20_0                                                                       (0x9c0)
#endif
#define CLP_PV_REG_PCR_ENTRY_20_1                                                                   (0x1001a9c4)
#ifndef PV_REG_PCR_ENTRY_20_1
#define PV_REG_PCR_ENTRY_20_1                                                                       (0x9c4)
#endif
#define CLP_PV_REG_PCR_ENTRY_20_2                                                                   (0x1001a9c8)
#ifndef PV_REG_PCR_ENTRY_20_2
#define PV_REG_PCR_ENTRY_20_2                                                                       (0x9c8)
#endif
#define CLP_PV_REG_PCR_ENTRY_20_3                                                                   (0x1001a9cc)
#ifndef PV_REG_PCR_ENTRY_20_3
#define PV_REG_PCR_ENTRY_20_3                                                                       (0x9cc)
#endif
#define CLP_PV_REG_PCR_ENTRY_20_4                                                                   (0x1001a9d0)
#ifndef PV_REG_PCR_ENTRY_20_4
#define PV_REG_PCR_ENTRY_20_4                                                                       (0x9d0)
#endif
#define CLP_PV_REG_PCR_ENTRY_20_5                                                                   (0x1001a9d4)
#ifndef PV_REG_PCR_ENTRY_20_5
#define PV_REG_PCR_ENTRY_20_5                                                                       (0x9d4)
#endif
#define CLP_PV_REG_PCR_ENTRY_20_6                                                                   (0x1001a9d8)
#ifndef PV_REG_PCR_ENTRY_20_6
#define PV_REG_PCR_ENTRY_20_6                                                                       (0x9d8)
#endif
#define CLP_PV_REG_PCR_ENTRY_20_7                                                                   (0x1001a9dc)
#ifndef PV_REG_PCR_ENTRY_20_7
#define PV_REG_PCR_ENTRY_20_7                                                                       (0x9dc)
#endif
#define CLP_PV_REG_PCR_ENTRY_20_8                                                                   (0x1001a9e0)
#ifndef PV_REG_PCR_ENTRY_20_8
#define PV_REG_PCR_ENTRY_20_8                                                                       (0x9e0)
#endif
#define CLP_PV_REG_PCR_ENTRY_20_9                                                                   (0x1001a9e4)
#ifndef PV_REG_PCR_ENTRY_20_9
#define PV_REG_PCR_ENTRY_20_9                                                                       (0x9e4)
#endif
#define CLP_PV_REG_PCR_ENTRY_20_10                                                                  (0x1001a9e8)
#ifndef PV_REG_PCR_ENTRY_20_10
#define PV_REG_PCR_ENTRY_20_10                                                                      (0x9e8)
#endif
#define CLP_PV_REG_PCR_ENTRY_20_11                                                                  (0x1001a9ec)
#ifndef PV_REG_PCR_ENTRY_20_11
#define PV_REG_PCR_ENTRY_20_11                                                                      (0x9ec)
#endif
#define CLP_PV_REG_PCR_ENTRY_21_0                                                                   (0x1001a9f0)
#ifndef PV_REG_PCR_ENTRY_21_0
#define PV_REG_PCR_ENTRY_21_0                                                                       (0x9f0)
#endif
#define CLP_PV_REG_PCR_ENTRY_21_1                                                                   (0x1001a9f4)
#ifndef PV_REG_PCR_ENTRY_21_1
#define PV_REG_PCR_ENTRY_21_1                                                                       (0x9f4)
#endif
#define CLP_PV_REG_PCR_ENTRY_21_2                                                                   (0x1001a9f8)
#ifndef PV_REG_PCR_ENTRY_21_2
#define PV_REG_PCR_ENTRY_21_2                                                                       (0x9f8)
#endif
#define CLP_PV_REG_PCR_ENTRY_21_3                                                                   (0x1001a9fc)
#ifndef PV_REG_PCR_ENTRY_21_3
#define PV_REG_PCR_ENTRY_21_3                                                                       (0x9fc)
#endif
#define CLP_PV_REG_PCR_ENTRY_21_4                                                                   (0x1001aa00)
#ifndef PV_REG_PCR_ENTRY_21_4
#define PV_REG_PCR_ENTRY_21_4                                                                       (0xa00)
#endif
#define CLP_PV_REG_PCR_ENTRY_21_5                                                                   (0x1001aa04)
#ifndef PV_REG_PCR_ENTRY_21_5
#define PV_REG_PCR_ENTRY_21_5                                                                       (0xa04)
#endif
#define CLP_PV_REG_PCR_ENTRY_21_6                                                                   (0x1001aa08)
#ifndef PV_REG_PCR_ENTRY_21_6
#define PV_REG_PCR_ENTRY_21_6                                                                       (0xa08)
#endif
#define CLP_PV_REG_PCR_ENTRY_21_7                                                                   (0x1001aa0c)
#ifndef PV_REG_PCR_ENTRY_21_7
#define PV_REG_PCR_ENTRY_21_7                                                                       (0xa0c)
#endif
#define CLP_PV_REG_PCR_ENTRY_21_8                                                                   (0x1001aa10)
#ifndef PV_REG_PCR_ENTRY_21_8
#define PV_REG_PCR_ENTRY_21_8                                                                       (0xa10)
#endif
#define CLP_PV_REG_PCR_ENTRY_21_9                                                                   (0x1001aa14)
#ifndef PV_REG_PCR_ENTRY_21_9
#define PV_REG_PCR_ENTRY_21_9                                                                       (0xa14)
#endif
#define CLP_PV_REG_PCR_ENTRY_21_10                                                                  (0x1001aa18)
#ifndef PV_REG_PCR_ENTRY_21_10
#define PV_REG_PCR_ENTRY_21_10                                                                      (0xa18)
#endif
#define CLP_PV_REG_PCR_ENTRY_21_11                                                                  (0x1001aa1c)
#ifndef PV_REG_PCR_ENTRY_21_11
#define PV_REG_PCR_ENTRY_21_11                                                                      (0xa1c)
#endif
#define CLP_PV_REG_PCR_ENTRY_22_0                                                                   (0x1001aa20)
#ifndef PV_REG_PCR_ENTRY_22_0
#define PV_REG_PCR_ENTRY_22_0                                                                       (0xa20)
#endif
#define CLP_PV_REG_PCR_ENTRY_22_1                                                                   (0x1001aa24)
#ifndef PV_REG_PCR_ENTRY_22_1
#define PV_REG_PCR_ENTRY_22_1                                                                       (0xa24)
#endif
#define CLP_PV_REG_PCR_ENTRY_22_2                                                                   (0x1001aa28)
#ifndef PV_REG_PCR_ENTRY_22_2
#define PV_REG_PCR_ENTRY_22_2                                                                       (0xa28)
#endif
#define CLP_PV_REG_PCR_ENTRY_22_3                                                                   (0x1001aa2c)
#ifndef PV_REG_PCR_ENTRY_22_3
#define PV_REG_PCR_ENTRY_22_3                                                                       (0xa2c)
#endif
#define CLP_PV_REG_PCR_ENTRY_22_4                                                                   (0x1001aa30)
#ifndef PV_REG_PCR_ENTRY_22_4
#define PV_REG_PCR_ENTRY_22_4                                                                       (0xa30)
#endif
#define CLP_PV_REG_PCR_ENTRY_22_5                                                                   (0x1001aa34)
#ifndef PV_REG_PCR_ENTRY_22_5
#define PV_REG_PCR_ENTRY_22_5                                                                       (0xa34)
#endif
#define CLP_PV_REG_PCR_ENTRY_22_6                                                                   (0x1001aa38)
#ifndef PV_REG_PCR_ENTRY_22_6
#define PV_REG_PCR_ENTRY_22_6                                                                       (0xa38)
#endif
#define CLP_PV_REG_PCR_ENTRY_22_7                                                                   (0x1001aa3c)
#ifndef PV_REG_PCR_ENTRY_22_7
#define PV_REG_PCR_ENTRY_22_7                                                                       (0xa3c)
#endif
#define CLP_PV_REG_PCR_ENTRY_22_8                                                                   (0x1001aa40)
#ifndef PV_REG_PCR_ENTRY_22_8
#define PV_REG_PCR_ENTRY_22_8                                                                       (0xa40)
#endif
#define CLP_PV_REG_PCR_ENTRY_22_9                                                                   (0x1001aa44)
#ifndef PV_REG_PCR_ENTRY_22_9
#define PV_REG_PCR_ENTRY_22_9                                                                       (0xa44)
#endif
#define CLP_PV_REG_PCR_ENTRY_22_10                                                                  (0x1001aa48)
#ifndef PV_REG_PCR_ENTRY_22_10
#define PV_REG_PCR_ENTRY_22_10                                                                      (0xa48)
#endif
#define CLP_PV_REG_PCR_ENTRY_22_11                                                                  (0x1001aa4c)
#ifndef PV_REG_PCR_ENTRY_22_11
#define PV_REG_PCR_ENTRY_22_11                                                                      (0xa4c)
#endif
#define CLP_PV_REG_PCR_ENTRY_23_0                                                                   (0x1001aa50)
#ifndef PV_REG_PCR_ENTRY_23_0
#define PV_REG_PCR_ENTRY_23_0                                                                       (0xa50)
#endif
#define CLP_PV_REG_PCR_ENTRY_23_1                                                                   (0x1001aa54)
#ifndef PV_REG_PCR_ENTRY_23_1
#define PV_REG_PCR_ENTRY_23_1                                                                       (0xa54)
#endif
#define CLP_PV_REG_PCR_ENTRY_23_2                                                                   (0x1001aa58)
#ifndef PV_REG_PCR_ENTRY_23_2
#define PV_REG_PCR_ENTRY_23_2                                                                       (0xa58)
#endif
#define CLP_PV_REG_PCR_ENTRY_23_3                                                                   (0x1001aa5c)
#ifndef PV_REG_PCR_ENTRY_23_3
#define PV_REG_PCR_ENTRY_23_3                                                                       (0xa5c)
#endif
#define CLP_PV_REG_PCR_ENTRY_23_4                                                                   (0x1001aa60)
#ifndef PV_REG_PCR_ENTRY_23_4
#define PV_REG_PCR_ENTRY_23_4                                                                       (0xa60)
#endif
#define CLP_PV_REG_PCR_ENTRY_23_5                                                                   (0x1001aa64)
#ifndef PV_REG_PCR_ENTRY_23_5
#define PV_REG_PCR_ENTRY_23_5                                                                       (0xa64)
#endif
#define CLP_PV_REG_PCR_ENTRY_23_6                                                                   (0x1001aa68)
#ifndef PV_REG_PCR_ENTRY_23_6
#define PV_REG_PCR_ENTRY_23_6                                                                       (0xa68)
#endif
#define CLP_PV_REG_PCR_ENTRY_23_7                                                                   (0x1001aa6c)
#ifndef PV_REG_PCR_ENTRY_23_7
#define PV_REG_PCR_ENTRY_23_7                                                                       (0xa6c)
#endif
#define CLP_PV_REG_PCR_ENTRY_23_8                                                                   (0x1001aa70)
#ifndef PV_REG_PCR_ENTRY_23_8
#define PV_REG_PCR_ENTRY_23_8                                                                       (0xa70)
#endif
#define CLP_PV_REG_PCR_ENTRY_23_9                                                                   (0x1001aa74)
#ifndef PV_REG_PCR_ENTRY_23_9
#define PV_REG_PCR_ENTRY_23_9                                                                       (0xa74)
#endif
#define CLP_PV_REG_PCR_ENTRY_23_10                                                                  (0x1001aa78)
#ifndef PV_REG_PCR_ENTRY_23_10
#define PV_REG_PCR_ENTRY_23_10                                                                      (0xa78)
#endif
#define CLP_PV_REG_PCR_ENTRY_23_11                                                                  (0x1001aa7c)
#ifndef PV_REG_PCR_ENTRY_23_11
#define PV_REG_PCR_ENTRY_23_11                                                                      (0xa7c)
#endif
#define CLP_PV_REG_PCR_ENTRY_24_0                                                                   (0x1001aa80)
#ifndef PV_REG_PCR_ENTRY_24_0
#define PV_REG_PCR_ENTRY_24_0                                                                       (0xa80)
#endif
#define CLP_PV_REG_PCR_ENTRY_24_1                                                                   (0x1001aa84)
#ifndef PV_REG_PCR_ENTRY_24_1
#define PV_REG_PCR_ENTRY_24_1                                                                       (0xa84)
#endif
#define CLP_PV_REG_PCR_ENTRY_24_2                                                                   (0x1001aa88)
#ifndef PV_REG_PCR_ENTRY_24_2
#define PV_REG_PCR_ENTRY_24_2                                                                       (0xa88)
#endif
#define CLP_PV_REG_PCR_ENTRY_24_3                                                                   (0x1001aa8c)
#ifndef PV_REG_PCR_ENTRY_24_3
#define PV_REG_PCR_ENTRY_24_3                                                                       (0xa8c)
#endif
#define CLP_PV_REG_PCR_ENTRY_24_4                                                                   (0x1001aa90)
#ifndef PV_REG_PCR_ENTRY_24_4
#define PV_REG_PCR_ENTRY_24_4                                                                       (0xa90)
#endif
#define CLP_PV_REG_PCR_ENTRY_24_5                                                                   (0x1001aa94)
#ifndef PV_REG_PCR_ENTRY_24_5
#define PV_REG_PCR_ENTRY_24_5                                                                       (0xa94)
#endif
#define CLP_PV_REG_PCR_ENTRY_24_6                                                                   (0x1001aa98)
#ifndef PV_REG_PCR_ENTRY_24_6
#define PV_REG_PCR_ENTRY_24_6                                                                       (0xa98)
#endif
#define CLP_PV_REG_PCR_ENTRY_24_7                                                                   (0x1001aa9c)
#ifndef PV_REG_PCR_ENTRY_24_7
#define PV_REG_PCR_ENTRY_24_7                                                                       (0xa9c)
#endif
#define CLP_PV_REG_PCR_ENTRY_24_8                                                                   (0x1001aaa0)
#ifndef PV_REG_PCR_ENTRY_24_8
#define PV_REG_PCR_ENTRY_24_8                                                                       (0xaa0)
#endif
#define CLP_PV_REG_PCR_ENTRY_24_9                                                                   (0x1001aaa4)
#ifndef PV_REG_PCR_ENTRY_24_9
#define PV_REG_PCR_ENTRY_24_9                                                                       (0xaa4)
#endif
#define CLP_PV_REG_PCR_ENTRY_24_10                                                                  (0x1001aaa8)
#ifndef PV_REG_PCR_ENTRY_24_10
#define PV_REG_PCR_ENTRY_24_10                                                                      (0xaa8)
#endif
#define CLP_PV_REG_PCR_ENTRY_24_11                                                                  (0x1001aaac)
#ifndef PV_REG_PCR_ENTRY_24_11
#define PV_REG_PCR_ENTRY_24_11                                                                      (0xaac)
#endif
#define CLP_PV_REG_PCR_ENTRY_25_0                                                                   (0x1001aab0)
#ifndef PV_REG_PCR_ENTRY_25_0
#define PV_REG_PCR_ENTRY_25_0                                                                       (0xab0)
#endif
#define CLP_PV_REG_PCR_ENTRY_25_1                                                                   (0x1001aab4)
#ifndef PV_REG_PCR_ENTRY_25_1
#define PV_REG_PCR_ENTRY_25_1                                                                       (0xab4)
#endif
#define CLP_PV_REG_PCR_ENTRY_25_2                                                                   (0x1001aab8)
#ifndef PV_REG_PCR_ENTRY_25_2
#define PV_REG_PCR_ENTRY_25_2                                                                       (0xab8)
#endif
#define CLP_PV_REG_PCR_ENTRY_25_3                                                                   (0x1001aabc)
#ifndef PV_REG_PCR_ENTRY_25_3
#define PV_REG_PCR_ENTRY_25_3                                                                       (0xabc)
#endif
#define CLP_PV_REG_PCR_ENTRY_25_4                                                                   (0x1001aac0)
#ifndef PV_REG_PCR_ENTRY_25_4
#define PV_REG_PCR_ENTRY_25_4                                                                       (0xac0)
#endif
#define CLP_PV_REG_PCR_ENTRY_25_5                                                                   (0x1001aac4)
#ifndef PV_REG_PCR_ENTRY_25_5
#define PV_REG_PCR_ENTRY_25_5                                                                       (0xac4)
#endif
#define CLP_PV_REG_PCR_ENTRY_25_6                                                                   (0x1001aac8)
#ifndef PV_REG_PCR_ENTRY_25_6
#define PV_REG_PCR_ENTRY_25_6                                                                       (0xac8)
#endif
#define CLP_PV_REG_PCR_ENTRY_25_7                                                                   (0x1001aacc)
#ifndef PV_REG_PCR_ENTRY_25_7
#define PV_REG_PCR_ENTRY_25_7                                                                       (0xacc)
#endif
#define CLP_PV_REG_PCR_ENTRY_25_8                                                                   (0x1001aad0)
#ifndef PV_REG_PCR_ENTRY_25_8
#define PV_REG_PCR_ENTRY_25_8                                                                       (0xad0)
#endif
#define CLP_PV_REG_PCR_ENTRY_25_9                                                                   (0x1001aad4)
#ifndef PV_REG_PCR_ENTRY_25_9
#define PV_REG_PCR_ENTRY_25_9                                                                       (0xad4)
#endif
#define CLP_PV_REG_PCR_ENTRY_25_10                                                                  (0x1001aad8)
#ifndef PV_REG_PCR_ENTRY_25_10
#define PV_REG_PCR_ENTRY_25_10                                                                      (0xad8)
#endif
#define CLP_PV_REG_PCR_ENTRY_25_11                                                                  (0x1001aadc)
#ifndef PV_REG_PCR_ENTRY_25_11
#define PV_REG_PCR_ENTRY_25_11                                                                      (0xadc)
#endif
#define CLP_PV_REG_PCR_ENTRY_26_0                                                                   (0x1001aae0)
#ifndef PV_REG_PCR_ENTRY_26_0
#define PV_REG_PCR_ENTRY_26_0                                                                       (0xae0)
#endif
#define CLP_PV_REG_PCR_ENTRY_26_1                                                                   (0x1001aae4)
#ifndef PV_REG_PCR_ENTRY_26_1
#define PV_REG_PCR_ENTRY_26_1                                                                       (0xae4)
#endif
#define CLP_PV_REG_PCR_ENTRY_26_2                                                                   (0x1001aae8)
#ifndef PV_REG_PCR_ENTRY_26_2
#define PV_REG_PCR_ENTRY_26_2                                                                       (0xae8)
#endif
#define CLP_PV_REG_PCR_ENTRY_26_3                                                                   (0x1001aaec)
#ifndef PV_REG_PCR_ENTRY_26_3
#define PV_REG_PCR_ENTRY_26_3                                                                       (0xaec)
#endif
#define CLP_PV_REG_PCR_ENTRY_26_4                                                                   (0x1001aaf0)
#ifndef PV_REG_PCR_ENTRY_26_4
#define PV_REG_PCR_ENTRY_26_4                                                                       (0xaf0)
#endif
#define CLP_PV_REG_PCR_ENTRY_26_5                                                                   (0x1001aaf4)
#ifndef PV_REG_PCR_ENTRY_26_5
#define PV_REG_PCR_ENTRY_26_5                                                                       (0xaf4)
#endif
#define CLP_PV_REG_PCR_ENTRY_26_6                                                                   (0x1001aaf8)
#ifndef PV_REG_PCR_ENTRY_26_6
#define PV_REG_PCR_ENTRY_26_6                                                                       (0xaf8)
#endif
#define CLP_PV_REG_PCR_ENTRY_26_7                                                                   (0x1001aafc)
#ifndef PV_REG_PCR_ENTRY_26_7
#define PV_REG_PCR_ENTRY_26_7                                                                       (0xafc)
#endif
#define CLP_PV_REG_PCR_ENTRY_26_8                                                                   (0x1001ab00)
#ifndef PV_REG_PCR_ENTRY_26_8
#define PV_REG_PCR_ENTRY_26_8                                                                       (0xb00)
#endif
#define CLP_PV_REG_PCR_ENTRY_26_9                                                                   (0x1001ab04)
#ifndef PV_REG_PCR_ENTRY_26_9
#define PV_REG_PCR_ENTRY_26_9                                                                       (0xb04)
#endif
#define CLP_PV_REG_PCR_ENTRY_26_10                                                                  (0x1001ab08)
#ifndef PV_REG_PCR_ENTRY_26_10
#define PV_REG_PCR_ENTRY_26_10                                                                      (0xb08)
#endif
#define CLP_PV_REG_PCR_ENTRY_26_11                                                                  (0x1001ab0c)
#ifndef PV_REG_PCR_ENTRY_26_11
#define PV_REG_PCR_ENTRY_26_11                                                                      (0xb0c)
#endif
#define CLP_PV_REG_PCR_ENTRY_27_0                                                                   (0x1001ab10)
#ifndef PV_REG_PCR_ENTRY_27_0
#define PV_REG_PCR_ENTRY_27_0                                                                       (0xb10)
#endif
#define CLP_PV_REG_PCR_ENTRY_27_1                                                                   (0x1001ab14)
#ifndef PV_REG_PCR_ENTRY_27_1
#define PV_REG_PCR_ENTRY_27_1                                                                       (0xb14)
#endif
#define CLP_PV_REG_PCR_ENTRY_27_2                                                                   (0x1001ab18)
#ifndef PV_REG_PCR_ENTRY_27_2
#define PV_REG_PCR_ENTRY_27_2                                                                       (0xb18)
#endif
#define CLP_PV_REG_PCR_ENTRY_27_3                                                                   (0x1001ab1c)
#ifndef PV_REG_PCR_ENTRY_27_3
#define PV_REG_PCR_ENTRY_27_3                                                                       (0xb1c)
#endif
#define CLP_PV_REG_PCR_ENTRY_27_4                                                                   (0x1001ab20)
#ifndef PV_REG_PCR_ENTRY_27_4
#define PV_REG_PCR_ENTRY_27_4                                                                       (0xb20)
#endif
#define CLP_PV_REG_PCR_ENTRY_27_5                                                                   (0x1001ab24)
#ifndef PV_REG_PCR_ENTRY_27_5
#define PV_REG_PCR_ENTRY_27_5                                                                       (0xb24)
#endif
#define CLP_PV_REG_PCR_ENTRY_27_6                                                                   (0x1001ab28)
#ifndef PV_REG_PCR_ENTRY_27_6
#define PV_REG_PCR_ENTRY_27_6                                                                       (0xb28)
#endif
#define CLP_PV_REG_PCR_ENTRY_27_7                                                                   (0x1001ab2c)
#ifndef PV_REG_PCR_ENTRY_27_7
#define PV_REG_PCR_ENTRY_27_7                                                                       (0xb2c)
#endif
#define CLP_PV_REG_PCR_ENTRY_27_8                                                                   (0x1001ab30)
#ifndef PV_REG_PCR_ENTRY_27_8
#define PV_REG_PCR_ENTRY_27_8                                                                       (0xb30)
#endif
#define CLP_PV_REG_PCR_ENTRY_27_9                                                                   (0x1001ab34)
#ifndef PV_REG_PCR_ENTRY_27_9
#define PV_REG_PCR_ENTRY_27_9                                                                       (0xb34)
#endif
#define CLP_PV_REG_PCR_ENTRY_27_10                                                                  (0x1001ab38)
#ifndef PV_REG_PCR_ENTRY_27_10
#define PV_REG_PCR_ENTRY_27_10                                                                      (0xb38)
#endif
#define CLP_PV_REG_PCR_ENTRY_27_11                                                                  (0x1001ab3c)
#ifndef PV_REG_PCR_ENTRY_27_11
#define PV_REG_PCR_ENTRY_27_11                                                                      (0xb3c)
#endif
#define CLP_PV_REG_PCR_ENTRY_28_0                                                                   (0x1001ab40)
#ifndef PV_REG_PCR_ENTRY_28_0
#define PV_REG_PCR_ENTRY_28_0                                                                       (0xb40)
#endif
#define CLP_PV_REG_PCR_ENTRY_28_1                                                                   (0x1001ab44)
#ifndef PV_REG_PCR_ENTRY_28_1
#define PV_REG_PCR_ENTRY_28_1                                                                       (0xb44)
#endif
#define CLP_PV_REG_PCR_ENTRY_28_2                                                                   (0x1001ab48)
#ifndef PV_REG_PCR_ENTRY_28_2
#define PV_REG_PCR_ENTRY_28_2                                                                       (0xb48)
#endif
#define CLP_PV_REG_PCR_ENTRY_28_3                                                                   (0x1001ab4c)
#ifndef PV_REG_PCR_ENTRY_28_3
#define PV_REG_PCR_ENTRY_28_3                                                                       (0xb4c)
#endif
#define CLP_PV_REG_PCR_ENTRY_28_4                                                                   (0x1001ab50)
#ifndef PV_REG_PCR_ENTRY_28_4
#define PV_REG_PCR_ENTRY_28_4                                                                       (0xb50)
#endif
#define CLP_PV_REG_PCR_ENTRY_28_5                                                                   (0x1001ab54)
#ifndef PV_REG_PCR_ENTRY_28_5
#define PV_REG_PCR_ENTRY_28_5                                                                       (0xb54)
#endif
#define CLP_PV_REG_PCR_ENTRY_28_6                                                                   (0x1001ab58)
#ifndef PV_REG_PCR_ENTRY_28_6
#define PV_REG_PCR_ENTRY_28_6                                                                       (0xb58)
#endif
#define CLP_PV_REG_PCR_ENTRY_28_7                                                                   (0x1001ab5c)
#ifndef PV_REG_PCR_ENTRY_28_7
#define PV_REG_PCR_ENTRY_28_7                                                                       (0xb5c)
#endif
#define CLP_PV_REG_PCR_ENTRY_28_8                                                                   (0x1001ab60)
#ifndef PV_REG_PCR_ENTRY_28_8
#define PV_REG_PCR_ENTRY_28_8                                                                       (0xb60)
#endif
#define CLP_PV_REG_PCR_ENTRY_28_9                                                                   (0x1001ab64)
#ifndef PV_REG_PCR_ENTRY_28_9
#define PV_REG_PCR_ENTRY_28_9                                                                       (0xb64)
#endif
#define CLP_PV_REG_PCR_ENTRY_28_10                                                                  (0x1001ab68)
#ifndef PV_REG_PCR_ENTRY_28_10
#define PV_REG_PCR_ENTRY_28_10                                                                      (0xb68)
#endif
#define CLP_PV_REG_PCR_ENTRY_28_11                                                                  (0x1001ab6c)
#ifndef PV_REG_PCR_ENTRY_28_11
#define PV_REG_PCR_ENTRY_28_11                                                                      (0xb6c)
#endif
#define CLP_PV_REG_PCR_ENTRY_29_0                                                                   (0x1001ab70)
#ifndef PV_REG_PCR_ENTRY_29_0
#define PV_REG_PCR_ENTRY_29_0                                                                       (0xb70)
#endif
#define CLP_PV_REG_PCR_ENTRY_29_1                                                                   (0x1001ab74)
#ifndef PV_REG_PCR_ENTRY_29_1
#define PV_REG_PCR_ENTRY_29_1                                                                       (0xb74)
#endif
#define CLP_PV_REG_PCR_ENTRY_29_2                                                                   (0x1001ab78)
#ifndef PV_REG_PCR_ENTRY_29_2
#define PV_REG_PCR_ENTRY_29_2                                                                       (0xb78)
#endif
#define CLP_PV_REG_PCR_ENTRY_29_3                                                                   (0x1001ab7c)
#ifndef PV_REG_PCR_ENTRY_29_3
#define PV_REG_PCR_ENTRY_29_3                                                                       (0xb7c)
#endif
#define CLP_PV_REG_PCR_ENTRY_29_4                                                                   (0x1001ab80)
#ifndef PV_REG_PCR_ENTRY_29_4
#define PV_REG_PCR_ENTRY_29_4                                                                       (0xb80)
#endif
#define CLP_PV_REG_PCR_ENTRY_29_5                                                                   (0x1001ab84)
#ifndef PV_REG_PCR_ENTRY_29_5
#define PV_REG_PCR_ENTRY_29_5                                                                       (0xb84)
#endif
#define CLP_PV_REG_PCR_ENTRY_29_6                                                                   (0x1001ab88)
#ifndef PV_REG_PCR_ENTRY_29_6
#define PV_REG_PCR_ENTRY_29_6                                                                       (0xb88)
#endif
#define CLP_PV_REG_PCR_ENTRY_29_7                                                                   (0x1001ab8c)
#ifndef PV_REG_PCR_ENTRY_29_7
#define PV_REG_PCR_ENTRY_29_7                                                                       (0xb8c)
#endif
#define CLP_PV_REG_PCR_ENTRY_29_8                                                                   (0x1001ab90)
#ifndef PV_REG_PCR_ENTRY_29_8
#define PV_REG_PCR_ENTRY_29_8                                                                       (0xb90)
#endif
#define CLP_PV_REG_PCR_ENTRY_29_9                                                                   (0x1001ab94)
#ifndef PV_REG_PCR_ENTRY_29_9
#define PV_REG_PCR_ENTRY_29_9                                                                       (0xb94)
#endif
#define CLP_PV_REG_PCR_ENTRY_29_10                                                                  (0x1001ab98)
#ifndef PV_REG_PCR_ENTRY_29_10
#define PV_REG_PCR_ENTRY_29_10                                                                      (0xb98)
#endif
#define CLP_PV_REG_PCR_ENTRY_29_11                                                                  (0x1001ab9c)
#ifndef PV_REG_PCR_ENTRY_29_11
#define PV_REG_PCR_ENTRY_29_11                                                                      (0xb9c)
#endif
#define CLP_PV_REG_PCR_ENTRY_30_0                                                                   (0x1001aba0)
#ifndef PV_REG_PCR_ENTRY_30_0
#define PV_REG_PCR_ENTRY_30_0                                                                       (0xba0)
#endif
#define CLP_PV_REG_PCR_ENTRY_30_1                                                                   (0x1001aba4)
#ifndef PV_REG_PCR_ENTRY_30_1
#define PV_REG_PCR_ENTRY_30_1                                                                       (0xba4)
#endif
#define CLP_PV_REG_PCR_ENTRY_30_2                                                                   (0x1001aba8)
#ifndef PV_REG_PCR_ENTRY_30_2
#define PV_REG_PCR_ENTRY_30_2                                                                       (0xba8)
#endif
#define CLP_PV_REG_PCR_ENTRY_30_3                                                                   (0x1001abac)
#ifndef PV_REG_PCR_ENTRY_30_3
#define PV_REG_PCR_ENTRY_30_3                                                                       (0xbac)
#endif
#define CLP_PV_REG_PCR_ENTRY_30_4                                                                   (0x1001abb0)
#ifndef PV_REG_PCR_ENTRY_30_4
#define PV_REG_PCR_ENTRY_30_4                                                                       (0xbb0)
#endif
#define CLP_PV_REG_PCR_ENTRY_30_5                                                                   (0x1001abb4)
#ifndef PV_REG_PCR_ENTRY_30_5
#define PV_REG_PCR_ENTRY_30_5                                                                       (0xbb4)
#endif
#define CLP_PV_REG_PCR_ENTRY_30_6                                                                   (0x1001abb8)
#ifndef PV_REG_PCR_ENTRY_30_6
#define PV_REG_PCR_ENTRY_30_6                                                                       (0xbb8)
#endif
#define CLP_PV_REG_PCR_ENTRY_30_7                                                                   (0x1001abbc)
#ifndef PV_REG_PCR_ENTRY_30_7
#define PV_REG_PCR_ENTRY_30_7                                                                       (0xbbc)
#endif
#define CLP_PV_REG_PCR_ENTRY_30_8                                                                   (0x1001abc0)
#ifndef PV_REG_PCR_ENTRY_30_8
#define PV_REG_PCR_ENTRY_30_8                                                                       (0xbc0)
#endif
#define CLP_PV_REG_PCR_ENTRY_30_9                                                                   (0x1001abc4)
#ifndef PV_REG_PCR_ENTRY_30_9
#define PV_REG_PCR_ENTRY_30_9                                                                       (0xbc4)
#endif
#define CLP_PV_REG_PCR_ENTRY_30_10                                                                  (0x1001abc8)
#ifndef PV_REG_PCR_ENTRY_30_10
#define PV_REG_PCR_ENTRY_30_10                                                                      (0xbc8)
#endif
#define CLP_PV_REG_PCR_ENTRY_30_11                                                                  (0x1001abcc)
#ifndef PV_REG_PCR_ENTRY_30_11
#define PV_REG_PCR_ENTRY_30_11                                                                      (0xbcc)
#endif
#define CLP_PV_REG_PCR_ENTRY_31_0                                                                   (0x1001abd0)
#ifndef PV_REG_PCR_ENTRY_31_0
#define PV_REG_PCR_ENTRY_31_0                                                                       (0xbd0)
#endif
#define CLP_PV_REG_PCR_ENTRY_31_1                                                                   (0x1001abd4)
#ifndef PV_REG_PCR_ENTRY_31_1
#define PV_REG_PCR_ENTRY_31_1                                                                       (0xbd4)
#endif
#define CLP_PV_REG_PCR_ENTRY_31_2                                                                   (0x1001abd8)
#ifndef PV_REG_PCR_ENTRY_31_2
#define PV_REG_PCR_ENTRY_31_2                                                                       (0xbd8)
#endif
#define CLP_PV_REG_PCR_ENTRY_31_3                                                                   (0x1001abdc)
#ifndef PV_REG_PCR_ENTRY_31_3
#define PV_REG_PCR_ENTRY_31_3                                                                       (0xbdc)
#endif
#define CLP_PV_REG_PCR_ENTRY_31_4                                                                   (0x1001abe0)
#ifndef PV_REG_PCR_ENTRY_31_4
#define PV_REG_PCR_ENTRY_31_4                                                                       (0xbe0)
#endif
#define CLP_PV_REG_PCR_ENTRY_31_5                                                                   (0x1001abe4)
#ifndef PV_REG_PCR_ENTRY_31_5
#define PV_REG_PCR_ENTRY_31_5                                                                       (0xbe4)
#endif
#define CLP_PV_REG_PCR_ENTRY_31_6                                                                   (0x1001abe8)
#ifndef PV_REG_PCR_ENTRY_31_6
#define PV_REG_PCR_ENTRY_31_6                                                                       (0xbe8)
#endif
#define CLP_PV_REG_PCR_ENTRY_31_7                                                                   (0x1001abec)
#ifndef PV_REG_PCR_ENTRY_31_7
#define PV_REG_PCR_ENTRY_31_7                                                                       (0xbec)
#endif
#define CLP_PV_REG_PCR_ENTRY_31_8                                                                   (0x1001abf0)
#ifndef PV_REG_PCR_ENTRY_31_8
#define PV_REG_PCR_ENTRY_31_8                                                                       (0xbf0)
#endif
#define CLP_PV_REG_PCR_ENTRY_31_9                                                                   (0x1001abf4)
#ifndef PV_REG_PCR_ENTRY_31_9
#define PV_REG_PCR_ENTRY_31_9                                                                       (0xbf4)
#endif
#define CLP_PV_REG_PCR_ENTRY_31_10                                                                  (0x1001abf8)
#ifndef PV_REG_PCR_ENTRY_31_10
#define PV_REG_PCR_ENTRY_31_10                                                                      (0xbf8)
#endif
#define CLP_PV_REG_PCR_ENTRY_31_11                                                                  (0x1001abfc)
#ifndef PV_REG_PCR_ENTRY_31_11
#define PV_REG_PCR_ENTRY_31_11                                                                      (0xbfc)
#endif
#define CLP_DV_REG_BASE_ADDR                                                                        (0x1001c000)
#define CLP_DV_REG_STICKYDATAVAULTCTRL_0                                                            (0x1001c000)
#ifndef DV_REG_STICKYDATAVAULTCTRL_0
#define DV_REG_STICKYDATAVAULTCTRL_0                                                                (0x0)
#define DV_REG_STICKYDATAVAULTCTRL_0_LOCK_ENTRY_LOW                                                 (0)
#define DV_REG_STICKYDATAVAULTCTRL_0_LOCK_ENTRY_MASK                                                (0x1)
#endif
#define CLP_DV_REG_STICKYDATAVAULTCTRL_1                                                            (0x1001c004)
#ifndef DV_REG_STICKYDATAVAULTCTRL_1
#define DV_REG_STICKYDATAVAULTCTRL_1                                                                (0x4)
#define DV_REG_STICKYDATAVAULTCTRL_1_LOCK_ENTRY_LOW                                                 (0)
#define DV_REG_STICKYDATAVAULTCTRL_1_LOCK_ENTRY_MASK                                                (0x1)
#endif
#define CLP_DV_REG_STICKYDATAVAULTCTRL_2                                                            (0x1001c008)
#ifndef DV_REG_STICKYDATAVAULTCTRL_2
#define DV_REG_STICKYDATAVAULTCTRL_2                                                                (0x8)
#define DV_REG_STICKYDATAVAULTCTRL_2_LOCK_ENTRY_LOW                                                 (0)
#define DV_REG_STICKYDATAVAULTCTRL_2_LOCK_ENTRY_MASK                                                (0x1)
#endif
#define CLP_DV_REG_STICKYDATAVAULTCTRL_3                                                            (0x1001c00c)
#ifndef DV_REG_STICKYDATAVAULTCTRL_3
#define DV_REG_STICKYDATAVAULTCTRL_3                                                                (0xc)
#define DV_REG_STICKYDATAVAULTCTRL_3_LOCK_ENTRY_LOW                                                 (0)
#define DV_REG_STICKYDATAVAULTCTRL_3_LOCK_ENTRY_MASK                                                (0x1)
#endif
#define CLP_DV_REG_STICKYDATAVAULTCTRL_4                                                            (0x1001c010)
#ifndef DV_REG_STICKYDATAVAULTCTRL_4
#define DV_REG_STICKYDATAVAULTCTRL_4                                                                (0x10)
#define DV_REG_STICKYDATAVAULTCTRL_4_LOCK_ENTRY_LOW                                                 (0)
#define DV_REG_STICKYDATAVAULTCTRL_4_LOCK_ENTRY_MASK                                                (0x1)
#endif
#define CLP_DV_REG_STICKYDATAVAULTCTRL_5                                                            (0x1001c014)
#ifndef DV_REG_STICKYDATAVAULTCTRL_5
#define DV_REG_STICKYDATAVAULTCTRL_5                                                                (0x14)
#define DV_REG_STICKYDATAVAULTCTRL_5_LOCK_ENTRY_LOW                                                 (0)
#define DV_REG_STICKYDATAVAULTCTRL_5_LOCK_ENTRY_MASK                                                (0x1)
#endif
#define CLP_DV_REG_STICKYDATAVAULTCTRL_6                                                            (0x1001c018)
#ifndef DV_REG_STICKYDATAVAULTCTRL_6
#define DV_REG_STICKYDATAVAULTCTRL_6                                                                (0x18)
#define DV_REG_STICKYDATAVAULTCTRL_6_LOCK_ENTRY_LOW                                                 (0)
#define DV_REG_STICKYDATAVAULTCTRL_6_LOCK_ENTRY_MASK                                                (0x1)
#endif
#define CLP_DV_REG_STICKYDATAVAULTCTRL_7                                                            (0x1001c01c)
#ifndef DV_REG_STICKYDATAVAULTCTRL_7
#define DV_REG_STICKYDATAVAULTCTRL_7                                                                (0x1c)
#define DV_REG_STICKYDATAVAULTCTRL_7_LOCK_ENTRY_LOW                                                 (0)
#define DV_REG_STICKYDATAVAULTCTRL_7_LOCK_ENTRY_MASK                                                (0x1)
#endif
#define CLP_DV_REG_STICKYDATAVAULTCTRL_8                                                            (0x1001c020)
#ifndef DV_REG_STICKYDATAVAULTCTRL_8
#define DV_REG_STICKYDATAVAULTCTRL_8                                                                (0x20)
#define DV_REG_STICKYDATAVAULTCTRL_8_LOCK_ENTRY_LOW                                                 (0)
#define DV_REG_STICKYDATAVAULTCTRL_8_LOCK_ENTRY_MASK                                                (0x1)
#endif
#define CLP_DV_REG_STICKYDATAVAULTCTRL_9                                                            (0x1001c024)
#ifndef DV_REG_STICKYDATAVAULTCTRL_9
#define DV_REG_STICKYDATAVAULTCTRL_9                                                                (0x24)
#define DV_REG_STICKYDATAVAULTCTRL_9_LOCK_ENTRY_LOW                                                 (0)
#define DV_REG_STICKYDATAVAULTCTRL_9_LOCK_ENTRY_MASK                                                (0x1)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_0_0                                                      (0x1001c028)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_0_0
#define DV_REG_STICKY_DATA_VAULT_ENTRY_0_0                                                          (0x28)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_0_1                                                      (0x1001c02c)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_0_1
#define DV_REG_STICKY_DATA_VAULT_ENTRY_0_1                                                          (0x2c)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_0_2                                                      (0x1001c030)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_0_2
#define DV_REG_STICKY_DATA_VAULT_ENTRY_0_2                                                          (0x30)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_0_3                                                      (0x1001c034)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_0_3
#define DV_REG_STICKY_DATA_VAULT_ENTRY_0_3                                                          (0x34)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_0_4                                                      (0x1001c038)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_0_4
#define DV_REG_STICKY_DATA_VAULT_ENTRY_0_4                                                          (0x38)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_0_5                                                      (0x1001c03c)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_0_5
#define DV_REG_STICKY_DATA_VAULT_ENTRY_0_5                                                          (0x3c)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_0_6                                                      (0x1001c040)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_0_6
#define DV_REG_STICKY_DATA_VAULT_ENTRY_0_6                                                          (0x40)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_0_7                                                      (0x1001c044)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_0_7
#define DV_REG_STICKY_DATA_VAULT_ENTRY_0_7                                                          (0x44)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_0_8                                                      (0x1001c048)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_0_8
#define DV_REG_STICKY_DATA_VAULT_ENTRY_0_8                                                          (0x48)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_0_9                                                      (0x1001c04c)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_0_9
#define DV_REG_STICKY_DATA_VAULT_ENTRY_0_9                                                          (0x4c)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_0_10                                                     (0x1001c050)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_0_10
#define DV_REG_STICKY_DATA_VAULT_ENTRY_0_10                                                         (0x50)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_0_11                                                     (0x1001c054)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_0_11
#define DV_REG_STICKY_DATA_VAULT_ENTRY_0_11                                                         (0x54)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_1_0                                                      (0x1001c058)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_1_0
#define DV_REG_STICKY_DATA_VAULT_ENTRY_1_0                                                          (0x58)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_1_1                                                      (0x1001c05c)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_1_1
#define DV_REG_STICKY_DATA_VAULT_ENTRY_1_1                                                          (0x5c)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_1_2                                                      (0x1001c060)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_1_2
#define DV_REG_STICKY_DATA_VAULT_ENTRY_1_2                                                          (0x60)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_1_3                                                      (0x1001c064)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_1_3
#define DV_REG_STICKY_DATA_VAULT_ENTRY_1_3                                                          (0x64)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_1_4                                                      (0x1001c068)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_1_4
#define DV_REG_STICKY_DATA_VAULT_ENTRY_1_4                                                          (0x68)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_1_5                                                      (0x1001c06c)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_1_5
#define DV_REG_STICKY_DATA_VAULT_ENTRY_1_5                                                          (0x6c)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_1_6                                                      (0x1001c070)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_1_6
#define DV_REG_STICKY_DATA_VAULT_ENTRY_1_6                                                          (0x70)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_1_7                                                      (0x1001c074)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_1_7
#define DV_REG_STICKY_DATA_VAULT_ENTRY_1_7                                                          (0x74)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_1_8                                                      (0x1001c078)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_1_8
#define DV_REG_STICKY_DATA_VAULT_ENTRY_1_8                                                          (0x78)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_1_9                                                      (0x1001c07c)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_1_9
#define DV_REG_STICKY_DATA_VAULT_ENTRY_1_9                                                          (0x7c)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_1_10                                                     (0x1001c080)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_1_10
#define DV_REG_STICKY_DATA_VAULT_ENTRY_1_10                                                         (0x80)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_1_11                                                     (0x1001c084)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_1_11
#define DV_REG_STICKY_DATA_VAULT_ENTRY_1_11                                                         (0x84)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_2_0                                                      (0x1001c088)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_2_0
#define DV_REG_STICKY_DATA_VAULT_ENTRY_2_0                                                          (0x88)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_2_1                                                      (0x1001c08c)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_2_1
#define DV_REG_STICKY_DATA_VAULT_ENTRY_2_1                                                          (0x8c)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_2_2                                                      (0x1001c090)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_2_2
#define DV_REG_STICKY_DATA_VAULT_ENTRY_2_2                                                          (0x90)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_2_3                                                      (0x1001c094)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_2_3
#define DV_REG_STICKY_DATA_VAULT_ENTRY_2_3                                                          (0x94)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_2_4                                                      (0x1001c098)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_2_4
#define DV_REG_STICKY_DATA_VAULT_ENTRY_2_4                                                          (0x98)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_2_5                                                      (0x1001c09c)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_2_5
#define DV_REG_STICKY_DATA_VAULT_ENTRY_2_5                                                          (0x9c)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_2_6                                                      (0x1001c0a0)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_2_6
#define DV_REG_STICKY_DATA_VAULT_ENTRY_2_6                                                          (0xa0)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_2_7                                                      (0x1001c0a4)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_2_7
#define DV_REG_STICKY_DATA_VAULT_ENTRY_2_7                                                          (0xa4)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_2_8                                                      (0x1001c0a8)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_2_8
#define DV_REG_STICKY_DATA_VAULT_ENTRY_2_8                                                          (0xa8)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_2_9                                                      (0x1001c0ac)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_2_9
#define DV_REG_STICKY_DATA_VAULT_ENTRY_2_9                                                          (0xac)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_2_10                                                     (0x1001c0b0)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_2_10
#define DV_REG_STICKY_DATA_VAULT_ENTRY_2_10                                                         (0xb0)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_2_11                                                     (0x1001c0b4)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_2_11
#define DV_REG_STICKY_DATA_VAULT_ENTRY_2_11                                                         (0xb4)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_3_0                                                      (0x1001c0b8)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_3_0
#define DV_REG_STICKY_DATA_VAULT_ENTRY_3_0                                                          (0xb8)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_3_1                                                      (0x1001c0bc)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_3_1
#define DV_REG_STICKY_DATA_VAULT_ENTRY_3_1                                                          (0xbc)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_3_2                                                      (0x1001c0c0)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_3_2
#define DV_REG_STICKY_DATA_VAULT_ENTRY_3_2                                                          (0xc0)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_3_3                                                      (0x1001c0c4)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_3_3
#define DV_REG_STICKY_DATA_VAULT_ENTRY_3_3                                                          (0xc4)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_3_4                                                      (0x1001c0c8)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_3_4
#define DV_REG_STICKY_DATA_VAULT_ENTRY_3_4                                                          (0xc8)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_3_5                                                      (0x1001c0cc)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_3_5
#define DV_REG_STICKY_DATA_VAULT_ENTRY_3_5                                                          (0xcc)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_3_6                                                      (0x1001c0d0)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_3_6
#define DV_REG_STICKY_DATA_VAULT_ENTRY_3_6                                                          (0xd0)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_3_7                                                      (0x1001c0d4)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_3_7
#define DV_REG_STICKY_DATA_VAULT_ENTRY_3_7                                                          (0xd4)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_3_8                                                      (0x1001c0d8)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_3_8
#define DV_REG_STICKY_DATA_VAULT_ENTRY_3_8                                                          (0xd8)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_3_9                                                      (0x1001c0dc)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_3_9
#define DV_REG_STICKY_DATA_VAULT_ENTRY_3_9                                                          (0xdc)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_3_10                                                     (0x1001c0e0)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_3_10
#define DV_REG_STICKY_DATA_VAULT_ENTRY_3_10                                                         (0xe0)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_3_11                                                     (0x1001c0e4)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_3_11
#define DV_REG_STICKY_DATA_VAULT_ENTRY_3_11                                                         (0xe4)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_4_0                                                      (0x1001c0e8)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_4_0
#define DV_REG_STICKY_DATA_VAULT_ENTRY_4_0                                                          (0xe8)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_4_1                                                      (0x1001c0ec)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_4_1
#define DV_REG_STICKY_DATA_VAULT_ENTRY_4_1                                                          (0xec)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_4_2                                                      (0x1001c0f0)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_4_2
#define DV_REG_STICKY_DATA_VAULT_ENTRY_4_2                                                          (0xf0)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_4_3                                                      (0x1001c0f4)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_4_3
#define DV_REG_STICKY_DATA_VAULT_ENTRY_4_3                                                          (0xf4)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_4_4                                                      (0x1001c0f8)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_4_4
#define DV_REG_STICKY_DATA_VAULT_ENTRY_4_4                                                          (0xf8)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_4_5                                                      (0x1001c0fc)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_4_5
#define DV_REG_STICKY_DATA_VAULT_ENTRY_4_5                                                          (0xfc)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_4_6                                                      (0x1001c100)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_4_6
#define DV_REG_STICKY_DATA_VAULT_ENTRY_4_6                                                          (0x100)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_4_7                                                      (0x1001c104)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_4_7
#define DV_REG_STICKY_DATA_VAULT_ENTRY_4_7                                                          (0x104)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_4_8                                                      (0x1001c108)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_4_8
#define DV_REG_STICKY_DATA_VAULT_ENTRY_4_8                                                          (0x108)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_4_9                                                      (0x1001c10c)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_4_9
#define DV_REG_STICKY_DATA_VAULT_ENTRY_4_9                                                          (0x10c)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_4_10                                                     (0x1001c110)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_4_10
#define DV_REG_STICKY_DATA_VAULT_ENTRY_4_10                                                         (0x110)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_4_11                                                     (0x1001c114)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_4_11
#define DV_REG_STICKY_DATA_VAULT_ENTRY_4_11                                                         (0x114)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_5_0                                                      (0x1001c118)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_5_0
#define DV_REG_STICKY_DATA_VAULT_ENTRY_5_0                                                          (0x118)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_5_1                                                      (0x1001c11c)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_5_1
#define DV_REG_STICKY_DATA_VAULT_ENTRY_5_1                                                          (0x11c)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_5_2                                                      (0x1001c120)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_5_2
#define DV_REG_STICKY_DATA_VAULT_ENTRY_5_2                                                          (0x120)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_5_3                                                      (0x1001c124)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_5_3
#define DV_REG_STICKY_DATA_VAULT_ENTRY_5_3                                                          (0x124)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_5_4                                                      (0x1001c128)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_5_4
#define DV_REG_STICKY_DATA_VAULT_ENTRY_5_4                                                          (0x128)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_5_5                                                      (0x1001c12c)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_5_5
#define DV_REG_STICKY_DATA_VAULT_ENTRY_5_5                                                          (0x12c)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_5_6                                                      (0x1001c130)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_5_6
#define DV_REG_STICKY_DATA_VAULT_ENTRY_5_6                                                          (0x130)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_5_7                                                      (0x1001c134)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_5_7
#define DV_REG_STICKY_DATA_VAULT_ENTRY_5_7                                                          (0x134)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_5_8                                                      (0x1001c138)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_5_8
#define DV_REG_STICKY_DATA_VAULT_ENTRY_5_8                                                          (0x138)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_5_9                                                      (0x1001c13c)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_5_9
#define DV_REG_STICKY_DATA_VAULT_ENTRY_5_9                                                          (0x13c)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_5_10                                                     (0x1001c140)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_5_10
#define DV_REG_STICKY_DATA_VAULT_ENTRY_5_10                                                         (0x140)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_5_11                                                     (0x1001c144)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_5_11
#define DV_REG_STICKY_DATA_VAULT_ENTRY_5_11                                                         (0x144)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_6_0                                                      (0x1001c148)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_6_0
#define DV_REG_STICKY_DATA_VAULT_ENTRY_6_0                                                          (0x148)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_6_1                                                      (0x1001c14c)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_6_1
#define DV_REG_STICKY_DATA_VAULT_ENTRY_6_1                                                          (0x14c)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_6_2                                                      (0x1001c150)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_6_2
#define DV_REG_STICKY_DATA_VAULT_ENTRY_6_2                                                          (0x150)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_6_3                                                      (0x1001c154)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_6_3
#define DV_REG_STICKY_DATA_VAULT_ENTRY_6_3                                                          (0x154)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_6_4                                                      (0x1001c158)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_6_4
#define DV_REG_STICKY_DATA_VAULT_ENTRY_6_4                                                          (0x158)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_6_5                                                      (0x1001c15c)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_6_5
#define DV_REG_STICKY_DATA_VAULT_ENTRY_6_5                                                          (0x15c)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_6_6                                                      (0x1001c160)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_6_6
#define DV_REG_STICKY_DATA_VAULT_ENTRY_6_6                                                          (0x160)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_6_7                                                      (0x1001c164)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_6_7
#define DV_REG_STICKY_DATA_VAULT_ENTRY_6_7                                                          (0x164)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_6_8                                                      (0x1001c168)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_6_8
#define DV_REG_STICKY_DATA_VAULT_ENTRY_6_8                                                          (0x168)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_6_9                                                      (0x1001c16c)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_6_9
#define DV_REG_STICKY_DATA_VAULT_ENTRY_6_9                                                          (0x16c)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_6_10                                                     (0x1001c170)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_6_10
#define DV_REG_STICKY_DATA_VAULT_ENTRY_6_10                                                         (0x170)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_6_11                                                     (0x1001c174)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_6_11
#define DV_REG_STICKY_DATA_VAULT_ENTRY_6_11                                                         (0x174)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_7_0                                                      (0x1001c178)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_7_0
#define DV_REG_STICKY_DATA_VAULT_ENTRY_7_0                                                          (0x178)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_7_1                                                      (0x1001c17c)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_7_1
#define DV_REG_STICKY_DATA_VAULT_ENTRY_7_1                                                          (0x17c)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_7_2                                                      (0x1001c180)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_7_2
#define DV_REG_STICKY_DATA_VAULT_ENTRY_7_2                                                          (0x180)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_7_3                                                      (0x1001c184)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_7_3
#define DV_REG_STICKY_DATA_VAULT_ENTRY_7_3                                                          (0x184)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_7_4                                                      (0x1001c188)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_7_4
#define DV_REG_STICKY_DATA_VAULT_ENTRY_7_4                                                          (0x188)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_7_5                                                      (0x1001c18c)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_7_5
#define DV_REG_STICKY_DATA_VAULT_ENTRY_7_5                                                          (0x18c)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_7_6                                                      (0x1001c190)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_7_6
#define DV_REG_STICKY_DATA_VAULT_ENTRY_7_6                                                          (0x190)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_7_7                                                      (0x1001c194)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_7_7
#define DV_REG_STICKY_DATA_VAULT_ENTRY_7_7                                                          (0x194)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_7_8                                                      (0x1001c198)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_7_8
#define DV_REG_STICKY_DATA_VAULT_ENTRY_7_8                                                          (0x198)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_7_9                                                      (0x1001c19c)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_7_9
#define DV_REG_STICKY_DATA_VAULT_ENTRY_7_9                                                          (0x19c)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_7_10                                                     (0x1001c1a0)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_7_10
#define DV_REG_STICKY_DATA_VAULT_ENTRY_7_10                                                         (0x1a0)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_7_11                                                     (0x1001c1a4)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_7_11
#define DV_REG_STICKY_DATA_VAULT_ENTRY_7_11                                                         (0x1a4)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_8_0                                                      (0x1001c1a8)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_8_0
#define DV_REG_STICKY_DATA_VAULT_ENTRY_8_0                                                          (0x1a8)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_8_1                                                      (0x1001c1ac)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_8_1
#define DV_REG_STICKY_DATA_VAULT_ENTRY_8_1                                                          (0x1ac)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_8_2                                                      (0x1001c1b0)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_8_2
#define DV_REG_STICKY_DATA_VAULT_ENTRY_8_2                                                          (0x1b0)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_8_3                                                      (0x1001c1b4)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_8_3
#define DV_REG_STICKY_DATA_VAULT_ENTRY_8_3                                                          (0x1b4)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_8_4                                                      (0x1001c1b8)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_8_4
#define DV_REG_STICKY_DATA_VAULT_ENTRY_8_4                                                          (0x1b8)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_8_5                                                      (0x1001c1bc)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_8_5
#define DV_REG_STICKY_DATA_VAULT_ENTRY_8_5                                                          (0x1bc)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_8_6                                                      (0x1001c1c0)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_8_6
#define DV_REG_STICKY_DATA_VAULT_ENTRY_8_6                                                          (0x1c0)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_8_7                                                      (0x1001c1c4)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_8_7
#define DV_REG_STICKY_DATA_VAULT_ENTRY_8_7                                                          (0x1c4)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_8_8                                                      (0x1001c1c8)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_8_8
#define DV_REG_STICKY_DATA_VAULT_ENTRY_8_8                                                          (0x1c8)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_8_9                                                      (0x1001c1cc)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_8_9
#define DV_REG_STICKY_DATA_VAULT_ENTRY_8_9                                                          (0x1cc)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_8_10                                                     (0x1001c1d0)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_8_10
#define DV_REG_STICKY_DATA_VAULT_ENTRY_8_10                                                         (0x1d0)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_8_11                                                     (0x1001c1d4)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_8_11
#define DV_REG_STICKY_DATA_VAULT_ENTRY_8_11                                                         (0x1d4)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_9_0                                                      (0x1001c1d8)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_9_0
#define DV_REG_STICKY_DATA_VAULT_ENTRY_9_0                                                          (0x1d8)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_9_1                                                      (0x1001c1dc)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_9_1
#define DV_REG_STICKY_DATA_VAULT_ENTRY_9_1                                                          (0x1dc)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_9_2                                                      (0x1001c1e0)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_9_2
#define DV_REG_STICKY_DATA_VAULT_ENTRY_9_2                                                          (0x1e0)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_9_3                                                      (0x1001c1e4)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_9_3
#define DV_REG_STICKY_DATA_VAULT_ENTRY_9_3                                                          (0x1e4)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_9_4                                                      (0x1001c1e8)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_9_4
#define DV_REG_STICKY_DATA_VAULT_ENTRY_9_4                                                          (0x1e8)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_9_5                                                      (0x1001c1ec)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_9_5
#define DV_REG_STICKY_DATA_VAULT_ENTRY_9_5                                                          (0x1ec)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_9_6                                                      (0x1001c1f0)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_9_6
#define DV_REG_STICKY_DATA_VAULT_ENTRY_9_6                                                          (0x1f0)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_9_7                                                      (0x1001c1f4)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_9_7
#define DV_REG_STICKY_DATA_VAULT_ENTRY_9_7                                                          (0x1f4)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_9_8                                                      (0x1001c1f8)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_9_8
#define DV_REG_STICKY_DATA_VAULT_ENTRY_9_8                                                          (0x1f8)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_9_9                                                      (0x1001c1fc)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_9_9
#define DV_REG_STICKY_DATA_VAULT_ENTRY_9_9                                                          (0x1fc)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_9_10                                                     (0x1001c200)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_9_10
#define DV_REG_STICKY_DATA_VAULT_ENTRY_9_10                                                         (0x200)
#endif
#define CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_9_11                                                     (0x1001c204)
#ifndef DV_REG_STICKY_DATA_VAULT_ENTRY_9_11
#define DV_REG_STICKY_DATA_VAULT_ENTRY_9_11                                                         (0x204)
#endif
#define CLP_DV_REG_DATAVAULTCTRL_0                                                                  (0x1001c208)
#ifndef DV_REG_DATAVAULTCTRL_0
#define DV_REG_DATAVAULTCTRL_0                                                                      (0x208)
#define DV_REG_DATAVAULTCTRL_0_LOCK_ENTRY_LOW                                                       (0)
#define DV_REG_DATAVAULTCTRL_0_LOCK_ENTRY_MASK                                                      (0x1)
#endif
#define CLP_DV_REG_DATAVAULTCTRL_1                                                                  (0x1001c20c)
#ifndef DV_REG_DATAVAULTCTRL_1
#define DV_REG_DATAVAULTCTRL_1                                                                      (0x20c)
#define DV_REG_DATAVAULTCTRL_1_LOCK_ENTRY_LOW                                                       (0)
#define DV_REG_DATAVAULTCTRL_1_LOCK_ENTRY_MASK                                                      (0x1)
#endif
#define CLP_DV_REG_DATAVAULTCTRL_2                                                                  (0x1001c210)
#ifndef DV_REG_DATAVAULTCTRL_2
#define DV_REG_DATAVAULTCTRL_2                                                                      (0x210)
#define DV_REG_DATAVAULTCTRL_2_LOCK_ENTRY_LOW                                                       (0)
#define DV_REG_DATAVAULTCTRL_2_LOCK_ENTRY_MASK                                                      (0x1)
#endif
#define CLP_DV_REG_DATAVAULTCTRL_3                                                                  (0x1001c214)
#ifndef DV_REG_DATAVAULTCTRL_3
#define DV_REG_DATAVAULTCTRL_3                                                                      (0x214)
#define DV_REG_DATAVAULTCTRL_3_LOCK_ENTRY_LOW                                                       (0)
#define DV_REG_DATAVAULTCTRL_3_LOCK_ENTRY_MASK                                                      (0x1)
#endif
#define CLP_DV_REG_DATAVAULTCTRL_4                                                                  (0x1001c218)
#ifndef DV_REG_DATAVAULTCTRL_4
#define DV_REG_DATAVAULTCTRL_4                                                                      (0x218)
#define DV_REG_DATAVAULTCTRL_4_LOCK_ENTRY_LOW                                                       (0)
#define DV_REG_DATAVAULTCTRL_4_LOCK_ENTRY_MASK                                                      (0x1)
#endif
#define CLP_DV_REG_DATAVAULTCTRL_5                                                                  (0x1001c21c)
#ifndef DV_REG_DATAVAULTCTRL_5
#define DV_REG_DATAVAULTCTRL_5                                                                      (0x21c)
#define DV_REG_DATAVAULTCTRL_5_LOCK_ENTRY_LOW                                                       (0)
#define DV_REG_DATAVAULTCTRL_5_LOCK_ENTRY_MASK                                                      (0x1)
#endif
#define CLP_DV_REG_DATAVAULTCTRL_6                                                                  (0x1001c220)
#ifndef DV_REG_DATAVAULTCTRL_6
#define DV_REG_DATAVAULTCTRL_6                                                                      (0x220)
#define DV_REG_DATAVAULTCTRL_6_LOCK_ENTRY_LOW                                                       (0)
#define DV_REG_DATAVAULTCTRL_6_LOCK_ENTRY_MASK                                                      (0x1)
#endif
#define CLP_DV_REG_DATAVAULTCTRL_7                                                                  (0x1001c224)
#ifndef DV_REG_DATAVAULTCTRL_7
#define DV_REG_DATAVAULTCTRL_7                                                                      (0x224)
#define DV_REG_DATAVAULTCTRL_7_LOCK_ENTRY_LOW                                                       (0)
#define DV_REG_DATAVAULTCTRL_7_LOCK_ENTRY_MASK                                                      (0x1)
#endif
#define CLP_DV_REG_DATAVAULTCTRL_8                                                                  (0x1001c228)
#ifndef DV_REG_DATAVAULTCTRL_8
#define DV_REG_DATAVAULTCTRL_8                                                                      (0x228)
#define DV_REG_DATAVAULTCTRL_8_LOCK_ENTRY_LOW                                                       (0)
#define DV_REG_DATAVAULTCTRL_8_LOCK_ENTRY_MASK                                                      (0x1)
#endif
#define CLP_DV_REG_DATAVAULTCTRL_9                                                                  (0x1001c22c)
#ifndef DV_REG_DATAVAULTCTRL_9
#define DV_REG_DATAVAULTCTRL_9                                                                      (0x22c)
#define DV_REG_DATAVAULTCTRL_9_LOCK_ENTRY_LOW                                                       (0)
#define DV_REG_DATAVAULTCTRL_9_LOCK_ENTRY_MASK                                                      (0x1)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_0_0                                                             (0x1001c230)
#ifndef DV_REG_DATA_VAULT_ENTRY_0_0
#define DV_REG_DATA_VAULT_ENTRY_0_0                                                                 (0x230)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_0_1                                                             (0x1001c234)
#ifndef DV_REG_DATA_VAULT_ENTRY_0_1
#define DV_REG_DATA_VAULT_ENTRY_0_1                                                                 (0x234)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_0_2                                                             (0x1001c238)
#ifndef DV_REG_DATA_VAULT_ENTRY_0_2
#define DV_REG_DATA_VAULT_ENTRY_0_2                                                                 (0x238)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_0_3                                                             (0x1001c23c)
#ifndef DV_REG_DATA_VAULT_ENTRY_0_3
#define DV_REG_DATA_VAULT_ENTRY_0_3                                                                 (0x23c)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_0_4                                                             (0x1001c240)
#ifndef DV_REG_DATA_VAULT_ENTRY_0_4
#define DV_REG_DATA_VAULT_ENTRY_0_4                                                                 (0x240)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_0_5                                                             (0x1001c244)
#ifndef DV_REG_DATA_VAULT_ENTRY_0_5
#define DV_REG_DATA_VAULT_ENTRY_0_5                                                                 (0x244)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_0_6                                                             (0x1001c248)
#ifndef DV_REG_DATA_VAULT_ENTRY_0_6
#define DV_REG_DATA_VAULT_ENTRY_0_6                                                                 (0x248)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_0_7                                                             (0x1001c24c)
#ifndef DV_REG_DATA_VAULT_ENTRY_0_7
#define DV_REG_DATA_VAULT_ENTRY_0_7                                                                 (0x24c)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_0_8                                                             (0x1001c250)
#ifndef DV_REG_DATA_VAULT_ENTRY_0_8
#define DV_REG_DATA_VAULT_ENTRY_0_8                                                                 (0x250)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_0_9                                                             (0x1001c254)
#ifndef DV_REG_DATA_VAULT_ENTRY_0_9
#define DV_REG_DATA_VAULT_ENTRY_0_9                                                                 (0x254)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_0_10                                                            (0x1001c258)
#ifndef DV_REG_DATA_VAULT_ENTRY_0_10
#define DV_REG_DATA_VAULT_ENTRY_0_10                                                                (0x258)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_0_11                                                            (0x1001c25c)
#ifndef DV_REG_DATA_VAULT_ENTRY_0_11
#define DV_REG_DATA_VAULT_ENTRY_0_11                                                                (0x25c)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_1_0                                                             (0x1001c260)
#ifndef DV_REG_DATA_VAULT_ENTRY_1_0
#define DV_REG_DATA_VAULT_ENTRY_1_0                                                                 (0x260)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_1_1                                                             (0x1001c264)
#ifndef DV_REG_DATA_VAULT_ENTRY_1_1
#define DV_REG_DATA_VAULT_ENTRY_1_1                                                                 (0x264)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_1_2                                                             (0x1001c268)
#ifndef DV_REG_DATA_VAULT_ENTRY_1_2
#define DV_REG_DATA_VAULT_ENTRY_1_2                                                                 (0x268)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_1_3                                                             (0x1001c26c)
#ifndef DV_REG_DATA_VAULT_ENTRY_1_3
#define DV_REG_DATA_VAULT_ENTRY_1_3                                                                 (0x26c)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_1_4                                                             (0x1001c270)
#ifndef DV_REG_DATA_VAULT_ENTRY_1_4
#define DV_REG_DATA_VAULT_ENTRY_1_4                                                                 (0x270)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_1_5                                                             (0x1001c274)
#ifndef DV_REG_DATA_VAULT_ENTRY_1_5
#define DV_REG_DATA_VAULT_ENTRY_1_5                                                                 (0x274)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_1_6                                                             (0x1001c278)
#ifndef DV_REG_DATA_VAULT_ENTRY_1_6
#define DV_REG_DATA_VAULT_ENTRY_1_6                                                                 (0x278)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_1_7                                                             (0x1001c27c)
#ifndef DV_REG_DATA_VAULT_ENTRY_1_7
#define DV_REG_DATA_VAULT_ENTRY_1_7                                                                 (0x27c)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_1_8                                                             (0x1001c280)
#ifndef DV_REG_DATA_VAULT_ENTRY_1_8
#define DV_REG_DATA_VAULT_ENTRY_1_8                                                                 (0x280)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_1_9                                                             (0x1001c284)
#ifndef DV_REG_DATA_VAULT_ENTRY_1_9
#define DV_REG_DATA_VAULT_ENTRY_1_9                                                                 (0x284)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_1_10                                                            (0x1001c288)
#ifndef DV_REG_DATA_VAULT_ENTRY_1_10
#define DV_REG_DATA_VAULT_ENTRY_1_10                                                                (0x288)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_1_11                                                            (0x1001c28c)
#ifndef DV_REG_DATA_VAULT_ENTRY_1_11
#define DV_REG_DATA_VAULT_ENTRY_1_11                                                                (0x28c)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_2_0                                                             (0x1001c290)
#ifndef DV_REG_DATA_VAULT_ENTRY_2_0
#define DV_REG_DATA_VAULT_ENTRY_2_0                                                                 (0x290)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_2_1                                                             (0x1001c294)
#ifndef DV_REG_DATA_VAULT_ENTRY_2_1
#define DV_REG_DATA_VAULT_ENTRY_2_1                                                                 (0x294)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_2_2                                                             (0x1001c298)
#ifndef DV_REG_DATA_VAULT_ENTRY_2_2
#define DV_REG_DATA_VAULT_ENTRY_2_2                                                                 (0x298)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_2_3                                                             (0x1001c29c)
#ifndef DV_REG_DATA_VAULT_ENTRY_2_3
#define DV_REG_DATA_VAULT_ENTRY_2_3                                                                 (0x29c)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_2_4                                                             (0x1001c2a0)
#ifndef DV_REG_DATA_VAULT_ENTRY_2_4
#define DV_REG_DATA_VAULT_ENTRY_2_4                                                                 (0x2a0)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_2_5                                                             (0x1001c2a4)
#ifndef DV_REG_DATA_VAULT_ENTRY_2_5
#define DV_REG_DATA_VAULT_ENTRY_2_5                                                                 (0x2a4)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_2_6                                                             (0x1001c2a8)
#ifndef DV_REG_DATA_VAULT_ENTRY_2_6
#define DV_REG_DATA_VAULT_ENTRY_2_6                                                                 (0x2a8)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_2_7                                                             (0x1001c2ac)
#ifndef DV_REG_DATA_VAULT_ENTRY_2_7
#define DV_REG_DATA_VAULT_ENTRY_2_7                                                                 (0x2ac)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_2_8                                                             (0x1001c2b0)
#ifndef DV_REG_DATA_VAULT_ENTRY_2_8
#define DV_REG_DATA_VAULT_ENTRY_2_8                                                                 (0x2b0)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_2_9                                                             (0x1001c2b4)
#ifndef DV_REG_DATA_VAULT_ENTRY_2_9
#define DV_REG_DATA_VAULT_ENTRY_2_9                                                                 (0x2b4)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_2_10                                                            (0x1001c2b8)
#ifndef DV_REG_DATA_VAULT_ENTRY_2_10
#define DV_REG_DATA_VAULT_ENTRY_2_10                                                                (0x2b8)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_2_11                                                            (0x1001c2bc)
#ifndef DV_REG_DATA_VAULT_ENTRY_2_11
#define DV_REG_DATA_VAULT_ENTRY_2_11                                                                (0x2bc)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_3_0                                                             (0x1001c2c0)
#ifndef DV_REG_DATA_VAULT_ENTRY_3_0
#define DV_REG_DATA_VAULT_ENTRY_3_0                                                                 (0x2c0)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_3_1                                                             (0x1001c2c4)
#ifndef DV_REG_DATA_VAULT_ENTRY_3_1
#define DV_REG_DATA_VAULT_ENTRY_3_1                                                                 (0x2c4)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_3_2                                                             (0x1001c2c8)
#ifndef DV_REG_DATA_VAULT_ENTRY_3_2
#define DV_REG_DATA_VAULT_ENTRY_3_2                                                                 (0x2c8)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_3_3                                                             (0x1001c2cc)
#ifndef DV_REG_DATA_VAULT_ENTRY_3_3
#define DV_REG_DATA_VAULT_ENTRY_3_3                                                                 (0x2cc)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_3_4                                                             (0x1001c2d0)
#ifndef DV_REG_DATA_VAULT_ENTRY_3_4
#define DV_REG_DATA_VAULT_ENTRY_3_4                                                                 (0x2d0)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_3_5                                                             (0x1001c2d4)
#ifndef DV_REG_DATA_VAULT_ENTRY_3_5
#define DV_REG_DATA_VAULT_ENTRY_3_5                                                                 (0x2d4)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_3_6                                                             (0x1001c2d8)
#ifndef DV_REG_DATA_VAULT_ENTRY_3_6
#define DV_REG_DATA_VAULT_ENTRY_3_6                                                                 (0x2d8)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_3_7                                                             (0x1001c2dc)
#ifndef DV_REG_DATA_VAULT_ENTRY_3_7
#define DV_REG_DATA_VAULT_ENTRY_3_7                                                                 (0x2dc)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_3_8                                                             (0x1001c2e0)
#ifndef DV_REG_DATA_VAULT_ENTRY_3_8
#define DV_REG_DATA_VAULT_ENTRY_3_8                                                                 (0x2e0)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_3_9                                                             (0x1001c2e4)
#ifndef DV_REG_DATA_VAULT_ENTRY_3_9
#define DV_REG_DATA_VAULT_ENTRY_3_9                                                                 (0x2e4)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_3_10                                                            (0x1001c2e8)
#ifndef DV_REG_DATA_VAULT_ENTRY_3_10
#define DV_REG_DATA_VAULT_ENTRY_3_10                                                                (0x2e8)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_3_11                                                            (0x1001c2ec)
#ifndef DV_REG_DATA_VAULT_ENTRY_3_11
#define DV_REG_DATA_VAULT_ENTRY_3_11                                                                (0x2ec)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_4_0                                                             (0x1001c2f0)
#ifndef DV_REG_DATA_VAULT_ENTRY_4_0
#define DV_REG_DATA_VAULT_ENTRY_4_0                                                                 (0x2f0)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_4_1                                                             (0x1001c2f4)
#ifndef DV_REG_DATA_VAULT_ENTRY_4_1
#define DV_REG_DATA_VAULT_ENTRY_4_1                                                                 (0x2f4)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_4_2                                                             (0x1001c2f8)
#ifndef DV_REG_DATA_VAULT_ENTRY_4_2
#define DV_REG_DATA_VAULT_ENTRY_4_2                                                                 (0x2f8)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_4_3                                                             (0x1001c2fc)
#ifndef DV_REG_DATA_VAULT_ENTRY_4_3
#define DV_REG_DATA_VAULT_ENTRY_4_3                                                                 (0x2fc)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_4_4                                                             (0x1001c300)
#ifndef DV_REG_DATA_VAULT_ENTRY_4_4
#define DV_REG_DATA_VAULT_ENTRY_4_4                                                                 (0x300)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_4_5                                                             (0x1001c304)
#ifndef DV_REG_DATA_VAULT_ENTRY_4_5
#define DV_REG_DATA_VAULT_ENTRY_4_5                                                                 (0x304)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_4_6                                                             (0x1001c308)
#ifndef DV_REG_DATA_VAULT_ENTRY_4_6
#define DV_REG_DATA_VAULT_ENTRY_4_6                                                                 (0x308)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_4_7                                                             (0x1001c30c)
#ifndef DV_REG_DATA_VAULT_ENTRY_4_7
#define DV_REG_DATA_VAULT_ENTRY_4_7                                                                 (0x30c)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_4_8                                                             (0x1001c310)
#ifndef DV_REG_DATA_VAULT_ENTRY_4_8
#define DV_REG_DATA_VAULT_ENTRY_4_8                                                                 (0x310)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_4_9                                                             (0x1001c314)
#ifndef DV_REG_DATA_VAULT_ENTRY_4_9
#define DV_REG_DATA_VAULT_ENTRY_4_9                                                                 (0x314)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_4_10                                                            (0x1001c318)
#ifndef DV_REG_DATA_VAULT_ENTRY_4_10
#define DV_REG_DATA_VAULT_ENTRY_4_10                                                                (0x318)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_4_11                                                            (0x1001c31c)
#ifndef DV_REG_DATA_VAULT_ENTRY_4_11
#define DV_REG_DATA_VAULT_ENTRY_4_11                                                                (0x31c)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_5_0                                                             (0x1001c320)
#ifndef DV_REG_DATA_VAULT_ENTRY_5_0
#define DV_REG_DATA_VAULT_ENTRY_5_0                                                                 (0x320)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_5_1                                                             (0x1001c324)
#ifndef DV_REG_DATA_VAULT_ENTRY_5_1
#define DV_REG_DATA_VAULT_ENTRY_5_1                                                                 (0x324)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_5_2                                                             (0x1001c328)
#ifndef DV_REG_DATA_VAULT_ENTRY_5_2
#define DV_REG_DATA_VAULT_ENTRY_5_2                                                                 (0x328)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_5_3                                                             (0x1001c32c)
#ifndef DV_REG_DATA_VAULT_ENTRY_5_3
#define DV_REG_DATA_VAULT_ENTRY_5_3                                                                 (0x32c)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_5_4                                                             (0x1001c330)
#ifndef DV_REG_DATA_VAULT_ENTRY_5_4
#define DV_REG_DATA_VAULT_ENTRY_5_4                                                                 (0x330)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_5_5                                                             (0x1001c334)
#ifndef DV_REG_DATA_VAULT_ENTRY_5_5
#define DV_REG_DATA_VAULT_ENTRY_5_5                                                                 (0x334)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_5_6                                                             (0x1001c338)
#ifndef DV_REG_DATA_VAULT_ENTRY_5_6
#define DV_REG_DATA_VAULT_ENTRY_5_6                                                                 (0x338)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_5_7                                                             (0x1001c33c)
#ifndef DV_REG_DATA_VAULT_ENTRY_5_7
#define DV_REG_DATA_VAULT_ENTRY_5_7                                                                 (0x33c)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_5_8                                                             (0x1001c340)
#ifndef DV_REG_DATA_VAULT_ENTRY_5_8
#define DV_REG_DATA_VAULT_ENTRY_5_8                                                                 (0x340)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_5_9                                                             (0x1001c344)
#ifndef DV_REG_DATA_VAULT_ENTRY_5_9
#define DV_REG_DATA_VAULT_ENTRY_5_9                                                                 (0x344)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_5_10                                                            (0x1001c348)
#ifndef DV_REG_DATA_VAULT_ENTRY_5_10
#define DV_REG_DATA_VAULT_ENTRY_5_10                                                                (0x348)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_5_11                                                            (0x1001c34c)
#ifndef DV_REG_DATA_VAULT_ENTRY_5_11
#define DV_REG_DATA_VAULT_ENTRY_5_11                                                                (0x34c)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_6_0                                                             (0x1001c350)
#ifndef DV_REG_DATA_VAULT_ENTRY_6_0
#define DV_REG_DATA_VAULT_ENTRY_6_0                                                                 (0x350)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_6_1                                                             (0x1001c354)
#ifndef DV_REG_DATA_VAULT_ENTRY_6_1
#define DV_REG_DATA_VAULT_ENTRY_6_1                                                                 (0x354)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_6_2                                                             (0x1001c358)
#ifndef DV_REG_DATA_VAULT_ENTRY_6_2
#define DV_REG_DATA_VAULT_ENTRY_6_2                                                                 (0x358)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_6_3                                                             (0x1001c35c)
#ifndef DV_REG_DATA_VAULT_ENTRY_6_3
#define DV_REG_DATA_VAULT_ENTRY_6_3                                                                 (0x35c)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_6_4                                                             (0x1001c360)
#ifndef DV_REG_DATA_VAULT_ENTRY_6_4
#define DV_REG_DATA_VAULT_ENTRY_6_4                                                                 (0x360)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_6_5                                                             (0x1001c364)
#ifndef DV_REG_DATA_VAULT_ENTRY_6_5
#define DV_REG_DATA_VAULT_ENTRY_6_5                                                                 (0x364)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_6_6                                                             (0x1001c368)
#ifndef DV_REG_DATA_VAULT_ENTRY_6_6
#define DV_REG_DATA_VAULT_ENTRY_6_6                                                                 (0x368)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_6_7                                                             (0x1001c36c)
#ifndef DV_REG_DATA_VAULT_ENTRY_6_7
#define DV_REG_DATA_VAULT_ENTRY_6_7                                                                 (0x36c)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_6_8                                                             (0x1001c370)
#ifndef DV_REG_DATA_VAULT_ENTRY_6_8
#define DV_REG_DATA_VAULT_ENTRY_6_8                                                                 (0x370)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_6_9                                                             (0x1001c374)
#ifndef DV_REG_DATA_VAULT_ENTRY_6_9
#define DV_REG_DATA_VAULT_ENTRY_6_9                                                                 (0x374)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_6_10                                                            (0x1001c378)
#ifndef DV_REG_DATA_VAULT_ENTRY_6_10
#define DV_REG_DATA_VAULT_ENTRY_6_10                                                                (0x378)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_6_11                                                            (0x1001c37c)
#ifndef DV_REG_DATA_VAULT_ENTRY_6_11
#define DV_REG_DATA_VAULT_ENTRY_6_11                                                                (0x37c)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_7_0                                                             (0x1001c380)
#ifndef DV_REG_DATA_VAULT_ENTRY_7_0
#define DV_REG_DATA_VAULT_ENTRY_7_0                                                                 (0x380)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_7_1                                                             (0x1001c384)
#ifndef DV_REG_DATA_VAULT_ENTRY_7_1
#define DV_REG_DATA_VAULT_ENTRY_7_1                                                                 (0x384)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_7_2                                                             (0x1001c388)
#ifndef DV_REG_DATA_VAULT_ENTRY_7_2
#define DV_REG_DATA_VAULT_ENTRY_7_2                                                                 (0x388)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_7_3                                                             (0x1001c38c)
#ifndef DV_REG_DATA_VAULT_ENTRY_7_3
#define DV_REG_DATA_VAULT_ENTRY_7_3                                                                 (0x38c)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_7_4                                                             (0x1001c390)
#ifndef DV_REG_DATA_VAULT_ENTRY_7_4
#define DV_REG_DATA_VAULT_ENTRY_7_4                                                                 (0x390)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_7_5                                                             (0x1001c394)
#ifndef DV_REG_DATA_VAULT_ENTRY_7_5
#define DV_REG_DATA_VAULT_ENTRY_7_5                                                                 (0x394)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_7_6                                                             (0x1001c398)
#ifndef DV_REG_DATA_VAULT_ENTRY_7_6
#define DV_REG_DATA_VAULT_ENTRY_7_6                                                                 (0x398)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_7_7                                                             (0x1001c39c)
#ifndef DV_REG_DATA_VAULT_ENTRY_7_7
#define DV_REG_DATA_VAULT_ENTRY_7_7                                                                 (0x39c)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_7_8                                                             (0x1001c3a0)
#ifndef DV_REG_DATA_VAULT_ENTRY_7_8
#define DV_REG_DATA_VAULT_ENTRY_7_8                                                                 (0x3a0)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_7_9                                                             (0x1001c3a4)
#ifndef DV_REG_DATA_VAULT_ENTRY_7_9
#define DV_REG_DATA_VAULT_ENTRY_7_9                                                                 (0x3a4)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_7_10                                                            (0x1001c3a8)
#ifndef DV_REG_DATA_VAULT_ENTRY_7_10
#define DV_REG_DATA_VAULT_ENTRY_7_10                                                                (0x3a8)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_7_11                                                            (0x1001c3ac)
#ifndef DV_REG_DATA_VAULT_ENTRY_7_11
#define DV_REG_DATA_VAULT_ENTRY_7_11                                                                (0x3ac)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_8_0                                                             (0x1001c3b0)
#ifndef DV_REG_DATA_VAULT_ENTRY_8_0
#define DV_REG_DATA_VAULT_ENTRY_8_0                                                                 (0x3b0)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_8_1                                                             (0x1001c3b4)
#ifndef DV_REG_DATA_VAULT_ENTRY_8_1
#define DV_REG_DATA_VAULT_ENTRY_8_1                                                                 (0x3b4)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_8_2                                                             (0x1001c3b8)
#ifndef DV_REG_DATA_VAULT_ENTRY_8_2
#define DV_REG_DATA_VAULT_ENTRY_8_2                                                                 (0x3b8)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_8_3                                                             (0x1001c3bc)
#ifndef DV_REG_DATA_VAULT_ENTRY_8_3
#define DV_REG_DATA_VAULT_ENTRY_8_3                                                                 (0x3bc)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_8_4                                                             (0x1001c3c0)
#ifndef DV_REG_DATA_VAULT_ENTRY_8_4
#define DV_REG_DATA_VAULT_ENTRY_8_4                                                                 (0x3c0)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_8_5                                                             (0x1001c3c4)
#ifndef DV_REG_DATA_VAULT_ENTRY_8_5
#define DV_REG_DATA_VAULT_ENTRY_8_5                                                                 (0x3c4)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_8_6                                                             (0x1001c3c8)
#ifndef DV_REG_DATA_VAULT_ENTRY_8_6
#define DV_REG_DATA_VAULT_ENTRY_8_6                                                                 (0x3c8)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_8_7                                                             (0x1001c3cc)
#ifndef DV_REG_DATA_VAULT_ENTRY_8_7
#define DV_REG_DATA_VAULT_ENTRY_8_7                                                                 (0x3cc)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_8_8                                                             (0x1001c3d0)
#ifndef DV_REG_DATA_VAULT_ENTRY_8_8
#define DV_REG_DATA_VAULT_ENTRY_8_8                                                                 (0x3d0)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_8_9                                                             (0x1001c3d4)
#ifndef DV_REG_DATA_VAULT_ENTRY_8_9
#define DV_REG_DATA_VAULT_ENTRY_8_9                                                                 (0x3d4)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_8_10                                                            (0x1001c3d8)
#ifndef DV_REG_DATA_VAULT_ENTRY_8_10
#define DV_REG_DATA_VAULT_ENTRY_8_10                                                                (0x3d8)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_8_11                                                            (0x1001c3dc)
#ifndef DV_REG_DATA_VAULT_ENTRY_8_11
#define DV_REG_DATA_VAULT_ENTRY_8_11                                                                (0x3dc)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_9_0                                                             (0x1001c3e0)
#ifndef DV_REG_DATA_VAULT_ENTRY_9_0
#define DV_REG_DATA_VAULT_ENTRY_9_0                                                                 (0x3e0)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_9_1                                                             (0x1001c3e4)
#ifndef DV_REG_DATA_VAULT_ENTRY_9_1
#define DV_REG_DATA_VAULT_ENTRY_9_1                                                                 (0x3e4)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_9_2                                                             (0x1001c3e8)
#ifndef DV_REG_DATA_VAULT_ENTRY_9_2
#define DV_REG_DATA_VAULT_ENTRY_9_2                                                                 (0x3e8)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_9_3                                                             (0x1001c3ec)
#ifndef DV_REG_DATA_VAULT_ENTRY_9_3
#define DV_REG_DATA_VAULT_ENTRY_9_3                                                                 (0x3ec)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_9_4                                                             (0x1001c3f0)
#ifndef DV_REG_DATA_VAULT_ENTRY_9_4
#define DV_REG_DATA_VAULT_ENTRY_9_4                                                                 (0x3f0)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_9_5                                                             (0x1001c3f4)
#ifndef DV_REG_DATA_VAULT_ENTRY_9_5
#define DV_REG_DATA_VAULT_ENTRY_9_5                                                                 (0x3f4)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_9_6                                                             (0x1001c3f8)
#ifndef DV_REG_DATA_VAULT_ENTRY_9_6
#define DV_REG_DATA_VAULT_ENTRY_9_6                                                                 (0x3f8)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_9_7                                                             (0x1001c3fc)
#ifndef DV_REG_DATA_VAULT_ENTRY_9_7
#define DV_REG_DATA_VAULT_ENTRY_9_7                                                                 (0x3fc)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_9_8                                                             (0x1001c400)
#ifndef DV_REG_DATA_VAULT_ENTRY_9_8
#define DV_REG_DATA_VAULT_ENTRY_9_8                                                                 (0x400)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_9_9                                                             (0x1001c404)
#ifndef DV_REG_DATA_VAULT_ENTRY_9_9
#define DV_REG_DATA_VAULT_ENTRY_9_9                                                                 (0x404)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_9_10                                                            (0x1001c408)
#ifndef DV_REG_DATA_VAULT_ENTRY_9_10
#define DV_REG_DATA_VAULT_ENTRY_9_10                                                                (0x408)
#endif
#define CLP_DV_REG_DATA_VAULT_ENTRY_9_11                                                            (0x1001c40c)
#ifndef DV_REG_DATA_VAULT_ENTRY_9_11
#define DV_REG_DATA_VAULT_ENTRY_9_11                                                                (0x40c)
#endif
#define CLP_DV_REG_LOCKABLESCRATCHREGCTRL_0                                                         (0x1001c410)
#ifndef DV_REG_LOCKABLESCRATCHREGCTRL_0
#define DV_REG_LOCKABLESCRATCHREGCTRL_0                                                             (0x410)
#define DV_REG_LOCKABLESCRATCHREGCTRL_0_LOCK_ENTRY_LOW                                              (0)
#define DV_REG_LOCKABLESCRATCHREGCTRL_0_LOCK_ENTRY_MASK                                             (0x1)
#endif
#define CLP_DV_REG_LOCKABLESCRATCHREGCTRL_1                                                         (0x1001c414)
#ifndef DV_REG_LOCKABLESCRATCHREGCTRL_1
#define DV_REG_LOCKABLESCRATCHREGCTRL_1                                                             (0x414)
#define DV_REG_LOCKABLESCRATCHREGCTRL_1_LOCK_ENTRY_LOW                                              (0)
#define DV_REG_LOCKABLESCRATCHREGCTRL_1_LOCK_ENTRY_MASK                                             (0x1)
#endif
#define CLP_DV_REG_LOCKABLESCRATCHREGCTRL_2                                                         (0x1001c418)
#ifndef DV_REG_LOCKABLESCRATCHREGCTRL_2
#define DV_REG_LOCKABLESCRATCHREGCTRL_2                                                             (0x418)
#define DV_REG_LOCKABLESCRATCHREGCTRL_2_LOCK_ENTRY_LOW                                              (0)
#define DV_REG_LOCKABLESCRATCHREGCTRL_2_LOCK_ENTRY_MASK                                             (0x1)
#endif
#define CLP_DV_REG_LOCKABLESCRATCHREGCTRL_3                                                         (0x1001c41c)
#ifndef DV_REG_LOCKABLESCRATCHREGCTRL_3
#define DV_REG_LOCKABLESCRATCHREGCTRL_3                                                             (0x41c)
#define DV_REG_LOCKABLESCRATCHREGCTRL_3_LOCK_ENTRY_LOW                                              (0)
#define DV_REG_LOCKABLESCRATCHREGCTRL_3_LOCK_ENTRY_MASK                                             (0x1)
#endif
#define CLP_DV_REG_LOCKABLESCRATCHREGCTRL_4                                                         (0x1001c420)
#ifndef DV_REG_LOCKABLESCRATCHREGCTRL_4
#define DV_REG_LOCKABLESCRATCHREGCTRL_4                                                             (0x420)
#define DV_REG_LOCKABLESCRATCHREGCTRL_4_LOCK_ENTRY_LOW                                              (0)
#define DV_REG_LOCKABLESCRATCHREGCTRL_4_LOCK_ENTRY_MASK                                             (0x1)
#endif
#define CLP_DV_REG_LOCKABLESCRATCHREGCTRL_5                                                         (0x1001c424)
#ifndef DV_REG_LOCKABLESCRATCHREGCTRL_5
#define DV_REG_LOCKABLESCRATCHREGCTRL_5                                                             (0x424)
#define DV_REG_LOCKABLESCRATCHREGCTRL_5_LOCK_ENTRY_LOW                                              (0)
#define DV_REG_LOCKABLESCRATCHREGCTRL_5_LOCK_ENTRY_MASK                                             (0x1)
#endif
#define CLP_DV_REG_LOCKABLESCRATCHREGCTRL_6                                                         (0x1001c428)
#ifndef DV_REG_LOCKABLESCRATCHREGCTRL_6
#define DV_REG_LOCKABLESCRATCHREGCTRL_6                                                             (0x428)
#define DV_REG_LOCKABLESCRATCHREGCTRL_6_LOCK_ENTRY_LOW                                              (0)
#define DV_REG_LOCKABLESCRATCHREGCTRL_6_LOCK_ENTRY_MASK                                             (0x1)
#endif
#define CLP_DV_REG_LOCKABLESCRATCHREGCTRL_7                                                         (0x1001c42c)
#ifndef DV_REG_LOCKABLESCRATCHREGCTRL_7
#define DV_REG_LOCKABLESCRATCHREGCTRL_7                                                             (0x42c)
#define DV_REG_LOCKABLESCRATCHREGCTRL_7_LOCK_ENTRY_LOW                                              (0)
#define DV_REG_LOCKABLESCRATCHREGCTRL_7_LOCK_ENTRY_MASK                                             (0x1)
#endif
#define CLP_DV_REG_LOCKABLESCRATCHREGCTRL_8                                                         (0x1001c430)
#ifndef DV_REG_LOCKABLESCRATCHREGCTRL_8
#define DV_REG_LOCKABLESCRATCHREGCTRL_8                                                             (0x430)
#define DV_REG_LOCKABLESCRATCHREGCTRL_8_LOCK_ENTRY_LOW                                              (0)
#define DV_REG_LOCKABLESCRATCHREGCTRL_8_LOCK_ENTRY_MASK                                             (0x1)
#endif
#define CLP_DV_REG_LOCKABLESCRATCHREGCTRL_9                                                         (0x1001c434)
#ifndef DV_REG_LOCKABLESCRATCHREGCTRL_9
#define DV_REG_LOCKABLESCRATCHREGCTRL_9                                                             (0x434)
#define DV_REG_LOCKABLESCRATCHREGCTRL_9_LOCK_ENTRY_LOW                                              (0)
#define DV_REG_LOCKABLESCRATCHREGCTRL_9_LOCK_ENTRY_MASK                                             (0x1)
#endif
#define CLP_DV_REG_LOCKABLESCRATCHREG_0                                                             (0x1001c438)
#ifndef DV_REG_LOCKABLESCRATCHREG_0
#define DV_REG_LOCKABLESCRATCHREG_0                                                                 (0x438)
#endif
#define CLP_DV_REG_LOCKABLESCRATCHREG_1                                                             (0x1001c43c)
#ifndef DV_REG_LOCKABLESCRATCHREG_1
#define DV_REG_LOCKABLESCRATCHREG_1                                                                 (0x43c)
#endif
#define CLP_DV_REG_LOCKABLESCRATCHREG_2                                                             (0x1001c440)
#ifndef DV_REG_LOCKABLESCRATCHREG_2
#define DV_REG_LOCKABLESCRATCHREG_2                                                                 (0x440)
#endif
#define CLP_DV_REG_LOCKABLESCRATCHREG_3                                                             (0x1001c444)
#ifndef DV_REG_LOCKABLESCRATCHREG_3
#define DV_REG_LOCKABLESCRATCHREG_3                                                                 (0x444)
#endif
#define CLP_DV_REG_LOCKABLESCRATCHREG_4                                                             (0x1001c448)
#ifndef DV_REG_LOCKABLESCRATCHREG_4
#define DV_REG_LOCKABLESCRATCHREG_4                                                                 (0x448)
#endif
#define CLP_DV_REG_LOCKABLESCRATCHREG_5                                                             (0x1001c44c)
#ifndef DV_REG_LOCKABLESCRATCHREG_5
#define DV_REG_LOCKABLESCRATCHREG_5                                                                 (0x44c)
#endif
#define CLP_DV_REG_LOCKABLESCRATCHREG_6                                                             (0x1001c450)
#ifndef DV_REG_LOCKABLESCRATCHREG_6
#define DV_REG_LOCKABLESCRATCHREG_6                                                                 (0x450)
#endif
#define CLP_DV_REG_LOCKABLESCRATCHREG_7                                                             (0x1001c454)
#ifndef DV_REG_LOCKABLESCRATCHREG_7
#define DV_REG_LOCKABLESCRATCHREG_7                                                                 (0x454)
#endif
#define CLP_DV_REG_LOCKABLESCRATCHREG_8                                                             (0x1001c458)
#ifndef DV_REG_LOCKABLESCRATCHREG_8
#define DV_REG_LOCKABLESCRATCHREG_8                                                                 (0x458)
#endif
#define CLP_DV_REG_LOCKABLESCRATCHREG_9                                                             (0x1001c45c)
#ifndef DV_REG_LOCKABLESCRATCHREG_9
#define DV_REG_LOCKABLESCRATCHREG_9                                                                 (0x45c)
#endif
#define CLP_DV_REG_NONSTICKYGENERICSCRATCHREG_0                                                     (0x1001c460)
#ifndef DV_REG_NONSTICKYGENERICSCRATCHREG_0
#define DV_REG_NONSTICKYGENERICSCRATCHREG_0                                                         (0x460)
#endif
#define CLP_DV_REG_NONSTICKYGENERICSCRATCHREG_1                                                     (0x1001c464)
#ifndef DV_REG_NONSTICKYGENERICSCRATCHREG_1
#define DV_REG_NONSTICKYGENERICSCRATCHREG_1                                                         (0x464)
#endif
#define CLP_DV_REG_NONSTICKYGENERICSCRATCHREG_2                                                     (0x1001c468)
#ifndef DV_REG_NONSTICKYGENERICSCRATCHREG_2
#define DV_REG_NONSTICKYGENERICSCRATCHREG_2                                                         (0x468)
#endif
#define CLP_DV_REG_NONSTICKYGENERICSCRATCHREG_3                                                     (0x1001c46c)
#ifndef DV_REG_NONSTICKYGENERICSCRATCHREG_3
#define DV_REG_NONSTICKYGENERICSCRATCHREG_3                                                         (0x46c)
#endif
#define CLP_DV_REG_NONSTICKYGENERICSCRATCHREG_4                                                     (0x1001c470)
#ifndef DV_REG_NONSTICKYGENERICSCRATCHREG_4
#define DV_REG_NONSTICKYGENERICSCRATCHREG_4                                                         (0x470)
#endif
#define CLP_DV_REG_NONSTICKYGENERICSCRATCHREG_5                                                     (0x1001c474)
#ifndef DV_REG_NONSTICKYGENERICSCRATCHREG_5
#define DV_REG_NONSTICKYGENERICSCRATCHREG_5                                                         (0x474)
#endif
#define CLP_DV_REG_NONSTICKYGENERICSCRATCHREG_6                                                     (0x1001c478)
#ifndef DV_REG_NONSTICKYGENERICSCRATCHREG_6
#define DV_REG_NONSTICKYGENERICSCRATCHREG_6                                                         (0x478)
#endif
#define CLP_DV_REG_NONSTICKYGENERICSCRATCHREG_7                                                     (0x1001c47c)
#ifndef DV_REG_NONSTICKYGENERICSCRATCHREG_7
#define DV_REG_NONSTICKYGENERICSCRATCHREG_7                                                         (0x47c)
#endif
#define CLP_DV_REG_STICKYLOCKABLESCRATCHREGCTRL_0                                                   (0x1001c480)
#ifndef DV_REG_STICKYLOCKABLESCRATCHREGCTRL_0
#define DV_REG_STICKYLOCKABLESCRATCHREGCTRL_0                                                       (0x480)
#define DV_REG_STICKYLOCKABLESCRATCHREGCTRL_0_LOCK_ENTRY_LOW                                        (0)
#define DV_REG_STICKYLOCKABLESCRATCHREGCTRL_0_LOCK_ENTRY_MASK                                       (0x1)
#endif
#define CLP_DV_REG_STICKYLOCKABLESCRATCHREGCTRL_1                                                   (0x1001c484)
#ifndef DV_REG_STICKYLOCKABLESCRATCHREGCTRL_1
#define DV_REG_STICKYLOCKABLESCRATCHREGCTRL_1                                                       (0x484)
#define DV_REG_STICKYLOCKABLESCRATCHREGCTRL_1_LOCK_ENTRY_LOW                                        (0)
#define DV_REG_STICKYLOCKABLESCRATCHREGCTRL_1_LOCK_ENTRY_MASK                                       (0x1)
#endif
#define CLP_DV_REG_STICKYLOCKABLESCRATCHREGCTRL_2                                                   (0x1001c488)
#ifndef DV_REG_STICKYLOCKABLESCRATCHREGCTRL_2
#define DV_REG_STICKYLOCKABLESCRATCHREGCTRL_2                                                       (0x488)
#define DV_REG_STICKYLOCKABLESCRATCHREGCTRL_2_LOCK_ENTRY_LOW                                        (0)
#define DV_REG_STICKYLOCKABLESCRATCHREGCTRL_2_LOCK_ENTRY_MASK                                       (0x1)
#endif
#define CLP_DV_REG_STICKYLOCKABLESCRATCHREGCTRL_3                                                   (0x1001c48c)
#ifndef DV_REG_STICKYLOCKABLESCRATCHREGCTRL_3
#define DV_REG_STICKYLOCKABLESCRATCHREGCTRL_3                                                       (0x48c)
#define DV_REG_STICKYLOCKABLESCRATCHREGCTRL_3_LOCK_ENTRY_LOW                                        (0)
#define DV_REG_STICKYLOCKABLESCRATCHREGCTRL_3_LOCK_ENTRY_MASK                                       (0x1)
#endif
#define CLP_DV_REG_STICKYLOCKABLESCRATCHREGCTRL_4                                                   (0x1001c490)
#ifndef DV_REG_STICKYLOCKABLESCRATCHREGCTRL_4
#define DV_REG_STICKYLOCKABLESCRATCHREGCTRL_4                                                       (0x490)
#define DV_REG_STICKYLOCKABLESCRATCHREGCTRL_4_LOCK_ENTRY_LOW                                        (0)
#define DV_REG_STICKYLOCKABLESCRATCHREGCTRL_4_LOCK_ENTRY_MASK                                       (0x1)
#endif
#define CLP_DV_REG_STICKYLOCKABLESCRATCHREGCTRL_5                                                   (0x1001c494)
#ifndef DV_REG_STICKYLOCKABLESCRATCHREGCTRL_5
#define DV_REG_STICKYLOCKABLESCRATCHREGCTRL_5                                                       (0x494)
#define DV_REG_STICKYLOCKABLESCRATCHREGCTRL_5_LOCK_ENTRY_LOW                                        (0)
#define DV_REG_STICKYLOCKABLESCRATCHREGCTRL_5_LOCK_ENTRY_MASK                                       (0x1)
#endif
#define CLP_DV_REG_STICKYLOCKABLESCRATCHREGCTRL_6                                                   (0x1001c498)
#ifndef DV_REG_STICKYLOCKABLESCRATCHREGCTRL_6
#define DV_REG_STICKYLOCKABLESCRATCHREGCTRL_6                                                       (0x498)
#define DV_REG_STICKYLOCKABLESCRATCHREGCTRL_6_LOCK_ENTRY_LOW                                        (0)
#define DV_REG_STICKYLOCKABLESCRATCHREGCTRL_6_LOCK_ENTRY_MASK                                       (0x1)
#endif
#define CLP_DV_REG_STICKYLOCKABLESCRATCHREGCTRL_7                                                   (0x1001c49c)
#ifndef DV_REG_STICKYLOCKABLESCRATCHREGCTRL_7
#define DV_REG_STICKYLOCKABLESCRATCHREGCTRL_7                                                       (0x49c)
#define DV_REG_STICKYLOCKABLESCRATCHREGCTRL_7_LOCK_ENTRY_LOW                                        (0)
#define DV_REG_STICKYLOCKABLESCRATCHREGCTRL_7_LOCK_ENTRY_MASK                                       (0x1)
#endif
#define CLP_DV_REG_STICKYLOCKABLESCRATCHREG_0                                                       (0x1001c4a0)
#ifndef DV_REG_STICKYLOCKABLESCRATCHREG_0
#define DV_REG_STICKYLOCKABLESCRATCHREG_0                                                           (0x4a0)
#endif
#define CLP_DV_REG_STICKYLOCKABLESCRATCHREG_1                                                       (0x1001c4a4)
#ifndef DV_REG_STICKYLOCKABLESCRATCHREG_1
#define DV_REG_STICKYLOCKABLESCRATCHREG_1                                                           (0x4a4)
#endif
#define CLP_DV_REG_STICKYLOCKABLESCRATCHREG_2                                                       (0x1001c4a8)
#ifndef DV_REG_STICKYLOCKABLESCRATCHREG_2
#define DV_REG_STICKYLOCKABLESCRATCHREG_2                                                           (0x4a8)
#endif
#define CLP_DV_REG_STICKYLOCKABLESCRATCHREG_3                                                       (0x1001c4ac)
#ifndef DV_REG_STICKYLOCKABLESCRATCHREG_3
#define DV_REG_STICKYLOCKABLESCRATCHREG_3                                                           (0x4ac)
#endif
#define CLP_DV_REG_STICKYLOCKABLESCRATCHREG_4                                                       (0x1001c4b0)
#ifndef DV_REG_STICKYLOCKABLESCRATCHREG_4
#define DV_REG_STICKYLOCKABLESCRATCHREG_4                                                           (0x4b0)
#endif
#define CLP_DV_REG_STICKYLOCKABLESCRATCHREG_5                                                       (0x1001c4b4)
#ifndef DV_REG_STICKYLOCKABLESCRATCHREG_5
#define DV_REG_STICKYLOCKABLESCRATCHREG_5                                                           (0x4b4)
#endif
#define CLP_DV_REG_STICKYLOCKABLESCRATCHREG_6                                                       (0x1001c4b8)
#ifndef DV_REG_STICKYLOCKABLESCRATCHREG_6
#define DV_REG_STICKYLOCKABLESCRATCHREG_6                                                           (0x4b8)
#endif
#define CLP_DV_REG_STICKYLOCKABLESCRATCHREG_7                                                       (0x1001c4bc)
#ifndef DV_REG_STICKYLOCKABLESCRATCHREG_7
#define DV_REG_STICKYLOCKABLESCRATCHREG_7                                                           (0x4bc)
#endif
#define CLP_SHA512_REG_BASE_ADDR                                                                    (0x10020000)
#define CLP_SHA512_REG_SHA512_NAME_0                                                                (0x10020000)
#ifndef SHA512_REG_SHA512_NAME_0
#define SHA512_REG_SHA512_NAME_0                                                                    (0x0)
#endif
#define CLP_SHA512_REG_SHA512_NAME_1                                                                (0x10020004)
#ifndef SHA512_REG_SHA512_NAME_1
#define SHA512_REG_SHA512_NAME_1                                                                    (0x4)
#endif
#define CLP_SHA512_REG_SHA512_VERSION_0                                                             (0x10020008)
#ifndef SHA512_REG_SHA512_VERSION_0
#define SHA512_REG_SHA512_VERSION_0                                                                 (0x8)
#endif
#define CLP_SHA512_REG_SHA512_VERSION_1                                                             (0x1002000c)
#ifndef SHA512_REG_SHA512_VERSION_1
#define SHA512_REG_SHA512_VERSION_1                                                                 (0xc)
#endif
#define CLP_SHA512_REG_SHA512_CTRL                                                                  (0x10020010)
#ifndef SHA512_REG_SHA512_CTRL
#define SHA512_REG_SHA512_CTRL                                                                      (0x10)
#define SHA512_REG_SHA512_CTRL_INIT_LOW                                                             (0)
#define SHA512_REG_SHA512_CTRL_INIT_MASK                                                            (0x1)
#define SHA512_REG_SHA512_CTRL_NEXT_LOW                                                             (1)
#define SHA512_REG_SHA512_CTRL_NEXT_MASK                                                            (0x2)
#define SHA512_REG_SHA512_CTRL_MODE_LOW                                                             (2)
#define SHA512_REG_SHA512_CTRL_MODE_MASK                                                            (0xc)
#define SHA512_REG_SHA512_CTRL_ZEROIZE_LOW                                                          (4)
#define SHA512_REG_SHA512_CTRL_ZEROIZE_MASK                                                         (0x10)
#define SHA512_REG_SHA512_CTRL_LAST_LOW                                                             (5)
#define SHA512_REG_SHA512_CTRL_LAST_MASK                                                            (0x20)
#define SHA512_REG_SHA512_CTRL_RESTORE_LOW                                                          (6)
#define SHA512_REG_SHA512_CTRL_RESTORE_MASK                                                         (0x40)
#endif
#define CLP_SHA512_REG_SHA512_STATUS                                                                (0x10020018)
#ifndef SHA512_REG_SHA512_STATUS
#define SHA512_REG_SHA512_STATUS                                                                    (0x18)
#define SHA512_REG_SHA512_STATUS_READY_LOW                                                          (0)
#define SHA512_REG_SHA512_STATUS_READY_MASK                                                         (0x1)
#define SHA512_REG_SHA512_STATUS_VALID_LOW                                                          (1)
#define SHA512_REG_SHA512_STATUS_VALID_MASK                                                         (0x2)
#endif
#define CLP_SHA512_REG_SHA512_BLOCK_0                                                               (0x10020080)
#ifndef SHA512_REG_SHA512_BLOCK_0
#define SHA512_REG_SHA512_BLOCK_0                                                                   (0x80)
#endif
#define CLP_SHA512_REG_SHA512_BLOCK_1                                                               (0x10020084)
#ifndef SHA512_REG_SHA512_BLOCK_1
#define SHA512_REG_SHA512_BLOCK_1                                                                   (0x84)
#endif
#define CLP_SHA512_REG_SHA512_BLOCK_2                                                               (0x10020088)
#ifndef SHA512_REG_SHA512_BLOCK_2
#define SHA512_REG_SHA512_BLOCK_2                                                                   (0x88)
#endif
#define CLP_SHA512_REG_SHA512_BLOCK_3                                                               (0x1002008c)
#ifndef SHA512_REG_SHA512_BLOCK_3
#define SHA512_REG_SHA512_BLOCK_3                                                                   (0x8c)
#endif
#define CLP_SHA512_REG_SHA512_BLOCK_4                                                               (0x10020090)
#ifndef SHA512_REG_SHA512_BLOCK_4
#define SHA512_REG_SHA512_BLOCK_4                                                                   (0x90)
#endif
#define CLP_SHA512_REG_SHA512_BLOCK_5                                                               (0x10020094)
#ifndef SHA512_REG_SHA512_BLOCK_5
#define SHA512_REG_SHA512_BLOCK_5                                                                   (0x94)
#endif
#define CLP_SHA512_REG_SHA512_BLOCK_6                                                               (0x10020098)
#ifndef SHA512_REG_SHA512_BLOCK_6
#define SHA512_REG_SHA512_BLOCK_6                                                                   (0x98)
#endif
#define CLP_SHA512_REG_SHA512_BLOCK_7                                                               (0x1002009c)
#ifndef SHA512_REG_SHA512_BLOCK_7
#define SHA512_REG_SHA512_BLOCK_7                                                                   (0x9c)
#endif
#define CLP_SHA512_REG_SHA512_BLOCK_8                                                               (0x100200a0)
#ifndef SHA512_REG_SHA512_BLOCK_8
#define SHA512_REG_SHA512_BLOCK_8                                                                   (0xa0)
#endif
#define CLP_SHA512_REG_SHA512_BLOCK_9                                                               (0x100200a4)
#ifndef SHA512_REG_SHA512_BLOCK_9
#define SHA512_REG_SHA512_BLOCK_9                                                                   (0xa4)
#endif
#define CLP_SHA512_REG_SHA512_BLOCK_10                                                              (0x100200a8)
#ifndef SHA512_REG_SHA512_BLOCK_10
#define SHA512_REG_SHA512_BLOCK_10                                                                  (0xa8)
#endif
#define CLP_SHA512_REG_SHA512_BLOCK_11                                                              (0x100200ac)
#ifndef SHA512_REG_SHA512_BLOCK_11
#define SHA512_REG_SHA512_BLOCK_11                                                                  (0xac)
#endif
#define CLP_SHA512_REG_SHA512_BLOCK_12                                                              (0x100200b0)
#ifndef SHA512_REG_SHA512_BLOCK_12
#define SHA512_REG_SHA512_BLOCK_12                                                                  (0xb0)
#endif
#define CLP_SHA512_REG_SHA512_BLOCK_13                                                              (0x100200b4)
#ifndef SHA512_REG_SHA512_BLOCK_13
#define SHA512_REG_SHA512_BLOCK_13                                                                  (0xb4)
#endif
#define CLP_SHA512_REG_SHA512_BLOCK_14                                                              (0x100200b8)
#ifndef SHA512_REG_SHA512_BLOCK_14
#define SHA512_REG_SHA512_BLOCK_14                                                                  (0xb8)
#endif
#define CLP_SHA512_REG_SHA512_BLOCK_15                                                              (0x100200bc)
#ifndef SHA512_REG_SHA512_BLOCK_15
#define SHA512_REG_SHA512_BLOCK_15                                                                  (0xbc)
#endif
#define CLP_SHA512_REG_SHA512_BLOCK_16                                                              (0x100200c0)
#ifndef SHA512_REG_SHA512_BLOCK_16
#define SHA512_REG_SHA512_BLOCK_16                                                                  (0xc0)
#endif
#define CLP_SHA512_REG_SHA512_BLOCK_17                                                              (0x100200c4)
#ifndef SHA512_REG_SHA512_BLOCK_17
#define SHA512_REG_SHA512_BLOCK_17                                                                  (0xc4)
#endif
#define CLP_SHA512_REG_SHA512_BLOCK_18                                                              (0x100200c8)
#ifndef SHA512_REG_SHA512_BLOCK_18
#define SHA512_REG_SHA512_BLOCK_18                                                                  (0xc8)
#endif
#define CLP_SHA512_REG_SHA512_BLOCK_19                                                              (0x100200cc)
#ifndef SHA512_REG_SHA512_BLOCK_19
#define SHA512_REG_SHA512_BLOCK_19                                                                  (0xcc)
#endif
#define CLP_SHA512_REG_SHA512_BLOCK_20                                                              (0x100200d0)
#ifndef SHA512_REG_SHA512_BLOCK_20
#define SHA512_REG_SHA512_BLOCK_20                                                                  (0xd0)
#endif
#define CLP_SHA512_REG_SHA512_BLOCK_21                                                              (0x100200d4)
#ifndef SHA512_REG_SHA512_BLOCK_21
#define SHA512_REG_SHA512_BLOCK_21                                                                  (0xd4)
#endif
#define CLP_SHA512_REG_SHA512_BLOCK_22                                                              (0x100200d8)
#ifndef SHA512_REG_SHA512_BLOCK_22
#define SHA512_REG_SHA512_BLOCK_22                                                                  (0xd8)
#endif
#define CLP_SHA512_REG_SHA512_BLOCK_23                                                              (0x100200dc)
#ifndef SHA512_REG_SHA512_BLOCK_23
#define SHA512_REG_SHA512_BLOCK_23                                                                  (0xdc)
#endif
#define CLP_SHA512_REG_SHA512_BLOCK_24                                                              (0x100200e0)
#ifndef SHA512_REG_SHA512_BLOCK_24
#define SHA512_REG_SHA512_BLOCK_24                                                                  (0xe0)
#endif
#define CLP_SHA512_REG_SHA512_BLOCK_25                                                              (0x100200e4)
#ifndef SHA512_REG_SHA512_BLOCK_25
#define SHA512_REG_SHA512_BLOCK_25                                                                  (0xe4)
#endif
#define CLP_SHA512_REG_SHA512_BLOCK_26                                                              (0x100200e8)
#ifndef SHA512_REG_SHA512_BLOCK_26
#define SHA512_REG_SHA512_BLOCK_26                                                                  (0xe8)
#endif
#define CLP_SHA512_REG_SHA512_BLOCK_27                                                              (0x100200ec)
#ifndef SHA512_REG_SHA512_BLOCK_27
#define SHA512_REG_SHA512_BLOCK_27                                                                  (0xec)
#endif
#define CLP_SHA512_REG_SHA512_BLOCK_28                                                              (0x100200f0)
#ifndef SHA512_REG_SHA512_BLOCK_28
#define SHA512_REG_SHA512_BLOCK_28                                                                  (0xf0)
#endif
#define CLP_SHA512_REG_SHA512_BLOCK_29                                                              (0x100200f4)
#ifndef SHA512_REG_SHA512_BLOCK_29
#define SHA512_REG_SHA512_BLOCK_29                                                                  (0xf4)
#endif
#define CLP_SHA512_REG_SHA512_BLOCK_30                                                              (0x100200f8)
#ifndef SHA512_REG_SHA512_BLOCK_30
#define SHA512_REG_SHA512_BLOCK_30                                                                  (0xf8)
#endif
#define CLP_SHA512_REG_SHA512_BLOCK_31                                                              (0x100200fc)
#ifndef SHA512_REG_SHA512_BLOCK_31
#define SHA512_REG_SHA512_BLOCK_31                                                                  (0xfc)
#endif
#define CLP_SHA512_REG_SHA512_DIGEST_0                                                              (0x10020100)
#ifndef SHA512_REG_SHA512_DIGEST_0
#define SHA512_REG_SHA512_DIGEST_0                                                                  (0x100)
#endif
#define CLP_SHA512_REG_SHA512_DIGEST_1                                                              (0x10020104)
#ifndef SHA512_REG_SHA512_DIGEST_1
#define SHA512_REG_SHA512_DIGEST_1                                                                  (0x104)
#endif
#define CLP_SHA512_REG_SHA512_DIGEST_2                                                              (0x10020108)
#ifndef SHA512_REG_SHA512_DIGEST_2
#define SHA512_REG_SHA512_DIGEST_2                                                                  (0x108)
#endif
#define CLP_SHA512_REG_SHA512_DIGEST_3                                                              (0x1002010c)
#ifndef SHA512_REG_SHA512_DIGEST_3
#define SHA512_REG_SHA512_DIGEST_3                                                                  (0x10c)
#endif
#define CLP_SHA512_REG_SHA512_DIGEST_4                                                              (0x10020110)
#ifndef SHA512_REG_SHA512_DIGEST_4
#define SHA512_REG_SHA512_DIGEST_4                                                                  (0x110)
#endif
#define CLP_SHA512_REG_SHA512_DIGEST_5                                                              (0x10020114)
#ifndef SHA512_REG_SHA512_DIGEST_5
#define SHA512_REG_SHA512_DIGEST_5                                                                  (0x114)
#endif
#define CLP_SHA512_REG_SHA512_DIGEST_6                                                              (0x10020118)
#ifndef SHA512_REG_SHA512_DIGEST_6
#define SHA512_REG_SHA512_DIGEST_6                                                                  (0x118)
#endif
#define CLP_SHA512_REG_SHA512_DIGEST_7                                                              (0x1002011c)
#ifndef SHA512_REG_SHA512_DIGEST_7
#define SHA512_REG_SHA512_DIGEST_7                                                                  (0x11c)
#endif
#define CLP_SHA512_REG_SHA512_DIGEST_8                                                              (0x10020120)
#ifndef SHA512_REG_SHA512_DIGEST_8
#define SHA512_REG_SHA512_DIGEST_8                                                                  (0x120)
#endif
#define CLP_SHA512_REG_SHA512_DIGEST_9                                                              (0x10020124)
#ifndef SHA512_REG_SHA512_DIGEST_9
#define SHA512_REG_SHA512_DIGEST_9                                                                  (0x124)
#endif
#define CLP_SHA512_REG_SHA512_DIGEST_10                                                             (0x10020128)
#ifndef SHA512_REG_SHA512_DIGEST_10
#define SHA512_REG_SHA512_DIGEST_10                                                                 (0x128)
#endif
#define CLP_SHA512_REG_SHA512_DIGEST_11                                                             (0x1002012c)
#ifndef SHA512_REG_SHA512_DIGEST_11
#define SHA512_REG_SHA512_DIGEST_11                                                                 (0x12c)
#endif
#define CLP_SHA512_REG_SHA512_DIGEST_12                                                             (0x10020130)
#ifndef SHA512_REG_SHA512_DIGEST_12
#define SHA512_REG_SHA512_DIGEST_12                                                                 (0x130)
#endif
#define CLP_SHA512_REG_SHA512_DIGEST_13                                                             (0x10020134)
#ifndef SHA512_REG_SHA512_DIGEST_13
#define SHA512_REG_SHA512_DIGEST_13                                                                 (0x134)
#endif
#define CLP_SHA512_REG_SHA512_DIGEST_14                                                             (0x10020138)
#ifndef SHA512_REG_SHA512_DIGEST_14
#define SHA512_REG_SHA512_DIGEST_14                                                                 (0x138)
#endif
#define CLP_SHA512_REG_SHA512_DIGEST_15                                                             (0x1002013c)
#ifndef SHA512_REG_SHA512_DIGEST_15
#define SHA512_REG_SHA512_DIGEST_15                                                                 (0x13c)
#endif
#define CLP_SHA512_REG_SHA512_VAULT_RD_CTRL                                                         (0x10020600)
#ifndef SHA512_REG_SHA512_VAULT_RD_CTRL
#define SHA512_REG_SHA512_VAULT_RD_CTRL                                                             (0x600)
#define SHA512_REG_SHA512_VAULT_RD_CTRL_READ_EN_LOW                                                 (0)
#define SHA512_REG_SHA512_VAULT_RD_CTRL_READ_EN_MASK                                                (0x1)
#define SHA512_REG_SHA512_VAULT_RD_CTRL_READ_ENTRY_LOW                                              (1)
#define SHA512_REG_SHA512_VAULT_RD_CTRL_READ_ENTRY_MASK                                             (0x3e)
#define SHA512_REG_SHA512_VAULT_RD_CTRL_PCR_HASH_EXTEND_LOW                                         (6)
#define SHA512_REG_SHA512_VAULT_RD_CTRL_PCR_HASH_EXTEND_MASK                                        (0x40)
#define SHA512_REG_SHA512_VAULT_RD_CTRL_RSVD_LOW                                                    (7)
#define SHA512_REG_SHA512_VAULT_RD_CTRL_RSVD_MASK                                                   (0xffffff80)
#endif
#define CLP_SHA512_REG_SHA512_VAULT_RD_STATUS                                                       (0x10020604)
#ifndef SHA512_REG_SHA512_VAULT_RD_STATUS
#define SHA512_REG_SHA512_VAULT_RD_STATUS                                                           (0x604)
#define SHA512_REG_SHA512_VAULT_RD_STATUS_READY_LOW                                                 (0)
#define SHA512_REG_SHA512_VAULT_RD_STATUS_READY_MASK                                                (0x1)
#define SHA512_REG_SHA512_VAULT_RD_STATUS_VALID_LOW                                                 (1)
#define SHA512_REG_SHA512_VAULT_RD_STATUS_VALID_MASK                                                (0x2)
#define SHA512_REG_SHA512_VAULT_RD_STATUS_ERROR_LOW                                                 (2)
#define SHA512_REG_SHA512_VAULT_RD_STATUS_ERROR_MASK                                                (0x3fc)
#endif
#define CLP_SHA512_REG_SHA512_KV_WR_CTRL                                                            (0x10020608)
#ifndef SHA512_REG_SHA512_KV_WR_CTRL
#define SHA512_REG_SHA512_KV_WR_CTRL                                                                (0x608)
#define SHA512_REG_SHA512_KV_WR_CTRL_WRITE_EN_LOW                                                   (0)
#define SHA512_REG_SHA512_KV_WR_CTRL_WRITE_EN_MASK                                                  (0x1)
#define SHA512_REG_SHA512_KV_WR_CTRL_WRITE_ENTRY_LOW                                                (1)
#define SHA512_REG_SHA512_KV_WR_CTRL_WRITE_ENTRY_MASK                                               (0x3e)
#define SHA512_REG_SHA512_KV_WR_CTRL_HMAC_KEY_DEST_VALID_LOW                                        (6)
#define SHA512_REG_SHA512_KV_WR_CTRL_HMAC_KEY_DEST_VALID_MASK                                       (0x40)
#define SHA512_REG_SHA512_KV_WR_CTRL_HMAC_BLOCK_DEST_VALID_LOW                                      (7)
#define SHA512_REG_SHA512_KV_WR_CTRL_HMAC_BLOCK_DEST_VALID_MASK                                     (0x80)
#define SHA512_REG_SHA512_KV_WR_CTRL_MLDSA_SEED_DEST_VALID_LOW                                      (8)
#define SHA512_REG_SHA512_KV_WR_CTRL_MLDSA_SEED_DEST_VALID_MASK                                     (0x100)
#define SHA512_REG_SHA512_KV_WR_CTRL_ECC_PKEY_DEST_VALID_LOW                                        (9)
#define SHA512_REG_SHA512_KV_WR_CTRL_ECC_PKEY_DEST_VALID_MASK                                       (0x200)
#define SHA512_REG_SHA512_KV_WR_CTRL_ECC_SEED_DEST_VALID_LOW                                        (10)
#define SHA512_REG_SHA512_KV_WR_CTRL_ECC_SEED_DEST_VALID_MASK                                       (0x400)
#define SHA512_REG_SHA512_KV_WR_CTRL_AES_KEY_DEST_VALID_LOW                                         (11)
#define SHA512_REG_SHA512_KV_WR_CTRL_AES_KEY_DEST_VALID_MASK                                        (0x800)
#define SHA512_REG_SHA512_KV_WR_CTRL_MLKEM_SEED_DEST_VALID_LOW                                      (12)
#define SHA512_REG_SHA512_KV_WR_CTRL_MLKEM_SEED_DEST_VALID_MASK                                     (0x1000)
#define SHA512_REG_SHA512_KV_WR_CTRL_MLKEM_MSG_DEST_VALID_LOW                                       (13)
#define SHA512_REG_SHA512_KV_WR_CTRL_MLKEM_MSG_DEST_VALID_MASK                                      (0x2000)
#define SHA512_REG_SHA512_KV_WR_CTRL_RSVD_LOW                                                       (14)
#define SHA512_REG_SHA512_KV_WR_CTRL_RSVD_MASK                                                      (0xffffc000)
#endif
#define CLP_SHA512_REG_SHA512_KV_WR_STATUS                                                          (0x1002060c)
#ifndef SHA512_REG_SHA512_KV_WR_STATUS
#define SHA512_REG_SHA512_KV_WR_STATUS                                                              (0x60c)
#define SHA512_REG_SHA512_KV_WR_STATUS_READY_LOW                                                    (0)
#define SHA512_REG_SHA512_KV_WR_STATUS_READY_MASK                                                   (0x1)
#define SHA512_REG_SHA512_KV_WR_STATUS_VALID_LOW                                                    (1)
#define SHA512_REG_SHA512_KV_WR_STATUS_VALID_MASK                                                   (0x2)
#define SHA512_REG_SHA512_KV_WR_STATUS_ERROR_LOW                                                    (2)
#define SHA512_REG_SHA512_KV_WR_STATUS_ERROR_MASK                                                   (0x3fc)
#endif
#define CLP_SHA512_REG_SHA512_GEN_PCR_HASH_NONCE_0                                                  (0x10020610)
#ifndef SHA512_REG_SHA512_GEN_PCR_HASH_NONCE_0
#define SHA512_REG_SHA512_GEN_PCR_HASH_NONCE_0                                                      (0x610)
#endif
#define CLP_SHA512_REG_SHA512_GEN_PCR_HASH_NONCE_1                                                  (0x10020614)
#ifndef SHA512_REG_SHA512_GEN_PCR_HASH_NONCE_1
#define SHA512_REG_SHA512_GEN_PCR_HASH_NONCE_1                                                      (0x614)
#endif
#define CLP_SHA512_REG_SHA512_GEN_PCR_HASH_NONCE_2                                                  (0x10020618)
#ifndef SHA512_REG_SHA512_GEN_PCR_HASH_NONCE_2
#define SHA512_REG_SHA512_GEN_PCR_HASH_NONCE_2                                                      (0x618)
#endif
#define CLP_SHA512_REG_SHA512_GEN_PCR_HASH_NONCE_3                                                  (0x1002061c)
#ifndef SHA512_REG_SHA512_GEN_PCR_HASH_NONCE_3
#define SHA512_REG_SHA512_GEN_PCR_HASH_NONCE_3                                                      (0x61c)
#endif
#define CLP_SHA512_REG_SHA512_GEN_PCR_HASH_NONCE_4                                                  (0x10020620)
#ifndef SHA512_REG_SHA512_GEN_PCR_HASH_NONCE_4
#define SHA512_REG_SHA512_GEN_PCR_HASH_NONCE_4                                                      (0x620)
#endif
#define CLP_SHA512_REG_SHA512_GEN_PCR_HASH_NONCE_5                                                  (0x10020624)
#ifndef SHA512_REG_SHA512_GEN_PCR_HASH_NONCE_5
#define SHA512_REG_SHA512_GEN_PCR_HASH_NONCE_5                                                      (0x624)
#endif
#define CLP_SHA512_REG_SHA512_GEN_PCR_HASH_NONCE_6                                                  (0x10020628)
#ifndef SHA512_REG_SHA512_GEN_PCR_HASH_NONCE_6
#define SHA512_REG_SHA512_GEN_PCR_HASH_NONCE_6                                                      (0x628)
#endif
#define CLP_SHA512_REG_SHA512_GEN_PCR_HASH_NONCE_7                                                  (0x1002062c)
#ifndef SHA512_REG_SHA512_GEN_PCR_HASH_NONCE_7
#define SHA512_REG_SHA512_GEN_PCR_HASH_NONCE_7                                                      (0x62c)
#endif
#define CLP_SHA512_REG_SHA512_GEN_PCR_HASH_CTRL                                                     (0x10020630)
#ifndef SHA512_REG_SHA512_GEN_PCR_HASH_CTRL
#define SHA512_REG_SHA512_GEN_PCR_HASH_CTRL                                                         (0x630)
#define SHA512_REG_SHA512_GEN_PCR_HASH_CTRL_START_LOW                                               (0)
#define SHA512_REG_SHA512_GEN_PCR_HASH_CTRL_START_MASK                                              (0x1)
#endif
#define CLP_SHA512_REG_SHA512_GEN_PCR_HASH_STATUS                                                   (0x10020634)
#ifndef SHA512_REG_SHA512_GEN_PCR_HASH_STATUS
#define SHA512_REG_SHA512_GEN_PCR_HASH_STATUS                                                       (0x634)
#define SHA512_REG_SHA512_GEN_PCR_HASH_STATUS_READY_LOW                                             (0)
#define SHA512_REG_SHA512_GEN_PCR_HASH_STATUS_READY_MASK                                            (0x1)
#define SHA512_REG_SHA512_GEN_PCR_HASH_STATUS_VALID_LOW                                             (1)
#define SHA512_REG_SHA512_GEN_PCR_HASH_STATUS_VALID_MASK                                            (0x2)
#endif
#define CLP_SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_0                                                 (0x10020638)
#ifndef SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_0
#define SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_0                                                     (0x638)
#endif
#define CLP_SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_1                                                 (0x1002063c)
#ifndef SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_1
#define SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_1                                                     (0x63c)
#endif
#define CLP_SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_2                                                 (0x10020640)
#ifndef SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_2
#define SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_2                                                     (0x640)
#endif
#define CLP_SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_3                                                 (0x10020644)
#ifndef SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_3
#define SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_3                                                     (0x644)
#endif
#define CLP_SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_4                                                 (0x10020648)
#ifndef SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_4
#define SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_4                                                     (0x648)
#endif
#define CLP_SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_5                                                 (0x1002064c)
#ifndef SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_5
#define SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_5                                                     (0x64c)
#endif
#define CLP_SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_6                                                 (0x10020650)
#ifndef SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_6
#define SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_6                                                     (0x650)
#endif
#define CLP_SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_7                                                 (0x10020654)
#ifndef SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_7
#define SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_7                                                     (0x654)
#endif
#define CLP_SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_8                                                 (0x10020658)
#ifndef SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_8
#define SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_8                                                     (0x658)
#endif
#define CLP_SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_9                                                 (0x1002065c)
#ifndef SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_9
#define SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_9                                                     (0x65c)
#endif
#define CLP_SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_10                                                (0x10020660)
#ifndef SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_10
#define SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_10                                                    (0x660)
#endif
#define CLP_SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_11                                                (0x10020664)
#ifndef SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_11
#define SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_11                                                    (0x664)
#endif
#define CLP_SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_12                                                (0x10020668)
#ifndef SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_12
#define SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_12                                                    (0x668)
#endif
#define CLP_SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_13                                                (0x1002066c)
#ifndef SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_13
#define SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_13                                                    (0x66c)
#endif
#define CLP_SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_14                                                (0x10020670)
#ifndef SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_14
#define SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_14                                                    (0x670)
#endif
#define CLP_SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_15                                                (0x10020674)
#ifndef SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_15
#define SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_15                                                    (0x674)
#endif
#define CLP_SHA512_REG_INTR_BLOCK_RF_START                                                          (0x10020800)
#define CLP_SHA512_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R                                               (0x10020800)
#ifndef SHA512_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R
#define SHA512_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R                                                   (0x800)
#define SHA512_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_LOW                                      (0)
#define SHA512_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_MASK                                     (0x1)
#define SHA512_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_LOW                                      (1)
#define SHA512_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_MASK                                     (0x2)
#endif
#define CLP_SHA512_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R                                                (0x10020804)
#ifndef SHA512_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R
#define SHA512_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R                                                    (0x804)
#define SHA512_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR0_EN_LOW                                      (0)
#define SHA512_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR0_EN_MASK                                     (0x1)
#define SHA512_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR1_EN_LOW                                      (1)
#define SHA512_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR1_EN_MASK                                     (0x2)
#define SHA512_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR2_EN_LOW                                      (2)
#define SHA512_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR2_EN_MASK                                     (0x4)
#define SHA512_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR3_EN_LOW                                      (3)
#define SHA512_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR3_EN_MASK                                     (0x8)
#endif
#define CLP_SHA512_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R                                                (0x10020808)
#ifndef SHA512_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R
#define SHA512_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R                                                    (0x808)
#define SHA512_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_CMD_DONE_EN_LOW                              (0)
#define SHA512_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_CMD_DONE_EN_MASK                             (0x1)
#endif
#define CLP_SHA512_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R                                            (0x1002080c)
#ifndef SHA512_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R
#define SHA512_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R                                                (0x80c)
#define SHA512_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS_LOW                                    (0)
#define SHA512_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS_MASK                                   (0x1)
#endif
#define CLP_SHA512_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R                                            (0x10020810)
#ifndef SHA512_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R
#define SHA512_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R                                                (0x810)
#define SHA512_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS_LOW                                    (0)
#define SHA512_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS_MASK                                   (0x1)
#endif
#define CLP_SHA512_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R                                          (0x10020814)
#ifndef SHA512_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R
#define SHA512_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R                                              (0x814)
#define SHA512_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR0_STS_LOW                               (0)
#define SHA512_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR0_STS_MASK                              (0x1)
#define SHA512_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR1_STS_LOW                               (1)
#define SHA512_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR1_STS_MASK                              (0x2)
#define SHA512_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR2_STS_LOW                               (2)
#define SHA512_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR2_STS_MASK                              (0x4)
#define SHA512_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR3_STS_LOW                               (3)
#define SHA512_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR3_STS_MASK                              (0x8)
#endif
#define CLP_SHA512_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R                                          (0x10020818)
#ifndef SHA512_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R
#define SHA512_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R                                              (0x818)
#define SHA512_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_LOW                       (0)
#define SHA512_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK                      (0x1)
#endif
#define CLP_SHA512_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R                                              (0x1002081c)
#ifndef SHA512_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R
#define SHA512_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R                                                  (0x81c)
#define SHA512_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR0_TRIG_LOW                                  (0)
#define SHA512_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR0_TRIG_MASK                                 (0x1)
#define SHA512_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR1_TRIG_LOW                                  (1)
#define SHA512_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR1_TRIG_MASK                                 (0x2)
#define SHA512_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR2_TRIG_LOW                                  (2)
#define SHA512_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR2_TRIG_MASK                                 (0x4)
#define SHA512_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR3_TRIG_LOW                                  (3)
#define SHA512_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR3_TRIG_MASK                                 (0x8)
#endif
#define CLP_SHA512_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R                                              (0x10020820)
#ifndef SHA512_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R
#define SHA512_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R                                                  (0x820)
#define SHA512_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_DONE_TRIG_LOW                          (0)
#define SHA512_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_DONE_TRIG_MASK                         (0x1)
#endif
#define CLP_SHA512_REG_INTR_BLOCK_RF_ERROR0_INTR_COUNT_R                                            (0x10020900)
#ifndef SHA512_REG_INTR_BLOCK_RF_ERROR0_INTR_COUNT_R
#define SHA512_REG_INTR_BLOCK_RF_ERROR0_INTR_COUNT_R                                                (0x900)
#endif
#define CLP_SHA512_REG_INTR_BLOCK_RF_ERROR1_INTR_COUNT_R                                            (0x10020904)
#ifndef SHA512_REG_INTR_BLOCK_RF_ERROR1_INTR_COUNT_R
#define SHA512_REG_INTR_BLOCK_RF_ERROR1_INTR_COUNT_R                                                (0x904)
#endif
#define CLP_SHA512_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_R                                            (0x10020908)
#ifndef SHA512_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_R
#define SHA512_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_R                                                (0x908)
#endif
#define CLP_SHA512_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_R                                            (0x1002090c)
#ifndef SHA512_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_R
#define SHA512_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_R                                                (0x90c)
#endif
#define CLP_SHA512_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R                                    (0x10020980)
#ifndef SHA512_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R
#define SHA512_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R                                        (0x980)
#endif
#define CLP_SHA512_REG_INTR_BLOCK_RF_ERROR0_INTR_COUNT_INCR_R                                       (0x10020a00)
#ifndef SHA512_REG_INTR_BLOCK_RF_ERROR0_INTR_COUNT_INCR_R
#define SHA512_REG_INTR_BLOCK_RF_ERROR0_INTR_COUNT_INCR_R                                           (0xa00)
#define SHA512_REG_INTR_BLOCK_RF_ERROR0_INTR_COUNT_INCR_R_PULSE_LOW                                 (0)
#define SHA512_REG_INTR_BLOCK_RF_ERROR0_INTR_COUNT_INCR_R_PULSE_MASK                                (0x1)
#endif
#define CLP_SHA512_REG_INTR_BLOCK_RF_ERROR1_INTR_COUNT_INCR_R                                       (0x10020a04)
#ifndef SHA512_REG_INTR_BLOCK_RF_ERROR1_INTR_COUNT_INCR_R
#define SHA512_REG_INTR_BLOCK_RF_ERROR1_INTR_COUNT_INCR_R                                           (0xa04)
#define SHA512_REG_INTR_BLOCK_RF_ERROR1_INTR_COUNT_INCR_R_PULSE_LOW                                 (0)
#define SHA512_REG_INTR_BLOCK_RF_ERROR1_INTR_COUNT_INCR_R_PULSE_MASK                                (0x1)
#endif
#define CLP_SHA512_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R                                       (0x10020a08)
#ifndef SHA512_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R
#define SHA512_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R                                           (0xa08)
#define SHA512_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R_PULSE_LOW                                 (0)
#define SHA512_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R_PULSE_MASK                                (0x1)
#endif
#define CLP_SHA512_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R                                       (0x10020a0c)
#ifndef SHA512_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R
#define SHA512_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R                                           (0xa0c)
#define SHA512_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R_PULSE_LOW                                 (0)
#define SHA512_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R_PULSE_MASK                                (0x1)
#endif
#define CLP_SHA512_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R                               (0x10020a10)
#ifndef SHA512_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R
#define SHA512_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R                                   (0xa10)
#define SHA512_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R_PULSE_LOW                         (0)
#define SHA512_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R_PULSE_MASK                        (0x1)
#endif
#define CLP_SHA256_REG_BASE_ADDR                                                                    (0x10028000)
#define CLP_SHA256_REG_SHA256_NAME_0                                                                (0x10028000)
#ifndef SHA256_REG_SHA256_NAME_0
#define SHA256_REG_SHA256_NAME_0                                                                    (0x0)
#endif
#define CLP_SHA256_REG_SHA256_NAME_1                                                                (0x10028004)
#ifndef SHA256_REG_SHA256_NAME_1
#define SHA256_REG_SHA256_NAME_1                                                                    (0x4)
#endif
#define CLP_SHA256_REG_SHA256_VERSION_0                                                             (0x10028008)
#ifndef SHA256_REG_SHA256_VERSION_0
#define SHA256_REG_SHA256_VERSION_0                                                                 (0x8)
#endif
#define CLP_SHA256_REG_SHA256_VERSION_1                                                             (0x1002800c)
#ifndef SHA256_REG_SHA256_VERSION_1
#define SHA256_REG_SHA256_VERSION_1                                                                 (0xc)
#endif
#define CLP_SHA256_REG_SHA256_CTRL                                                                  (0x10028010)
#ifndef SHA256_REG_SHA256_CTRL
#define SHA256_REG_SHA256_CTRL                                                                      (0x10)
#define SHA256_REG_SHA256_CTRL_INIT_LOW                                                             (0)
#define SHA256_REG_SHA256_CTRL_INIT_MASK                                                            (0x1)
#define SHA256_REG_SHA256_CTRL_NEXT_LOW                                                             (1)
#define SHA256_REG_SHA256_CTRL_NEXT_MASK                                                            (0x2)
#define SHA256_REG_SHA256_CTRL_MODE_LOW                                                             (2)
#define SHA256_REG_SHA256_CTRL_MODE_MASK                                                            (0x4)
#define SHA256_REG_SHA256_CTRL_ZEROIZE_LOW                                                          (3)
#define SHA256_REG_SHA256_CTRL_ZEROIZE_MASK                                                         (0x8)
#define SHA256_REG_SHA256_CTRL_WNTZ_MODE_LOW                                                        (4)
#define SHA256_REG_SHA256_CTRL_WNTZ_MODE_MASK                                                       (0x10)
#define SHA256_REG_SHA256_CTRL_WNTZ_W_LOW                                                           (5)
#define SHA256_REG_SHA256_CTRL_WNTZ_W_MASK                                                          (0x1e0)
#define SHA256_REG_SHA256_CTRL_WNTZ_N_MODE_LOW                                                      (9)
#define SHA256_REG_SHA256_CTRL_WNTZ_N_MODE_MASK                                                     (0x200)
#endif
#define CLP_SHA256_REG_SHA256_STATUS                                                                (0x10028018)
#ifndef SHA256_REG_SHA256_STATUS
#define SHA256_REG_SHA256_STATUS                                                                    (0x18)
#define SHA256_REG_SHA256_STATUS_READY_LOW                                                          (0)
#define SHA256_REG_SHA256_STATUS_READY_MASK                                                         (0x1)
#define SHA256_REG_SHA256_STATUS_VALID_LOW                                                          (1)
#define SHA256_REG_SHA256_STATUS_VALID_MASK                                                         (0x2)
#define SHA256_REG_SHA256_STATUS_WNTZ_BUSY_LOW                                                      (2)
#define SHA256_REG_SHA256_STATUS_WNTZ_BUSY_MASK                                                     (0x4)
#endif
#define CLP_SHA256_REG_SHA256_BLOCK_0                                                               (0x10028080)
#ifndef SHA256_REG_SHA256_BLOCK_0
#define SHA256_REG_SHA256_BLOCK_0                                                                   (0x80)
#endif
#define CLP_SHA256_REG_SHA256_BLOCK_1                                                               (0x10028084)
#ifndef SHA256_REG_SHA256_BLOCK_1
#define SHA256_REG_SHA256_BLOCK_1                                                                   (0x84)
#endif
#define CLP_SHA256_REG_SHA256_BLOCK_2                                                               (0x10028088)
#ifndef SHA256_REG_SHA256_BLOCK_2
#define SHA256_REG_SHA256_BLOCK_2                                                                   (0x88)
#endif
#define CLP_SHA256_REG_SHA256_BLOCK_3                                                               (0x1002808c)
#ifndef SHA256_REG_SHA256_BLOCK_3
#define SHA256_REG_SHA256_BLOCK_3                                                                   (0x8c)
#endif
#define CLP_SHA256_REG_SHA256_BLOCK_4                                                               (0x10028090)
#ifndef SHA256_REG_SHA256_BLOCK_4
#define SHA256_REG_SHA256_BLOCK_4                                                                   (0x90)
#endif
#define CLP_SHA256_REG_SHA256_BLOCK_5                                                               (0x10028094)
#ifndef SHA256_REG_SHA256_BLOCK_5
#define SHA256_REG_SHA256_BLOCK_5                                                                   (0x94)
#endif
#define CLP_SHA256_REG_SHA256_BLOCK_6                                                               (0x10028098)
#ifndef SHA256_REG_SHA256_BLOCK_6
#define SHA256_REG_SHA256_BLOCK_6                                                                   (0x98)
#endif
#define CLP_SHA256_REG_SHA256_BLOCK_7                                                               (0x1002809c)
#ifndef SHA256_REG_SHA256_BLOCK_7
#define SHA256_REG_SHA256_BLOCK_7                                                                   (0x9c)
#endif
#define CLP_SHA256_REG_SHA256_BLOCK_8                                                               (0x100280a0)
#ifndef SHA256_REG_SHA256_BLOCK_8
#define SHA256_REG_SHA256_BLOCK_8                                                                   (0xa0)
#endif
#define CLP_SHA256_REG_SHA256_BLOCK_9                                                               (0x100280a4)
#ifndef SHA256_REG_SHA256_BLOCK_9
#define SHA256_REG_SHA256_BLOCK_9                                                                   (0xa4)
#endif
#define CLP_SHA256_REG_SHA256_BLOCK_10                                                              (0x100280a8)
#ifndef SHA256_REG_SHA256_BLOCK_10
#define SHA256_REG_SHA256_BLOCK_10                                                                  (0xa8)
#endif
#define CLP_SHA256_REG_SHA256_BLOCK_11                                                              (0x100280ac)
#ifndef SHA256_REG_SHA256_BLOCK_11
#define SHA256_REG_SHA256_BLOCK_11                                                                  (0xac)
#endif
#define CLP_SHA256_REG_SHA256_BLOCK_12                                                              (0x100280b0)
#ifndef SHA256_REG_SHA256_BLOCK_12
#define SHA256_REG_SHA256_BLOCK_12                                                                  (0xb0)
#endif
#define CLP_SHA256_REG_SHA256_BLOCK_13                                                              (0x100280b4)
#ifndef SHA256_REG_SHA256_BLOCK_13
#define SHA256_REG_SHA256_BLOCK_13                                                                  (0xb4)
#endif
#define CLP_SHA256_REG_SHA256_BLOCK_14                                                              (0x100280b8)
#ifndef SHA256_REG_SHA256_BLOCK_14
#define SHA256_REG_SHA256_BLOCK_14                                                                  (0xb8)
#endif
#define CLP_SHA256_REG_SHA256_BLOCK_15                                                              (0x100280bc)
#ifndef SHA256_REG_SHA256_BLOCK_15
#define SHA256_REG_SHA256_BLOCK_15                                                                  (0xbc)
#endif
#define CLP_SHA256_REG_SHA256_DIGEST_0                                                              (0x10028100)
#ifndef SHA256_REG_SHA256_DIGEST_0
#define SHA256_REG_SHA256_DIGEST_0                                                                  (0x100)
#endif
#define CLP_SHA256_REG_SHA256_DIGEST_1                                                              (0x10028104)
#ifndef SHA256_REG_SHA256_DIGEST_1
#define SHA256_REG_SHA256_DIGEST_1                                                                  (0x104)
#endif
#define CLP_SHA256_REG_SHA256_DIGEST_2                                                              (0x10028108)
#ifndef SHA256_REG_SHA256_DIGEST_2
#define SHA256_REG_SHA256_DIGEST_2                                                                  (0x108)
#endif
#define CLP_SHA256_REG_SHA256_DIGEST_3                                                              (0x1002810c)
#ifndef SHA256_REG_SHA256_DIGEST_3
#define SHA256_REG_SHA256_DIGEST_3                                                                  (0x10c)
#endif
#define CLP_SHA256_REG_SHA256_DIGEST_4                                                              (0x10028110)
#ifndef SHA256_REG_SHA256_DIGEST_4
#define SHA256_REG_SHA256_DIGEST_4                                                                  (0x110)
#endif
#define CLP_SHA256_REG_SHA256_DIGEST_5                                                              (0x10028114)
#ifndef SHA256_REG_SHA256_DIGEST_5
#define SHA256_REG_SHA256_DIGEST_5                                                                  (0x114)
#endif
#define CLP_SHA256_REG_SHA256_DIGEST_6                                                              (0x10028118)
#ifndef SHA256_REG_SHA256_DIGEST_6
#define SHA256_REG_SHA256_DIGEST_6                                                                  (0x118)
#endif
#define CLP_SHA256_REG_SHA256_DIGEST_7                                                              (0x1002811c)
#ifndef SHA256_REG_SHA256_DIGEST_7
#define SHA256_REG_SHA256_DIGEST_7                                                                  (0x11c)
#endif
#define CLP_SHA256_REG_INTR_BLOCK_RF_START                                                          (0x10028800)
#define CLP_SHA256_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R                                               (0x10028800)
#ifndef SHA256_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R
#define SHA256_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R                                                   (0x800)
#define SHA256_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_LOW                                      (0)
#define SHA256_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_MASK                                     (0x1)
#define SHA256_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_LOW                                      (1)
#define SHA256_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_MASK                                     (0x2)
#endif
#define CLP_SHA256_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R                                                (0x10028804)
#ifndef SHA256_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R
#define SHA256_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R                                                    (0x804)
#define SHA256_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR0_EN_LOW                                      (0)
#define SHA256_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR0_EN_MASK                                     (0x1)
#define SHA256_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR1_EN_LOW                                      (1)
#define SHA256_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR1_EN_MASK                                     (0x2)
#define SHA256_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR2_EN_LOW                                      (2)
#define SHA256_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR2_EN_MASK                                     (0x4)
#define SHA256_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR3_EN_LOW                                      (3)
#define SHA256_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR3_EN_MASK                                     (0x8)
#endif
#define CLP_SHA256_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R                                                (0x10028808)
#ifndef SHA256_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R
#define SHA256_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R                                                    (0x808)
#define SHA256_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_CMD_DONE_EN_LOW                              (0)
#define SHA256_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_CMD_DONE_EN_MASK                             (0x1)
#endif
#define CLP_SHA256_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R                                            (0x1002880c)
#ifndef SHA256_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R
#define SHA256_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R                                                (0x80c)
#define SHA256_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS_LOW                                    (0)
#define SHA256_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS_MASK                                   (0x1)
#endif
#define CLP_SHA256_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R                                            (0x10028810)
#ifndef SHA256_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R
#define SHA256_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R                                                (0x810)
#define SHA256_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS_LOW                                    (0)
#define SHA256_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS_MASK                                   (0x1)
#endif
#define CLP_SHA256_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R                                          (0x10028814)
#ifndef SHA256_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R
#define SHA256_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R                                              (0x814)
#define SHA256_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR0_STS_LOW                               (0)
#define SHA256_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR0_STS_MASK                              (0x1)
#define SHA256_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR1_STS_LOW                               (1)
#define SHA256_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR1_STS_MASK                              (0x2)
#define SHA256_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR2_STS_LOW                               (2)
#define SHA256_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR2_STS_MASK                              (0x4)
#define SHA256_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR3_STS_LOW                               (3)
#define SHA256_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR3_STS_MASK                              (0x8)
#endif
#define CLP_SHA256_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R                                          (0x10028818)
#ifndef SHA256_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R
#define SHA256_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R                                              (0x818)
#define SHA256_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_LOW                       (0)
#define SHA256_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK                      (0x1)
#endif
#define CLP_SHA256_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R                                              (0x1002881c)
#ifndef SHA256_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R
#define SHA256_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R                                                  (0x81c)
#define SHA256_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR0_TRIG_LOW                                  (0)
#define SHA256_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR0_TRIG_MASK                                 (0x1)
#define SHA256_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR1_TRIG_LOW                                  (1)
#define SHA256_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR1_TRIG_MASK                                 (0x2)
#define SHA256_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR2_TRIG_LOW                                  (2)
#define SHA256_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR2_TRIG_MASK                                 (0x4)
#define SHA256_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR3_TRIG_LOW                                  (3)
#define SHA256_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR3_TRIG_MASK                                 (0x8)
#endif
#define CLP_SHA256_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R                                              (0x10028820)
#ifndef SHA256_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R
#define SHA256_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R                                                  (0x820)
#define SHA256_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_DONE_TRIG_LOW                          (0)
#define SHA256_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_DONE_TRIG_MASK                         (0x1)
#endif
#define CLP_SHA256_REG_INTR_BLOCK_RF_ERROR0_INTR_COUNT_R                                            (0x10028900)
#ifndef SHA256_REG_INTR_BLOCK_RF_ERROR0_INTR_COUNT_R
#define SHA256_REG_INTR_BLOCK_RF_ERROR0_INTR_COUNT_R                                                (0x900)
#endif
#define CLP_SHA256_REG_INTR_BLOCK_RF_ERROR1_INTR_COUNT_R                                            (0x10028904)
#ifndef SHA256_REG_INTR_BLOCK_RF_ERROR1_INTR_COUNT_R
#define SHA256_REG_INTR_BLOCK_RF_ERROR1_INTR_COUNT_R                                                (0x904)
#endif
#define CLP_SHA256_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_R                                            (0x10028908)
#ifndef SHA256_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_R
#define SHA256_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_R                                                (0x908)
#endif
#define CLP_SHA256_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_R                                            (0x1002890c)
#ifndef SHA256_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_R
#define SHA256_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_R                                                (0x90c)
#endif
#define CLP_SHA256_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R                                    (0x10028980)
#ifndef SHA256_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R
#define SHA256_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R                                        (0x980)
#endif
#define CLP_SHA256_REG_INTR_BLOCK_RF_ERROR0_INTR_COUNT_INCR_R                                       (0x10028a00)
#ifndef SHA256_REG_INTR_BLOCK_RF_ERROR0_INTR_COUNT_INCR_R
#define SHA256_REG_INTR_BLOCK_RF_ERROR0_INTR_COUNT_INCR_R                                           (0xa00)
#define SHA256_REG_INTR_BLOCK_RF_ERROR0_INTR_COUNT_INCR_R_PULSE_LOW                                 (0)
#define SHA256_REG_INTR_BLOCK_RF_ERROR0_INTR_COUNT_INCR_R_PULSE_MASK                                (0x1)
#endif
#define CLP_SHA256_REG_INTR_BLOCK_RF_ERROR1_INTR_COUNT_INCR_R                                       (0x10028a04)
#ifndef SHA256_REG_INTR_BLOCK_RF_ERROR1_INTR_COUNT_INCR_R
#define SHA256_REG_INTR_BLOCK_RF_ERROR1_INTR_COUNT_INCR_R                                           (0xa04)
#define SHA256_REG_INTR_BLOCK_RF_ERROR1_INTR_COUNT_INCR_R_PULSE_LOW                                 (0)
#define SHA256_REG_INTR_BLOCK_RF_ERROR1_INTR_COUNT_INCR_R_PULSE_MASK                                (0x1)
#endif
#define CLP_SHA256_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R                                       (0x10028a08)
#ifndef SHA256_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R
#define SHA256_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R                                           (0xa08)
#define SHA256_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R_PULSE_LOW                                 (0)
#define SHA256_REG_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R_PULSE_MASK                                (0x1)
#endif
#define CLP_SHA256_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R                                       (0x10028a0c)
#ifndef SHA256_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R
#define SHA256_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R                                           (0xa0c)
#define SHA256_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R_PULSE_LOW                                 (0)
#define SHA256_REG_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R_PULSE_MASK                                (0x1)
#endif
#define CLP_SHA256_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R                               (0x10028a10)
#ifndef SHA256_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R
#define SHA256_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R                                   (0xa10)
#define SHA256_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R_PULSE_LOW                         (0)
#define SHA256_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R_PULSE_MASK                        (0x1)
#endif
#define CLP_ABR_REG_BASE_ADDR                                                                       (0x10030000)
#define CLP_ABR_REG_MLDSA_NAME_0                                                                    (0x10030000)
#ifndef ABR_REG_MLDSA_NAME_0
#define ABR_REG_MLDSA_NAME_0                                                                        (0x0)
#endif
#define CLP_ABR_REG_MLDSA_NAME_1                                                                    (0x10030004)
#ifndef ABR_REG_MLDSA_NAME_1
#define ABR_REG_MLDSA_NAME_1                                                                        (0x4)
#endif
#define CLP_ABR_REG_MLDSA_VERSION_0                                                                 (0x10030008)
#ifndef ABR_REG_MLDSA_VERSION_0
#define ABR_REG_MLDSA_VERSION_0                                                                     (0x8)
#endif
#define CLP_ABR_REG_MLDSA_VERSION_1                                                                 (0x1003000c)
#ifndef ABR_REG_MLDSA_VERSION_1
#define ABR_REG_MLDSA_VERSION_1                                                                     (0xc)
#endif
#define CLP_ABR_REG_MLDSA_CTRL                                                                      (0x10030010)
#ifndef ABR_REG_MLDSA_CTRL
#define ABR_REG_MLDSA_CTRL                                                                          (0x10)
#define ABR_REG_MLDSA_CTRL_CTRL_LOW                                                                 (0)
#define ABR_REG_MLDSA_CTRL_CTRL_MASK                                                                (0x7)
#define ABR_REG_MLDSA_CTRL_ZEROIZE_LOW                                                              (3)
#define ABR_REG_MLDSA_CTRL_ZEROIZE_MASK                                                             (0x8)
#define ABR_REG_MLDSA_CTRL_PCR_SIGN_LOW                                                             (4)
#define ABR_REG_MLDSA_CTRL_PCR_SIGN_MASK                                                            (0x10)
#define ABR_REG_MLDSA_CTRL_EXTERNAL_MU_LOW                                                          (5)
#define ABR_REG_MLDSA_CTRL_EXTERNAL_MU_MASK                                                         (0x20)
#define ABR_REG_MLDSA_CTRL_STREAM_MSG_LOW                                                           (6)
#define ABR_REG_MLDSA_CTRL_STREAM_MSG_MASK                                                          (0x40)
#endif
#define CLP_ABR_REG_MLDSA_STATUS                                                                    (0x10030014)
#ifndef ABR_REG_MLDSA_STATUS
#define ABR_REG_MLDSA_STATUS                                                                        (0x14)
#define ABR_REG_MLDSA_STATUS_READY_LOW                                                              (0)
#define ABR_REG_MLDSA_STATUS_READY_MASK                                                             (0x1)
#define ABR_REG_MLDSA_STATUS_VALID_LOW                                                              (1)
#define ABR_REG_MLDSA_STATUS_VALID_MASK                                                             (0x2)
#define ABR_REG_MLDSA_STATUS_MSG_STREAM_READY_LOW                                                   (2)
#define ABR_REG_MLDSA_STATUS_MSG_STREAM_READY_MASK                                                  (0x4)
#endif
#define CLP_ABR_REG_ABR_ENTROPY_0                                                                   (0x10030018)
#ifndef ABR_REG_ABR_ENTROPY_0
#define ABR_REG_ABR_ENTROPY_0                                                                       (0x18)
#endif
#define CLP_ABR_REG_ABR_ENTROPY_1                                                                   (0x1003001c)
#ifndef ABR_REG_ABR_ENTROPY_1
#define ABR_REG_ABR_ENTROPY_1                                                                       (0x1c)
#endif
#define CLP_ABR_REG_ABR_ENTROPY_2                                                                   (0x10030020)
#ifndef ABR_REG_ABR_ENTROPY_2
#define ABR_REG_ABR_ENTROPY_2                                                                       (0x20)
#endif
#define CLP_ABR_REG_ABR_ENTROPY_3                                                                   (0x10030024)
#ifndef ABR_REG_ABR_ENTROPY_3
#define ABR_REG_ABR_ENTROPY_3                                                                       (0x24)
#endif
#define CLP_ABR_REG_ABR_ENTROPY_4                                                                   (0x10030028)
#ifndef ABR_REG_ABR_ENTROPY_4
#define ABR_REG_ABR_ENTROPY_4                                                                       (0x28)
#endif
#define CLP_ABR_REG_ABR_ENTROPY_5                                                                   (0x1003002c)
#ifndef ABR_REG_ABR_ENTROPY_5
#define ABR_REG_ABR_ENTROPY_5                                                                       (0x2c)
#endif
#define CLP_ABR_REG_ABR_ENTROPY_6                                                                   (0x10030030)
#ifndef ABR_REG_ABR_ENTROPY_6
#define ABR_REG_ABR_ENTROPY_6                                                                       (0x30)
#endif
#define CLP_ABR_REG_ABR_ENTROPY_7                                                                   (0x10030034)
#ifndef ABR_REG_ABR_ENTROPY_7
#define ABR_REG_ABR_ENTROPY_7                                                                       (0x34)
#endif
#define CLP_ABR_REG_ABR_ENTROPY_8                                                                   (0x10030038)
#ifndef ABR_REG_ABR_ENTROPY_8
#define ABR_REG_ABR_ENTROPY_8                                                                       (0x38)
#endif
#define CLP_ABR_REG_ABR_ENTROPY_9                                                                   (0x1003003c)
#ifndef ABR_REG_ABR_ENTROPY_9
#define ABR_REG_ABR_ENTROPY_9                                                                       (0x3c)
#endif
#define CLP_ABR_REG_ABR_ENTROPY_10                                                                  (0x10030040)
#ifndef ABR_REG_ABR_ENTROPY_10
#define ABR_REG_ABR_ENTROPY_10                                                                      (0x40)
#endif
#define CLP_ABR_REG_ABR_ENTROPY_11                                                                  (0x10030044)
#ifndef ABR_REG_ABR_ENTROPY_11
#define ABR_REG_ABR_ENTROPY_11                                                                      (0x44)
#endif
#define CLP_ABR_REG_ABR_ENTROPY_12                                                                  (0x10030048)
#ifndef ABR_REG_ABR_ENTROPY_12
#define ABR_REG_ABR_ENTROPY_12                                                                      (0x48)
#endif
#define CLP_ABR_REG_ABR_ENTROPY_13                                                                  (0x1003004c)
#ifndef ABR_REG_ABR_ENTROPY_13
#define ABR_REG_ABR_ENTROPY_13                                                                      (0x4c)
#endif
#define CLP_ABR_REG_ABR_ENTROPY_14                                                                  (0x10030050)
#ifndef ABR_REG_ABR_ENTROPY_14
#define ABR_REG_ABR_ENTROPY_14                                                                      (0x50)
#endif
#define CLP_ABR_REG_ABR_ENTROPY_15                                                                  (0x10030054)
#ifndef ABR_REG_ABR_ENTROPY_15
#define ABR_REG_ABR_ENTROPY_15                                                                      (0x54)
#endif
#define CLP_ABR_REG_MLDSA_SEED_0                                                                    (0x10030058)
#ifndef ABR_REG_MLDSA_SEED_0
#define ABR_REG_MLDSA_SEED_0                                                                        (0x58)
#endif
#define CLP_ABR_REG_MLDSA_SEED_1                                                                    (0x1003005c)
#ifndef ABR_REG_MLDSA_SEED_1
#define ABR_REG_MLDSA_SEED_1                                                                        (0x5c)
#endif
#define CLP_ABR_REG_MLDSA_SEED_2                                                                    (0x10030060)
#ifndef ABR_REG_MLDSA_SEED_2
#define ABR_REG_MLDSA_SEED_2                                                                        (0x60)
#endif
#define CLP_ABR_REG_MLDSA_SEED_3                                                                    (0x10030064)
#ifndef ABR_REG_MLDSA_SEED_3
#define ABR_REG_MLDSA_SEED_3                                                                        (0x64)
#endif
#define CLP_ABR_REG_MLDSA_SEED_4                                                                    (0x10030068)
#ifndef ABR_REG_MLDSA_SEED_4
#define ABR_REG_MLDSA_SEED_4                                                                        (0x68)
#endif
#define CLP_ABR_REG_MLDSA_SEED_5                                                                    (0x1003006c)
#ifndef ABR_REG_MLDSA_SEED_5
#define ABR_REG_MLDSA_SEED_5                                                                        (0x6c)
#endif
#define CLP_ABR_REG_MLDSA_SEED_6                                                                    (0x10030070)
#ifndef ABR_REG_MLDSA_SEED_6
#define ABR_REG_MLDSA_SEED_6                                                                        (0x70)
#endif
#define CLP_ABR_REG_MLDSA_SEED_7                                                                    (0x10030074)
#ifndef ABR_REG_MLDSA_SEED_7
#define ABR_REG_MLDSA_SEED_7                                                                        (0x74)
#endif
#define CLP_ABR_REG_MLDSA_SIGN_RND_0                                                                (0x10030078)
#ifndef ABR_REG_MLDSA_SIGN_RND_0
#define ABR_REG_MLDSA_SIGN_RND_0                                                                    (0x78)
#endif
#define CLP_ABR_REG_MLDSA_SIGN_RND_1                                                                (0x1003007c)
#ifndef ABR_REG_MLDSA_SIGN_RND_1
#define ABR_REG_MLDSA_SIGN_RND_1                                                                    (0x7c)
#endif
#define CLP_ABR_REG_MLDSA_SIGN_RND_2                                                                (0x10030080)
#ifndef ABR_REG_MLDSA_SIGN_RND_2
#define ABR_REG_MLDSA_SIGN_RND_2                                                                    (0x80)
#endif
#define CLP_ABR_REG_MLDSA_SIGN_RND_3                                                                (0x10030084)
#ifndef ABR_REG_MLDSA_SIGN_RND_3
#define ABR_REG_MLDSA_SIGN_RND_3                                                                    (0x84)
#endif
#define CLP_ABR_REG_MLDSA_SIGN_RND_4                                                                (0x10030088)
#ifndef ABR_REG_MLDSA_SIGN_RND_4
#define ABR_REG_MLDSA_SIGN_RND_4                                                                    (0x88)
#endif
#define CLP_ABR_REG_MLDSA_SIGN_RND_5                                                                (0x1003008c)
#ifndef ABR_REG_MLDSA_SIGN_RND_5
#define ABR_REG_MLDSA_SIGN_RND_5                                                                    (0x8c)
#endif
#define CLP_ABR_REG_MLDSA_SIGN_RND_6                                                                (0x10030090)
#ifndef ABR_REG_MLDSA_SIGN_RND_6
#define ABR_REG_MLDSA_SIGN_RND_6                                                                    (0x90)
#endif
#define CLP_ABR_REG_MLDSA_SIGN_RND_7                                                                (0x10030094)
#ifndef ABR_REG_MLDSA_SIGN_RND_7
#define ABR_REG_MLDSA_SIGN_RND_7                                                                    (0x94)
#endif
#define CLP_ABR_REG_MLDSA_MSG_0                                                                     (0x10030098)
#ifndef ABR_REG_MLDSA_MSG_0
#define ABR_REG_MLDSA_MSG_0                                                                         (0x98)
#endif
#define CLP_ABR_REG_MLDSA_MSG_1                                                                     (0x1003009c)
#ifndef ABR_REG_MLDSA_MSG_1
#define ABR_REG_MLDSA_MSG_1                                                                         (0x9c)
#endif
#define CLP_ABR_REG_MLDSA_MSG_2                                                                     (0x100300a0)
#ifndef ABR_REG_MLDSA_MSG_2
#define ABR_REG_MLDSA_MSG_2                                                                         (0xa0)
#endif
#define CLP_ABR_REG_MLDSA_MSG_3                                                                     (0x100300a4)
#ifndef ABR_REG_MLDSA_MSG_3
#define ABR_REG_MLDSA_MSG_3                                                                         (0xa4)
#endif
#define CLP_ABR_REG_MLDSA_MSG_4                                                                     (0x100300a8)
#ifndef ABR_REG_MLDSA_MSG_4
#define ABR_REG_MLDSA_MSG_4                                                                         (0xa8)
#endif
#define CLP_ABR_REG_MLDSA_MSG_5                                                                     (0x100300ac)
#ifndef ABR_REG_MLDSA_MSG_5
#define ABR_REG_MLDSA_MSG_5                                                                         (0xac)
#endif
#define CLP_ABR_REG_MLDSA_MSG_6                                                                     (0x100300b0)
#ifndef ABR_REG_MLDSA_MSG_6
#define ABR_REG_MLDSA_MSG_6                                                                         (0xb0)
#endif
#define CLP_ABR_REG_MLDSA_MSG_7                                                                     (0x100300b4)
#ifndef ABR_REG_MLDSA_MSG_7
#define ABR_REG_MLDSA_MSG_7                                                                         (0xb4)
#endif
#define CLP_ABR_REG_MLDSA_MSG_8                                                                     (0x100300b8)
#ifndef ABR_REG_MLDSA_MSG_8
#define ABR_REG_MLDSA_MSG_8                                                                         (0xb8)
#endif
#define CLP_ABR_REG_MLDSA_MSG_9                                                                     (0x100300bc)
#ifndef ABR_REG_MLDSA_MSG_9
#define ABR_REG_MLDSA_MSG_9                                                                         (0xbc)
#endif
#define CLP_ABR_REG_MLDSA_MSG_10                                                                    (0x100300c0)
#ifndef ABR_REG_MLDSA_MSG_10
#define ABR_REG_MLDSA_MSG_10                                                                        (0xc0)
#endif
#define CLP_ABR_REG_MLDSA_MSG_11                                                                    (0x100300c4)
#ifndef ABR_REG_MLDSA_MSG_11
#define ABR_REG_MLDSA_MSG_11                                                                        (0xc4)
#endif
#define CLP_ABR_REG_MLDSA_MSG_12                                                                    (0x100300c8)
#ifndef ABR_REG_MLDSA_MSG_12
#define ABR_REG_MLDSA_MSG_12                                                                        (0xc8)
#endif
#define CLP_ABR_REG_MLDSA_MSG_13                                                                    (0x100300cc)
#ifndef ABR_REG_MLDSA_MSG_13
#define ABR_REG_MLDSA_MSG_13                                                                        (0xcc)
#endif
#define CLP_ABR_REG_MLDSA_MSG_14                                                                    (0x100300d0)
#ifndef ABR_REG_MLDSA_MSG_14
#define ABR_REG_MLDSA_MSG_14                                                                        (0xd0)
#endif
#define CLP_ABR_REG_MLDSA_MSG_15                                                                    (0x100300d4)
#ifndef ABR_REG_MLDSA_MSG_15
#define ABR_REG_MLDSA_MSG_15                                                                        (0xd4)
#endif
#define CLP_ABR_REG_MLDSA_VERIFY_RES_0                                                              (0x100300d8)
#ifndef ABR_REG_MLDSA_VERIFY_RES_0
#define ABR_REG_MLDSA_VERIFY_RES_0                                                                  (0xd8)
#endif
#define CLP_ABR_REG_MLDSA_VERIFY_RES_1                                                              (0x100300dc)
#ifndef ABR_REG_MLDSA_VERIFY_RES_1
#define ABR_REG_MLDSA_VERIFY_RES_1                                                                  (0xdc)
#endif
#define CLP_ABR_REG_MLDSA_VERIFY_RES_2                                                              (0x100300e0)
#ifndef ABR_REG_MLDSA_VERIFY_RES_2
#define ABR_REG_MLDSA_VERIFY_RES_2                                                                  (0xe0)
#endif
#define CLP_ABR_REG_MLDSA_VERIFY_RES_3                                                              (0x100300e4)
#ifndef ABR_REG_MLDSA_VERIFY_RES_3
#define ABR_REG_MLDSA_VERIFY_RES_3                                                                  (0xe4)
#endif
#define CLP_ABR_REG_MLDSA_VERIFY_RES_4                                                              (0x100300e8)
#ifndef ABR_REG_MLDSA_VERIFY_RES_4
#define ABR_REG_MLDSA_VERIFY_RES_4                                                                  (0xe8)
#endif
#define CLP_ABR_REG_MLDSA_VERIFY_RES_5                                                              (0x100300ec)
#ifndef ABR_REG_MLDSA_VERIFY_RES_5
#define ABR_REG_MLDSA_VERIFY_RES_5                                                                  (0xec)
#endif
#define CLP_ABR_REG_MLDSA_VERIFY_RES_6                                                              (0x100300f0)
#ifndef ABR_REG_MLDSA_VERIFY_RES_6
#define ABR_REG_MLDSA_VERIFY_RES_6                                                                  (0xf0)
#endif
#define CLP_ABR_REG_MLDSA_VERIFY_RES_7                                                              (0x100300f4)
#ifndef ABR_REG_MLDSA_VERIFY_RES_7
#define ABR_REG_MLDSA_VERIFY_RES_7                                                                  (0xf4)
#endif
#define CLP_ABR_REG_MLDSA_VERIFY_RES_8                                                              (0x100300f8)
#ifndef ABR_REG_MLDSA_VERIFY_RES_8
#define ABR_REG_MLDSA_VERIFY_RES_8                                                                  (0xf8)
#endif
#define CLP_ABR_REG_MLDSA_VERIFY_RES_9                                                              (0x100300fc)
#ifndef ABR_REG_MLDSA_VERIFY_RES_9
#define ABR_REG_MLDSA_VERIFY_RES_9                                                                  (0xfc)
#endif
#define CLP_ABR_REG_MLDSA_VERIFY_RES_10                                                             (0x10030100)
#ifndef ABR_REG_MLDSA_VERIFY_RES_10
#define ABR_REG_MLDSA_VERIFY_RES_10                                                                 (0x100)
#endif
#define CLP_ABR_REG_MLDSA_VERIFY_RES_11                                                             (0x10030104)
#ifndef ABR_REG_MLDSA_VERIFY_RES_11
#define ABR_REG_MLDSA_VERIFY_RES_11                                                                 (0x104)
#endif
#define CLP_ABR_REG_MLDSA_VERIFY_RES_12                                                             (0x10030108)
#ifndef ABR_REG_MLDSA_VERIFY_RES_12
#define ABR_REG_MLDSA_VERIFY_RES_12                                                                 (0x108)
#endif
#define CLP_ABR_REG_MLDSA_VERIFY_RES_13                                                             (0x1003010c)
#ifndef ABR_REG_MLDSA_VERIFY_RES_13
#define ABR_REG_MLDSA_VERIFY_RES_13                                                                 (0x10c)
#endif
#define CLP_ABR_REG_MLDSA_VERIFY_RES_14                                                             (0x10030110)
#ifndef ABR_REG_MLDSA_VERIFY_RES_14
#define ABR_REG_MLDSA_VERIFY_RES_14                                                                 (0x110)
#endif
#define CLP_ABR_REG_MLDSA_VERIFY_RES_15                                                             (0x10030114)
#ifndef ABR_REG_MLDSA_VERIFY_RES_15
#define ABR_REG_MLDSA_VERIFY_RES_15                                                                 (0x114)
#endif
#define CLP_ABR_REG_MLDSA_EXTERNAL_MU_0                                                             (0x10030118)
#ifndef ABR_REG_MLDSA_EXTERNAL_MU_0
#define ABR_REG_MLDSA_EXTERNAL_MU_0                                                                 (0x118)
#endif
#define CLP_ABR_REG_MLDSA_EXTERNAL_MU_1                                                             (0x1003011c)
#ifndef ABR_REG_MLDSA_EXTERNAL_MU_1
#define ABR_REG_MLDSA_EXTERNAL_MU_1                                                                 (0x11c)
#endif
#define CLP_ABR_REG_MLDSA_EXTERNAL_MU_2                                                             (0x10030120)
#ifndef ABR_REG_MLDSA_EXTERNAL_MU_2
#define ABR_REG_MLDSA_EXTERNAL_MU_2                                                                 (0x120)
#endif
#define CLP_ABR_REG_MLDSA_EXTERNAL_MU_3                                                             (0x10030124)
#ifndef ABR_REG_MLDSA_EXTERNAL_MU_3
#define ABR_REG_MLDSA_EXTERNAL_MU_3                                                                 (0x124)
#endif
#define CLP_ABR_REG_MLDSA_EXTERNAL_MU_4                                                             (0x10030128)
#ifndef ABR_REG_MLDSA_EXTERNAL_MU_4
#define ABR_REG_MLDSA_EXTERNAL_MU_4                                                                 (0x128)
#endif
#define CLP_ABR_REG_MLDSA_EXTERNAL_MU_5                                                             (0x1003012c)
#ifndef ABR_REG_MLDSA_EXTERNAL_MU_5
#define ABR_REG_MLDSA_EXTERNAL_MU_5                                                                 (0x12c)
#endif
#define CLP_ABR_REG_MLDSA_EXTERNAL_MU_6                                                             (0x10030130)
#ifndef ABR_REG_MLDSA_EXTERNAL_MU_6
#define ABR_REG_MLDSA_EXTERNAL_MU_6                                                                 (0x130)
#endif
#define CLP_ABR_REG_MLDSA_EXTERNAL_MU_7                                                             (0x10030134)
#ifndef ABR_REG_MLDSA_EXTERNAL_MU_7
#define ABR_REG_MLDSA_EXTERNAL_MU_7                                                                 (0x134)
#endif
#define CLP_ABR_REG_MLDSA_EXTERNAL_MU_8                                                             (0x10030138)
#ifndef ABR_REG_MLDSA_EXTERNAL_MU_8
#define ABR_REG_MLDSA_EXTERNAL_MU_8                                                                 (0x138)
#endif
#define CLP_ABR_REG_MLDSA_EXTERNAL_MU_9                                                             (0x1003013c)
#ifndef ABR_REG_MLDSA_EXTERNAL_MU_9
#define ABR_REG_MLDSA_EXTERNAL_MU_9                                                                 (0x13c)
#endif
#define CLP_ABR_REG_MLDSA_EXTERNAL_MU_10                                                            (0x10030140)
#ifndef ABR_REG_MLDSA_EXTERNAL_MU_10
#define ABR_REG_MLDSA_EXTERNAL_MU_10                                                                (0x140)
#endif
#define CLP_ABR_REG_MLDSA_EXTERNAL_MU_11                                                            (0x10030144)
#ifndef ABR_REG_MLDSA_EXTERNAL_MU_11
#define ABR_REG_MLDSA_EXTERNAL_MU_11                                                                (0x144)
#endif
#define CLP_ABR_REG_MLDSA_EXTERNAL_MU_12                                                            (0x10030148)
#ifndef ABR_REG_MLDSA_EXTERNAL_MU_12
#define ABR_REG_MLDSA_EXTERNAL_MU_12                                                                (0x148)
#endif
#define CLP_ABR_REG_MLDSA_EXTERNAL_MU_13                                                            (0x1003014c)
#ifndef ABR_REG_MLDSA_EXTERNAL_MU_13
#define ABR_REG_MLDSA_EXTERNAL_MU_13                                                                (0x14c)
#endif
#define CLP_ABR_REG_MLDSA_EXTERNAL_MU_14                                                            (0x10030150)
#ifndef ABR_REG_MLDSA_EXTERNAL_MU_14
#define ABR_REG_MLDSA_EXTERNAL_MU_14                                                                (0x150)
#endif
#define CLP_ABR_REG_MLDSA_EXTERNAL_MU_15                                                            (0x10030154)
#ifndef ABR_REG_MLDSA_EXTERNAL_MU_15
#define ABR_REG_MLDSA_EXTERNAL_MU_15                                                                (0x154)
#endif
#define CLP_ABR_REG_MLDSA_MSG_STROBE                                                                (0x10030158)
#ifndef ABR_REG_MLDSA_MSG_STROBE
#define ABR_REG_MLDSA_MSG_STROBE                                                                    (0x158)
#define ABR_REG_MLDSA_MSG_STROBE_STROBE_LOW                                                         (0)
#define ABR_REG_MLDSA_MSG_STROBE_STROBE_MASK                                                        (0xf)
#endif
#define CLP_ABR_REG_MLDSA_CTX_CONFIG                                                                (0x1003015c)
#ifndef ABR_REG_MLDSA_CTX_CONFIG
#define ABR_REG_MLDSA_CTX_CONFIG                                                                    (0x15c)
#define ABR_REG_MLDSA_CTX_CONFIG_CTX_SIZE_LOW                                                       (0)
#define ABR_REG_MLDSA_CTX_CONFIG_CTX_SIZE_MASK                                                      (0xff)
#endif
#define CLP_ABR_REG_MLDSA_CTX_0                                                                     (0x10030160)
#ifndef ABR_REG_MLDSA_CTX_0
#define ABR_REG_MLDSA_CTX_0                                                                         (0x160)
#endif
#define CLP_ABR_REG_MLDSA_CTX_1                                                                     (0x10030164)
#ifndef ABR_REG_MLDSA_CTX_1
#define ABR_REG_MLDSA_CTX_1                                                                         (0x164)
#endif
#define CLP_ABR_REG_MLDSA_CTX_2                                                                     (0x10030168)
#ifndef ABR_REG_MLDSA_CTX_2
#define ABR_REG_MLDSA_CTX_2                                                                         (0x168)
#endif
#define CLP_ABR_REG_MLDSA_CTX_3                                                                     (0x1003016c)
#ifndef ABR_REG_MLDSA_CTX_3
#define ABR_REG_MLDSA_CTX_3                                                                         (0x16c)
#endif
#define CLP_ABR_REG_MLDSA_CTX_4                                                                     (0x10030170)
#ifndef ABR_REG_MLDSA_CTX_4
#define ABR_REG_MLDSA_CTX_4                                                                         (0x170)
#endif
#define CLP_ABR_REG_MLDSA_CTX_5                                                                     (0x10030174)
#ifndef ABR_REG_MLDSA_CTX_5
#define ABR_REG_MLDSA_CTX_5                                                                         (0x174)
#endif
#define CLP_ABR_REG_MLDSA_CTX_6                                                                     (0x10030178)
#ifndef ABR_REG_MLDSA_CTX_6
#define ABR_REG_MLDSA_CTX_6                                                                         (0x178)
#endif
#define CLP_ABR_REG_MLDSA_CTX_7                                                                     (0x1003017c)
#ifndef ABR_REG_MLDSA_CTX_7
#define ABR_REG_MLDSA_CTX_7                                                                         (0x17c)
#endif
#define CLP_ABR_REG_MLDSA_CTX_8                                                                     (0x10030180)
#ifndef ABR_REG_MLDSA_CTX_8
#define ABR_REG_MLDSA_CTX_8                                                                         (0x180)
#endif
#define CLP_ABR_REG_MLDSA_CTX_9                                                                     (0x10030184)
#ifndef ABR_REG_MLDSA_CTX_9
#define ABR_REG_MLDSA_CTX_9                                                                         (0x184)
#endif
#define CLP_ABR_REG_MLDSA_CTX_10                                                                    (0x10030188)
#ifndef ABR_REG_MLDSA_CTX_10
#define ABR_REG_MLDSA_CTX_10                                                                        (0x188)
#endif
#define CLP_ABR_REG_MLDSA_CTX_11                                                                    (0x1003018c)
#ifndef ABR_REG_MLDSA_CTX_11
#define ABR_REG_MLDSA_CTX_11                                                                        (0x18c)
#endif
#define CLP_ABR_REG_MLDSA_CTX_12                                                                    (0x10030190)
#ifndef ABR_REG_MLDSA_CTX_12
#define ABR_REG_MLDSA_CTX_12                                                                        (0x190)
#endif
#define CLP_ABR_REG_MLDSA_CTX_13                                                                    (0x10030194)
#ifndef ABR_REG_MLDSA_CTX_13
#define ABR_REG_MLDSA_CTX_13                                                                        (0x194)
#endif
#define CLP_ABR_REG_MLDSA_CTX_14                                                                    (0x10030198)
#ifndef ABR_REG_MLDSA_CTX_14
#define ABR_REG_MLDSA_CTX_14                                                                        (0x198)
#endif
#define CLP_ABR_REG_MLDSA_CTX_15                                                                    (0x1003019c)
#ifndef ABR_REG_MLDSA_CTX_15
#define ABR_REG_MLDSA_CTX_15                                                                        (0x19c)
#endif
#define CLP_ABR_REG_MLDSA_CTX_16                                                                    (0x100301a0)
#ifndef ABR_REG_MLDSA_CTX_16
#define ABR_REG_MLDSA_CTX_16                                                                        (0x1a0)
#endif
#define CLP_ABR_REG_MLDSA_CTX_17                                                                    (0x100301a4)
#ifndef ABR_REG_MLDSA_CTX_17
#define ABR_REG_MLDSA_CTX_17                                                                        (0x1a4)
#endif
#define CLP_ABR_REG_MLDSA_CTX_18                                                                    (0x100301a8)
#ifndef ABR_REG_MLDSA_CTX_18
#define ABR_REG_MLDSA_CTX_18                                                                        (0x1a8)
#endif
#define CLP_ABR_REG_MLDSA_CTX_19                                                                    (0x100301ac)
#ifndef ABR_REG_MLDSA_CTX_19
#define ABR_REG_MLDSA_CTX_19                                                                        (0x1ac)
#endif
#define CLP_ABR_REG_MLDSA_CTX_20                                                                    (0x100301b0)
#ifndef ABR_REG_MLDSA_CTX_20
#define ABR_REG_MLDSA_CTX_20                                                                        (0x1b0)
#endif
#define CLP_ABR_REG_MLDSA_CTX_21                                                                    (0x100301b4)
#ifndef ABR_REG_MLDSA_CTX_21
#define ABR_REG_MLDSA_CTX_21                                                                        (0x1b4)
#endif
#define CLP_ABR_REG_MLDSA_CTX_22                                                                    (0x100301b8)
#ifndef ABR_REG_MLDSA_CTX_22
#define ABR_REG_MLDSA_CTX_22                                                                        (0x1b8)
#endif
#define CLP_ABR_REG_MLDSA_CTX_23                                                                    (0x100301bc)
#ifndef ABR_REG_MLDSA_CTX_23
#define ABR_REG_MLDSA_CTX_23                                                                        (0x1bc)
#endif
#define CLP_ABR_REG_MLDSA_CTX_24                                                                    (0x100301c0)
#ifndef ABR_REG_MLDSA_CTX_24
#define ABR_REG_MLDSA_CTX_24                                                                        (0x1c0)
#endif
#define CLP_ABR_REG_MLDSA_CTX_25                                                                    (0x100301c4)
#ifndef ABR_REG_MLDSA_CTX_25
#define ABR_REG_MLDSA_CTX_25                                                                        (0x1c4)
#endif
#define CLP_ABR_REG_MLDSA_CTX_26                                                                    (0x100301c8)
#ifndef ABR_REG_MLDSA_CTX_26
#define ABR_REG_MLDSA_CTX_26                                                                        (0x1c8)
#endif
#define CLP_ABR_REG_MLDSA_CTX_27                                                                    (0x100301cc)
#ifndef ABR_REG_MLDSA_CTX_27
#define ABR_REG_MLDSA_CTX_27                                                                        (0x1cc)
#endif
#define CLP_ABR_REG_MLDSA_CTX_28                                                                    (0x100301d0)
#ifndef ABR_REG_MLDSA_CTX_28
#define ABR_REG_MLDSA_CTX_28                                                                        (0x1d0)
#endif
#define CLP_ABR_REG_MLDSA_CTX_29                                                                    (0x100301d4)
#ifndef ABR_REG_MLDSA_CTX_29
#define ABR_REG_MLDSA_CTX_29                                                                        (0x1d4)
#endif
#define CLP_ABR_REG_MLDSA_CTX_30                                                                    (0x100301d8)
#ifndef ABR_REG_MLDSA_CTX_30
#define ABR_REG_MLDSA_CTX_30                                                                        (0x1d8)
#endif
#define CLP_ABR_REG_MLDSA_CTX_31                                                                    (0x100301dc)
#ifndef ABR_REG_MLDSA_CTX_31
#define ABR_REG_MLDSA_CTX_31                                                                        (0x1dc)
#endif
#define CLP_ABR_REG_MLDSA_CTX_32                                                                    (0x100301e0)
#ifndef ABR_REG_MLDSA_CTX_32
#define ABR_REG_MLDSA_CTX_32                                                                        (0x1e0)
#endif
#define CLP_ABR_REG_MLDSA_CTX_33                                                                    (0x100301e4)
#ifndef ABR_REG_MLDSA_CTX_33
#define ABR_REG_MLDSA_CTX_33                                                                        (0x1e4)
#endif
#define CLP_ABR_REG_MLDSA_CTX_34                                                                    (0x100301e8)
#ifndef ABR_REG_MLDSA_CTX_34
#define ABR_REG_MLDSA_CTX_34                                                                        (0x1e8)
#endif
#define CLP_ABR_REG_MLDSA_CTX_35                                                                    (0x100301ec)
#ifndef ABR_REG_MLDSA_CTX_35
#define ABR_REG_MLDSA_CTX_35                                                                        (0x1ec)
#endif
#define CLP_ABR_REG_MLDSA_CTX_36                                                                    (0x100301f0)
#ifndef ABR_REG_MLDSA_CTX_36
#define ABR_REG_MLDSA_CTX_36                                                                        (0x1f0)
#endif
#define CLP_ABR_REG_MLDSA_CTX_37                                                                    (0x100301f4)
#ifndef ABR_REG_MLDSA_CTX_37
#define ABR_REG_MLDSA_CTX_37                                                                        (0x1f4)
#endif
#define CLP_ABR_REG_MLDSA_CTX_38                                                                    (0x100301f8)
#ifndef ABR_REG_MLDSA_CTX_38
#define ABR_REG_MLDSA_CTX_38                                                                        (0x1f8)
#endif
#define CLP_ABR_REG_MLDSA_CTX_39                                                                    (0x100301fc)
#ifndef ABR_REG_MLDSA_CTX_39
#define ABR_REG_MLDSA_CTX_39                                                                        (0x1fc)
#endif
#define CLP_ABR_REG_MLDSA_CTX_40                                                                    (0x10030200)
#ifndef ABR_REG_MLDSA_CTX_40
#define ABR_REG_MLDSA_CTX_40                                                                        (0x200)
#endif
#define CLP_ABR_REG_MLDSA_CTX_41                                                                    (0x10030204)
#ifndef ABR_REG_MLDSA_CTX_41
#define ABR_REG_MLDSA_CTX_41                                                                        (0x204)
#endif
#define CLP_ABR_REG_MLDSA_CTX_42                                                                    (0x10030208)
#ifndef ABR_REG_MLDSA_CTX_42
#define ABR_REG_MLDSA_CTX_42                                                                        (0x208)
#endif
#define CLP_ABR_REG_MLDSA_CTX_43                                                                    (0x1003020c)
#ifndef ABR_REG_MLDSA_CTX_43
#define ABR_REG_MLDSA_CTX_43                                                                        (0x20c)
#endif
#define CLP_ABR_REG_MLDSA_CTX_44                                                                    (0x10030210)
#ifndef ABR_REG_MLDSA_CTX_44
#define ABR_REG_MLDSA_CTX_44                                                                        (0x210)
#endif
#define CLP_ABR_REG_MLDSA_CTX_45                                                                    (0x10030214)
#ifndef ABR_REG_MLDSA_CTX_45
#define ABR_REG_MLDSA_CTX_45                                                                        (0x214)
#endif
#define CLP_ABR_REG_MLDSA_CTX_46                                                                    (0x10030218)
#ifndef ABR_REG_MLDSA_CTX_46
#define ABR_REG_MLDSA_CTX_46                                                                        (0x218)
#endif
#define CLP_ABR_REG_MLDSA_CTX_47                                                                    (0x1003021c)
#ifndef ABR_REG_MLDSA_CTX_47
#define ABR_REG_MLDSA_CTX_47                                                                        (0x21c)
#endif
#define CLP_ABR_REG_MLDSA_CTX_48                                                                    (0x10030220)
#ifndef ABR_REG_MLDSA_CTX_48
#define ABR_REG_MLDSA_CTX_48                                                                        (0x220)
#endif
#define CLP_ABR_REG_MLDSA_CTX_49                                                                    (0x10030224)
#ifndef ABR_REG_MLDSA_CTX_49
#define ABR_REG_MLDSA_CTX_49                                                                        (0x224)
#endif
#define CLP_ABR_REG_MLDSA_CTX_50                                                                    (0x10030228)
#ifndef ABR_REG_MLDSA_CTX_50
#define ABR_REG_MLDSA_CTX_50                                                                        (0x228)
#endif
#define CLP_ABR_REG_MLDSA_CTX_51                                                                    (0x1003022c)
#ifndef ABR_REG_MLDSA_CTX_51
#define ABR_REG_MLDSA_CTX_51                                                                        (0x22c)
#endif
#define CLP_ABR_REG_MLDSA_CTX_52                                                                    (0x10030230)
#ifndef ABR_REG_MLDSA_CTX_52
#define ABR_REG_MLDSA_CTX_52                                                                        (0x230)
#endif
#define CLP_ABR_REG_MLDSA_CTX_53                                                                    (0x10030234)
#ifndef ABR_REG_MLDSA_CTX_53
#define ABR_REG_MLDSA_CTX_53                                                                        (0x234)
#endif
#define CLP_ABR_REG_MLDSA_CTX_54                                                                    (0x10030238)
#ifndef ABR_REG_MLDSA_CTX_54
#define ABR_REG_MLDSA_CTX_54                                                                        (0x238)
#endif
#define CLP_ABR_REG_MLDSA_CTX_55                                                                    (0x1003023c)
#ifndef ABR_REG_MLDSA_CTX_55
#define ABR_REG_MLDSA_CTX_55                                                                        (0x23c)
#endif
#define CLP_ABR_REG_MLDSA_CTX_56                                                                    (0x10030240)
#ifndef ABR_REG_MLDSA_CTX_56
#define ABR_REG_MLDSA_CTX_56                                                                        (0x240)
#endif
#define CLP_ABR_REG_MLDSA_CTX_57                                                                    (0x10030244)
#ifndef ABR_REG_MLDSA_CTX_57
#define ABR_REG_MLDSA_CTX_57                                                                        (0x244)
#endif
#define CLP_ABR_REG_MLDSA_CTX_58                                                                    (0x10030248)
#ifndef ABR_REG_MLDSA_CTX_58
#define ABR_REG_MLDSA_CTX_58                                                                        (0x248)
#endif
#define CLP_ABR_REG_MLDSA_CTX_59                                                                    (0x1003024c)
#ifndef ABR_REG_MLDSA_CTX_59
#define ABR_REG_MLDSA_CTX_59                                                                        (0x24c)
#endif
#define CLP_ABR_REG_MLDSA_CTX_60                                                                    (0x10030250)
#ifndef ABR_REG_MLDSA_CTX_60
#define ABR_REG_MLDSA_CTX_60                                                                        (0x250)
#endif
#define CLP_ABR_REG_MLDSA_CTX_61                                                                    (0x10030254)
#ifndef ABR_REG_MLDSA_CTX_61
#define ABR_REG_MLDSA_CTX_61                                                                        (0x254)
#endif
#define CLP_ABR_REG_MLDSA_CTX_62                                                                    (0x10030258)
#ifndef ABR_REG_MLDSA_CTX_62
#define ABR_REG_MLDSA_CTX_62                                                                        (0x258)
#endif
#define CLP_ABR_REG_MLDSA_CTX_63                                                                    (0x1003025c)
#ifndef ABR_REG_MLDSA_CTX_63
#define ABR_REG_MLDSA_CTX_63                                                                        (0x25c)
#endif
#define CLP_ABR_REG_MLDSA_PUBKEY_BASE_ADDR                                                          (0x10031000)
#define CLP_ABR_REG_MLDSA_PUBKEY_END_ADDR                                                           (0x10031a1f)
#define CLP_ABR_REG_MLDSA_SIGNATURE_BASE_ADDR                                                       (0x10032000)
#define CLP_ABR_REG_MLDSA_SIGNATURE_END_ADDR                                                        (0x10033213)
#define CLP_ABR_REG_MLDSA_PRIVKEY_OUT_BASE_ADDR                                                     (0x10034000)
#define CLP_ABR_REG_MLDSA_PRIVKEY_OUT_END_ADDR                                                      (0x1003531f)
#define CLP_ABR_REG_MLDSA_PRIVKEY_IN_BASE_ADDR                                                      (0x10036000)
#define CLP_ABR_REG_MLDSA_PRIVKEY_IN_END_ADDR                                                       (0x1003731f)
#define CLP_ABR_REG_KV_MLDSA_SEED_RD_CTRL                                                           (0x10037320)
#ifndef ABR_REG_KV_MLDSA_SEED_RD_CTRL
#define ABR_REG_KV_MLDSA_SEED_RD_CTRL                                                               (0x7320)
#define ABR_REG_KV_MLDSA_SEED_RD_CTRL_READ_EN_LOW                                                   (0)
#define ABR_REG_KV_MLDSA_SEED_RD_CTRL_READ_EN_MASK                                                  (0x1)
#define ABR_REG_KV_MLDSA_SEED_RD_CTRL_READ_ENTRY_LOW                                                (1)
#define ABR_REG_KV_MLDSA_SEED_RD_CTRL_READ_ENTRY_MASK                                               (0x3e)
#define ABR_REG_KV_MLDSA_SEED_RD_CTRL_PCR_HASH_EXTEND_LOW                                           (6)
#define ABR_REG_KV_MLDSA_SEED_RD_CTRL_PCR_HASH_EXTEND_MASK                                          (0x40)
#define ABR_REG_KV_MLDSA_SEED_RD_CTRL_RSVD_LOW                                                      (7)
#define ABR_REG_KV_MLDSA_SEED_RD_CTRL_RSVD_MASK                                                     (0xffffff80)
#endif
#define CLP_ABR_REG_KV_MLDSA_SEED_RD_STATUS                                                         (0x10037324)
#ifndef ABR_REG_KV_MLDSA_SEED_RD_STATUS
#define ABR_REG_KV_MLDSA_SEED_RD_STATUS                                                             (0x7324)
#define ABR_REG_KV_MLDSA_SEED_RD_STATUS_READY_LOW                                                   (0)
#define ABR_REG_KV_MLDSA_SEED_RD_STATUS_READY_MASK                                                  (0x1)
#define ABR_REG_KV_MLDSA_SEED_RD_STATUS_VALID_LOW                                                   (1)
#define ABR_REG_KV_MLDSA_SEED_RD_STATUS_VALID_MASK                                                  (0x2)
#define ABR_REG_KV_MLDSA_SEED_RD_STATUS_ERROR_LOW                                                   (2)
#define ABR_REG_KV_MLDSA_SEED_RD_STATUS_ERROR_MASK                                                  (0x3fc)
#endif
#define CLP_ABR_REG_MLKEM_NAME_0                                                                    (0x10038000)
#ifndef ABR_REG_MLKEM_NAME_0
#define ABR_REG_MLKEM_NAME_0                                                                        (0x8000)
#endif
#define CLP_ABR_REG_MLKEM_NAME_1                                                                    (0x10038004)
#ifndef ABR_REG_MLKEM_NAME_1
#define ABR_REG_MLKEM_NAME_1                                                                        (0x8004)
#endif
#define CLP_ABR_REG_MLKEM_VERSION_0                                                                 (0x10038008)
#ifndef ABR_REG_MLKEM_VERSION_0
#define ABR_REG_MLKEM_VERSION_0                                                                     (0x8008)
#endif
#define CLP_ABR_REG_MLKEM_VERSION_1                                                                 (0x1003800c)
#ifndef ABR_REG_MLKEM_VERSION_1
#define ABR_REG_MLKEM_VERSION_1                                                                     (0x800c)
#endif
#define CLP_ABR_REG_MLKEM_CTRL                                                                      (0x10038010)
#ifndef ABR_REG_MLKEM_CTRL
#define ABR_REG_MLKEM_CTRL                                                                          (0x8010)
#define ABR_REG_MLKEM_CTRL_CTRL_LOW                                                                 (0)
#define ABR_REG_MLKEM_CTRL_CTRL_MASK                                                                (0x7)
#define ABR_REG_MLKEM_CTRL_ZEROIZE_LOW                                                              (3)
#define ABR_REG_MLKEM_CTRL_ZEROIZE_MASK                                                             (0x8)
#endif
#define CLP_ABR_REG_MLKEM_STATUS                                                                    (0x10038014)
#ifndef ABR_REG_MLKEM_STATUS
#define ABR_REG_MLKEM_STATUS                                                                        (0x8014)
#define ABR_REG_MLKEM_STATUS_READY_LOW                                                              (0)
#define ABR_REG_MLKEM_STATUS_READY_MASK                                                             (0x1)
#define ABR_REG_MLKEM_STATUS_VALID_LOW                                                              (1)
#define ABR_REG_MLKEM_STATUS_VALID_MASK                                                             (0x2)
#endif
#define CLP_ABR_REG_MLKEM_SEED_D_0                                                                  (0x10038018)
#ifndef ABR_REG_MLKEM_SEED_D_0
#define ABR_REG_MLKEM_SEED_D_0                                                                      (0x8018)
#endif
#define CLP_ABR_REG_MLKEM_SEED_D_1                                                                  (0x1003801c)
#ifndef ABR_REG_MLKEM_SEED_D_1
#define ABR_REG_MLKEM_SEED_D_1                                                                      (0x801c)
#endif
#define CLP_ABR_REG_MLKEM_SEED_D_2                                                                  (0x10038020)
#ifndef ABR_REG_MLKEM_SEED_D_2
#define ABR_REG_MLKEM_SEED_D_2                                                                      (0x8020)
#endif
#define CLP_ABR_REG_MLKEM_SEED_D_3                                                                  (0x10038024)
#ifndef ABR_REG_MLKEM_SEED_D_3
#define ABR_REG_MLKEM_SEED_D_3                                                                      (0x8024)
#endif
#define CLP_ABR_REG_MLKEM_SEED_D_4                                                                  (0x10038028)
#ifndef ABR_REG_MLKEM_SEED_D_4
#define ABR_REG_MLKEM_SEED_D_4                                                                      (0x8028)
#endif
#define CLP_ABR_REG_MLKEM_SEED_D_5                                                                  (0x1003802c)
#ifndef ABR_REG_MLKEM_SEED_D_5
#define ABR_REG_MLKEM_SEED_D_5                                                                      (0x802c)
#endif
#define CLP_ABR_REG_MLKEM_SEED_D_6                                                                  (0x10038030)
#ifndef ABR_REG_MLKEM_SEED_D_6
#define ABR_REG_MLKEM_SEED_D_6                                                                      (0x8030)
#endif
#define CLP_ABR_REG_MLKEM_SEED_D_7                                                                  (0x10038034)
#ifndef ABR_REG_MLKEM_SEED_D_7
#define ABR_REG_MLKEM_SEED_D_7                                                                      (0x8034)
#endif
#define CLP_ABR_REG_MLKEM_SEED_Z_0                                                                  (0x10038038)
#ifndef ABR_REG_MLKEM_SEED_Z_0
#define ABR_REG_MLKEM_SEED_Z_0                                                                      (0x8038)
#endif
#define CLP_ABR_REG_MLKEM_SEED_Z_1                                                                  (0x1003803c)
#ifndef ABR_REG_MLKEM_SEED_Z_1
#define ABR_REG_MLKEM_SEED_Z_1                                                                      (0x803c)
#endif
#define CLP_ABR_REG_MLKEM_SEED_Z_2                                                                  (0x10038040)
#ifndef ABR_REG_MLKEM_SEED_Z_2
#define ABR_REG_MLKEM_SEED_Z_2                                                                      (0x8040)
#endif
#define CLP_ABR_REG_MLKEM_SEED_Z_3                                                                  (0x10038044)
#ifndef ABR_REG_MLKEM_SEED_Z_3
#define ABR_REG_MLKEM_SEED_Z_3                                                                      (0x8044)
#endif
#define CLP_ABR_REG_MLKEM_SEED_Z_4                                                                  (0x10038048)
#ifndef ABR_REG_MLKEM_SEED_Z_4
#define ABR_REG_MLKEM_SEED_Z_4                                                                      (0x8048)
#endif
#define CLP_ABR_REG_MLKEM_SEED_Z_5                                                                  (0x1003804c)
#ifndef ABR_REG_MLKEM_SEED_Z_5
#define ABR_REG_MLKEM_SEED_Z_5                                                                      (0x804c)
#endif
#define CLP_ABR_REG_MLKEM_SEED_Z_6                                                                  (0x10038050)
#ifndef ABR_REG_MLKEM_SEED_Z_6
#define ABR_REG_MLKEM_SEED_Z_6                                                                      (0x8050)
#endif
#define CLP_ABR_REG_MLKEM_SEED_Z_7                                                                  (0x10038054)
#ifndef ABR_REG_MLKEM_SEED_Z_7
#define ABR_REG_MLKEM_SEED_Z_7                                                                      (0x8054)
#endif
#define CLP_ABR_REG_MLKEM_SHARED_KEY_0                                                              (0x10038058)
#ifndef ABR_REG_MLKEM_SHARED_KEY_0
#define ABR_REG_MLKEM_SHARED_KEY_0                                                                  (0x8058)
#endif
#define CLP_ABR_REG_MLKEM_SHARED_KEY_1                                                              (0x1003805c)
#ifndef ABR_REG_MLKEM_SHARED_KEY_1
#define ABR_REG_MLKEM_SHARED_KEY_1                                                                  (0x805c)
#endif
#define CLP_ABR_REG_MLKEM_SHARED_KEY_2                                                              (0x10038060)
#ifndef ABR_REG_MLKEM_SHARED_KEY_2
#define ABR_REG_MLKEM_SHARED_KEY_2                                                                  (0x8060)
#endif
#define CLP_ABR_REG_MLKEM_SHARED_KEY_3                                                              (0x10038064)
#ifndef ABR_REG_MLKEM_SHARED_KEY_3
#define ABR_REG_MLKEM_SHARED_KEY_3                                                                  (0x8064)
#endif
#define CLP_ABR_REG_MLKEM_SHARED_KEY_4                                                              (0x10038068)
#ifndef ABR_REG_MLKEM_SHARED_KEY_4
#define ABR_REG_MLKEM_SHARED_KEY_4                                                                  (0x8068)
#endif
#define CLP_ABR_REG_MLKEM_SHARED_KEY_5                                                              (0x1003806c)
#ifndef ABR_REG_MLKEM_SHARED_KEY_5
#define ABR_REG_MLKEM_SHARED_KEY_5                                                                  (0x806c)
#endif
#define CLP_ABR_REG_MLKEM_SHARED_KEY_6                                                              (0x10038070)
#ifndef ABR_REG_MLKEM_SHARED_KEY_6
#define ABR_REG_MLKEM_SHARED_KEY_6                                                                  (0x8070)
#endif
#define CLP_ABR_REG_MLKEM_SHARED_KEY_7                                                              (0x10038074)
#ifndef ABR_REG_MLKEM_SHARED_KEY_7
#define ABR_REG_MLKEM_SHARED_KEY_7                                                                  (0x8074)
#endif
#define CLP_ABR_REG_MLKEM_MSG_BASE_ADDR                                                             (0x10038080)
#define CLP_ABR_REG_MLKEM_MSG_END_ADDR                                                              (0x1003809f)
#define CLP_ABR_REG_MLKEM_DECAPS_KEY_BASE_ADDR                                                      (0x10039000)
#define CLP_ABR_REG_MLKEM_DECAPS_KEY_END_ADDR                                                       (0x10039c5f)
#define CLP_ABR_REG_MLKEM_ENCAPS_KEY_BASE_ADDR                                                      (0x1003a000)
#define CLP_ABR_REG_MLKEM_ENCAPS_KEY_END_ADDR                                                       (0x1003a61f)
#define CLP_ABR_REG_MLKEM_CIPHERTEXT_BASE_ADDR                                                      (0x1003a800)
#define CLP_ABR_REG_MLKEM_CIPHERTEXT_END_ADDR                                                       (0x1003ae1f)
#define CLP_ABR_REG_KV_MLKEM_SEED_RD_CTRL                                                           (0x1003ae20)
#ifndef ABR_REG_KV_MLKEM_SEED_RD_CTRL
#define ABR_REG_KV_MLKEM_SEED_RD_CTRL                                                               (0xae20)
#define ABR_REG_KV_MLKEM_SEED_RD_CTRL_READ_EN_LOW                                                   (0)
#define ABR_REG_KV_MLKEM_SEED_RD_CTRL_READ_EN_MASK                                                  (0x1)
#define ABR_REG_KV_MLKEM_SEED_RD_CTRL_READ_ENTRY_LOW                                                (1)
#define ABR_REG_KV_MLKEM_SEED_RD_CTRL_READ_ENTRY_MASK                                               (0x3e)
#define ABR_REG_KV_MLKEM_SEED_RD_CTRL_PCR_HASH_EXTEND_LOW                                           (6)
#define ABR_REG_KV_MLKEM_SEED_RD_CTRL_PCR_HASH_EXTEND_MASK                                          (0x40)
#define ABR_REG_KV_MLKEM_SEED_RD_CTRL_RSVD_LOW                                                      (7)
#define ABR_REG_KV_MLKEM_SEED_RD_CTRL_RSVD_MASK                                                     (0xffffff80)
#endif
#define CLP_ABR_REG_KV_MLKEM_SEED_RD_STATUS                                                         (0x1003ae24)
#ifndef ABR_REG_KV_MLKEM_SEED_RD_STATUS
#define ABR_REG_KV_MLKEM_SEED_RD_STATUS                                                             (0xae24)
#define ABR_REG_KV_MLKEM_SEED_RD_STATUS_READY_LOW                                                   (0)
#define ABR_REG_KV_MLKEM_SEED_RD_STATUS_READY_MASK                                                  (0x1)
#define ABR_REG_KV_MLKEM_SEED_RD_STATUS_VALID_LOW                                                   (1)
#define ABR_REG_KV_MLKEM_SEED_RD_STATUS_VALID_MASK                                                  (0x2)
#define ABR_REG_KV_MLKEM_SEED_RD_STATUS_ERROR_LOW                                                   (2)
#define ABR_REG_KV_MLKEM_SEED_RD_STATUS_ERROR_MASK                                                  (0x3fc)
#endif
#define CLP_ABR_REG_KV_MLKEM_MSG_RD_CTRL                                                            (0x1003ae28)
#ifndef ABR_REG_KV_MLKEM_MSG_RD_CTRL
#define ABR_REG_KV_MLKEM_MSG_RD_CTRL                                                                (0xae28)
#define ABR_REG_KV_MLKEM_MSG_RD_CTRL_READ_EN_LOW                                                    (0)
#define ABR_REG_KV_MLKEM_MSG_RD_CTRL_READ_EN_MASK                                                   (0x1)
#define ABR_REG_KV_MLKEM_MSG_RD_CTRL_READ_ENTRY_LOW                                                 (1)
#define ABR_REG_KV_MLKEM_MSG_RD_CTRL_READ_ENTRY_MASK                                                (0x3e)
#define ABR_REG_KV_MLKEM_MSG_RD_CTRL_PCR_HASH_EXTEND_LOW                                            (6)
#define ABR_REG_KV_MLKEM_MSG_RD_CTRL_PCR_HASH_EXTEND_MASK                                           (0x40)
#define ABR_REG_KV_MLKEM_MSG_RD_CTRL_RSVD_LOW                                                       (7)
#define ABR_REG_KV_MLKEM_MSG_RD_CTRL_RSVD_MASK                                                      (0xffffff80)
#endif
#define CLP_ABR_REG_KV_MLKEM_MSG_RD_STATUS                                                          (0x1003ae2c)
#ifndef ABR_REG_KV_MLKEM_MSG_RD_STATUS
#define ABR_REG_KV_MLKEM_MSG_RD_STATUS                                                              (0xae2c)
#define ABR_REG_KV_MLKEM_MSG_RD_STATUS_READY_LOW                                                    (0)
#define ABR_REG_KV_MLKEM_MSG_RD_STATUS_READY_MASK                                                   (0x1)
#define ABR_REG_KV_MLKEM_MSG_RD_STATUS_VALID_LOW                                                    (1)
#define ABR_REG_KV_MLKEM_MSG_RD_STATUS_VALID_MASK                                                   (0x2)
#define ABR_REG_KV_MLKEM_MSG_RD_STATUS_ERROR_LOW                                                    (2)
#define ABR_REG_KV_MLKEM_MSG_RD_STATUS_ERROR_MASK                                                   (0x3fc)
#endif
#define CLP_ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL                                                      (0x1003ae30)
#ifndef ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL
#define ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL                                                          (0xae30)
#define ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_WRITE_EN_LOW                                             (0)
#define ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_WRITE_EN_MASK                                            (0x1)
#define ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_WRITE_ENTRY_LOW                                          (1)
#define ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_WRITE_ENTRY_MASK                                         (0x3e)
#define ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_HMAC_KEY_DEST_VALID_LOW                                  (6)
#define ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_HMAC_KEY_DEST_VALID_MASK                                 (0x40)
#define ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_HMAC_BLOCK_DEST_VALID_LOW                                (7)
#define ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_HMAC_BLOCK_DEST_VALID_MASK                               (0x80)
#define ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_MLDSA_SEED_DEST_VALID_LOW                                (8)
#define ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_MLDSA_SEED_DEST_VALID_MASK                               (0x100)
#define ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_ECC_PKEY_DEST_VALID_LOW                                  (9)
#define ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_ECC_PKEY_DEST_VALID_MASK                                 (0x200)
#define ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_ECC_SEED_DEST_VALID_LOW                                  (10)
#define ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_ECC_SEED_DEST_VALID_MASK                                 (0x400)
#define ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_AES_KEY_DEST_VALID_LOW                                   (11)
#define ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_AES_KEY_DEST_VALID_MASK                                  (0x800)
#define ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_MLKEM_SEED_DEST_VALID_LOW                                (12)
#define ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_MLKEM_SEED_DEST_VALID_MASK                               (0x1000)
#define ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_MLKEM_MSG_DEST_VALID_LOW                                 (13)
#define ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_MLKEM_MSG_DEST_VALID_MASK                                (0x2000)
#define ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_RSVD_LOW                                                 (14)
#define ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_RSVD_MASK                                                (0xffffc000)
#endif
#define CLP_ABR_REG_KV_MLKEM_SHAREDKEY_WR_STATUS                                                    (0x1003ae34)
#ifndef ABR_REG_KV_MLKEM_SHAREDKEY_WR_STATUS
#define ABR_REG_KV_MLKEM_SHAREDKEY_WR_STATUS                                                        (0xae34)
#define ABR_REG_KV_MLKEM_SHAREDKEY_WR_STATUS_READY_LOW                                              (0)
#define ABR_REG_KV_MLKEM_SHAREDKEY_WR_STATUS_READY_MASK                                             (0x1)
#define ABR_REG_KV_MLKEM_SHAREDKEY_WR_STATUS_VALID_LOW                                              (1)
#define ABR_REG_KV_MLKEM_SHAREDKEY_WR_STATUS_VALID_MASK                                             (0x2)
#define ABR_REG_KV_MLKEM_SHAREDKEY_WR_STATUS_ERROR_LOW                                              (2)
#define ABR_REG_KV_MLKEM_SHAREDKEY_WR_STATUS_ERROR_MASK                                             (0x3fc)
#endif
#define CLP_ABR_REG_INTR_BLOCK_RF_START                                                             (0x1003b000)
#define CLP_ABR_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R                                                  (0x1003b000)
#ifndef ABR_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R
#define ABR_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R                                                      (0xb000)
#define ABR_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_LOW                                         (0)
#define ABR_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_MASK                                        (0x1)
#define ABR_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_LOW                                         (1)
#define ABR_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_MASK                                        (0x2)
#endif
#define CLP_ABR_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R                                                   (0x1003b004)
#ifndef ABR_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R
#define ABR_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R                                                       (0xb004)
#define ABR_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_INTERNAL_EN_LOW                                 (0)
#define ABR_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_INTERNAL_EN_MASK                                (0x1)
#endif
#define CLP_ABR_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R                                                   (0x1003b008)
#ifndef ABR_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R
#define ABR_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R                                                       (0xb008)
#define ABR_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_CMD_DONE_EN_LOW                                 (0)
#define ABR_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_CMD_DONE_EN_MASK                                (0x1)
#endif
#define CLP_ABR_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R                                               (0x1003b00c)
#ifndef ABR_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R
#define ABR_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R                                                   (0xb00c)
#define ABR_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS_LOW                                       (0)
#define ABR_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS_MASK                                      (0x1)
#endif
#define CLP_ABR_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R                                               (0x1003b010)
#ifndef ABR_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R
#define ABR_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R                                                   (0xb010)
#define ABR_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS_LOW                                       (0)
#define ABR_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS_MASK                                      (0x1)
#endif
#define CLP_ABR_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R                                             (0x1003b014)
#ifndef ABR_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R
#define ABR_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R                                                 (0xb014)
#define ABR_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_INTERNAL_STS_LOW                          (0)
#define ABR_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_INTERNAL_STS_MASK                         (0x1)
#endif
#define CLP_ABR_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R                                             (0x1003b018)
#ifndef ABR_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R
#define ABR_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R                                                 (0xb018)
#define ABR_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_LOW                          (0)
#define ABR_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK                         (0x1)
#endif
#define CLP_ABR_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R                                                 (0x1003b01c)
#ifndef ABR_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R
#define ABR_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R                                                     (0xb01c)
#define ABR_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_INTERNAL_TRIG_LOW                             (0)
#define ABR_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_INTERNAL_TRIG_MASK                            (0x1)
#endif
#define CLP_ABR_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R                                                 (0x1003b020)
#ifndef ABR_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R
#define ABR_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R                                                     (0xb020)
#define ABR_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_DONE_TRIG_LOW                             (0)
#define ABR_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_DONE_TRIG_MASK                            (0x1)
#endif
#define CLP_ABR_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_R                                       (0x1003b100)
#ifndef ABR_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_R
#define ABR_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_R                                           (0xb100)
#endif
#define CLP_ABR_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R                                       (0x1003b180)
#ifndef ABR_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R
#define ABR_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R                                           (0xb180)
#endif
#define CLP_ABR_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R                                  (0x1003b200)
#ifndef ABR_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R
#define ABR_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R                                      (0xb200)
#define ABR_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R_PULSE_LOW                            (0)
#define ABR_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R_PULSE_MASK                           (0x1)
#endif
#define CLP_ABR_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R                                  (0x1003b204)
#ifndef ABR_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R
#define ABR_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R                                      (0xb204)
#define ABR_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R_PULSE_LOW                            (0)
#define ABR_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R_PULSE_MASK                           (0x1)
#endif
#define CLP_SHA3_REG_BASE_ADDR                                                                      (0x10040000)
#define CLP_CSRNG_REG_BASE_ADDR                                                                     (0x20002000)
#define CLP_CSRNG_REG_INTERRUPT_STATE                                                               (0x20002000)
#ifndef CSRNG_REG_INTERRUPT_STATE
#define CSRNG_REG_INTERRUPT_STATE                                                                   (0x0)
#define CSRNG_REG_INTERRUPT_STATE_CS_CMD_REQ_DONE_LOW                                               (0)
#define CSRNG_REG_INTERRUPT_STATE_CS_CMD_REQ_DONE_MASK                                              (0x1)
#define CSRNG_REG_INTERRUPT_STATE_CS_ENTROPY_REQ_LOW                                                (1)
#define CSRNG_REG_INTERRUPT_STATE_CS_ENTROPY_REQ_MASK                                               (0x2)
#define CSRNG_REG_INTERRUPT_STATE_CS_HW_INST_EXC_LOW                                                (2)
#define CSRNG_REG_INTERRUPT_STATE_CS_HW_INST_EXC_MASK                                               (0x4)
#define CSRNG_REG_INTERRUPT_STATE_CS_FATAL_ERR_LOW                                                  (3)
#define CSRNG_REG_INTERRUPT_STATE_CS_FATAL_ERR_MASK                                                 (0x8)
#endif
#define CLP_CSRNG_REG_INTERRUPT_ENABLE                                                              (0x20002004)
#ifndef CSRNG_REG_INTERRUPT_ENABLE
#define CSRNG_REG_INTERRUPT_ENABLE                                                                  (0x4)
#define CSRNG_REG_INTERRUPT_ENABLE_CS_CMD_REQ_DONE_LOW                                              (0)
#define CSRNG_REG_INTERRUPT_ENABLE_CS_CMD_REQ_DONE_MASK                                             (0x1)
#define CSRNG_REG_INTERRUPT_ENABLE_CS_ENTROPY_REQ_LOW                                               (1)
#define CSRNG_REG_INTERRUPT_ENABLE_CS_ENTROPY_REQ_MASK                                              (0x2)
#define CSRNG_REG_INTERRUPT_ENABLE_CS_HW_INST_EXC_LOW                                               (2)
#define CSRNG_REG_INTERRUPT_ENABLE_CS_HW_INST_EXC_MASK                                              (0x4)
#define CSRNG_REG_INTERRUPT_ENABLE_CS_FATAL_ERR_LOW                                                 (3)
#define CSRNG_REG_INTERRUPT_ENABLE_CS_FATAL_ERR_MASK                                                (0x8)
#endif
#define CLP_CSRNG_REG_INTERRUPT_TEST                                                                (0x20002008)
#ifndef CSRNG_REG_INTERRUPT_TEST
#define CSRNG_REG_INTERRUPT_TEST                                                                    (0x8)
#define CSRNG_REG_INTERRUPT_TEST_CS_CMD_REQ_DONE_LOW                                                (0)
#define CSRNG_REG_INTERRUPT_TEST_CS_CMD_REQ_DONE_MASK                                               (0x1)
#define CSRNG_REG_INTERRUPT_TEST_CS_ENTROPY_REQ_LOW                                                 (1)
#define CSRNG_REG_INTERRUPT_TEST_CS_ENTROPY_REQ_MASK                                                (0x2)
#define CSRNG_REG_INTERRUPT_TEST_CS_HW_INST_EXC_LOW                                                 (2)
#define CSRNG_REG_INTERRUPT_TEST_CS_HW_INST_EXC_MASK                                                (0x4)
#define CSRNG_REG_INTERRUPT_TEST_CS_FATAL_ERR_LOW                                                   (3)
#define CSRNG_REG_INTERRUPT_TEST_CS_FATAL_ERR_MASK                                                  (0x8)
#endif
#define CLP_CSRNG_REG_ALERT_TEST                                                                    (0x2000200c)
#ifndef CSRNG_REG_ALERT_TEST
#define CSRNG_REG_ALERT_TEST                                                                        (0xc)
#define CSRNG_REG_ALERT_TEST_RECOV_ALERT_LOW                                                        (0)
#define CSRNG_REG_ALERT_TEST_RECOV_ALERT_MASK                                                       (0x1)
#define CSRNG_REG_ALERT_TEST_FATAL_ALERT_LOW                                                        (1)
#define CSRNG_REG_ALERT_TEST_FATAL_ALERT_MASK                                                       (0x2)
#endif
#define CLP_CSRNG_REG_REGWEN                                                                        (0x20002010)
#ifndef CSRNG_REG_REGWEN
#define CSRNG_REG_REGWEN                                                                            (0x10)
#define CSRNG_REG_REGWEN_REGWEN_LOW                                                                 (0)
#define CSRNG_REG_REGWEN_REGWEN_MASK                                                                (0x1)
#endif
#define CLP_CSRNG_REG_CTRL                                                                          (0x20002014)
#ifndef CSRNG_REG_CTRL
#define CSRNG_REG_CTRL                                                                              (0x14)
#define CSRNG_REG_CTRL_ENABLE_LOW                                                                   (0)
#define CSRNG_REG_CTRL_ENABLE_MASK                                                                  (0xf)
#define CSRNG_REG_CTRL_SW_APP_ENABLE_LOW                                                            (4)
#define CSRNG_REG_CTRL_SW_APP_ENABLE_MASK                                                           (0xf0)
#define CSRNG_REG_CTRL_READ_INT_STATE_LOW                                                           (8)
#define CSRNG_REG_CTRL_READ_INT_STATE_MASK                                                          (0xf00)
#define CSRNG_REG_CTRL_FIPS_FORCE_ENABLE_LOW                                                        (12)
#define CSRNG_REG_CTRL_FIPS_FORCE_ENABLE_MASK                                                       (0xf000)
#endif
#define CLP_CSRNG_REG_CMD_REQ                                                                       (0x20002018)
#ifndef CSRNG_REG_CMD_REQ
#define CSRNG_REG_CMD_REQ                                                                           (0x18)
#define CSRNG_REG_CMD_REQ_ACMD_LOW                                                                  (0)
#define CSRNG_REG_CMD_REQ_ACMD_MASK                                                                 (0xf)
#define CSRNG_REG_CMD_REQ_CLEN_LOW                                                                  (4)
#define CSRNG_REG_CMD_REQ_CLEN_MASK                                                                 (0xf0)
#define CSRNG_REG_CMD_REQ_FLAG0_LOW                                                                 (8)
#define CSRNG_REG_CMD_REQ_FLAG0_MASK                                                                (0xf00)
#define CSRNG_REG_CMD_REQ_GLEN_LOW                                                                  (12)
#define CSRNG_REG_CMD_REQ_GLEN_MASK                                                                 (0x1fff000)
#endif
#define CLP_CSRNG_REG_RESEED_INTERVAL                                                               (0x2000201c)
#ifndef CSRNG_REG_RESEED_INTERVAL
#define CSRNG_REG_RESEED_INTERVAL                                                                   (0x1c)
#endif
#define CLP_CSRNG_REG_RESEED_COUNTER_0                                                              (0x20002020)
#ifndef CSRNG_REG_RESEED_COUNTER_0
#define CSRNG_REG_RESEED_COUNTER_0                                                                  (0x20)
#endif
#define CLP_CSRNG_REG_RESEED_COUNTER_1                                                              (0x20002024)
#ifndef CSRNG_REG_RESEED_COUNTER_1
#define CSRNG_REG_RESEED_COUNTER_1                                                                  (0x24)
#endif
#define CLP_CSRNG_REG_RESEED_COUNTER_2                                                              (0x20002028)
#ifndef CSRNG_REG_RESEED_COUNTER_2
#define CSRNG_REG_RESEED_COUNTER_2                                                                  (0x28)
#endif
#define CLP_CSRNG_REG_SW_CMD_STS                                                                    (0x2000202c)
#ifndef CSRNG_REG_SW_CMD_STS
#define CSRNG_REG_SW_CMD_STS                                                                        (0x2c)
#define CSRNG_REG_SW_CMD_STS_CMD_RDY_LOW                                                            (1)
#define CSRNG_REG_SW_CMD_STS_CMD_RDY_MASK                                                           (0x2)
#define CSRNG_REG_SW_CMD_STS_CMD_ACK_LOW                                                            (2)
#define CSRNG_REG_SW_CMD_STS_CMD_ACK_MASK                                                           (0x4)
#define CSRNG_REG_SW_CMD_STS_CMD_STS_LOW                                                            (3)
#define CSRNG_REG_SW_CMD_STS_CMD_STS_MASK                                                           (0x38)
#endif
#define CLP_CSRNG_REG_GENBITS_VLD                                                                   (0x20002030)
#ifndef CSRNG_REG_GENBITS_VLD
#define CSRNG_REG_GENBITS_VLD                                                                       (0x30)
#define CSRNG_REG_GENBITS_VLD_GENBITS_VLD_LOW                                                       (0)
#define CSRNG_REG_GENBITS_VLD_GENBITS_VLD_MASK                                                      (0x1)
#define CSRNG_REG_GENBITS_VLD_GENBITS_FIPS_LOW                                                      (1)
#define CSRNG_REG_GENBITS_VLD_GENBITS_FIPS_MASK                                                     (0x2)
#endif
#define CLP_CSRNG_REG_GENBITS                                                                       (0x20002034)
#ifndef CSRNG_REG_GENBITS
#define CSRNG_REG_GENBITS                                                                           (0x34)
#endif
#define CLP_CSRNG_REG_INT_STATE_READ_ENABLE                                                         (0x20002038)
#ifndef CSRNG_REG_INT_STATE_READ_ENABLE
#define CSRNG_REG_INT_STATE_READ_ENABLE                                                             (0x38)
#define CSRNG_REG_INT_STATE_READ_ENABLE_INT_STATE_READ_ENABLE_LOW                                   (0)
#define CSRNG_REG_INT_STATE_READ_ENABLE_INT_STATE_READ_ENABLE_MASK                                  (0x7)
#endif
#define CLP_CSRNG_REG_INT_STATE_READ_ENABLE_REGWEN                                                  (0x2000203c)
#ifndef CSRNG_REG_INT_STATE_READ_ENABLE_REGWEN
#define CSRNG_REG_INT_STATE_READ_ENABLE_REGWEN                                                      (0x3c)
#define CSRNG_REG_INT_STATE_READ_ENABLE_REGWEN_INT_STATE_READ_ENABLE_REGWEN_LOW                     (0)
#define CSRNG_REG_INT_STATE_READ_ENABLE_REGWEN_INT_STATE_READ_ENABLE_REGWEN_MASK                    (0x1)
#endif
#define CLP_CSRNG_REG_INT_STATE_NUM                                                                 (0x20002040)
#ifndef CSRNG_REG_INT_STATE_NUM
#define CSRNG_REG_INT_STATE_NUM                                                                     (0x40)
#define CSRNG_REG_INT_STATE_NUM_INT_STATE_NUM_LOW                                                   (0)
#define CSRNG_REG_INT_STATE_NUM_INT_STATE_NUM_MASK                                                  (0xf)
#endif
#define CLP_CSRNG_REG_INT_STATE_VAL                                                                 (0x20002044)
#ifndef CSRNG_REG_INT_STATE_VAL
#define CSRNG_REG_INT_STATE_VAL                                                                     (0x44)
#endif
#define CLP_CSRNG_REG_FIPS_FORCE                                                                    (0x20002048)
#ifndef CSRNG_REG_FIPS_FORCE
#define CSRNG_REG_FIPS_FORCE                                                                        (0x48)
#define CSRNG_REG_FIPS_FORCE_FIPS_FORCE_LOW                                                         (0)
#define CSRNG_REG_FIPS_FORCE_FIPS_FORCE_MASK                                                        (0x7)
#endif
#define CLP_CSRNG_REG_HW_EXC_STS                                                                    (0x2000204c)
#ifndef CSRNG_REG_HW_EXC_STS
#define CSRNG_REG_HW_EXC_STS                                                                        (0x4c)
#define CSRNG_REG_HW_EXC_STS_HW_EXC_STS_LOW                                                         (0)
#define CSRNG_REG_HW_EXC_STS_HW_EXC_STS_MASK                                                        (0xffff)
#endif
#define CLP_CSRNG_REG_RECOV_ALERT_STS                                                               (0x20002050)
#ifndef CSRNG_REG_RECOV_ALERT_STS
#define CSRNG_REG_RECOV_ALERT_STS                                                                   (0x50)
#define CSRNG_REG_RECOV_ALERT_STS_ENABLE_FIELD_ALERT_LOW                                            (0)
#define CSRNG_REG_RECOV_ALERT_STS_ENABLE_FIELD_ALERT_MASK                                           (0x1)
#define CSRNG_REG_RECOV_ALERT_STS_SW_APP_ENABLE_FIELD_ALERT_LOW                                     (1)
#define CSRNG_REG_RECOV_ALERT_STS_SW_APP_ENABLE_FIELD_ALERT_MASK                                    (0x2)
#define CSRNG_REG_RECOV_ALERT_STS_READ_INT_STATE_FIELD_ALERT_LOW                                    (2)
#define CSRNG_REG_RECOV_ALERT_STS_READ_INT_STATE_FIELD_ALERT_MASK                                   (0x4)
#define CSRNG_REG_RECOV_ALERT_STS_FIPS_FORCE_ENABLE_FIELD_ALERT_LOW                                 (3)
#define CSRNG_REG_RECOV_ALERT_STS_FIPS_FORCE_ENABLE_FIELD_ALERT_MASK                                (0x8)
#define CSRNG_REG_RECOV_ALERT_STS_ACMD_FLAG0_FIELD_ALERT_LOW                                        (4)
#define CSRNG_REG_RECOV_ALERT_STS_ACMD_FLAG0_FIELD_ALERT_MASK                                       (0x10)
#define CSRNG_REG_RECOV_ALERT_STS_CS_BUS_CMP_ALERT_LOW                                              (12)
#define CSRNG_REG_RECOV_ALERT_STS_CS_BUS_CMP_ALERT_MASK                                             (0x1000)
#define CSRNG_REG_RECOV_ALERT_STS_CMD_STAGE_INVALID_ACMD_ALERT_LOW                                  (13)
#define CSRNG_REG_RECOV_ALERT_STS_CMD_STAGE_INVALID_ACMD_ALERT_MASK                                 (0x2000)
#define CSRNG_REG_RECOV_ALERT_STS_CMD_STAGE_INVALID_CMD_SEQ_ALERT_LOW                               (14)
#define CSRNG_REG_RECOV_ALERT_STS_CMD_STAGE_INVALID_CMD_SEQ_ALERT_MASK                              (0x4000)
#define CSRNG_REG_RECOV_ALERT_STS_CMD_STAGE_RESEED_CNT_ALERT_LOW                                    (15)
#define CSRNG_REG_RECOV_ALERT_STS_CMD_STAGE_RESEED_CNT_ALERT_MASK                                   (0x8000)
#endif
#define CLP_CSRNG_REG_ERR_CODE                                                                      (0x20002054)
#ifndef CSRNG_REG_ERR_CODE
#define CSRNG_REG_ERR_CODE                                                                          (0x54)
#define CSRNG_REG_ERR_CODE_SFIFO_CMD_ERR_LOW                                                        (0)
#define CSRNG_REG_ERR_CODE_SFIFO_CMD_ERR_MASK                                                       (0x1)
#define CSRNG_REG_ERR_CODE_SFIFO_GENBITS_ERR_LOW                                                    (1)
#define CSRNG_REG_ERR_CODE_SFIFO_GENBITS_ERR_MASK                                                   (0x2)
#define CSRNG_REG_ERR_CODE_SFIFO_CMDREQ_ERR_LOW                                                     (2)
#define CSRNG_REG_ERR_CODE_SFIFO_CMDREQ_ERR_MASK                                                    (0x4)
#define CSRNG_REG_ERR_CODE_SFIFO_RCSTAGE_ERR_LOW                                                    (3)
#define CSRNG_REG_ERR_CODE_SFIFO_RCSTAGE_ERR_MASK                                                   (0x8)
#define CSRNG_REG_ERR_CODE_SFIFO_KEYVRC_ERR_LOW                                                     (4)
#define CSRNG_REG_ERR_CODE_SFIFO_KEYVRC_ERR_MASK                                                    (0x10)
#define CSRNG_REG_ERR_CODE_SFIFO_UPDREQ_ERR_LOW                                                     (5)
#define CSRNG_REG_ERR_CODE_SFIFO_UPDREQ_ERR_MASK                                                    (0x20)
#define CSRNG_REG_ERR_CODE_SFIFO_BENCREQ_ERR_LOW                                                    (6)
#define CSRNG_REG_ERR_CODE_SFIFO_BENCREQ_ERR_MASK                                                   (0x40)
#define CSRNG_REG_ERR_CODE_SFIFO_BENCACK_ERR_LOW                                                    (7)
#define CSRNG_REG_ERR_CODE_SFIFO_BENCACK_ERR_MASK                                                   (0x80)
#define CSRNG_REG_ERR_CODE_SFIFO_PDATA_ERR_LOW                                                      (8)
#define CSRNG_REG_ERR_CODE_SFIFO_PDATA_ERR_MASK                                                     (0x100)
#define CSRNG_REG_ERR_CODE_SFIFO_FINAL_ERR_LOW                                                      (9)
#define CSRNG_REG_ERR_CODE_SFIFO_FINAL_ERR_MASK                                                     (0x200)
#define CSRNG_REG_ERR_CODE_SFIFO_GBENCACK_ERR_LOW                                                   (10)
#define CSRNG_REG_ERR_CODE_SFIFO_GBENCACK_ERR_MASK                                                  (0x400)
#define CSRNG_REG_ERR_CODE_SFIFO_GRCSTAGE_ERR_LOW                                                   (11)
#define CSRNG_REG_ERR_CODE_SFIFO_GRCSTAGE_ERR_MASK                                                  (0x800)
#define CSRNG_REG_ERR_CODE_SFIFO_GGENREQ_ERR_LOW                                                    (12)
#define CSRNG_REG_ERR_CODE_SFIFO_GGENREQ_ERR_MASK                                                   (0x1000)
#define CSRNG_REG_ERR_CODE_SFIFO_GADSTAGE_ERR_LOW                                                   (13)
#define CSRNG_REG_ERR_CODE_SFIFO_GADSTAGE_ERR_MASK                                                  (0x2000)
#define CSRNG_REG_ERR_CODE_SFIFO_GGENBITS_ERR_LOW                                                   (14)
#define CSRNG_REG_ERR_CODE_SFIFO_GGENBITS_ERR_MASK                                                  (0x4000)
#define CSRNG_REG_ERR_CODE_SFIFO_BLKENC_ERR_LOW                                                     (15)
#define CSRNG_REG_ERR_CODE_SFIFO_BLKENC_ERR_MASK                                                    (0x8000)
#define CSRNG_REG_ERR_CODE_CMD_STAGE_SM_ERR_LOW                                                     (20)
#define CSRNG_REG_ERR_CODE_CMD_STAGE_SM_ERR_MASK                                                    (0x100000)
#define CSRNG_REG_ERR_CODE_MAIN_SM_ERR_LOW                                                          (21)
#define CSRNG_REG_ERR_CODE_MAIN_SM_ERR_MASK                                                         (0x200000)
#define CSRNG_REG_ERR_CODE_DRBG_GEN_SM_ERR_LOW                                                      (22)
#define CSRNG_REG_ERR_CODE_DRBG_GEN_SM_ERR_MASK                                                     (0x400000)
#define CSRNG_REG_ERR_CODE_DRBG_UPDBE_SM_ERR_LOW                                                    (23)
#define CSRNG_REG_ERR_CODE_DRBG_UPDBE_SM_ERR_MASK                                                   (0x800000)
#define CSRNG_REG_ERR_CODE_DRBG_UPDOB_SM_ERR_LOW                                                    (24)
#define CSRNG_REG_ERR_CODE_DRBG_UPDOB_SM_ERR_MASK                                                   (0x1000000)
#define CSRNG_REG_ERR_CODE_AES_CIPHER_SM_ERR_LOW                                                    (25)
#define CSRNG_REG_ERR_CODE_AES_CIPHER_SM_ERR_MASK                                                   (0x2000000)
#define CSRNG_REG_ERR_CODE_CMD_GEN_CNT_ERR_LOW                                                      (26)
#define CSRNG_REG_ERR_CODE_CMD_GEN_CNT_ERR_MASK                                                     (0x4000000)
#define CSRNG_REG_ERR_CODE_FIFO_WRITE_ERR_LOW                                                       (28)
#define CSRNG_REG_ERR_CODE_FIFO_WRITE_ERR_MASK                                                      (0x10000000)
#define CSRNG_REG_ERR_CODE_FIFO_READ_ERR_LOW                                                        (29)
#define CSRNG_REG_ERR_CODE_FIFO_READ_ERR_MASK                                                       (0x20000000)
#define CSRNG_REG_ERR_CODE_FIFO_STATE_ERR_LOW                                                       (30)
#define CSRNG_REG_ERR_CODE_FIFO_STATE_ERR_MASK                                                      (0x40000000)
#endif
#define CLP_CSRNG_REG_ERR_CODE_TEST                                                                 (0x20002058)
#ifndef CSRNG_REG_ERR_CODE_TEST
#define CSRNG_REG_ERR_CODE_TEST                                                                     (0x58)
#define CSRNG_REG_ERR_CODE_TEST_ERR_CODE_TEST_LOW                                                   (0)
#define CSRNG_REG_ERR_CODE_TEST_ERR_CODE_TEST_MASK                                                  (0x1f)
#endif
#define CLP_CSRNG_REG_MAIN_SM_STATE                                                                 (0x2000205c)
#ifndef CSRNG_REG_MAIN_SM_STATE
#define CSRNG_REG_MAIN_SM_STATE                                                                     (0x5c)
#define CSRNG_REG_MAIN_SM_STATE_MAIN_SM_STATE_LOW                                                   (0)
#define CSRNG_REG_MAIN_SM_STATE_MAIN_SM_STATE_MASK                                                  (0xff)
#endif
#define CLP_ENTROPY_SRC_REG_BASE_ADDR                                                               (0x20003000)
#define CLP_ENTROPY_SRC_REG_INTERRUPT_STATE                                                         (0x20003000)
#ifndef ENTROPY_SRC_REG_INTERRUPT_STATE
#define ENTROPY_SRC_REG_INTERRUPT_STATE                                                             (0x0)
#define ENTROPY_SRC_REG_INTERRUPT_STATE_ES_ENTROPY_VALID_LOW                                        (0)
#define ENTROPY_SRC_REG_INTERRUPT_STATE_ES_ENTROPY_VALID_MASK                                       (0x1)
#define ENTROPY_SRC_REG_INTERRUPT_STATE_ES_HEALTH_TEST_FAILED_LOW                                   (1)
#define ENTROPY_SRC_REG_INTERRUPT_STATE_ES_HEALTH_TEST_FAILED_MASK                                  (0x2)
#define ENTROPY_SRC_REG_INTERRUPT_STATE_ES_OBSERVE_FIFO_READY_LOW                                   (2)
#define ENTROPY_SRC_REG_INTERRUPT_STATE_ES_OBSERVE_FIFO_READY_MASK                                  (0x4)
#define ENTROPY_SRC_REG_INTERRUPT_STATE_ES_FATAL_ERR_LOW                                            (3)
#define ENTROPY_SRC_REG_INTERRUPT_STATE_ES_FATAL_ERR_MASK                                           (0x8)
#endif
#define CLP_ENTROPY_SRC_REG_INTERRUPT_ENABLE                                                        (0x20003004)
#ifndef ENTROPY_SRC_REG_INTERRUPT_ENABLE
#define ENTROPY_SRC_REG_INTERRUPT_ENABLE                                                            (0x4)
#define ENTROPY_SRC_REG_INTERRUPT_ENABLE_ES_ENTROPY_VALID_LOW                                       (0)
#define ENTROPY_SRC_REG_INTERRUPT_ENABLE_ES_ENTROPY_VALID_MASK                                      (0x1)
#define ENTROPY_SRC_REG_INTERRUPT_ENABLE_ES_HEALTH_TEST_FAILED_LOW                                  (1)
#define ENTROPY_SRC_REG_INTERRUPT_ENABLE_ES_HEALTH_TEST_FAILED_MASK                                 (0x2)
#define ENTROPY_SRC_REG_INTERRUPT_ENABLE_ES_OBSERVE_FIFO_READY_LOW                                  (2)
#define ENTROPY_SRC_REG_INTERRUPT_ENABLE_ES_OBSERVE_FIFO_READY_MASK                                 (0x4)
#define ENTROPY_SRC_REG_INTERRUPT_ENABLE_ES_FATAL_ERR_LOW                                           (3)
#define ENTROPY_SRC_REG_INTERRUPT_ENABLE_ES_FATAL_ERR_MASK                                          (0x8)
#endif
#define CLP_ENTROPY_SRC_REG_INTERRUPT_TEST                                                          (0x20003008)
#ifndef ENTROPY_SRC_REG_INTERRUPT_TEST
#define ENTROPY_SRC_REG_INTERRUPT_TEST                                                              (0x8)
#define ENTROPY_SRC_REG_INTERRUPT_TEST_ES_ENTROPY_VALID_LOW                                         (0)
#define ENTROPY_SRC_REG_INTERRUPT_TEST_ES_ENTROPY_VALID_MASK                                        (0x1)
#define ENTROPY_SRC_REG_INTERRUPT_TEST_ES_HEALTH_TEST_FAILED_LOW                                    (1)
#define ENTROPY_SRC_REG_INTERRUPT_TEST_ES_HEALTH_TEST_FAILED_MASK                                   (0x2)
#define ENTROPY_SRC_REG_INTERRUPT_TEST_ES_OBSERVE_FIFO_READY_LOW                                    (2)
#define ENTROPY_SRC_REG_INTERRUPT_TEST_ES_OBSERVE_FIFO_READY_MASK                                   (0x4)
#define ENTROPY_SRC_REG_INTERRUPT_TEST_ES_FATAL_ERR_LOW                                             (3)
#define ENTROPY_SRC_REG_INTERRUPT_TEST_ES_FATAL_ERR_MASK                                            (0x8)
#endif
#define CLP_ENTROPY_SRC_REG_ALERT_TEST                                                              (0x2000300c)
#ifndef ENTROPY_SRC_REG_ALERT_TEST
#define ENTROPY_SRC_REG_ALERT_TEST                                                                  (0xc)
#define ENTROPY_SRC_REG_ALERT_TEST_RECOV_ALERT_LOW                                                  (0)
#define ENTROPY_SRC_REG_ALERT_TEST_RECOV_ALERT_MASK                                                 (0x1)
#define ENTROPY_SRC_REG_ALERT_TEST_FATAL_ALERT_LOW                                                  (1)
#define ENTROPY_SRC_REG_ALERT_TEST_FATAL_ALERT_MASK                                                 (0x2)
#endif
#define CLP_ENTROPY_SRC_REG_ME_REGWEN                                                               (0x20003010)
#ifndef ENTROPY_SRC_REG_ME_REGWEN
#define ENTROPY_SRC_REG_ME_REGWEN                                                                   (0x10)
#define ENTROPY_SRC_REG_ME_REGWEN_ME_REGWEN_LOW                                                     (0)
#define ENTROPY_SRC_REG_ME_REGWEN_ME_REGWEN_MASK                                                    (0x1)
#endif
#define CLP_ENTROPY_SRC_REG_SW_REGUPD                                                               (0x20003014)
#ifndef ENTROPY_SRC_REG_SW_REGUPD
#define ENTROPY_SRC_REG_SW_REGUPD                                                                   (0x14)
#define ENTROPY_SRC_REG_SW_REGUPD_SW_REGUPD_LOW                                                     (0)
#define ENTROPY_SRC_REG_SW_REGUPD_SW_REGUPD_MASK                                                    (0x1)
#endif
#define CLP_ENTROPY_SRC_REG_REGWEN                                                                  (0x20003018)
#ifndef ENTROPY_SRC_REG_REGWEN
#define ENTROPY_SRC_REG_REGWEN                                                                      (0x18)
#define ENTROPY_SRC_REG_REGWEN_REGWEN_LOW                                                           (0)
#define ENTROPY_SRC_REG_REGWEN_REGWEN_MASK                                                          (0x1)
#endif
#define CLP_ENTROPY_SRC_REG_REV                                                                     (0x2000301c)
#ifndef ENTROPY_SRC_REG_REV
#define ENTROPY_SRC_REG_REV                                                                         (0x1c)
#define ENTROPY_SRC_REG_REV_ABI_REVISION_LOW                                                        (0)
#define ENTROPY_SRC_REG_REV_ABI_REVISION_MASK                                                       (0xff)
#define ENTROPY_SRC_REG_REV_HW_REVISION_LOW                                                         (8)
#define ENTROPY_SRC_REG_REV_HW_REVISION_MASK                                                        (0xff00)
#define ENTROPY_SRC_REG_REV_CHIP_TYPE_LOW                                                           (16)
#define ENTROPY_SRC_REG_REV_CHIP_TYPE_MASK                                                          (0xff0000)
#endif
#define CLP_ENTROPY_SRC_REG_MODULE_ENABLE                                                           (0x20003020)
#ifndef ENTROPY_SRC_REG_MODULE_ENABLE
#define ENTROPY_SRC_REG_MODULE_ENABLE                                                               (0x20)
#define ENTROPY_SRC_REG_MODULE_ENABLE_MODULE_ENABLE_LOW                                             (0)
#define ENTROPY_SRC_REG_MODULE_ENABLE_MODULE_ENABLE_MASK                                            (0xf)
#endif
#define CLP_ENTROPY_SRC_REG_CONF                                                                    (0x20003024)
#ifndef ENTROPY_SRC_REG_CONF
#define ENTROPY_SRC_REG_CONF                                                                        (0x24)
#define ENTROPY_SRC_REG_CONF_FIPS_ENABLE_LOW                                                        (0)
#define ENTROPY_SRC_REG_CONF_FIPS_ENABLE_MASK                                                       (0xf)
#define ENTROPY_SRC_REG_CONF_FIPS_FLAG_LOW                                                          (4)
#define ENTROPY_SRC_REG_CONF_FIPS_FLAG_MASK                                                         (0xf0)
#define ENTROPY_SRC_REG_CONF_RNG_FIPS_LOW                                                           (8)
#define ENTROPY_SRC_REG_CONF_RNG_FIPS_MASK                                                          (0xf00)
#define ENTROPY_SRC_REG_CONF_RNG_BIT_ENABLE_LOW                                                     (12)
#define ENTROPY_SRC_REG_CONF_RNG_BIT_ENABLE_MASK                                                    (0xf000)
#define ENTROPY_SRC_REG_CONF_RNG_BIT_SEL_LOW                                                        (16)
#define ENTROPY_SRC_REG_CONF_RNG_BIT_SEL_MASK                                                       (0x30000)
#define ENTROPY_SRC_REG_CONF_THRESHOLD_SCOPE_LOW                                                    (18)
#define ENTROPY_SRC_REG_CONF_THRESHOLD_SCOPE_MASK                                                   (0x3c0000)
#define ENTROPY_SRC_REG_CONF_ENTROPY_DATA_REG_ENABLE_LOW                                            (22)
#define ENTROPY_SRC_REG_CONF_ENTROPY_DATA_REG_ENABLE_MASK                                           (0x3c00000)
#endif
#define CLP_ENTROPY_SRC_REG_ENTROPY_CONTROL                                                         (0x20003028)
#ifndef ENTROPY_SRC_REG_ENTROPY_CONTROL
#define ENTROPY_SRC_REG_ENTROPY_CONTROL                                                             (0x28)
#define ENTROPY_SRC_REG_ENTROPY_CONTROL_ES_ROUTE_LOW                                                (0)
#define ENTROPY_SRC_REG_ENTROPY_CONTROL_ES_ROUTE_MASK                                               (0xf)
#define ENTROPY_SRC_REG_ENTROPY_CONTROL_ES_TYPE_LOW                                                 (4)
#define ENTROPY_SRC_REG_ENTROPY_CONTROL_ES_TYPE_MASK                                                (0xf0)
#endif
#define CLP_ENTROPY_SRC_REG_ENTROPY_DATA                                                            (0x2000302c)
#ifndef ENTROPY_SRC_REG_ENTROPY_DATA
#define ENTROPY_SRC_REG_ENTROPY_DATA                                                                (0x2c)
#endif
#define CLP_ENTROPY_SRC_REG_HEALTH_TEST_WINDOWS                                                     (0x20003030)
#ifndef ENTROPY_SRC_REG_HEALTH_TEST_WINDOWS
#define ENTROPY_SRC_REG_HEALTH_TEST_WINDOWS                                                         (0x30)
#define ENTROPY_SRC_REG_HEALTH_TEST_WINDOWS_FIPS_WINDOW_LOW                                         (0)
#define ENTROPY_SRC_REG_HEALTH_TEST_WINDOWS_FIPS_WINDOW_MASK                                        (0xffff)
#define ENTROPY_SRC_REG_HEALTH_TEST_WINDOWS_BYPASS_WINDOW_LOW                                       (16)
#define ENTROPY_SRC_REG_HEALTH_TEST_WINDOWS_BYPASS_WINDOW_MASK                                      (0xffff0000)
#endif
#define CLP_ENTROPY_SRC_REG_REPCNT_THRESHOLDS                                                       (0x20003034)
#ifndef ENTROPY_SRC_REG_REPCNT_THRESHOLDS
#define ENTROPY_SRC_REG_REPCNT_THRESHOLDS                                                           (0x34)
#define ENTROPY_SRC_REG_REPCNT_THRESHOLDS_FIPS_THRESH_LOW                                           (0)
#define ENTROPY_SRC_REG_REPCNT_THRESHOLDS_FIPS_THRESH_MASK                                          (0xffff)
#define ENTROPY_SRC_REG_REPCNT_THRESHOLDS_BYPASS_THRESH_LOW                                         (16)
#define ENTROPY_SRC_REG_REPCNT_THRESHOLDS_BYPASS_THRESH_MASK                                        (0xffff0000)
#endif
#define CLP_ENTROPY_SRC_REG_REPCNTS_THRESHOLDS                                                      (0x20003038)
#ifndef ENTROPY_SRC_REG_REPCNTS_THRESHOLDS
#define ENTROPY_SRC_REG_REPCNTS_THRESHOLDS                                                          (0x38)
#define ENTROPY_SRC_REG_REPCNTS_THRESHOLDS_FIPS_THRESH_LOW                                          (0)
#define ENTROPY_SRC_REG_REPCNTS_THRESHOLDS_FIPS_THRESH_MASK                                         (0xffff)
#define ENTROPY_SRC_REG_REPCNTS_THRESHOLDS_BYPASS_THRESH_LOW                                        (16)
#define ENTROPY_SRC_REG_REPCNTS_THRESHOLDS_BYPASS_THRESH_MASK                                       (0xffff0000)
#endif
#define CLP_ENTROPY_SRC_REG_ADAPTP_HI_THRESHOLDS                                                    (0x2000303c)
#ifndef ENTROPY_SRC_REG_ADAPTP_HI_THRESHOLDS
#define ENTROPY_SRC_REG_ADAPTP_HI_THRESHOLDS                                                        (0x3c)
#define ENTROPY_SRC_REG_ADAPTP_HI_THRESHOLDS_FIPS_THRESH_LOW                                        (0)
#define ENTROPY_SRC_REG_ADAPTP_HI_THRESHOLDS_FIPS_THRESH_MASK                                       (0xffff)
#define ENTROPY_SRC_REG_ADAPTP_HI_THRESHOLDS_BYPASS_THRESH_LOW                                      (16)
#define ENTROPY_SRC_REG_ADAPTP_HI_THRESHOLDS_BYPASS_THRESH_MASK                                     (0xffff0000)
#endif
#define CLP_ENTROPY_SRC_REG_ADAPTP_LO_THRESHOLDS                                                    (0x20003040)
#ifndef ENTROPY_SRC_REG_ADAPTP_LO_THRESHOLDS
#define ENTROPY_SRC_REG_ADAPTP_LO_THRESHOLDS                                                        (0x40)
#define ENTROPY_SRC_REG_ADAPTP_LO_THRESHOLDS_FIPS_THRESH_LOW                                        (0)
#define ENTROPY_SRC_REG_ADAPTP_LO_THRESHOLDS_FIPS_THRESH_MASK                                       (0xffff)
#define ENTROPY_SRC_REG_ADAPTP_LO_THRESHOLDS_BYPASS_THRESH_LOW                                      (16)
#define ENTROPY_SRC_REG_ADAPTP_LO_THRESHOLDS_BYPASS_THRESH_MASK                                     (0xffff0000)
#endif
#define CLP_ENTROPY_SRC_REG_BUCKET_THRESHOLDS                                                       (0x20003044)
#ifndef ENTROPY_SRC_REG_BUCKET_THRESHOLDS
#define ENTROPY_SRC_REG_BUCKET_THRESHOLDS                                                           (0x44)
#define ENTROPY_SRC_REG_BUCKET_THRESHOLDS_FIPS_THRESH_LOW                                           (0)
#define ENTROPY_SRC_REG_BUCKET_THRESHOLDS_FIPS_THRESH_MASK                                          (0xffff)
#define ENTROPY_SRC_REG_BUCKET_THRESHOLDS_BYPASS_THRESH_LOW                                         (16)
#define ENTROPY_SRC_REG_BUCKET_THRESHOLDS_BYPASS_THRESH_MASK                                        (0xffff0000)
#endif
#define CLP_ENTROPY_SRC_REG_MARKOV_HI_THRESHOLDS                                                    (0x20003048)
#ifndef ENTROPY_SRC_REG_MARKOV_HI_THRESHOLDS
#define ENTROPY_SRC_REG_MARKOV_HI_THRESHOLDS                                                        (0x48)
#define ENTROPY_SRC_REG_MARKOV_HI_THRESHOLDS_FIPS_THRESH_LOW                                        (0)
#define ENTROPY_SRC_REG_MARKOV_HI_THRESHOLDS_FIPS_THRESH_MASK                                       (0xffff)
#define ENTROPY_SRC_REG_MARKOV_HI_THRESHOLDS_BYPASS_THRESH_LOW                                      (16)
#define ENTROPY_SRC_REG_MARKOV_HI_THRESHOLDS_BYPASS_THRESH_MASK                                     (0xffff0000)
#endif
#define CLP_ENTROPY_SRC_REG_MARKOV_LO_THRESHOLDS                                                    (0x2000304c)
#ifndef ENTROPY_SRC_REG_MARKOV_LO_THRESHOLDS
#define ENTROPY_SRC_REG_MARKOV_LO_THRESHOLDS                                                        (0x4c)
#define ENTROPY_SRC_REG_MARKOV_LO_THRESHOLDS_FIPS_THRESH_LOW                                        (0)
#define ENTROPY_SRC_REG_MARKOV_LO_THRESHOLDS_FIPS_THRESH_MASK                                       (0xffff)
#define ENTROPY_SRC_REG_MARKOV_LO_THRESHOLDS_BYPASS_THRESH_LOW                                      (16)
#define ENTROPY_SRC_REG_MARKOV_LO_THRESHOLDS_BYPASS_THRESH_MASK                                     (0xffff0000)
#endif
#define CLP_ENTROPY_SRC_REG_EXTHT_HI_THRESHOLDS                                                     (0x20003050)
#ifndef ENTROPY_SRC_REG_EXTHT_HI_THRESHOLDS
#define ENTROPY_SRC_REG_EXTHT_HI_THRESHOLDS                                                         (0x50)
#define ENTROPY_SRC_REG_EXTHT_HI_THRESHOLDS_FIPS_THRESH_LOW                                         (0)
#define ENTROPY_SRC_REG_EXTHT_HI_THRESHOLDS_FIPS_THRESH_MASK                                        (0xffff)
#define ENTROPY_SRC_REG_EXTHT_HI_THRESHOLDS_BYPASS_THRESH_LOW                                       (16)
#define ENTROPY_SRC_REG_EXTHT_HI_THRESHOLDS_BYPASS_THRESH_MASK                                      (0xffff0000)
#endif
#define CLP_ENTROPY_SRC_REG_EXTHT_LO_THRESHOLDS                                                     (0x20003054)
#ifndef ENTROPY_SRC_REG_EXTHT_LO_THRESHOLDS
#define ENTROPY_SRC_REG_EXTHT_LO_THRESHOLDS                                                         (0x54)
#define ENTROPY_SRC_REG_EXTHT_LO_THRESHOLDS_FIPS_THRESH_LOW                                         (0)
#define ENTROPY_SRC_REG_EXTHT_LO_THRESHOLDS_FIPS_THRESH_MASK                                        (0xffff)
#define ENTROPY_SRC_REG_EXTHT_LO_THRESHOLDS_BYPASS_THRESH_LOW                                       (16)
#define ENTROPY_SRC_REG_EXTHT_LO_THRESHOLDS_BYPASS_THRESH_MASK                                      (0xffff0000)
#endif
#define CLP_ENTROPY_SRC_REG_REPCNT_HI_WATERMARKS                                                    (0x20003058)
#ifndef ENTROPY_SRC_REG_REPCNT_HI_WATERMARKS
#define ENTROPY_SRC_REG_REPCNT_HI_WATERMARKS                                                        (0x58)
#define ENTROPY_SRC_REG_REPCNT_HI_WATERMARKS_FIPS_WATERMARK_LOW                                     (0)
#define ENTROPY_SRC_REG_REPCNT_HI_WATERMARKS_FIPS_WATERMARK_MASK                                    (0xffff)
#define ENTROPY_SRC_REG_REPCNT_HI_WATERMARKS_BYPASS_WATERMARK_LOW                                   (16)
#define ENTROPY_SRC_REG_REPCNT_HI_WATERMARKS_BYPASS_WATERMARK_MASK                                  (0xffff0000)
#endif
#define CLP_ENTROPY_SRC_REG_REPCNTS_HI_WATERMARKS                                                   (0x2000305c)
#ifndef ENTROPY_SRC_REG_REPCNTS_HI_WATERMARKS
#define ENTROPY_SRC_REG_REPCNTS_HI_WATERMARKS                                                       (0x5c)
#define ENTROPY_SRC_REG_REPCNTS_HI_WATERMARKS_FIPS_WATERMARK_LOW                                    (0)
#define ENTROPY_SRC_REG_REPCNTS_HI_WATERMARKS_FIPS_WATERMARK_MASK                                   (0xffff)
#define ENTROPY_SRC_REG_REPCNTS_HI_WATERMARKS_BYPASS_WATERMARK_LOW                                  (16)
#define ENTROPY_SRC_REG_REPCNTS_HI_WATERMARKS_BYPASS_WATERMARK_MASK                                 (0xffff0000)
#endif
#define CLP_ENTROPY_SRC_REG_ADAPTP_HI_WATERMARKS                                                    (0x20003060)
#ifndef ENTROPY_SRC_REG_ADAPTP_HI_WATERMARKS
#define ENTROPY_SRC_REG_ADAPTP_HI_WATERMARKS                                                        (0x60)
#define ENTROPY_SRC_REG_ADAPTP_HI_WATERMARKS_FIPS_WATERMARK_LOW                                     (0)
#define ENTROPY_SRC_REG_ADAPTP_HI_WATERMARKS_FIPS_WATERMARK_MASK                                    (0xffff)
#define ENTROPY_SRC_REG_ADAPTP_HI_WATERMARKS_BYPASS_WATERMARK_LOW                                   (16)
#define ENTROPY_SRC_REG_ADAPTP_HI_WATERMARKS_BYPASS_WATERMARK_MASK                                  (0xffff0000)
#endif
#define CLP_ENTROPY_SRC_REG_ADAPTP_LO_WATERMARKS                                                    (0x20003064)
#ifndef ENTROPY_SRC_REG_ADAPTP_LO_WATERMARKS
#define ENTROPY_SRC_REG_ADAPTP_LO_WATERMARKS                                                        (0x64)
#define ENTROPY_SRC_REG_ADAPTP_LO_WATERMARKS_FIPS_WATERMARK_LOW                                     (0)
#define ENTROPY_SRC_REG_ADAPTP_LO_WATERMARKS_FIPS_WATERMARK_MASK                                    (0xffff)
#define ENTROPY_SRC_REG_ADAPTP_LO_WATERMARKS_BYPASS_WATERMARK_LOW                                   (16)
#define ENTROPY_SRC_REG_ADAPTP_LO_WATERMARKS_BYPASS_WATERMARK_MASK                                  (0xffff0000)
#endif
#define CLP_ENTROPY_SRC_REG_EXTHT_HI_WATERMARKS                                                     (0x20003068)
#ifndef ENTROPY_SRC_REG_EXTHT_HI_WATERMARKS
#define ENTROPY_SRC_REG_EXTHT_HI_WATERMARKS                                                         (0x68)
#define ENTROPY_SRC_REG_EXTHT_HI_WATERMARKS_FIPS_WATERMARK_LOW                                      (0)
#define ENTROPY_SRC_REG_EXTHT_HI_WATERMARKS_FIPS_WATERMARK_MASK                                     (0xffff)
#define ENTROPY_SRC_REG_EXTHT_HI_WATERMARKS_BYPASS_WATERMARK_LOW                                    (16)
#define ENTROPY_SRC_REG_EXTHT_HI_WATERMARKS_BYPASS_WATERMARK_MASK                                   (0xffff0000)
#endif
#define CLP_ENTROPY_SRC_REG_EXTHT_LO_WATERMARKS                                                     (0x2000306c)
#ifndef ENTROPY_SRC_REG_EXTHT_LO_WATERMARKS
#define ENTROPY_SRC_REG_EXTHT_LO_WATERMARKS                                                         (0x6c)
#define ENTROPY_SRC_REG_EXTHT_LO_WATERMARKS_FIPS_WATERMARK_LOW                                      (0)
#define ENTROPY_SRC_REG_EXTHT_LO_WATERMARKS_FIPS_WATERMARK_MASK                                     (0xffff)
#define ENTROPY_SRC_REG_EXTHT_LO_WATERMARKS_BYPASS_WATERMARK_LOW                                    (16)
#define ENTROPY_SRC_REG_EXTHT_LO_WATERMARKS_BYPASS_WATERMARK_MASK                                   (0xffff0000)
#endif
#define CLP_ENTROPY_SRC_REG_BUCKET_HI_WATERMARKS                                                    (0x20003070)
#ifndef ENTROPY_SRC_REG_BUCKET_HI_WATERMARKS
#define ENTROPY_SRC_REG_BUCKET_HI_WATERMARKS                                                        (0x70)
#define ENTROPY_SRC_REG_BUCKET_HI_WATERMARKS_FIPS_WATERMARK_LOW                                     (0)
#define ENTROPY_SRC_REG_BUCKET_HI_WATERMARKS_FIPS_WATERMARK_MASK                                    (0xffff)
#define ENTROPY_SRC_REG_BUCKET_HI_WATERMARKS_BYPASS_WATERMARK_LOW                                   (16)
#define ENTROPY_SRC_REG_BUCKET_HI_WATERMARKS_BYPASS_WATERMARK_MASK                                  (0xffff0000)
#endif
#define CLP_ENTROPY_SRC_REG_MARKOV_HI_WATERMARKS                                                    (0x20003074)
#ifndef ENTROPY_SRC_REG_MARKOV_HI_WATERMARKS
#define ENTROPY_SRC_REG_MARKOV_HI_WATERMARKS                                                        (0x74)
#define ENTROPY_SRC_REG_MARKOV_HI_WATERMARKS_FIPS_WATERMARK_LOW                                     (0)
#define ENTROPY_SRC_REG_MARKOV_HI_WATERMARKS_FIPS_WATERMARK_MASK                                    (0xffff)
#define ENTROPY_SRC_REG_MARKOV_HI_WATERMARKS_BYPASS_WATERMARK_LOW                                   (16)
#define ENTROPY_SRC_REG_MARKOV_HI_WATERMARKS_BYPASS_WATERMARK_MASK                                  (0xffff0000)
#endif
#define CLP_ENTROPY_SRC_REG_MARKOV_LO_WATERMARKS                                                    (0x20003078)
#ifndef ENTROPY_SRC_REG_MARKOV_LO_WATERMARKS
#define ENTROPY_SRC_REG_MARKOV_LO_WATERMARKS                                                        (0x78)
#define ENTROPY_SRC_REG_MARKOV_LO_WATERMARKS_FIPS_WATERMARK_LOW                                     (0)
#define ENTROPY_SRC_REG_MARKOV_LO_WATERMARKS_FIPS_WATERMARK_MASK                                    (0xffff)
#define ENTROPY_SRC_REG_MARKOV_LO_WATERMARKS_BYPASS_WATERMARK_LOW                                   (16)
#define ENTROPY_SRC_REG_MARKOV_LO_WATERMARKS_BYPASS_WATERMARK_MASK                                  (0xffff0000)
#endif
#define CLP_ENTROPY_SRC_REG_REPCNT_TOTAL_FAILS                                                      (0x2000307c)
#ifndef ENTROPY_SRC_REG_REPCNT_TOTAL_FAILS
#define ENTROPY_SRC_REG_REPCNT_TOTAL_FAILS                                                          (0x7c)
#endif
#define CLP_ENTROPY_SRC_REG_REPCNTS_TOTAL_FAILS                                                     (0x20003080)
#ifndef ENTROPY_SRC_REG_REPCNTS_TOTAL_FAILS
#define ENTROPY_SRC_REG_REPCNTS_TOTAL_FAILS                                                         (0x80)
#endif
#define CLP_ENTROPY_SRC_REG_ADAPTP_HI_TOTAL_FAILS                                                   (0x20003084)
#ifndef ENTROPY_SRC_REG_ADAPTP_HI_TOTAL_FAILS
#define ENTROPY_SRC_REG_ADAPTP_HI_TOTAL_FAILS                                                       (0x84)
#endif
#define CLP_ENTROPY_SRC_REG_ADAPTP_LO_TOTAL_FAILS                                                   (0x20003088)
#ifndef ENTROPY_SRC_REG_ADAPTP_LO_TOTAL_FAILS
#define ENTROPY_SRC_REG_ADAPTP_LO_TOTAL_FAILS                                                       (0x88)
#endif
#define CLP_ENTROPY_SRC_REG_BUCKET_TOTAL_FAILS                                                      (0x2000308c)
#ifndef ENTROPY_SRC_REG_BUCKET_TOTAL_FAILS
#define ENTROPY_SRC_REG_BUCKET_TOTAL_FAILS                                                          (0x8c)
#endif
#define CLP_ENTROPY_SRC_REG_MARKOV_HI_TOTAL_FAILS                                                   (0x20003090)
#ifndef ENTROPY_SRC_REG_MARKOV_HI_TOTAL_FAILS
#define ENTROPY_SRC_REG_MARKOV_HI_TOTAL_FAILS                                                       (0x90)
#endif
#define CLP_ENTROPY_SRC_REG_MARKOV_LO_TOTAL_FAILS                                                   (0x20003094)
#ifndef ENTROPY_SRC_REG_MARKOV_LO_TOTAL_FAILS
#define ENTROPY_SRC_REG_MARKOV_LO_TOTAL_FAILS                                                       (0x94)
#endif
#define CLP_ENTROPY_SRC_REG_EXTHT_HI_TOTAL_FAILS                                                    (0x20003098)
#ifndef ENTROPY_SRC_REG_EXTHT_HI_TOTAL_FAILS
#define ENTROPY_SRC_REG_EXTHT_HI_TOTAL_FAILS                                                        (0x98)
#endif
#define CLP_ENTROPY_SRC_REG_EXTHT_LO_TOTAL_FAILS                                                    (0x2000309c)
#ifndef ENTROPY_SRC_REG_EXTHT_LO_TOTAL_FAILS
#define ENTROPY_SRC_REG_EXTHT_LO_TOTAL_FAILS                                                        (0x9c)
#endif
#define CLP_ENTROPY_SRC_REG_ALERT_THRESHOLD                                                         (0x200030a0)
#ifndef ENTROPY_SRC_REG_ALERT_THRESHOLD
#define ENTROPY_SRC_REG_ALERT_THRESHOLD                                                             (0xa0)
#define ENTROPY_SRC_REG_ALERT_THRESHOLD_ALERT_THRESHOLD_LOW                                         (0)
#define ENTROPY_SRC_REG_ALERT_THRESHOLD_ALERT_THRESHOLD_MASK                                        (0xffff)
#define ENTROPY_SRC_REG_ALERT_THRESHOLD_ALERT_THRESHOLD_INV_LOW                                     (16)
#define ENTROPY_SRC_REG_ALERT_THRESHOLD_ALERT_THRESHOLD_INV_MASK                                    (0xffff0000)
#endif
#define CLP_ENTROPY_SRC_REG_ALERT_SUMMARY_FAIL_COUNTS                                               (0x200030a4)
#ifndef ENTROPY_SRC_REG_ALERT_SUMMARY_FAIL_COUNTS
#define ENTROPY_SRC_REG_ALERT_SUMMARY_FAIL_COUNTS                                                   (0xa4)
#define ENTROPY_SRC_REG_ALERT_SUMMARY_FAIL_COUNTS_ANY_FAIL_COUNT_LOW                                (0)
#define ENTROPY_SRC_REG_ALERT_SUMMARY_FAIL_COUNTS_ANY_FAIL_COUNT_MASK                               (0xffff)
#endif
#define CLP_ENTROPY_SRC_REG_ALERT_FAIL_COUNTS                                                       (0x200030a8)
#ifndef ENTROPY_SRC_REG_ALERT_FAIL_COUNTS
#define ENTROPY_SRC_REG_ALERT_FAIL_COUNTS                                                           (0xa8)
#define ENTROPY_SRC_REG_ALERT_FAIL_COUNTS_REPCNT_FAIL_COUNT_LOW                                     (4)
#define ENTROPY_SRC_REG_ALERT_FAIL_COUNTS_REPCNT_FAIL_COUNT_MASK                                    (0xf0)
#define ENTROPY_SRC_REG_ALERT_FAIL_COUNTS_ADAPTP_HI_FAIL_COUNT_LOW                                  (8)
#define ENTROPY_SRC_REG_ALERT_FAIL_COUNTS_ADAPTP_HI_FAIL_COUNT_MASK                                 (0xf00)
#define ENTROPY_SRC_REG_ALERT_FAIL_COUNTS_ADAPTP_LO_FAIL_COUNT_LOW                                  (12)
#define ENTROPY_SRC_REG_ALERT_FAIL_COUNTS_ADAPTP_LO_FAIL_COUNT_MASK                                 (0xf000)
#define ENTROPY_SRC_REG_ALERT_FAIL_COUNTS_BUCKET_FAIL_COUNT_LOW                                     (16)
#define ENTROPY_SRC_REG_ALERT_FAIL_COUNTS_BUCKET_FAIL_COUNT_MASK                                    (0xf0000)
#define ENTROPY_SRC_REG_ALERT_FAIL_COUNTS_MARKOV_HI_FAIL_COUNT_LOW                                  (20)
#define ENTROPY_SRC_REG_ALERT_FAIL_COUNTS_MARKOV_HI_FAIL_COUNT_MASK                                 (0xf00000)
#define ENTROPY_SRC_REG_ALERT_FAIL_COUNTS_MARKOV_LO_FAIL_COUNT_LOW                                  (24)
#define ENTROPY_SRC_REG_ALERT_FAIL_COUNTS_MARKOV_LO_FAIL_COUNT_MASK                                 (0xf000000)
#define ENTROPY_SRC_REG_ALERT_FAIL_COUNTS_REPCNTS_FAIL_COUNT_LOW                                    (28)
#define ENTROPY_SRC_REG_ALERT_FAIL_COUNTS_REPCNTS_FAIL_COUNT_MASK                                   (0xf0000000)
#endif
#define CLP_ENTROPY_SRC_REG_EXTHT_FAIL_COUNTS                                                       (0x200030ac)
#ifndef ENTROPY_SRC_REG_EXTHT_FAIL_COUNTS
#define ENTROPY_SRC_REG_EXTHT_FAIL_COUNTS                                                           (0xac)
#define ENTROPY_SRC_REG_EXTHT_FAIL_COUNTS_EXTHT_HI_FAIL_COUNT_LOW                                   (0)
#define ENTROPY_SRC_REG_EXTHT_FAIL_COUNTS_EXTHT_HI_FAIL_COUNT_MASK                                  (0xf)
#define ENTROPY_SRC_REG_EXTHT_FAIL_COUNTS_EXTHT_LO_FAIL_COUNT_LOW                                   (4)
#define ENTROPY_SRC_REG_EXTHT_FAIL_COUNTS_EXTHT_LO_FAIL_COUNT_MASK                                  (0xf0)
#endif
#define CLP_ENTROPY_SRC_REG_FW_OV_CONTROL                                                           (0x200030b0)
#ifndef ENTROPY_SRC_REG_FW_OV_CONTROL
#define ENTROPY_SRC_REG_FW_OV_CONTROL                                                               (0xb0)
#define ENTROPY_SRC_REG_FW_OV_CONTROL_FW_OV_MODE_LOW                                                (0)
#define ENTROPY_SRC_REG_FW_OV_CONTROL_FW_OV_MODE_MASK                                               (0xf)
#define ENTROPY_SRC_REG_FW_OV_CONTROL_FW_OV_ENTROPY_INSERT_LOW                                      (4)
#define ENTROPY_SRC_REG_FW_OV_CONTROL_FW_OV_ENTROPY_INSERT_MASK                                     (0xf0)
#endif
#define CLP_ENTROPY_SRC_REG_FW_OV_SHA3_START                                                        (0x200030b4)
#ifndef ENTROPY_SRC_REG_FW_OV_SHA3_START
#define ENTROPY_SRC_REG_FW_OV_SHA3_START                                                            (0xb4)
#define ENTROPY_SRC_REG_FW_OV_SHA3_START_FW_OV_INSERT_START_LOW                                     (0)
#define ENTROPY_SRC_REG_FW_OV_SHA3_START_FW_OV_INSERT_START_MASK                                    (0xf)
#endif
#define CLP_ENTROPY_SRC_REG_FW_OV_WR_FIFO_FULL                                                      (0x200030b8)
#ifndef ENTROPY_SRC_REG_FW_OV_WR_FIFO_FULL
#define ENTROPY_SRC_REG_FW_OV_WR_FIFO_FULL                                                          (0xb8)
#define ENTROPY_SRC_REG_FW_OV_WR_FIFO_FULL_FW_OV_WR_FIFO_FULL_LOW                                   (0)
#define ENTROPY_SRC_REG_FW_OV_WR_FIFO_FULL_FW_OV_WR_FIFO_FULL_MASK                                  (0x1)
#endif
#define CLP_ENTROPY_SRC_REG_FW_OV_RD_FIFO_OVERFLOW                                                  (0x200030bc)
#ifndef ENTROPY_SRC_REG_FW_OV_RD_FIFO_OVERFLOW
#define ENTROPY_SRC_REG_FW_OV_RD_FIFO_OVERFLOW                                                      (0xbc)
#define ENTROPY_SRC_REG_FW_OV_RD_FIFO_OVERFLOW_FW_OV_RD_FIFO_OVERFLOW_LOW                           (0)
#define ENTROPY_SRC_REG_FW_OV_RD_FIFO_OVERFLOW_FW_OV_RD_FIFO_OVERFLOW_MASK                          (0x1)
#endif
#define CLP_ENTROPY_SRC_REG_FW_OV_RD_DATA                                                           (0x200030c0)
#ifndef ENTROPY_SRC_REG_FW_OV_RD_DATA
#define ENTROPY_SRC_REG_FW_OV_RD_DATA                                                               (0xc0)
#endif
#define CLP_ENTROPY_SRC_REG_FW_OV_WR_DATA                                                           (0x200030c4)
#ifndef ENTROPY_SRC_REG_FW_OV_WR_DATA
#define ENTROPY_SRC_REG_FW_OV_WR_DATA                                                               (0xc4)
#endif
#define CLP_ENTROPY_SRC_REG_OBSERVE_FIFO_THRESH                                                     (0x200030c8)
#ifndef ENTROPY_SRC_REG_OBSERVE_FIFO_THRESH
#define ENTROPY_SRC_REG_OBSERVE_FIFO_THRESH                                                         (0xc8)
#define ENTROPY_SRC_REG_OBSERVE_FIFO_THRESH_OBSERVE_FIFO_THRESH_LOW                                 (0)
#define ENTROPY_SRC_REG_OBSERVE_FIFO_THRESH_OBSERVE_FIFO_THRESH_MASK                                (0x3f)
#endif
#define CLP_ENTROPY_SRC_REG_OBSERVE_FIFO_DEPTH                                                      (0x200030cc)
#ifndef ENTROPY_SRC_REG_OBSERVE_FIFO_DEPTH
#define ENTROPY_SRC_REG_OBSERVE_FIFO_DEPTH                                                          (0xcc)
#define ENTROPY_SRC_REG_OBSERVE_FIFO_DEPTH_OBSERVE_FIFO_DEPTH_LOW                                   (0)
#define ENTROPY_SRC_REG_OBSERVE_FIFO_DEPTH_OBSERVE_FIFO_DEPTH_MASK                                  (0x3f)
#endif
#define CLP_ENTROPY_SRC_REG_DEBUG_STATUS                                                            (0x200030d0)
#ifndef ENTROPY_SRC_REG_DEBUG_STATUS
#define ENTROPY_SRC_REG_DEBUG_STATUS                                                                (0xd0)
#define ENTROPY_SRC_REG_DEBUG_STATUS_ENTROPY_FIFO_DEPTH_LOW                                         (0)
#define ENTROPY_SRC_REG_DEBUG_STATUS_ENTROPY_FIFO_DEPTH_MASK                                        (0x3)
#define ENTROPY_SRC_REG_DEBUG_STATUS_SHA3_FSM_LOW                                                   (3)
#define ENTROPY_SRC_REG_DEBUG_STATUS_SHA3_FSM_MASK                                                  (0x38)
#define ENTROPY_SRC_REG_DEBUG_STATUS_SHA3_BLOCK_PR_LOW                                              (6)
#define ENTROPY_SRC_REG_DEBUG_STATUS_SHA3_BLOCK_PR_MASK                                             (0x40)
#define ENTROPY_SRC_REG_DEBUG_STATUS_SHA3_SQUEEZING_LOW                                             (7)
#define ENTROPY_SRC_REG_DEBUG_STATUS_SHA3_SQUEEZING_MASK                                            (0x80)
#define ENTROPY_SRC_REG_DEBUG_STATUS_SHA3_ABSORBED_LOW                                              (8)
#define ENTROPY_SRC_REG_DEBUG_STATUS_SHA3_ABSORBED_MASK                                             (0x100)
#define ENTROPY_SRC_REG_DEBUG_STATUS_SHA3_ERR_LOW                                                   (9)
#define ENTROPY_SRC_REG_DEBUG_STATUS_SHA3_ERR_MASK                                                  (0x200)
#define ENTROPY_SRC_REG_DEBUG_STATUS_MAIN_SM_IDLE_LOW                                               (16)
#define ENTROPY_SRC_REG_DEBUG_STATUS_MAIN_SM_IDLE_MASK                                              (0x10000)
#define ENTROPY_SRC_REG_DEBUG_STATUS_MAIN_SM_BOOT_DONE_LOW                                          (17)
#define ENTROPY_SRC_REG_DEBUG_STATUS_MAIN_SM_BOOT_DONE_MASK                                         (0x20000)
#endif
#define CLP_ENTROPY_SRC_REG_RECOV_ALERT_STS                                                         (0x200030d4)
#ifndef ENTROPY_SRC_REG_RECOV_ALERT_STS
#define ENTROPY_SRC_REG_RECOV_ALERT_STS                                                             (0xd4)
#define ENTROPY_SRC_REG_RECOV_ALERT_STS_FIPS_ENABLE_FIELD_ALERT_LOW                                 (0)
#define ENTROPY_SRC_REG_RECOV_ALERT_STS_FIPS_ENABLE_FIELD_ALERT_MASK                                (0x1)
#define ENTROPY_SRC_REG_RECOV_ALERT_STS_ENTROPY_DATA_REG_EN_FIELD_ALERT_LOW                         (1)
#define ENTROPY_SRC_REG_RECOV_ALERT_STS_ENTROPY_DATA_REG_EN_FIELD_ALERT_MASK                        (0x2)
#define ENTROPY_SRC_REG_RECOV_ALERT_STS_MODULE_ENABLE_FIELD_ALERT_LOW                               (2)
#define ENTROPY_SRC_REG_RECOV_ALERT_STS_MODULE_ENABLE_FIELD_ALERT_MASK                              (0x4)
#define ENTROPY_SRC_REG_RECOV_ALERT_STS_THRESHOLD_SCOPE_FIELD_ALERT_LOW                             (3)
#define ENTROPY_SRC_REG_RECOV_ALERT_STS_THRESHOLD_SCOPE_FIELD_ALERT_MASK                            (0x8)
#define ENTROPY_SRC_REG_RECOV_ALERT_STS_RNG_BIT_ENABLE_FIELD_ALERT_LOW                              (5)
#define ENTROPY_SRC_REG_RECOV_ALERT_STS_RNG_BIT_ENABLE_FIELD_ALERT_MASK                             (0x20)
#define ENTROPY_SRC_REG_RECOV_ALERT_STS_FW_OV_SHA3_START_FIELD_ALERT_LOW                            (7)
#define ENTROPY_SRC_REG_RECOV_ALERT_STS_FW_OV_SHA3_START_FIELD_ALERT_MASK                           (0x80)
#define ENTROPY_SRC_REG_RECOV_ALERT_STS_FW_OV_MODE_FIELD_ALERT_LOW                                  (8)
#define ENTROPY_SRC_REG_RECOV_ALERT_STS_FW_OV_MODE_FIELD_ALERT_MASK                                 (0x100)
#define ENTROPY_SRC_REG_RECOV_ALERT_STS_FW_OV_ENTROPY_INSERT_FIELD_ALERT_LOW                        (9)
#define ENTROPY_SRC_REG_RECOV_ALERT_STS_FW_OV_ENTROPY_INSERT_FIELD_ALERT_MASK                       (0x200)
#define ENTROPY_SRC_REG_RECOV_ALERT_STS_ES_ROUTE_FIELD_ALERT_LOW                                    (10)
#define ENTROPY_SRC_REG_RECOV_ALERT_STS_ES_ROUTE_FIELD_ALERT_MASK                                   (0x400)
#define ENTROPY_SRC_REG_RECOV_ALERT_STS_ES_TYPE_FIELD_ALERT_LOW                                     (11)
#define ENTROPY_SRC_REG_RECOV_ALERT_STS_ES_TYPE_FIELD_ALERT_MASK                                    (0x800)
#define ENTROPY_SRC_REG_RECOV_ALERT_STS_ES_MAIN_SM_ALERT_LOW                                        (12)
#define ENTROPY_SRC_REG_RECOV_ALERT_STS_ES_MAIN_SM_ALERT_MASK                                       (0x1000)
#define ENTROPY_SRC_REG_RECOV_ALERT_STS_ES_BUS_CMP_ALERT_LOW                                        (13)
#define ENTROPY_SRC_REG_RECOV_ALERT_STS_ES_BUS_CMP_ALERT_MASK                                       (0x2000)
#define ENTROPY_SRC_REG_RECOV_ALERT_STS_ES_THRESH_CFG_ALERT_LOW                                     (14)
#define ENTROPY_SRC_REG_RECOV_ALERT_STS_ES_THRESH_CFG_ALERT_MASK                                    (0x4000)
#define ENTROPY_SRC_REG_RECOV_ALERT_STS_ES_FW_OV_WR_ALERT_LOW                                       (15)
#define ENTROPY_SRC_REG_RECOV_ALERT_STS_ES_FW_OV_WR_ALERT_MASK                                      (0x8000)
#define ENTROPY_SRC_REG_RECOV_ALERT_STS_ES_FW_OV_DISABLE_ALERT_LOW                                  (16)
#define ENTROPY_SRC_REG_RECOV_ALERT_STS_ES_FW_OV_DISABLE_ALERT_MASK                                 (0x10000)
#define ENTROPY_SRC_REG_RECOV_ALERT_STS_FIPS_FLAG_FIELD_ALERT_LOW                                   (17)
#define ENTROPY_SRC_REG_RECOV_ALERT_STS_FIPS_FLAG_FIELD_ALERT_MASK                                  (0x20000)
#define ENTROPY_SRC_REG_RECOV_ALERT_STS_RNG_FIPS_FIELD_ALERT_LOW                                    (18)
#define ENTROPY_SRC_REG_RECOV_ALERT_STS_RNG_FIPS_FIELD_ALERT_MASK                                   (0x40000)
#define ENTROPY_SRC_REG_RECOV_ALERT_STS_POSTHT_ENTROPY_DROP_ALERT_LOW                               (31)
#define ENTROPY_SRC_REG_RECOV_ALERT_STS_POSTHT_ENTROPY_DROP_ALERT_MASK                              (0x80000000)
#endif
#define CLP_ENTROPY_SRC_REG_ERR_CODE                                                                (0x200030d8)
#ifndef ENTROPY_SRC_REG_ERR_CODE
#define ENTROPY_SRC_REG_ERR_CODE                                                                    (0xd8)
#define ENTROPY_SRC_REG_ERR_CODE_SFIFO_ESRNG_ERR_LOW                                                (0)
#define ENTROPY_SRC_REG_ERR_CODE_SFIFO_ESRNG_ERR_MASK                                               (0x1)
#define ENTROPY_SRC_REG_ERR_CODE_SFIFO_DISTR_ERR_LOW                                                (1)
#define ENTROPY_SRC_REG_ERR_CODE_SFIFO_DISTR_ERR_MASK                                               (0x2)
#define ENTROPY_SRC_REG_ERR_CODE_SFIFO_OBSERVE_ERR_LOW                                              (2)
#define ENTROPY_SRC_REG_ERR_CODE_SFIFO_OBSERVE_ERR_MASK                                             (0x4)
#define ENTROPY_SRC_REG_ERR_CODE_SFIFO_ESFINAL_ERR_LOW                                              (3)
#define ENTROPY_SRC_REG_ERR_CODE_SFIFO_ESFINAL_ERR_MASK                                             (0x8)
#define ENTROPY_SRC_REG_ERR_CODE_ES_ACK_SM_ERR_LOW                                                  (20)
#define ENTROPY_SRC_REG_ERR_CODE_ES_ACK_SM_ERR_MASK                                                 (0x100000)
#define ENTROPY_SRC_REG_ERR_CODE_ES_MAIN_SM_ERR_LOW                                                 (21)
#define ENTROPY_SRC_REG_ERR_CODE_ES_MAIN_SM_ERR_MASK                                                (0x200000)
#define ENTROPY_SRC_REG_ERR_CODE_ES_CNTR_ERR_LOW                                                    (22)
#define ENTROPY_SRC_REG_ERR_CODE_ES_CNTR_ERR_MASK                                                   (0x400000)
#define ENTROPY_SRC_REG_ERR_CODE_SHA3_STATE_ERR_LOW                                                 (23)
#define ENTROPY_SRC_REG_ERR_CODE_SHA3_STATE_ERR_MASK                                                (0x800000)
#define ENTROPY_SRC_REG_ERR_CODE_SHA3_RST_STORAGE_ERR_LOW                                           (24)
#define ENTROPY_SRC_REG_ERR_CODE_SHA3_RST_STORAGE_ERR_MASK                                          (0x1000000)
#define ENTROPY_SRC_REG_ERR_CODE_FIFO_WRITE_ERR_LOW                                                 (28)
#define ENTROPY_SRC_REG_ERR_CODE_FIFO_WRITE_ERR_MASK                                                (0x10000000)
#define ENTROPY_SRC_REG_ERR_CODE_FIFO_READ_ERR_LOW                                                  (29)
#define ENTROPY_SRC_REG_ERR_CODE_FIFO_READ_ERR_MASK                                                 (0x20000000)
#define ENTROPY_SRC_REG_ERR_CODE_FIFO_STATE_ERR_LOW                                                 (30)
#define ENTROPY_SRC_REG_ERR_CODE_FIFO_STATE_ERR_MASK                                                (0x40000000)
#endif
#define CLP_ENTROPY_SRC_REG_ERR_CODE_TEST                                                           (0x200030dc)
#ifndef ENTROPY_SRC_REG_ERR_CODE_TEST
#define ENTROPY_SRC_REG_ERR_CODE_TEST                                                               (0xdc)
#define ENTROPY_SRC_REG_ERR_CODE_TEST_ERR_CODE_TEST_LOW                                             (0)
#define ENTROPY_SRC_REG_ERR_CODE_TEST_ERR_CODE_TEST_MASK                                            (0x1f)
#endif
#define CLP_ENTROPY_SRC_REG_MAIN_SM_STATE                                                           (0x200030e0)
#ifndef ENTROPY_SRC_REG_MAIN_SM_STATE
#define ENTROPY_SRC_REG_MAIN_SM_STATE                                                               (0xe0)
#define ENTROPY_SRC_REG_MAIN_SM_STATE_MAIN_SM_STATE_LOW                                             (0)
#define ENTROPY_SRC_REG_MAIN_SM_STATE_MAIN_SM_STATE_MASK                                            (0x1ff)
#endif
#define CLP_MBOX_CSR_BASE_ADDR                                                                      (0x30020000)
#define CLP_MBOX_CSR_MBOX_LOCK                                                                      (0x30020000)
#ifndef MBOX_CSR_MBOX_LOCK
#define MBOX_CSR_MBOX_LOCK                                                                          (0x0)
#define MBOX_CSR_MBOX_LOCK_LOCK_LOW                                                                 (0)
#define MBOX_CSR_MBOX_LOCK_LOCK_MASK                                                                (0x1)
#endif
#define CLP_MBOX_CSR_MBOX_USER                                                                      (0x30020004)
#ifndef MBOX_CSR_MBOX_USER
#define MBOX_CSR_MBOX_USER                                                                          (0x4)
#endif
#define CLP_MBOX_CSR_MBOX_CMD                                                                       (0x30020008)
#ifndef MBOX_CSR_MBOX_CMD
#define MBOX_CSR_MBOX_CMD                                                                           (0x8)
#endif
#define CLP_MBOX_CSR_MBOX_DLEN                                                                      (0x3002000c)
#ifndef MBOX_CSR_MBOX_DLEN
#define MBOX_CSR_MBOX_DLEN                                                                          (0xc)
#endif
#define CLP_MBOX_CSR_MBOX_DATAIN                                                                    (0x30020010)
#ifndef MBOX_CSR_MBOX_DATAIN
#define MBOX_CSR_MBOX_DATAIN                                                                        (0x10)
#endif
#define CLP_MBOX_CSR_MBOX_DATAOUT                                                                   (0x30020014)
#ifndef MBOX_CSR_MBOX_DATAOUT
#define MBOX_CSR_MBOX_DATAOUT                                                                       (0x14)
#endif
#define CLP_MBOX_CSR_MBOX_EXECUTE                                                                   (0x30020018)
#ifndef MBOX_CSR_MBOX_EXECUTE
#define MBOX_CSR_MBOX_EXECUTE                                                                       (0x18)
#define MBOX_CSR_MBOX_EXECUTE_EXECUTE_LOW                                                           (0)
#define MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK                                                          (0x1)
#endif
#define CLP_MBOX_CSR_MBOX_STATUS                                                                    (0x3002001c)
#ifndef MBOX_CSR_MBOX_STATUS
#define MBOX_CSR_MBOX_STATUS                                                                        (0x1c)
#define MBOX_CSR_MBOX_STATUS_STATUS_LOW                                                             (0)
#define MBOX_CSR_MBOX_STATUS_STATUS_MASK                                                            (0xf)
#define MBOX_CSR_MBOX_STATUS_ECC_SINGLE_ERROR_LOW                                                   (4)
#define MBOX_CSR_MBOX_STATUS_ECC_SINGLE_ERROR_MASK                                                  (0x10)
#define MBOX_CSR_MBOX_STATUS_ECC_DOUBLE_ERROR_LOW                                                   (5)
#define MBOX_CSR_MBOX_STATUS_ECC_DOUBLE_ERROR_MASK                                                  (0x20)
#define MBOX_CSR_MBOX_STATUS_MBOX_FSM_PS_LOW                                                        (6)
#define MBOX_CSR_MBOX_STATUS_MBOX_FSM_PS_MASK                                                       (0x1c0)
#define MBOX_CSR_MBOX_STATUS_SOC_HAS_LOCK_LOW                                                       (9)
#define MBOX_CSR_MBOX_STATUS_SOC_HAS_LOCK_MASK                                                      (0x200)
#define MBOX_CSR_MBOX_STATUS_MBOX_RDPTR_LOW                                                         (10)
#define MBOX_CSR_MBOX_STATUS_MBOX_RDPTR_MASK                                                        (0x3fffc00)
#define MBOX_CSR_MBOX_STATUS_TAP_HAS_LOCK_LOW                                                       (26)
#define MBOX_CSR_MBOX_STATUS_TAP_HAS_LOCK_MASK                                                      (0x4000000)
#endif
#define CLP_MBOX_CSR_MBOX_UNLOCK                                                                    (0x30020020)
#ifndef MBOX_CSR_MBOX_UNLOCK
#define MBOX_CSR_MBOX_UNLOCK                                                                        (0x20)
#define MBOX_CSR_MBOX_UNLOCK_UNLOCK_LOW                                                             (0)
#define MBOX_CSR_MBOX_UNLOCK_UNLOCK_MASK                                                            (0x1)
#endif
#define CLP_MBOX_CSR_TAP_MODE                                                                       (0x30020024)
#ifndef MBOX_CSR_TAP_MODE
#define MBOX_CSR_TAP_MODE                                                                           (0x24)
#define MBOX_CSR_TAP_MODE_ENABLED_LOW                                                               (0)
#define MBOX_CSR_TAP_MODE_ENABLED_MASK                                                              (0x1)
#endif
#define CLP_SHA512_ACC_CSR_BASE_ADDR                                                                (0x30021000)
#define CLP_SHA512_ACC_CSR_LOCK                                                                     (0x30021000)
#ifndef SHA512_ACC_CSR_LOCK
#define SHA512_ACC_CSR_LOCK                                                                         (0x0)
#define SHA512_ACC_CSR_LOCK_LOCK_LOW                                                                (0)
#define SHA512_ACC_CSR_LOCK_LOCK_MASK                                                               (0x1)
#endif
#define CLP_SHA512_ACC_CSR_USER                                                                     (0x30021004)
#ifndef SHA512_ACC_CSR_USER
#define SHA512_ACC_CSR_USER                                                                         (0x4)
#endif
#define CLP_SHA512_ACC_CSR_MODE                                                                     (0x30021008)
#ifndef SHA512_ACC_CSR_MODE
#define SHA512_ACC_CSR_MODE                                                                         (0x8)
#define SHA512_ACC_CSR_MODE_MODE_LOW                                                                (0)
#define SHA512_ACC_CSR_MODE_MODE_MASK                                                               (0x3)
#define SHA512_ACC_CSR_MODE_ENDIAN_TOGGLE_LOW                                                       (2)
#define SHA512_ACC_CSR_MODE_ENDIAN_TOGGLE_MASK                                                      (0x4)
#endif
#define CLP_SHA512_ACC_CSR_START_ADDRESS                                                            (0x3002100c)
#ifndef SHA512_ACC_CSR_START_ADDRESS
#define SHA512_ACC_CSR_START_ADDRESS                                                                (0xc)
#endif
#define CLP_SHA512_ACC_CSR_DLEN                                                                     (0x30021010)
#ifndef SHA512_ACC_CSR_DLEN
#define SHA512_ACC_CSR_DLEN                                                                         (0x10)
#endif
#define CLP_SHA512_ACC_CSR_DATAIN                                                                   (0x30021014)
#ifndef SHA512_ACC_CSR_DATAIN
#define SHA512_ACC_CSR_DATAIN                                                                       (0x14)
#endif
#define CLP_SHA512_ACC_CSR_EXECUTE                                                                  (0x30021018)
#ifndef SHA512_ACC_CSR_EXECUTE
#define SHA512_ACC_CSR_EXECUTE                                                                      (0x18)
#define SHA512_ACC_CSR_EXECUTE_EXECUTE_LOW                                                          (0)
#define SHA512_ACC_CSR_EXECUTE_EXECUTE_MASK                                                         (0x1)
#endif
#define CLP_SHA512_ACC_CSR_STATUS                                                                   (0x3002101c)
#ifndef SHA512_ACC_CSR_STATUS
#define SHA512_ACC_CSR_STATUS                                                                       (0x1c)
#define SHA512_ACC_CSR_STATUS_VALID_LOW                                                             (0)
#define SHA512_ACC_CSR_STATUS_VALID_MASK                                                            (0x1)
#define SHA512_ACC_CSR_STATUS_SOC_HAS_LOCK_LOW                                                      (1)
#define SHA512_ACC_CSR_STATUS_SOC_HAS_LOCK_MASK                                                     (0x2)
#endif
#define CLP_SHA512_ACC_CSR_DIGEST_0                                                                 (0x30021020)
#ifndef SHA512_ACC_CSR_DIGEST_0
#define SHA512_ACC_CSR_DIGEST_0                                                                     (0x20)
#endif
#define CLP_SHA512_ACC_CSR_DIGEST_1                                                                 (0x30021024)
#ifndef SHA512_ACC_CSR_DIGEST_1
#define SHA512_ACC_CSR_DIGEST_1                                                                     (0x24)
#endif
#define CLP_SHA512_ACC_CSR_DIGEST_2                                                                 (0x30021028)
#ifndef SHA512_ACC_CSR_DIGEST_2
#define SHA512_ACC_CSR_DIGEST_2                                                                     (0x28)
#endif
#define CLP_SHA512_ACC_CSR_DIGEST_3                                                                 (0x3002102c)
#ifndef SHA512_ACC_CSR_DIGEST_3
#define SHA512_ACC_CSR_DIGEST_3                                                                     (0x2c)
#endif
#define CLP_SHA512_ACC_CSR_DIGEST_4                                                                 (0x30021030)
#ifndef SHA512_ACC_CSR_DIGEST_4
#define SHA512_ACC_CSR_DIGEST_4                                                                     (0x30)
#endif
#define CLP_SHA512_ACC_CSR_DIGEST_5                                                                 (0x30021034)
#ifndef SHA512_ACC_CSR_DIGEST_5
#define SHA512_ACC_CSR_DIGEST_5                                                                     (0x34)
#endif
#define CLP_SHA512_ACC_CSR_DIGEST_6                                                                 (0x30021038)
#ifndef SHA512_ACC_CSR_DIGEST_6
#define SHA512_ACC_CSR_DIGEST_6                                                                     (0x38)
#endif
#define CLP_SHA512_ACC_CSR_DIGEST_7                                                                 (0x3002103c)
#ifndef SHA512_ACC_CSR_DIGEST_7
#define SHA512_ACC_CSR_DIGEST_7                                                                     (0x3c)
#endif
#define CLP_SHA512_ACC_CSR_DIGEST_8                                                                 (0x30021040)
#ifndef SHA512_ACC_CSR_DIGEST_8
#define SHA512_ACC_CSR_DIGEST_8                                                                     (0x40)
#endif
#define CLP_SHA512_ACC_CSR_DIGEST_9                                                                 (0x30021044)
#ifndef SHA512_ACC_CSR_DIGEST_9
#define SHA512_ACC_CSR_DIGEST_9                                                                     (0x44)
#endif
#define CLP_SHA512_ACC_CSR_DIGEST_10                                                                (0x30021048)
#ifndef SHA512_ACC_CSR_DIGEST_10
#define SHA512_ACC_CSR_DIGEST_10                                                                    (0x48)
#endif
#define CLP_SHA512_ACC_CSR_DIGEST_11                                                                (0x3002104c)
#ifndef SHA512_ACC_CSR_DIGEST_11
#define SHA512_ACC_CSR_DIGEST_11                                                                    (0x4c)
#endif
#define CLP_SHA512_ACC_CSR_DIGEST_12                                                                (0x30021050)
#ifndef SHA512_ACC_CSR_DIGEST_12
#define SHA512_ACC_CSR_DIGEST_12                                                                    (0x50)
#endif
#define CLP_SHA512_ACC_CSR_DIGEST_13                                                                (0x30021054)
#ifndef SHA512_ACC_CSR_DIGEST_13
#define SHA512_ACC_CSR_DIGEST_13                                                                    (0x54)
#endif
#define CLP_SHA512_ACC_CSR_DIGEST_14                                                                (0x30021058)
#ifndef SHA512_ACC_CSR_DIGEST_14
#define SHA512_ACC_CSR_DIGEST_14                                                                    (0x58)
#endif
#define CLP_SHA512_ACC_CSR_DIGEST_15                                                                (0x3002105c)
#ifndef SHA512_ACC_CSR_DIGEST_15
#define SHA512_ACC_CSR_DIGEST_15                                                                    (0x5c)
#endif
#define CLP_SHA512_ACC_CSR_CONTROL                                                                  (0x30021060)
#ifndef SHA512_ACC_CSR_CONTROL
#define SHA512_ACC_CSR_CONTROL                                                                      (0x60)
#define SHA512_ACC_CSR_CONTROL_ZEROIZE_LOW                                                          (0)
#define SHA512_ACC_CSR_CONTROL_ZEROIZE_MASK                                                         (0x1)
#endif
#define CLP_SHA512_ACC_CSR_INTR_BLOCK_RF_START                                                      (0x30021800)
#define CLP_SHA512_ACC_CSR_INTR_BLOCK_RF_GLOBAL_INTR_EN_R                                           (0x30021800)
#ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_GLOBAL_INTR_EN_R
#define SHA512_ACC_CSR_INTR_BLOCK_RF_GLOBAL_INTR_EN_R                                               (0x800)
#define SHA512_ACC_CSR_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_LOW                                  (0)
#define SHA512_ACC_CSR_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_MASK                                 (0x1)
#define SHA512_ACC_CSR_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_LOW                                  (1)
#define SHA512_ACC_CSR_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_MASK                                 (0x2)
#endif
#define CLP_SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_EN_R                                            (0x30021804)
#ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_EN_R
#define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_EN_R                                                (0x804)
#define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR0_EN_LOW                                  (0)
#define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR0_EN_MASK                                 (0x1)
#define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR1_EN_LOW                                  (1)
#define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR1_EN_MASK                                 (0x2)
#define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR2_EN_LOW                                  (2)
#define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR2_EN_MASK                                 (0x4)
#define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR3_EN_LOW                                  (3)
#define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR3_EN_MASK                                 (0x8)
#endif
#define CLP_SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTR_EN_R                                            (0x30021808)
#ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTR_EN_R
#define SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTR_EN_R                                                (0x808)
#define SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_CMD_DONE_EN_LOW                          (0)
#define SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_CMD_DONE_EN_MASK                         (0x1)
#endif
#define CLP_SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R                                        (0x3002180c)
#ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R
#define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R                                            (0x80c)
#define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS_LOW                                (0)
#define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS_MASK                               (0x1)
#endif
#define CLP_SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R                                        (0x30021810)
#ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R
#define SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R                                            (0x810)
#define SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS_LOW                                (0)
#define SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS_MASK                               (0x1)
#endif
#define CLP_SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R                                      (0x30021814)
#ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R
#define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R                                          (0x814)
#define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR0_STS_LOW                           (0)
#define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR0_STS_MASK                          (0x1)
#define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR1_STS_LOW                           (1)
#define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR1_STS_MASK                          (0x2)
#define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR2_STS_LOW                           (2)
#define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR2_STS_MASK                          (0x4)
#define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR3_STS_LOW                           (3)
#define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR3_STS_MASK                          (0x8)
#endif
#define CLP_SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R                                      (0x30021818)
#ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R
#define SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R                                          (0x818)
#define SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_LOW                   (0)
#define SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK                  (0x1)
#endif
#define CLP_SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_TRIG_R                                          (0x3002181c)
#ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_TRIG_R
#define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_TRIG_R                                              (0x81c)
#define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR0_TRIG_LOW                              (0)
#define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR0_TRIG_MASK                             (0x1)
#define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR1_TRIG_LOW                              (1)
#define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR1_TRIG_MASK                             (0x2)
#define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR2_TRIG_LOW                              (2)
#define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR2_TRIG_MASK                             (0x4)
#define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR3_TRIG_LOW                              (3)
#define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR3_TRIG_MASK                             (0x8)
#endif
#define CLP_SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R                                          (0x30021820)
#ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R
#define SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R                                              (0x820)
#define SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_DONE_TRIG_LOW                      (0)
#define SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_DONE_TRIG_MASK                     (0x1)
#endif
#define CLP_SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR0_INTR_COUNT_R                                        (0x30021900)
#ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR0_INTR_COUNT_R
#define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR0_INTR_COUNT_R                                            (0x900)
#endif
#define CLP_SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR1_INTR_COUNT_R                                        (0x30021904)
#ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR1_INTR_COUNT_R
#define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR1_INTR_COUNT_R                                            (0x904)
#endif
#define CLP_SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR2_INTR_COUNT_R                                        (0x30021908)
#ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR2_INTR_COUNT_R
#define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR2_INTR_COUNT_R                                            (0x908)
#endif
#define CLP_SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR3_INTR_COUNT_R                                        (0x3002190c)
#ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR3_INTR_COUNT_R
#define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR3_INTR_COUNT_R                                            (0x90c)
#endif
#define CLP_SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R                                (0x30021980)
#ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R
#define SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R                                    (0x980)
#endif
#define CLP_SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR0_INTR_COUNT_INCR_R                                   (0x30021a00)
#ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR0_INTR_COUNT_INCR_R
#define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR0_INTR_COUNT_INCR_R                                       (0xa00)
#define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR0_INTR_COUNT_INCR_R_PULSE_LOW                             (0)
#define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR0_INTR_COUNT_INCR_R_PULSE_MASK                            (0x1)
#endif
#define CLP_SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR1_INTR_COUNT_INCR_R                                   (0x30021a04)
#ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR1_INTR_COUNT_INCR_R
#define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR1_INTR_COUNT_INCR_R                                       (0xa04)
#define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR1_INTR_COUNT_INCR_R_PULSE_LOW                             (0)
#define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR1_INTR_COUNT_INCR_R_PULSE_MASK                            (0x1)
#endif
#define CLP_SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R                                   (0x30021a08)
#ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R
#define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R                                       (0xa08)
#define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R_PULSE_LOW                             (0)
#define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R_PULSE_MASK                            (0x1)
#endif
#define CLP_SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R                                   (0x30021a0c)
#ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R
#define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R                                       (0xa0c)
#define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R_PULSE_LOW                             (0)
#define SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R_PULSE_MASK                            (0x1)
#endif
#define CLP_SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R                           (0x30021a10)
#ifndef SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R
#define SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R                               (0xa10)
#define SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R_PULSE_LOW                     (0)
#define SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R_PULSE_MASK                    (0x1)
#endif
#define CLP_AXI_DMA_REG_BASE_ADDR                                                                   (0x30022000)
#define CLP_AXI_DMA_REG_ID                                                                          (0x30022000)
#ifndef AXI_DMA_REG_ID
#define AXI_DMA_REG_ID                                                                              (0x0)
#endif
#define CLP_AXI_DMA_REG_CAP                                                                         (0x30022004)
#ifndef AXI_DMA_REG_CAP
#define AXI_DMA_REG_CAP                                                                             (0x4)
#define AXI_DMA_REG_CAP_FIFO_MAX_DEPTH_LOW                                                          (0)
#define AXI_DMA_REG_CAP_FIFO_MAX_DEPTH_MASK                                                         (0xfff)
#define AXI_DMA_REG_CAP_RSVD_LOW                                                                    (12)
#define AXI_DMA_REG_CAP_RSVD_MASK                                                                   (0xfffff000)
#endif
#define CLP_AXI_DMA_REG_CTRL                                                                        (0x30022008)
#ifndef AXI_DMA_REG_CTRL
#define AXI_DMA_REG_CTRL                                                                            (0x8)
#define AXI_DMA_REG_CTRL_GO_LOW                                                                     (0)
#define AXI_DMA_REG_CTRL_GO_MASK                                                                    (0x1)
#define AXI_DMA_REG_CTRL_FLUSH_LOW                                                                  (1)
#define AXI_DMA_REG_CTRL_FLUSH_MASK                                                                 (0x2)
#define AXI_DMA_REG_CTRL_AES_MODE_EN_LOW                                                            (2)
#define AXI_DMA_REG_CTRL_AES_MODE_EN_MASK                                                           (0x4)
#define AXI_DMA_REG_CTRL_AES_GCM_MODE_LOW                                                           (3)
#define AXI_DMA_REG_CTRL_AES_GCM_MODE_MASK                                                          (0x8)
#define AXI_DMA_REG_CTRL_RSVD0_LOW                                                                  (4)
#define AXI_DMA_REG_CTRL_RSVD0_MASK                                                                 (0xfff0)
#define AXI_DMA_REG_CTRL_RD_ROUTE_LOW                                                               (16)
#define AXI_DMA_REG_CTRL_RD_ROUTE_MASK                                                              (0x30000)
#define AXI_DMA_REG_CTRL_RSVD1_LOW                                                                  (18)
#define AXI_DMA_REG_CTRL_RSVD1_MASK                                                                 (0xc0000)
#define AXI_DMA_REG_CTRL_RD_FIXED_LOW                                                               (20)
#define AXI_DMA_REG_CTRL_RD_FIXED_MASK                                                              (0x100000)
#define AXI_DMA_REG_CTRL_RSVD2_LOW                                                                  (21)
#define AXI_DMA_REG_CTRL_RSVD2_MASK                                                                 (0xe00000)
#define AXI_DMA_REG_CTRL_WR_ROUTE_LOW                                                               (24)
#define AXI_DMA_REG_CTRL_WR_ROUTE_MASK                                                              (0x3000000)
#define AXI_DMA_REG_CTRL_RSVD3_LOW                                                                  (26)
#define AXI_DMA_REG_CTRL_RSVD3_MASK                                                                 (0xc000000)
#define AXI_DMA_REG_CTRL_WR_FIXED_LOW                                                               (28)
#define AXI_DMA_REG_CTRL_WR_FIXED_MASK                                                              (0x10000000)
#define AXI_DMA_REG_CTRL_RSVD4_LOW                                                                  (29)
#define AXI_DMA_REG_CTRL_RSVD4_MASK                                                                 (0xe0000000)
#endif
#define CLP_AXI_DMA_REG_STATUS0                                                                     (0x3002200c)
#ifndef AXI_DMA_REG_STATUS0
#define AXI_DMA_REG_STATUS0                                                                         (0xc)
#define AXI_DMA_REG_STATUS0_BUSY_LOW                                                                (0)
#define AXI_DMA_REG_STATUS0_BUSY_MASK                                                               (0x1)
#define AXI_DMA_REG_STATUS0_ERROR_LOW                                                               (1)
#define AXI_DMA_REG_STATUS0_ERROR_MASK                                                              (0x2)
#define AXI_DMA_REG_STATUS0_RSVD0_LOW                                                               (2)
#define AXI_DMA_REG_STATUS0_RSVD0_MASK                                                              (0xc)
#define AXI_DMA_REG_STATUS0_FIFO_DEPTH_LOW                                                          (4)
#define AXI_DMA_REG_STATUS0_FIFO_DEPTH_MASK                                                         (0xfff0)
#define AXI_DMA_REG_STATUS0_AXI_DMA_FSM_PS_LOW                                                      (16)
#define AXI_DMA_REG_STATUS0_AXI_DMA_FSM_PS_MASK                                                     (0x30000)
#define AXI_DMA_REG_STATUS0_PAYLOAD_AVAILABLE_LOW                                                   (18)
#define AXI_DMA_REG_STATUS0_PAYLOAD_AVAILABLE_MASK                                                  (0x40000)
#define AXI_DMA_REG_STATUS0_IMAGE_ACTIVATED_LOW                                                     (19)
#define AXI_DMA_REG_STATUS0_IMAGE_ACTIVATED_MASK                                                    (0x80000)
#define AXI_DMA_REG_STATUS0_AXI_DMA_AES_FSM_PS_LOW                                                  (20)
#define AXI_DMA_REG_STATUS0_AXI_DMA_AES_FSM_PS_MASK                                                 (0xf00000)
#define AXI_DMA_REG_STATUS0_RSVD1_LOW                                                               (24)
#define AXI_DMA_REG_STATUS0_RSVD1_MASK                                                              (0xff000000)
#endif
#define CLP_AXI_DMA_REG_STATUS1                                                                     (0x30022010)
#ifndef AXI_DMA_REG_STATUS1
#define AXI_DMA_REG_STATUS1                                                                         (0x10)
#endif
#define CLP_AXI_DMA_REG_SRC_ADDR_L                                                                  (0x30022014)
#ifndef AXI_DMA_REG_SRC_ADDR_L
#define AXI_DMA_REG_SRC_ADDR_L                                                                      (0x14)
#endif
#define CLP_AXI_DMA_REG_SRC_ADDR_H                                                                  (0x30022018)
#ifndef AXI_DMA_REG_SRC_ADDR_H
#define AXI_DMA_REG_SRC_ADDR_H                                                                      (0x18)
#endif
#define CLP_AXI_DMA_REG_DST_ADDR_L                                                                  (0x3002201c)
#ifndef AXI_DMA_REG_DST_ADDR_L
#define AXI_DMA_REG_DST_ADDR_L                                                                      (0x1c)
#endif
#define CLP_AXI_DMA_REG_DST_ADDR_H                                                                  (0x30022020)
#ifndef AXI_DMA_REG_DST_ADDR_H
#define AXI_DMA_REG_DST_ADDR_H                                                                      (0x20)
#endif
#define CLP_AXI_DMA_REG_BYTE_COUNT                                                                  (0x30022024)
#ifndef AXI_DMA_REG_BYTE_COUNT
#define AXI_DMA_REG_BYTE_COUNT                                                                      (0x24)
#endif
#define CLP_AXI_DMA_REG_BLOCK_SIZE                                                                  (0x30022028)
#ifndef AXI_DMA_REG_BLOCK_SIZE
#define AXI_DMA_REG_BLOCK_SIZE                                                                      (0x28)
#define AXI_DMA_REG_BLOCK_SIZE_SIZE_LOW                                                             (0)
#define AXI_DMA_REG_BLOCK_SIZE_SIZE_MASK                                                            (0xfff)
#define AXI_DMA_REG_BLOCK_SIZE_RSVD_LOW                                                             (12)
#define AXI_DMA_REG_BLOCK_SIZE_RSVD_MASK                                                            (0xfffff000)
#endif
#define CLP_AXI_DMA_REG_WRITE_DATA                                                                  (0x3002202c)
#ifndef AXI_DMA_REG_WRITE_DATA
#define AXI_DMA_REG_WRITE_DATA                                                                      (0x2c)
#endif
#define CLP_AXI_DMA_REG_READ_DATA                                                                   (0x30022030)
#ifndef AXI_DMA_REG_READ_DATA
#define AXI_DMA_REG_READ_DATA                                                                       (0x30)
#endif
#define CLP_AXI_DMA_REG_INTR_BLOCK_RF_START                                                         (0x30022800)
#define CLP_AXI_DMA_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R                                              (0x30022800)
#ifndef AXI_DMA_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R
#define AXI_DMA_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R                                                  (0x800)
#define AXI_DMA_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_LOW                                     (0)
#define AXI_DMA_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_MASK                                    (0x1)
#define AXI_DMA_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_LOW                                     (1)
#define AXI_DMA_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_MASK                                    (0x2)
#endif
#define CLP_AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R                                               (0x30022804)
#ifndef AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R                                                   (0x804)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_CMD_DEC_EN_LOW                              (0)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_CMD_DEC_EN_MASK                             (0x1)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_AXI_RD_EN_LOW                               (1)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_AXI_RD_EN_MASK                              (0x2)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_AXI_WR_EN_LOW                               (2)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_AXI_WR_EN_MASK                              (0x4)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_MBOX_LOCK_EN_LOW                            (3)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_MBOX_LOCK_EN_MASK                           (0x8)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_SHA_LOCK_EN_LOW                             (4)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_SHA_LOCK_EN_MASK                            (0x10)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_FIFO_OFLOW_EN_LOW                           (5)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_FIFO_OFLOW_EN_MASK                          (0x20)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_FIFO_UFLOW_EN_LOW                           (6)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_FIFO_UFLOW_EN_MASK                          (0x40)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_AES_CIF_EN_LOW                              (7)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_AES_CIF_EN_MASK                             (0x80)
#endif
#define CLP_AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R                                               (0x30022808)
#ifndef AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R
#define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R                                                   (0x808)
#define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_TXN_DONE_EN_LOW                             (0)
#define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_TXN_DONE_EN_MASK                            (0x1)
#define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_FIFO_EMPTY_EN_LOW                           (1)
#define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_FIFO_EMPTY_EN_MASK                          (0x2)
#define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_FIFO_NOT_EMPTY_EN_LOW                       (2)
#define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_FIFO_NOT_EMPTY_EN_MASK                      (0x4)
#define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_FIFO_FULL_EN_LOW                            (3)
#define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_FIFO_FULL_EN_MASK                           (0x8)
#define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_FIFO_NOT_FULL_EN_LOW                        (4)
#define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_FIFO_NOT_FULL_EN_MASK                       (0x10)
#endif
#define CLP_AXI_DMA_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R                                           (0x3002280c)
#ifndef AXI_DMA_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R                                               (0x80c)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS_LOW                                   (0)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS_MASK                                  (0x1)
#endif
#define CLP_AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R                                           (0x30022810)
#ifndef AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R
#define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R                                               (0x810)
#define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS_LOW                                   (0)
#define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS_MASK                                  (0x1)
#endif
#define CLP_AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R                                         (0x30022814)
#ifndef AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R                                             (0x814)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_CMD_DEC_STS_LOW                       (0)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_CMD_DEC_STS_MASK                      (0x1)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_AXI_RD_STS_LOW                        (1)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_AXI_RD_STS_MASK                       (0x2)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_AXI_WR_STS_LOW                        (2)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_AXI_WR_STS_MASK                       (0x4)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_MBOX_LOCK_STS_LOW                     (3)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_MBOX_LOCK_STS_MASK                    (0x8)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_SHA_LOCK_STS_LOW                      (4)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_SHA_LOCK_STS_MASK                     (0x10)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_FIFO_OFLOW_STS_LOW                    (5)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_FIFO_OFLOW_STS_MASK                   (0x20)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_FIFO_UFLOW_STS_LOW                    (6)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_FIFO_UFLOW_STS_MASK                   (0x40)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_AES_CIF_STS_LOW                       (7)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_AES_CIF_STS_MASK                      (0x80)
#endif
#define CLP_AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R                                         (0x30022818)
#ifndef AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R
#define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R                                             (0x818)
#define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_TXN_DONE_STS_LOW                      (0)
#define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_TXN_DONE_STS_MASK                     (0x1)
#define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_FIFO_EMPTY_STS_LOW                    (1)
#define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_FIFO_EMPTY_STS_MASK                   (0x2)
#define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_FIFO_NOT_EMPTY_STS_LOW                (2)
#define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_FIFO_NOT_EMPTY_STS_MASK               (0x4)
#define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_FIFO_FULL_STS_LOW                     (3)
#define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_FIFO_FULL_STS_MASK                    (0x8)
#define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_FIFO_NOT_FULL_STS_LOW                 (4)
#define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_FIFO_NOT_FULL_STS_MASK                (0x10)
#endif
#define CLP_AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R                                             (0x3002281c)
#ifndef AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R                                                 (0x81c)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_CMD_DEC_TRIG_LOW                          (0)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_CMD_DEC_TRIG_MASK                         (0x1)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_AXI_RD_TRIG_LOW                           (1)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_AXI_RD_TRIG_MASK                          (0x2)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_AXI_WR_TRIG_LOW                           (2)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_AXI_WR_TRIG_MASK                          (0x4)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_MBOX_LOCK_TRIG_LOW                        (3)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_MBOX_LOCK_TRIG_MASK                       (0x8)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_SHA_LOCK_TRIG_LOW                         (4)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_SHA_LOCK_TRIG_MASK                        (0x10)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_FIFO_OFLOW_TRIG_LOW                       (5)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_FIFO_OFLOW_TRIG_MASK                      (0x20)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_FIFO_UFLOW_TRIG_LOW                       (6)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_FIFO_UFLOW_TRIG_MASK                      (0x40)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_AES_CIF_TRIG_LOW                          (7)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_AES_CIF_TRIG_MASK                         (0x80)
#endif
#define CLP_AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R                                             (0x30022820)
#ifndef AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R
#define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R                                                 (0x820)
#define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_TXN_DONE_TRIG_LOW                         (0)
#define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_TXN_DONE_TRIG_MASK                        (0x1)
#define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_FIFO_EMPTY_TRIG_LOW                       (1)
#define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_FIFO_EMPTY_TRIG_MASK                      (0x2)
#define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_FIFO_NOT_EMPTY_TRIG_LOW                   (2)
#define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_FIFO_NOT_EMPTY_TRIG_MASK                  (0x4)
#define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_FIFO_FULL_TRIG_LOW                        (3)
#define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_FIFO_FULL_TRIG_MASK                       (0x8)
#define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_FIFO_NOT_FULL_TRIG_LOW                    (4)
#define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_FIFO_NOT_FULL_TRIG_MASK                   (0x10)
#endif
#define CLP_AXI_DMA_REG_INTR_BLOCK_RF_ERROR_CMD_DEC_INTR_COUNT_R                                    (0x30022900)
#ifndef AXI_DMA_REG_INTR_BLOCK_RF_ERROR_CMD_DEC_INTR_COUNT_R
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_CMD_DEC_INTR_COUNT_R                                        (0x900)
#endif
#define CLP_AXI_DMA_REG_INTR_BLOCK_RF_ERROR_AXI_RD_INTR_COUNT_R                                     (0x30022904)
#ifndef AXI_DMA_REG_INTR_BLOCK_RF_ERROR_AXI_RD_INTR_COUNT_R
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_AXI_RD_INTR_COUNT_R                                         (0x904)
#endif
#define CLP_AXI_DMA_REG_INTR_BLOCK_RF_ERROR_AXI_WR_INTR_COUNT_R                                     (0x30022908)
#ifndef AXI_DMA_REG_INTR_BLOCK_RF_ERROR_AXI_WR_INTR_COUNT_R
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_AXI_WR_INTR_COUNT_R                                         (0x908)
#endif
#define CLP_AXI_DMA_REG_INTR_BLOCK_RF_ERROR_MBOX_LOCK_INTR_COUNT_R                                  (0x3002290c)
#ifndef AXI_DMA_REG_INTR_BLOCK_RF_ERROR_MBOX_LOCK_INTR_COUNT_R
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_MBOX_LOCK_INTR_COUNT_R                                      (0x90c)
#endif
#define CLP_AXI_DMA_REG_INTR_BLOCK_RF_ERROR_SHA_LOCK_INTR_COUNT_R                                   (0x30022910)
#ifndef AXI_DMA_REG_INTR_BLOCK_RF_ERROR_SHA_LOCK_INTR_COUNT_R
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_SHA_LOCK_INTR_COUNT_R                                       (0x910)
#endif
#define CLP_AXI_DMA_REG_INTR_BLOCK_RF_ERROR_FIFO_OFLOW_INTR_COUNT_R                                 (0x30022914)
#ifndef AXI_DMA_REG_INTR_BLOCK_RF_ERROR_FIFO_OFLOW_INTR_COUNT_R
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_FIFO_OFLOW_INTR_COUNT_R                                     (0x914)
#endif
#define CLP_AXI_DMA_REG_INTR_BLOCK_RF_ERROR_FIFO_UFLOW_INTR_COUNT_R                                 (0x30022918)
#ifndef AXI_DMA_REG_INTR_BLOCK_RF_ERROR_FIFO_UFLOW_INTR_COUNT_R
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_FIFO_UFLOW_INTR_COUNT_R                                     (0x918)
#endif
#define CLP_AXI_DMA_REG_INTR_BLOCK_RF_ERROR_AES_CIF_INTR_COUNT_R                                    (0x3002291c)
#ifndef AXI_DMA_REG_INTR_BLOCK_RF_ERROR_AES_CIF_INTR_COUNT_R
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_AES_CIF_INTR_COUNT_R                                        (0x91c)
#endif
#define CLP_AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_TXN_DONE_INTR_COUNT_R                                   (0x30022980)
#ifndef AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_TXN_DONE_INTR_COUNT_R
#define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_TXN_DONE_INTR_COUNT_R                                       (0x980)
#endif
#define CLP_AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_FIFO_EMPTY_INTR_COUNT_R                                 (0x30022984)
#ifndef AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_FIFO_EMPTY_INTR_COUNT_R
#define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_FIFO_EMPTY_INTR_COUNT_R                                     (0x984)
#endif
#define CLP_AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_FIFO_NOT_EMPTY_INTR_COUNT_R                             (0x30022988)
#ifndef AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_FIFO_NOT_EMPTY_INTR_COUNT_R
#define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_FIFO_NOT_EMPTY_INTR_COUNT_R                                 (0x988)
#endif
#define CLP_AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_FIFO_FULL_INTR_COUNT_R                                  (0x3002298c)
#ifndef AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_FIFO_FULL_INTR_COUNT_R
#define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_FIFO_FULL_INTR_COUNT_R                                      (0x98c)
#endif
#define CLP_AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_FIFO_NOT_FULL_INTR_COUNT_R                              (0x30022990)
#ifndef AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_FIFO_NOT_FULL_INTR_COUNT_R
#define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_FIFO_NOT_FULL_INTR_COUNT_R                                  (0x990)
#endif
#define CLP_AXI_DMA_REG_INTR_BLOCK_RF_ERROR_CMD_DEC_INTR_COUNT_INCR_R                               (0x30022a00)
#ifndef AXI_DMA_REG_INTR_BLOCK_RF_ERROR_CMD_DEC_INTR_COUNT_INCR_R
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_CMD_DEC_INTR_COUNT_INCR_R                                   (0xa00)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_CMD_DEC_INTR_COUNT_INCR_R_PULSE_LOW                         (0)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_CMD_DEC_INTR_COUNT_INCR_R_PULSE_MASK                        (0x1)
#endif
#define CLP_AXI_DMA_REG_INTR_BLOCK_RF_ERROR_AXI_RD_INTR_COUNT_INCR_R                                (0x30022a04)
#ifndef AXI_DMA_REG_INTR_BLOCK_RF_ERROR_AXI_RD_INTR_COUNT_INCR_R
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_AXI_RD_INTR_COUNT_INCR_R                                    (0xa04)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_AXI_RD_INTR_COUNT_INCR_R_PULSE_LOW                          (0)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_AXI_RD_INTR_COUNT_INCR_R_PULSE_MASK                         (0x1)
#endif
#define CLP_AXI_DMA_REG_INTR_BLOCK_RF_ERROR_AXI_WR_INTR_COUNT_INCR_R                                (0x30022a08)
#ifndef AXI_DMA_REG_INTR_BLOCK_RF_ERROR_AXI_WR_INTR_COUNT_INCR_R
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_AXI_WR_INTR_COUNT_INCR_R                                    (0xa08)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_AXI_WR_INTR_COUNT_INCR_R_PULSE_LOW                          (0)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_AXI_WR_INTR_COUNT_INCR_R_PULSE_MASK                         (0x1)
#endif
#define CLP_AXI_DMA_REG_INTR_BLOCK_RF_ERROR_MBOX_LOCK_INTR_COUNT_INCR_R                             (0x30022a0c)
#ifndef AXI_DMA_REG_INTR_BLOCK_RF_ERROR_MBOX_LOCK_INTR_COUNT_INCR_R
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_MBOX_LOCK_INTR_COUNT_INCR_R                                 (0xa0c)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_MBOX_LOCK_INTR_COUNT_INCR_R_PULSE_LOW                       (0)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_MBOX_LOCK_INTR_COUNT_INCR_R_PULSE_MASK                      (0x1)
#endif
#define CLP_AXI_DMA_REG_INTR_BLOCK_RF_ERROR_SHA_LOCK_INTR_COUNT_INCR_R                              (0x30022a10)
#ifndef AXI_DMA_REG_INTR_BLOCK_RF_ERROR_SHA_LOCK_INTR_COUNT_INCR_R
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_SHA_LOCK_INTR_COUNT_INCR_R                                  (0xa10)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_SHA_LOCK_INTR_COUNT_INCR_R_PULSE_LOW                        (0)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_SHA_LOCK_INTR_COUNT_INCR_R_PULSE_MASK                       (0x1)
#endif
#define CLP_AXI_DMA_REG_INTR_BLOCK_RF_ERROR_FIFO_OFLOW_INTR_COUNT_INCR_R                            (0x30022a14)
#ifndef AXI_DMA_REG_INTR_BLOCK_RF_ERROR_FIFO_OFLOW_INTR_COUNT_INCR_R
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_FIFO_OFLOW_INTR_COUNT_INCR_R                                (0xa14)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_FIFO_OFLOW_INTR_COUNT_INCR_R_PULSE_LOW                      (0)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_FIFO_OFLOW_INTR_COUNT_INCR_R_PULSE_MASK                     (0x1)
#endif
#define CLP_AXI_DMA_REG_INTR_BLOCK_RF_ERROR_FIFO_UFLOW_INTR_COUNT_INCR_R                            (0x30022a18)
#ifndef AXI_DMA_REG_INTR_BLOCK_RF_ERROR_FIFO_UFLOW_INTR_COUNT_INCR_R
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_FIFO_UFLOW_INTR_COUNT_INCR_R                                (0xa18)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_FIFO_UFLOW_INTR_COUNT_INCR_R_PULSE_LOW                      (0)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_FIFO_UFLOW_INTR_COUNT_INCR_R_PULSE_MASK                     (0x1)
#endif
#define CLP_AXI_DMA_REG_INTR_BLOCK_RF_ERROR_AES_CIF_INTR_COUNT_INCR_R                               (0x30022a1c)
#ifndef AXI_DMA_REG_INTR_BLOCK_RF_ERROR_AES_CIF_INTR_COUNT_INCR_R
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_AES_CIF_INTR_COUNT_INCR_R                                   (0xa1c)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_AES_CIF_INTR_COUNT_INCR_R_PULSE_LOW                         (0)
#define AXI_DMA_REG_INTR_BLOCK_RF_ERROR_AES_CIF_INTR_COUNT_INCR_R_PULSE_MASK                        (0x1)
#endif
#define CLP_AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_TXN_DONE_INTR_COUNT_INCR_R                              (0x30022a20)
#ifndef AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_TXN_DONE_INTR_COUNT_INCR_R
#define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_TXN_DONE_INTR_COUNT_INCR_R                                  (0xa20)
#define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_TXN_DONE_INTR_COUNT_INCR_R_PULSE_LOW                        (0)
#define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_TXN_DONE_INTR_COUNT_INCR_R_PULSE_MASK                       (0x1)
#endif
#define CLP_AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_FIFO_EMPTY_INTR_COUNT_INCR_R                            (0x30022a24)
#ifndef AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_FIFO_EMPTY_INTR_COUNT_INCR_R
#define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_FIFO_EMPTY_INTR_COUNT_INCR_R                                (0xa24)
#define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_FIFO_EMPTY_INTR_COUNT_INCR_R_PULSE_LOW                      (0)
#define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_FIFO_EMPTY_INTR_COUNT_INCR_R_PULSE_MASK                     (0x1)
#endif
#define CLP_AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_FIFO_NOT_EMPTY_INTR_COUNT_INCR_R                        (0x30022a28)
#ifndef AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_FIFO_NOT_EMPTY_INTR_COUNT_INCR_R
#define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_FIFO_NOT_EMPTY_INTR_COUNT_INCR_R                            (0xa28)
#define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_FIFO_NOT_EMPTY_INTR_COUNT_INCR_R_PULSE_LOW                  (0)
#define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_FIFO_NOT_EMPTY_INTR_COUNT_INCR_R_PULSE_MASK                 (0x1)
#endif
#define CLP_AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_FIFO_FULL_INTR_COUNT_INCR_R                             (0x30022a2c)
#ifndef AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_FIFO_FULL_INTR_COUNT_INCR_R
#define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_FIFO_FULL_INTR_COUNT_INCR_R                                 (0xa2c)
#define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_FIFO_FULL_INTR_COUNT_INCR_R_PULSE_LOW                       (0)
#define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_FIFO_FULL_INTR_COUNT_INCR_R_PULSE_MASK                      (0x1)
#endif
#define CLP_AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_FIFO_NOT_FULL_INTR_COUNT_INCR_R                         (0x30022a30)
#ifndef AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_FIFO_NOT_FULL_INTR_COUNT_INCR_R
#define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_FIFO_NOT_FULL_INTR_COUNT_INCR_R                             (0xa30)
#define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_FIFO_NOT_FULL_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
#define AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_FIFO_NOT_FULL_INTR_COUNT_INCR_R_PULSE_MASK                  (0x1)
#endif
#define CLP_SOC_IFC_REG_BASE_ADDR                                                                   (0x30030000)
#define CLP_SOC_IFC_REG_CPTRA_HW_ERROR_FATAL                                                        (0x30030000)
#ifndef SOC_IFC_REG_CPTRA_HW_ERROR_FATAL
#define SOC_IFC_REG_CPTRA_HW_ERROR_FATAL                                                            (0x0)
#define SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_ICCM_ECC_UNC_LOW                                           (0)
#define SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_ICCM_ECC_UNC_MASK                                          (0x1)
#define SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_DCCM_ECC_UNC_LOW                                           (1)
#define SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_DCCM_ECC_UNC_MASK                                          (0x2)
#define SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_NMI_PIN_LOW                                                (2)
#define SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_NMI_PIN_MASK                                               (0x4)
#define SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_CRYPTO_ERR_LOW                                             (3)
#define SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_CRYPTO_ERR_MASK                                            (0x8)
#define SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_RSVD_LOW                                                   (4)
#define SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_RSVD_MASK                                                  (0xfffffff0)
#endif
#define CLP_SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL                                                    (0x30030004)
#ifndef SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL
#define SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL                                                        (0x4)
#define SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL_MBOX_PROT_NO_LOCK_LOW                                  (0)
#define SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL_MBOX_PROT_NO_LOCK_MASK                                 (0x1)
#define SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL_MBOX_PROT_OOO_LOW                                      (1)
#define SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL_MBOX_PROT_OOO_MASK                                     (0x2)
#define SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL_MBOX_ECC_UNC_LOW                                       (2)
#define SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL_MBOX_ECC_UNC_MASK                                      (0x4)
#define SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL_RSVD_LOW                                               (3)
#define SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL_RSVD_MASK                                              (0xfffffff8)
#endif
#define CLP_SOC_IFC_REG_CPTRA_FW_ERROR_FATAL                                                        (0x30030008)
#ifndef SOC_IFC_REG_CPTRA_FW_ERROR_FATAL
#define SOC_IFC_REG_CPTRA_FW_ERROR_FATAL                                                            (0x8)
#endif
#define CLP_SOC_IFC_REG_CPTRA_FW_ERROR_NON_FATAL                                                    (0x3003000c)
#ifndef SOC_IFC_REG_CPTRA_FW_ERROR_NON_FATAL
#define SOC_IFC_REG_CPTRA_FW_ERROR_NON_FATAL                                                        (0xc)
#endif
#define CLP_SOC_IFC_REG_CPTRA_HW_ERROR_ENC                                                          (0x30030010)
#ifndef SOC_IFC_REG_CPTRA_HW_ERROR_ENC
#define SOC_IFC_REG_CPTRA_HW_ERROR_ENC                                                              (0x10)
#endif
#define CLP_SOC_IFC_REG_CPTRA_FW_ERROR_ENC                                                          (0x30030014)
#ifndef SOC_IFC_REG_CPTRA_FW_ERROR_ENC
#define SOC_IFC_REG_CPTRA_FW_ERROR_ENC                                                              (0x14)
#endif
#define CLP_SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_0                                              (0x30030018)
#ifndef SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_0
#define SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_0                                                  (0x18)
#endif
#define CLP_SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_1                                              (0x3003001c)
#ifndef SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_1
#define SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_1                                                  (0x1c)
#endif
#define CLP_SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_2                                              (0x30030020)
#ifndef SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_2
#define SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_2                                                  (0x20)
#endif
#define CLP_SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_3                                              (0x30030024)
#ifndef SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_3
#define SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_3                                                  (0x24)
#endif
#define CLP_SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_4                                              (0x30030028)
#ifndef SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_4
#define SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_4                                                  (0x28)
#endif
#define CLP_SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_5                                              (0x3003002c)
#ifndef SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_5
#define SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_5                                                  (0x2c)
#endif
#define CLP_SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_6                                              (0x30030030)
#ifndef SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_6
#define SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_6                                                  (0x30)
#endif
#define CLP_SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_7                                              (0x30030034)
#ifndef SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_7
#define SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_7                                                  (0x34)
#endif
#define CLP_SOC_IFC_REG_CPTRA_BOOT_STATUS                                                           (0x30030038)
#ifndef SOC_IFC_REG_CPTRA_BOOT_STATUS
#define SOC_IFC_REG_CPTRA_BOOT_STATUS                                                               (0x38)
#endif
#define CLP_SOC_IFC_REG_CPTRA_FLOW_STATUS                                                           (0x3003003c)
#ifndef SOC_IFC_REG_CPTRA_FLOW_STATUS
#define SOC_IFC_REG_CPTRA_FLOW_STATUS                                                               (0x3c)
#define SOC_IFC_REG_CPTRA_FLOW_STATUS_STATUS_LOW                                                    (0)
#define SOC_IFC_REG_CPTRA_FLOW_STATUS_STATUS_MASK                                                   (0xffffff)
#define SOC_IFC_REG_CPTRA_FLOW_STATUS_IDEVID_CSR_READY_LOW                                          (24)
#define SOC_IFC_REG_CPTRA_FLOW_STATUS_IDEVID_CSR_READY_MASK                                         (0x1000000)
#define SOC_IFC_REG_CPTRA_FLOW_STATUS_BOOT_FSM_PS_LOW                                               (25)
#define SOC_IFC_REG_CPTRA_FLOW_STATUS_BOOT_FSM_PS_MASK                                              (0xe000000)
#define SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_MB_PROCESSING_LOW                                   (28)
#define SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_MB_PROCESSING_MASK                                  (0x10000000)
#define SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_RUNTIME_LOW                                         (29)
#define SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_RUNTIME_MASK                                        (0x20000000)
#define SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_FUSES_LOW                                           (30)
#define SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_FUSES_MASK                                          (0x40000000)
#define SOC_IFC_REG_CPTRA_FLOW_STATUS_MAILBOX_FLOW_DONE_LOW                                         (31)
#define SOC_IFC_REG_CPTRA_FLOW_STATUS_MAILBOX_FLOW_DONE_MASK                                        (0x80000000)
#endif
#define CLP_SOC_IFC_REG_CPTRA_RESET_REASON                                                          (0x30030040)
#ifndef SOC_IFC_REG_CPTRA_RESET_REASON
#define SOC_IFC_REG_CPTRA_RESET_REASON                                                              (0x40)
#define SOC_IFC_REG_CPTRA_RESET_REASON_FW_UPD_RESET_LOW                                             (0)
#define SOC_IFC_REG_CPTRA_RESET_REASON_FW_UPD_RESET_MASK                                            (0x1)
#define SOC_IFC_REG_CPTRA_RESET_REASON_WARM_RESET_LOW                                               (1)
#define SOC_IFC_REG_CPTRA_RESET_REASON_WARM_RESET_MASK                                              (0x2)
#endif
#define CLP_SOC_IFC_REG_CPTRA_SECURITY_STATE                                                        (0x30030044)
#ifndef SOC_IFC_REG_CPTRA_SECURITY_STATE
#define SOC_IFC_REG_CPTRA_SECURITY_STATE                                                            (0x44)
#define SOC_IFC_REG_CPTRA_SECURITY_STATE_DEVICE_LIFECYCLE_LOW                                       (0)
#define SOC_IFC_REG_CPTRA_SECURITY_STATE_DEVICE_LIFECYCLE_MASK                                      (0x3)
#define SOC_IFC_REG_CPTRA_SECURITY_STATE_DEBUG_LOCKED_LOW                                           (2)
#define SOC_IFC_REG_CPTRA_SECURITY_STATE_DEBUG_LOCKED_MASK                                          (0x4)
#define SOC_IFC_REG_CPTRA_SECURITY_STATE_SCAN_MODE_LOW                                              (3)
#define SOC_IFC_REG_CPTRA_SECURITY_STATE_SCAN_MODE_MASK                                             (0x8)
#define SOC_IFC_REG_CPTRA_SECURITY_STATE_RSVD_LOW                                                   (4)
#define SOC_IFC_REG_CPTRA_SECURITY_STATE_RSVD_MASK                                                  (0xfffffff0)
#endif
#define CLP_SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_0                                                 (0x30030048)
#ifndef SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_0
#define SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_0                                                     (0x48)
#endif
#define CLP_SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_1                                                 (0x3003004c)
#ifndef SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_1
#define SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_1                                                     (0x4c)
#endif
#define CLP_SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_2                                                 (0x30030050)
#ifndef SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_2
#define SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_2                                                     (0x50)
#endif
#define CLP_SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_3                                                 (0x30030054)
#ifndef SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_3
#define SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_3                                                     (0x54)
#endif
#define CLP_SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_4                                                 (0x30030058)
#ifndef SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_4
#define SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_4                                                     (0x58)
#endif
#define CLP_SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_0                                                  (0x3003005c)
#ifndef SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_0
#define SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_0                                                      (0x5c)
#define SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_0_LOCK_LOW                                             (0)
#define SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_0_LOCK_MASK                                            (0x1)
#endif
#define CLP_SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_1                                                  (0x30030060)
#ifndef SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_1
#define SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_1                                                      (0x60)
#define SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_1_LOCK_LOW                                             (0)
#define SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_1_LOCK_MASK                                            (0x1)
#endif
#define CLP_SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_2                                                  (0x30030064)
#ifndef SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_2
#define SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_2                                                      (0x64)
#define SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_2_LOCK_LOW                                             (0)
#define SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_2_LOCK_MASK                                            (0x1)
#endif
#define CLP_SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_3                                                  (0x30030068)
#ifndef SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_3
#define SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_3                                                      (0x68)
#define SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_3_LOCK_LOW                                             (0)
#define SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_3_LOCK_MASK                                            (0x1)
#endif
#define CLP_SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_4                                                  (0x3003006c)
#ifndef SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_4
#define SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_4                                                      (0x6c)
#define SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_4_LOCK_LOW                                             (0)
#define SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_4_LOCK_MASK                                            (0x1)
#endif
#define CLP_SOC_IFC_REG_CPTRA_TRNG_VALID_AXI_USER                                                   (0x30030070)
#ifndef SOC_IFC_REG_CPTRA_TRNG_VALID_AXI_USER
#define SOC_IFC_REG_CPTRA_TRNG_VALID_AXI_USER                                                       (0x70)
#endif
#define CLP_SOC_IFC_REG_CPTRA_TRNG_AXI_USER_LOCK                                                    (0x30030074)
#ifndef SOC_IFC_REG_CPTRA_TRNG_AXI_USER_LOCK
#define SOC_IFC_REG_CPTRA_TRNG_AXI_USER_LOCK                                                        (0x74)
#define SOC_IFC_REG_CPTRA_TRNG_AXI_USER_LOCK_LOCK_LOW                                               (0)
#define SOC_IFC_REG_CPTRA_TRNG_AXI_USER_LOCK_LOCK_MASK                                              (0x1)
#endif
#define CLP_SOC_IFC_REG_CPTRA_TRNG_DATA_0                                                           (0x30030078)
#ifndef SOC_IFC_REG_CPTRA_TRNG_DATA_0
#define SOC_IFC_REG_CPTRA_TRNG_DATA_0                                                               (0x78)
#endif
#define CLP_SOC_IFC_REG_CPTRA_TRNG_DATA_1                                                           (0x3003007c)
#ifndef SOC_IFC_REG_CPTRA_TRNG_DATA_1
#define SOC_IFC_REG_CPTRA_TRNG_DATA_1                                                               (0x7c)
#endif
#define CLP_SOC_IFC_REG_CPTRA_TRNG_DATA_2                                                           (0x30030080)
#ifndef SOC_IFC_REG_CPTRA_TRNG_DATA_2
#define SOC_IFC_REG_CPTRA_TRNG_DATA_2                                                               (0x80)
#endif
#define CLP_SOC_IFC_REG_CPTRA_TRNG_DATA_3                                                           (0x30030084)
#ifndef SOC_IFC_REG_CPTRA_TRNG_DATA_3
#define SOC_IFC_REG_CPTRA_TRNG_DATA_3                                                               (0x84)
#endif
#define CLP_SOC_IFC_REG_CPTRA_TRNG_DATA_4                                                           (0x30030088)
#ifndef SOC_IFC_REG_CPTRA_TRNG_DATA_4
#define SOC_IFC_REG_CPTRA_TRNG_DATA_4                                                               (0x88)
#endif
#define CLP_SOC_IFC_REG_CPTRA_TRNG_DATA_5                                                           (0x3003008c)
#ifndef SOC_IFC_REG_CPTRA_TRNG_DATA_5
#define SOC_IFC_REG_CPTRA_TRNG_DATA_5                                                               (0x8c)
#endif
#define CLP_SOC_IFC_REG_CPTRA_TRNG_DATA_6                                                           (0x30030090)
#ifndef SOC_IFC_REG_CPTRA_TRNG_DATA_6
#define SOC_IFC_REG_CPTRA_TRNG_DATA_6                                                               (0x90)
#endif
#define CLP_SOC_IFC_REG_CPTRA_TRNG_DATA_7                                                           (0x30030094)
#ifndef SOC_IFC_REG_CPTRA_TRNG_DATA_7
#define SOC_IFC_REG_CPTRA_TRNG_DATA_7                                                               (0x94)
#endif
#define CLP_SOC_IFC_REG_CPTRA_TRNG_DATA_8                                                           (0x30030098)
#ifndef SOC_IFC_REG_CPTRA_TRNG_DATA_8
#define SOC_IFC_REG_CPTRA_TRNG_DATA_8                                                               (0x98)
#endif
#define CLP_SOC_IFC_REG_CPTRA_TRNG_DATA_9                                                           (0x3003009c)
#ifndef SOC_IFC_REG_CPTRA_TRNG_DATA_9
#define SOC_IFC_REG_CPTRA_TRNG_DATA_9                                                               (0x9c)
#endif
#define CLP_SOC_IFC_REG_CPTRA_TRNG_DATA_10                                                          (0x300300a0)
#ifndef SOC_IFC_REG_CPTRA_TRNG_DATA_10
#define SOC_IFC_REG_CPTRA_TRNG_DATA_10                                                              (0xa0)
#endif
#define CLP_SOC_IFC_REG_CPTRA_TRNG_DATA_11                                                          (0x300300a4)
#ifndef SOC_IFC_REG_CPTRA_TRNG_DATA_11
#define SOC_IFC_REG_CPTRA_TRNG_DATA_11                                                              (0xa4)
#endif
#define CLP_SOC_IFC_REG_CPTRA_TRNG_CTRL                                                             (0x300300a8)
#ifndef SOC_IFC_REG_CPTRA_TRNG_CTRL
#define SOC_IFC_REG_CPTRA_TRNG_CTRL                                                                 (0xa8)
#define SOC_IFC_REG_CPTRA_TRNG_CTRL_CLEAR_LOW                                                       (0)
#define SOC_IFC_REG_CPTRA_TRNG_CTRL_CLEAR_MASK                                                      (0x1)
#endif
#define CLP_SOC_IFC_REG_CPTRA_TRNG_STATUS                                                           (0x300300ac)
#ifndef SOC_IFC_REG_CPTRA_TRNG_STATUS
#define SOC_IFC_REG_CPTRA_TRNG_STATUS                                                               (0xac)
#define SOC_IFC_REG_CPTRA_TRNG_STATUS_DATA_REQ_LOW                                                  (0)
#define SOC_IFC_REG_CPTRA_TRNG_STATUS_DATA_REQ_MASK                                                 (0x1)
#define SOC_IFC_REG_CPTRA_TRNG_STATUS_DATA_WR_DONE_LOW                                              (1)
#define SOC_IFC_REG_CPTRA_TRNG_STATUS_DATA_WR_DONE_MASK                                             (0x2)
#endif
#define CLP_SOC_IFC_REG_CPTRA_FUSE_WR_DONE                                                          (0x300300b0)
#ifndef SOC_IFC_REG_CPTRA_FUSE_WR_DONE
#define SOC_IFC_REG_CPTRA_FUSE_WR_DONE                                                              (0xb0)
#define SOC_IFC_REG_CPTRA_FUSE_WR_DONE_DONE_LOW                                                     (0)
#define SOC_IFC_REG_CPTRA_FUSE_WR_DONE_DONE_MASK                                                    (0x1)
#endif
#define CLP_SOC_IFC_REG_CPTRA_TIMER_CONFIG                                                          (0x300300b4)
#ifndef SOC_IFC_REG_CPTRA_TIMER_CONFIG
#define SOC_IFC_REG_CPTRA_TIMER_CONFIG                                                              (0xb4)
#endif
#define CLP_SOC_IFC_REG_CPTRA_BOOTFSM_GO                                                            (0x300300b8)
#ifndef SOC_IFC_REG_CPTRA_BOOTFSM_GO
#define SOC_IFC_REG_CPTRA_BOOTFSM_GO                                                                (0xb8)
#define SOC_IFC_REG_CPTRA_BOOTFSM_GO_GO_LOW                                                         (0)
#define SOC_IFC_REG_CPTRA_BOOTFSM_GO_GO_MASK                                                        (0x1)
#endif
#define CLP_SOC_IFC_REG_CPTRA_DBG_MANUF_SERVICE_REG                                                 (0x300300bc)
#ifndef SOC_IFC_REG_CPTRA_DBG_MANUF_SERVICE_REG
#define SOC_IFC_REG_CPTRA_DBG_MANUF_SERVICE_REG                                                     (0xbc)
#endif
#define CLP_SOC_IFC_REG_CPTRA_CLK_GATING_EN                                                         (0x300300c0)
#ifndef SOC_IFC_REG_CPTRA_CLK_GATING_EN
#define SOC_IFC_REG_CPTRA_CLK_GATING_EN                                                             (0xc0)
#define SOC_IFC_REG_CPTRA_CLK_GATING_EN_CLK_GATING_EN_LOW                                           (0)
#define SOC_IFC_REG_CPTRA_CLK_GATING_EN_CLK_GATING_EN_MASK                                          (0x1)
#endif
#define CLP_SOC_IFC_REG_CPTRA_GENERIC_INPUT_WIRES_0                                                 (0x300300c4)
#ifndef SOC_IFC_REG_CPTRA_GENERIC_INPUT_WIRES_0
#define SOC_IFC_REG_CPTRA_GENERIC_INPUT_WIRES_0                                                     (0xc4)
#endif
#define CLP_SOC_IFC_REG_CPTRA_GENERIC_INPUT_WIRES_1                                                 (0x300300c8)
#ifndef SOC_IFC_REG_CPTRA_GENERIC_INPUT_WIRES_1
#define SOC_IFC_REG_CPTRA_GENERIC_INPUT_WIRES_1                                                     (0xc8)
#endif
#define CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0                                                (0x300300cc)
#ifndef SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0
#define SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0                                                    (0xcc)
#endif
#define CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_1                                                (0x300300d0)
#ifndef SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_1
#define SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_1                                                    (0xd0)
#endif
#define CLP_SOC_IFC_REG_CPTRA_HW_REV_ID                                                             (0x300300d4)
#ifndef SOC_IFC_REG_CPTRA_HW_REV_ID
#define SOC_IFC_REG_CPTRA_HW_REV_ID                                                                 (0xd4)
#define SOC_IFC_REG_CPTRA_HW_REV_ID_CPTRA_GENERATION_LOW                                            (0)
#define SOC_IFC_REG_CPTRA_HW_REV_ID_CPTRA_GENERATION_MASK                                           (0xffff)
#define SOC_IFC_REG_CPTRA_HW_REV_ID_SOC_STEPPING_ID_LOW                                             (16)
#define SOC_IFC_REG_CPTRA_HW_REV_ID_SOC_STEPPING_ID_MASK                                            (0xffff0000)
#endif
#define CLP_SOC_IFC_REG_CPTRA_FW_REV_ID_0                                                           (0x300300d8)
#ifndef SOC_IFC_REG_CPTRA_FW_REV_ID_0
#define SOC_IFC_REG_CPTRA_FW_REV_ID_0                                                               (0xd8)
#endif
#define CLP_SOC_IFC_REG_CPTRA_FW_REV_ID_1                                                           (0x300300dc)
#ifndef SOC_IFC_REG_CPTRA_FW_REV_ID_1
#define SOC_IFC_REG_CPTRA_FW_REV_ID_1                                                               (0xdc)
#endif
#define CLP_SOC_IFC_REG_CPTRA_HW_CONFIG                                                             (0x300300e0)
#ifndef SOC_IFC_REG_CPTRA_HW_CONFIG
#define SOC_IFC_REG_CPTRA_HW_CONFIG                                                                 (0xe0)
#define SOC_IFC_REG_CPTRA_HW_CONFIG_ITRNG_EN_LOW                                                    (0)
#define SOC_IFC_REG_CPTRA_HW_CONFIG_ITRNG_EN_MASK                                                   (0x1)
#define SOC_IFC_REG_CPTRA_HW_CONFIG_FUSE_GRANULARITY_LOW                                            (1)
#define SOC_IFC_REG_CPTRA_HW_CONFIG_FUSE_GRANULARITY_MASK                                           (0x2)
#define SOC_IFC_REG_CPTRA_HW_CONFIG_RSVD_EN_LOW                                                     (2)
#define SOC_IFC_REG_CPTRA_HW_CONFIG_RSVD_EN_MASK                                                    (0xc)
#define SOC_IFC_REG_CPTRA_HW_CONFIG_LMS_ACC_EN_LOW                                                  (4)
#define SOC_IFC_REG_CPTRA_HW_CONFIG_LMS_ACC_EN_MASK                                                 (0x10)
#define SOC_IFC_REG_CPTRA_HW_CONFIG_SUBSYSTEM_MODE_EN_LOW                                           (5)
#define SOC_IFC_REG_CPTRA_HW_CONFIG_SUBSYSTEM_MODE_EN_MASK                                          (0x20)
#endif
#define CLP_SOC_IFC_REG_CPTRA_WDT_TIMER1_EN                                                         (0x300300e4)
#ifndef SOC_IFC_REG_CPTRA_WDT_TIMER1_EN
#define SOC_IFC_REG_CPTRA_WDT_TIMER1_EN                                                             (0xe4)
#define SOC_IFC_REG_CPTRA_WDT_TIMER1_EN_TIMER1_EN_LOW                                               (0)
#define SOC_IFC_REG_CPTRA_WDT_TIMER1_EN_TIMER1_EN_MASK                                              (0x1)
#endif
#define CLP_SOC_IFC_REG_CPTRA_WDT_TIMER1_CTRL                                                       (0x300300e8)
#ifndef SOC_IFC_REG_CPTRA_WDT_TIMER1_CTRL
#define SOC_IFC_REG_CPTRA_WDT_TIMER1_CTRL                                                           (0xe8)
#define SOC_IFC_REG_CPTRA_WDT_TIMER1_CTRL_TIMER1_RESTART_LOW                                        (0)
#define SOC_IFC_REG_CPTRA_WDT_TIMER1_CTRL_TIMER1_RESTART_MASK                                       (0x1)
#endif
#define CLP_SOC_IFC_REG_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD_0                                           (0x300300ec)
#ifndef SOC_IFC_REG_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD_0
#define SOC_IFC_REG_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD_0                                               (0xec)
#endif
#define CLP_SOC_IFC_REG_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD_1                                           (0x300300f0)
#ifndef SOC_IFC_REG_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD_1
#define SOC_IFC_REG_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD_1                                               (0xf0)
#endif
#define CLP_SOC_IFC_REG_CPTRA_WDT_TIMER2_EN                                                         (0x300300f4)
#ifndef SOC_IFC_REG_CPTRA_WDT_TIMER2_EN
#define SOC_IFC_REG_CPTRA_WDT_TIMER2_EN                                                             (0xf4)
#define SOC_IFC_REG_CPTRA_WDT_TIMER2_EN_TIMER2_EN_LOW                                               (0)
#define SOC_IFC_REG_CPTRA_WDT_TIMER2_EN_TIMER2_EN_MASK                                              (0x1)
#endif
#define CLP_SOC_IFC_REG_CPTRA_WDT_TIMER2_CTRL                                                       (0x300300f8)
#ifndef SOC_IFC_REG_CPTRA_WDT_TIMER2_CTRL
#define SOC_IFC_REG_CPTRA_WDT_TIMER2_CTRL                                                           (0xf8)
#define SOC_IFC_REG_CPTRA_WDT_TIMER2_CTRL_TIMER2_RESTART_LOW                                        (0)
#define SOC_IFC_REG_CPTRA_WDT_TIMER2_CTRL_TIMER2_RESTART_MASK                                       (0x1)
#endif
#define CLP_SOC_IFC_REG_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD_0                                           (0x300300fc)
#ifndef SOC_IFC_REG_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD_0
#define SOC_IFC_REG_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD_0                                               (0xfc)
#endif
#define CLP_SOC_IFC_REG_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD_1                                           (0x30030100)
#ifndef SOC_IFC_REG_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD_1
#define SOC_IFC_REG_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD_1                                               (0x100)
#endif
#define CLP_SOC_IFC_REG_CPTRA_WDT_STATUS                                                            (0x30030104)
#ifndef SOC_IFC_REG_CPTRA_WDT_STATUS
#define SOC_IFC_REG_CPTRA_WDT_STATUS                                                                (0x104)
#define SOC_IFC_REG_CPTRA_WDT_STATUS_T1_TIMEOUT_LOW                                                 (0)
#define SOC_IFC_REG_CPTRA_WDT_STATUS_T1_TIMEOUT_MASK                                                (0x1)
#define SOC_IFC_REG_CPTRA_WDT_STATUS_T2_TIMEOUT_LOW                                                 (1)
#define SOC_IFC_REG_CPTRA_WDT_STATUS_T2_TIMEOUT_MASK                                                (0x2)
#endif
#define CLP_SOC_IFC_REG_CPTRA_FUSE_VALID_AXI_USER                                                   (0x30030108)
#ifndef SOC_IFC_REG_CPTRA_FUSE_VALID_AXI_USER
#define SOC_IFC_REG_CPTRA_FUSE_VALID_AXI_USER                                                       (0x108)
#endif
#define CLP_SOC_IFC_REG_CPTRA_FUSE_AXI_USER_LOCK                                                    (0x3003010c)
#ifndef SOC_IFC_REG_CPTRA_FUSE_AXI_USER_LOCK
#define SOC_IFC_REG_CPTRA_FUSE_AXI_USER_LOCK                                                        (0x10c)
#define SOC_IFC_REG_CPTRA_FUSE_AXI_USER_LOCK_LOCK_LOW                                               (0)
#define SOC_IFC_REG_CPTRA_FUSE_AXI_USER_LOCK_LOCK_MASK                                              (0x1)
#endif
#define CLP_SOC_IFC_REG_CPTRA_WDT_CFG_0                                                             (0x30030110)
#ifndef SOC_IFC_REG_CPTRA_WDT_CFG_0
#define SOC_IFC_REG_CPTRA_WDT_CFG_0                                                                 (0x110)
#endif
#define CLP_SOC_IFC_REG_CPTRA_WDT_CFG_1                                                             (0x30030114)
#ifndef SOC_IFC_REG_CPTRA_WDT_CFG_1
#define SOC_IFC_REG_CPTRA_WDT_CFG_1                                                                 (0x114)
#endif
#define CLP_SOC_IFC_REG_CPTRA_ITRNG_ENTROPY_CONFIG_0                                                (0x30030118)
#ifndef SOC_IFC_REG_CPTRA_ITRNG_ENTROPY_CONFIG_0
#define SOC_IFC_REG_CPTRA_ITRNG_ENTROPY_CONFIG_0                                                    (0x118)
#define SOC_IFC_REG_CPTRA_ITRNG_ENTROPY_CONFIG_0_LOW_THRESHOLD_LOW                                  (0)
#define SOC_IFC_REG_CPTRA_ITRNG_ENTROPY_CONFIG_0_LOW_THRESHOLD_MASK                                 (0xffff)
#define SOC_IFC_REG_CPTRA_ITRNG_ENTROPY_CONFIG_0_HIGH_THRESHOLD_LOW                                 (16)
#define SOC_IFC_REG_CPTRA_ITRNG_ENTROPY_CONFIG_0_HIGH_THRESHOLD_MASK                                (0xffff0000)
#endif
#define CLP_SOC_IFC_REG_CPTRA_ITRNG_ENTROPY_CONFIG_1                                                (0x3003011c)
#ifndef SOC_IFC_REG_CPTRA_ITRNG_ENTROPY_CONFIG_1
#define SOC_IFC_REG_CPTRA_ITRNG_ENTROPY_CONFIG_1                                                    (0x11c)
#define SOC_IFC_REG_CPTRA_ITRNG_ENTROPY_CONFIG_1_REPETITION_COUNT_LOW                               (0)
#define SOC_IFC_REG_CPTRA_ITRNG_ENTROPY_CONFIG_1_REPETITION_COUNT_MASK                              (0xffff)
#define SOC_IFC_REG_CPTRA_ITRNG_ENTROPY_CONFIG_1_RSVD_LOW                                           (16)
#define SOC_IFC_REG_CPTRA_ITRNG_ENTROPY_CONFIG_1_RSVD_MASK                                          (0xffff0000)
#endif
#define CLP_SOC_IFC_REG_CPTRA_RSVD_REG_0                                                            (0x30030120)
#ifndef SOC_IFC_REG_CPTRA_RSVD_REG_0
#define SOC_IFC_REG_CPTRA_RSVD_REG_0                                                                (0x120)
#endif
#define CLP_SOC_IFC_REG_CPTRA_RSVD_REG_1                                                            (0x30030124)
#ifndef SOC_IFC_REG_CPTRA_RSVD_REG_1
#define SOC_IFC_REG_CPTRA_RSVD_REG_1                                                                (0x124)
#endif
#define CLP_SOC_IFC_REG_CPTRA_HW_CAPABILITIES                                                       (0x30030128)
#ifndef SOC_IFC_REG_CPTRA_HW_CAPABILITIES
#define SOC_IFC_REG_CPTRA_HW_CAPABILITIES                                                           (0x128)
#endif
#define CLP_SOC_IFC_REG_CPTRA_FW_CAPABILITIES                                                       (0x3003012c)
#ifndef SOC_IFC_REG_CPTRA_FW_CAPABILITIES
#define SOC_IFC_REG_CPTRA_FW_CAPABILITIES                                                           (0x12c)
#endif
#define CLP_SOC_IFC_REG_CPTRA_CAP_LOCK                                                              (0x30030130)
#ifndef SOC_IFC_REG_CPTRA_CAP_LOCK
#define SOC_IFC_REG_CPTRA_CAP_LOCK                                                                  (0x130)
#define SOC_IFC_REG_CPTRA_CAP_LOCK_LOCK_LOW                                                         (0)
#define SOC_IFC_REG_CPTRA_CAP_LOCK_LOCK_MASK                                                        (0x1)
#endif
#define CLP_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_0                                                       (0x30030140)
#ifndef SOC_IFC_REG_CPTRA_OWNER_PK_HASH_0
#define SOC_IFC_REG_CPTRA_OWNER_PK_HASH_0                                                           (0x140)
#endif
#define CLP_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_1                                                       (0x30030144)
#ifndef SOC_IFC_REG_CPTRA_OWNER_PK_HASH_1
#define SOC_IFC_REG_CPTRA_OWNER_PK_HASH_1                                                           (0x144)
#endif
#define CLP_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_2                                                       (0x30030148)
#ifndef SOC_IFC_REG_CPTRA_OWNER_PK_HASH_2
#define SOC_IFC_REG_CPTRA_OWNER_PK_HASH_2                                                           (0x148)
#endif
#define CLP_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_3                                                       (0x3003014c)
#ifndef SOC_IFC_REG_CPTRA_OWNER_PK_HASH_3
#define SOC_IFC_REG_CPTRA_OWNER_PK_HASH_3                                                           (0x14c)
#endif
#define CLP_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_4                                                       (0x30030150)
#ifndef SOC_IFC_REG_CPTRA_OWNER_PK_HASH_4
#define SOC_IFC_REG_CPTRA_OWNER_PK_HASH_4                                                           (0x150)
#endif
#define CLP_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_5                                                       (0x30030154)
#ifndef SOC_IFC_REG_CPTRA_OWNER_PK_HASH_5
#define SOC_IFC_REG_CPTRA_OWNER_PK_HASH_5                                                           (0x154)
#endif
#define CLP_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_6                                                       (0x30030158)
#ifndef SOC_IFC_REG_CPTRA_OWNER_PK_HASH_6
#define SOC_IFC_REG_CPTRA_OWNER_PK_HASH_6                                                           (0x158)
#endif
#define CLP_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_7                                                       (0x3003015c)
#ifndef SOC_IFC_REG_CPTRA_OWNER_PK_HASH_7
#define SOC_IFC_REG_CPTRA_OWNER_PK_HASH_7                                                           (0x15c)
#endif
#define CLP_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_8                                                       (0x30030160)
#ifndef SOC_IFC_REG_CPTRA_OWNER_PK_HASH_8
#define SOC_IFC_REG_CPTRA_OWNER_PK_HASH_8                                                           (0x160)
#endif
#define CLP_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_9                                                       (0x30030164)
#ifndef SOC_IFC_REG_CPTRA_OWNER_PK_HASH_9
#define SOC_IFC_REG_CPTRA_OWNER_PK_HASH_9                                                           (0x164)
#endif
#define CLP_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_10                                                      (0x30030168)
#ifndef SOC_IFC_REG_CPTRA_OWNER_PK_HASH_10
#define SOC_IFC_REG_CPTRA_OWNER_PK_HASH_10                                                          (0x168)
#endif
#define CLP_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_11                                                      (0x3003016c)
#ifndef SOC_IFC_REG_CPTRA_OWNER_PK_HASH_11
#define SOC_IFC_REG_CPTRA_OWNER_PK_HASH_11                                                          (0x16c)
#endif
#define CLP_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_LOCK                                                    (0x30030170)
#ifndef SOC_IFC_REG_CPTRA_OWNER_PK_HASH_LOCK
#define SOC_IFC_REG_CPTRA_OWNER_PK_HASH_LOCK                                                        (0x170)
#define SOC_IFC_REG_CPTRA_OWNER_PK_HASH_LOCK_LOCK_LOW                                               (0)
#define SOC_IFC_REG_CPTRA_OWNER_PK_HASH_LOCK_LOCK_MASK                                              (0x1)
#endif
#define CLP_SOC_IFC_REG_FUSE_UDS_SEED_0                                                             (0x30030200)
#ifndef SOC_IFC_REG_FUSE_UDS_SEED_0
#define SOC_IFC_REG_FUSE_UDS_SEED_0                                                                 (0x200)
#endif
#define CLP_SOC_IFC_REG_FUSE_UDS_SEED_1                                                             (0x30030204)
#ifndef SOC_IFC_REG_FUSE_UDS_SEED_1
#define SOC_IFC_REG_FUSE_UDS_SEED_1                                                                 (0x204)
#endif
#define CLP_SOC_IFC_REG_FUSE_UDS_SEED_2                                                             (0x30030208)
#ifndef SOC_IFC_REG_FUSE_UDS_SEED_2
#define SOC_IFC_REG_FUSE_UDS_SEED_2                                                                 (0x208)
#endif
#define CLP_SOC_IFC_REG_FUSE_UDS_SEED_3                                                             (0x3003020c)
#ifndef SOC_IFC_REG_FUSE_UDS_SEED_3
#define SOC_IFC_REG_FUSE_UDS_SEED_3                                                                 (0x20c)
#endif
#define CLP_SOC_IFC_REG_FUSE_UDS_SEED_4                                                             (0x30030210)
#ifndef SOC_IFC_REG_FUSE_UDS_SEED_4
#define SOC_IFC_REG_FUSE_UDS_SEED_4                                                                 (0x210)
#endif
#define CLP_SOC_IFC_REG_FUSE_UDS_SEED_5                                                             (0x30030214)
#ifndef SOC_IFC_REG_FUSE_UDS_SEED_5
#define SOC_IFC_REG_FUSE_UDS_SEED_5                                                                 (0x214)
#endif
#define CLP_SOC_IFC_REG_FUSE_UDS_SEED_6                                                             (0x30030218)
#ifndef SOC_IFC_REG_FUSE_UDS_SEED_6
#define SOC_IFC_REG_FUSE_UDS_SEED_6                                                                 (0x218)
#endif
#define CLP_SOC_IFC_REG_FUSE_UDS_SEED_7                                                             (0x3003021c)
#ifndef SOC_IFC_REG_FUSE_UDS_SEED_7
#define SOC_IFC_REG_FUSE_UDS_SEED_7                                                                 (0x21c)
#endif
#define CLP_SOC_IFC_REG_FUSE_UDS_SEED_8                                                             (0x30030220)
#ifndef SOC_IFC_REG_FUSE_UDS_SEED_8
#define SOC_IFC_REG_FUSE_UDS_SEED_8                                                                 (0x220)
#endif
#define CLP_SOC_IFC_REG_FUSE_UDS_SEED_9                                                             (0x30030224)
#ifndef SOC_IFC_REG_FUSE_UDS_SEED_9
#define SOC_IFC_REG_FUSE_UDS_SEED_9                                                                 (0x224)
#endif
#define CLP_SOC_IFC_REG_FUSE_UDS_SEED_10                                                            (0x30030228)
#ifndef SOC_IFC_REG_FUSE_UDS_SEED_10
#define SOC_IFC_REG_FUSE_UDS_SEED_10                                                                (0x228)
#endif
#define CLP_SOC_IFC_REG_FUSE_UDS_SEED_11                                                            (0x3003022c)
#ifndef SOC_IFC_REG_FUSE_UDS_SEED_11
#define SOC_IFC_REG_FUSE_UDS_SEED_11                                                                (0x22c)
#endif
#define CLP_SOC_IFC_REG_FUSE_UDS_SEED_12                                                            (0x30030230)
#ifndef SOC_IFC_REG_FUSE_UDS_SEED_12
#define SOC_IFC_REG_FUSE_UDS_SEED_12                                                                (0x230)
#endif
#define CLP_SOC_IFC_REG_FUSE_UDS_SEED_13                                                            (0x30030234)
#ifndef SOC_IFC_REG_FUSE_UDS_SEED_13
#define SOC_IFC_REG_FUSE_UDS_SEED_13                                                                (0x234)
#endif
#define CLP_SOC_IFC_REG_FUSE_UDS_SEED_14                                                            (0x30030238)
#ifndef SOC_IFC_REG_FUSE_UDS_SEED_14
#define SOC_IFC_REG_FUSE_UDS_SEED_14                                                                (0x238)
#endif
#define CLP_SOC_IFC_REG_FUSE_UDS_SEED_15                                                            (0x3003023c)
#ifndef SOC_IFC_REG_FUSE_UDS_SEED_15
#define SOC_IFC_REG_FUSE_UDS_SEED_15                                                                (0x23c)
#endif
#define CLP_SOC_IFC_REG_FUSE_FIELD_ENTROPY_0                                                        (0x30030240)
#ifndef SOC_IFC_REG_FUSE_FIELD_ENTROPY_0
#define SOC_IFC_REG_FUSE_FIELD_ENTROPY_0                                                            (0x240)
#endif
#define CLP_SOC_IFC_REG_FUSE_FIELD_ENTROPY_1                                                        (0x30030244)
#ifndef SOC_IFC_REG_FUSE_FIELD_ENTROPY_1
#define SOC_IFC_REG_FUSE_FIELD_ENTROPY_1                                                            (0x244)
#endif
#define CLP_SOC_IFC_REG_FUSE_FIELD_ENTROPY_2                                                        (0x30030248)
#ifndef SOC_IFC_REG_FUSE_FIELD_ENTROPY_2
#define SOC_IFC_REG_FUSE_FIELD_ENTROPY_2                                                            (0x248)
#endif
#define CLP_SOC_IFC_REG_FUSE_FIELD_ENTROPY_3                                                        (0x3003024c)
#ifndef SOC_IFC_REG_FUSE_FIELD_ENTROPY_3
#define SOC_IFC_REG_FUSE_FIELD_ENTROPY_3                                                            (0x24c)
#endif
#define CLP_SOC_IFC_REG_FUSE_FIELD_ENTROPY_4                                                        (0x30030250)
#ifndef SOC_IFC_REG_FUSE_FIELD_ENTROPY_4
#define SOC_IFC_REG_FUSE_FIELD_ENTROPY_4                                                            (0x250)
#endif
#define CLP_SOC_IFC_REG_FUSE_FIELD_ENTROPY_5                                                        (0x30030254)
#ifndef SOC_IFC_REG_FUSE_FIELD_ENTROPY_5
#define SOC_IFC_REG_FUSE_FIELD_ENTROPY_5                                                            (0x254)
#endif
#define CLP_SOC_IFC_REG_FUSE_FIELD_ENTROPY_6                                                        (0x30030258)
#ifndef SOC_IFC_REG_FUSE_FIELD_ENTROPY_6
#define SOC_IFC_REG_FUSE_FIELD_ENTROPY_6                                                            (0x258)
#endif
#define CLP_SOC_IFC_REG_FUSE_FIELD_ENTROPY_7                                                        (0x3003025c)
#ifndef SOC_IFC_REG_FUSE_FIELD_ENTROPY_7
#define SOC_IFC_REG_FUSE_FIELD_ENTROPY_7                                                            (0x25c)
#endif
#define CLP_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_0                                                       (0x30030260)
#ifndef SOC_IFC_REG_FUSE_VENDOR_PK_HASH_0
#define SOC_IFC_REG_FUSE_VENDOR_PK_HASH_0                                                           (0x260)
#endif
#define CLP_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_1                                                       (0x30030264)
#ifndef SOC_IFC_REG_FUSE_VENDOR_PK_HASH_1
#define SOC_IFC_REG_FUSE_VENDOR_PK_HASH_1                                                           (0x264)
#endif
#define CLP_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_2                                                       (0x30030268)
#ifndef SOC_IFC_REG_FUSE_VENDOR_PK_HASH_2
#define SOC_IFC_REG_FUSE_VENDOR_PK_HASH_2                                                           (0x268)
#endif
#define CLP_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_3                                                       (0x3003026c)
#ifndef SOC_IFC_REG_FUSE_VENDOR_PK_HASH_3
#define SOC_IFC_REG_FUSE_VENDOR_PK_HASH_3                                                           (0x26c)
#endif
#define CLP_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_4                                                       (0x30030270)
#ifndef SOC_IFC_REG_FUSE_VENDOR_PK_HASH_4
#define SOC_IFC_REG_FUSE_VENDOR_PK_HASH_4                                                           (0x270)
#endif
#define CLP_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_5                                                       (0x30030274)
#ifndef SOC_IFC_REG_FUSE_VENDOR_PK_HASH_5
#define SOC_IFC_REG_FUSE_VENDOR_PK_HASH_5                                                           (0x274)
#endif
#define CLP_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_6                                                       (0x30030278)
#ifndef SOC_IFC_REG_FUSE_VENDOR_PK_HASH_6
#define SOC_IFC_REG_FUSE_VENDOR_PK_HASH_6                                                           (0x278)
#endif
#define CLP_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_7                                                       (0x3003027c)
#ifndef SOC_IFC_REG_FUSE_VENDOR_PK_HASH_7
#define SOC_IFC_REG_FUSE_VENDOR_PK_HASH_7                                                           (0x27c)
#endif
#define CLP_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_8                                                       (0x30030280)
#ifndef SOC_IFC_REG_FUSE_VENDOR_PK_HASH_8
#define SOC_IFC_REG_FUSE_VENDOR_PK_HASH_8                                                           (0x280)
#endif
#define CLP_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_9                                                       (0x30030284)
#ifndef SOC_IFC_REG_FUSE_VENDOR_PK_HASH_9
#define SOC_IFC_REG_FUSE_VENDOR_PK_HASH_9                                                           (0x284)
#endif
#define CLP_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_10                                                      (0x30030288)
#ifndef SOC_IFC_REG_FUSE_VENDOR_PK_HASH_10
#define SOC_IFC_REG_FUSE_VENDOR_PK_HASH_10                                                          (0x288)
#endif
#define CLP_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_11                                                      (0x3003028c)
#ifndef SOC_IFC_REG_FUSE_VENDOR_PK_HASH_11
#define SOC_IFC_REG_FUSE_VENDOR_PK_HASH_11                                                          (0x28c)
#endif
#define CLP_SOC_IFC_REG_FUSE_ECC_REVOCATION                                                         (0x30030290)
#ifndef SOC_IFC_REG_FUSE_ECC_REVOCATION
#define SOC_IFC_REG_FUSE_ECC_REVOCATION                                                             (0x290)
#define SOC_IFC_REG_FUSE_ECC_REVOCATION_ECC_REVOCATION_LOW                                          (0)
#define SOC_IFC_REG_FUSE_ECC_REVOCATION_ECC_REVOCATION_MASK                                         (0xf)
#endif
#define CLP_SOC_IFC_REG_FUSE_FMC_KEY_MANIFEST_SVN                                                   (0x300302b4)
#ifndef SOC_IFC_REG_FUSE_FMC_KEY_MANIFEST_SVN
#define SOC_IFC_REG_FUSE_FMC_KEY_MANIFEST_SVN                                                       (0x2b4)
#endif
#define CLP_SOC_IFC_REG_FUSE_RUNTIME_SVN_0                                                          (0x300302b8)
#ifndef SOC_IFC_REG_FUSE_RUNTIME_SVN_0
#define SOC_IFC_REG_FUSE_RUNTIME_SVN_0                                                              (0x2b8)
#endif
#define CLP_SOC_IFC_REG_FUSE_RUNTIME_SVN_1                                                          (0x300302bc)
#ifndef SOC_IFC_REG_FUSE_RUNTIME_SVN_1
#define SOC_IFC_REG_FUSE_RUNTIME_SVN_1                                                              (0x2bc)
#endif
#define CLP_SOC_IFC_REG_FUSE_RUNTIME_SVN_2                                                          (0x300302c0)
#ifndef SOC_IFC_REG_FUSE_RUNTIME_SVN_2
#define SOC_IFC_REG_FUSE_RUNTIME_SVN_2                                                              (0x2c0)
#endif
#define CLP_SOC_IFC_REG_FUSE_RUNTIME_SVN_3                                                          (0x300302c4)
#ifndef SOC_IFC_REG_FUSE_RUNTIME_SVN_3
#define SOC_IFC_REG_FUSE_RUNTIME_SVN_3                                                              (0x2c4)
#endif
#define CLP_SOC_IFC_REG_FUSE_ANTI_ROLLBACK_DISABLE                                                  (0x300302c8)
#ifndef SOC_IFC_REG_FUSE_ANTI_ROLLBACK_DISABLE
#define SOC_IFC_REG_FUSE_ANTI_ROLLBACK_DISABLE                                                      (0x2c8)
#define SOC_IFC_REG_FUSE_ANTI_ROLLBACK_DISABLE_DIS_LOW                                              (0)
#define SOC_IFC_REG_FUSE_ANTI_ROLLBACK_DISABLE_DIS_MASK                                             (0x1)
#endif
#define CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_0                                                     (0x300302cc)
#ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_0
#define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_0                                                         (0x2cc)
#endif
#define CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_1                                                     (0x300302d0)
#ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_1
#define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_1                                                         (0x2d0)
#endif
#define CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_2                                                     (0x300302d4)
#ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_2
#define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_2                                                         (0x2d4)
#endif
#define CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_3                                                     (0x300302d8)
#ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_3
#define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_3                                                         (0x2d8)
#endif
#define CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_4                                                     (0x300302dc)
#ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_4
#define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_4                                                         (0x2dc)
#endif
#define CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_5                                                     (0x300302e0)
#ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_5
#define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_5                                                         (0x2e0)
#endif
#define CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_6                                                     (0x300302e4)
#ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_6
#define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_6                                                         (0x2e4)
#endif
#define CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_7                                                     (0x300302e8)
#ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_7
#define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_7                                                         (0x2e8)
#endif
#define CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_8                                                     (0x300302ec)
#ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_8
#define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_8                                                         (0x2ec)
#endif
#define CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_9                                                     (0x300302f0)
#ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_9
#define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_9                                                         (0x2f0)
#endif
#define CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_10                                                    (0x300302f4)
#ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_10
#define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_10                                                        (0x2f4)
#endif
#define CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_11                                                    (0x300302f8)
#ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_11
#define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_11                                                        (0x2f8)
#endif
#define CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_12                                                    (0x300302fc)
#ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_12
#define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_12                                                        (0x2fc)
#endif
#define CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_13                                                    (0x30030300)
#ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_13
#define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_13                                                        (0x300)
#endif
#define CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_14                                                    (0x30030304)
#ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_14
#define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_14                                                        (0x304)
#endif
#define CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_15                                                    (0x30030308)
#ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_15
#define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_15                                                        (0x308)
#endif
#define CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_16                                                    (0x3003030c)
#ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_16
#define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_16                                                        (0x30c)
#endif
#define CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_17                                                    (0x30030310)
#ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_17
#define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_17                                                        (0x310)
#endif
#define CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_18                                                    (0x30030314)
#ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_18
#define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_18                                                        (0x314)
#endif
#define CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_19                                                    (0x30030318)
#ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_19
#define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_19                                                        (0x318)
#endif
#define CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_20                                                    (0x3003031c)
#ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_20
#define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_20                                                        (0x31c)
#endif
#define CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_21                                                    (0x30030320)
#ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_21
#define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_21                                                        (0x320)
#endif
#define CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_22                                                    (0x30030324)
#ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_22
#define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_22                                                        (0x324)
#endif
#define CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_23                                                    (0x30030328)
#ifndef SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_23
#define SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_23                                                        (0x328)
#endif
#define CLP_SOC_IFC_REG_FUSE_IDEVID_MANUF_HSM_ID_0                                                  (0x3003032c)
#ifndef SOC_IFC_REG_FUSE_IDEVID_MANUF_HSM_ID_0
#define SOC_IFC_REG_FUSE_IDEVID_MANUF_HSM_ID_0                                                      (0x32c)
#endif
#define CLP_SOC_IFC_REG_FUSE_IDEVID_MANUF_HSM_ID_1                                                  (0x30030330)
#ifndef SOC_IFC_REG_FUSE_IDEVID_MANUF_HSM_ID_1
#define SOC_IFC_REG_FUSE_IDEVID_MANUF_HSM_ID_1                                                      (0x330)
#endif
#define CLP_SOC_IFC_REG_FUSE_IDEVID_MANUF_HSM_ID_2                                                  (0x30030334)
#ifndef SOC_IFC_REG_FUSE_IDEVID_MANUF_HSM_ID_2
#define SOC_IFC_REG_FUSE_IDEVID_MANUF_HSM_ID_2                                                      (0x334)
#endif
#define CLP_SOC_IFC_REG_FUSE_IDEVID_MANUF_HSM_ID_3                                                  (0x30030338)
#ifndef SOC_IFC_REG_FUSE_IDEVID_MANUF_HSM_ID_3
#define SOC_IFC_REG_FUSE_IDEVID_MANUF_HSM_ID_3                                                      (0x338)
#endif
#define CLP_SOC_IFC_REG_FUSE_LMS_REVOCATION                                                         (0x30030340)
#ifndef SOC_IFC_REG_FUSE_LMS_REVOCATION
#define SOC_IFC_REG_FUSE_LMS_REVOCATION                                                             (0x340)
#endif
#define CLP_SOC_IFC_REG_FUSE_MLDSA_REVOCATION                                                       (0x30030344)
#ifndef SOC_IFC_REG_FUSE_MLDSA_REVOCATION
#define SOC_IFC_REG_FUSE_MLDSA_REVOCATION                                                           (0x344)
#define SOC_IFC_REG_FUSE_MLDSA_REVOCATION_MLDSA_REVOCATION_LOW                                      (0)
#define SOC_IFC_REG_FUSE_MLDSA_REVOCATION_MLDSA_REVOCATION_MASK                                     (0xf)
#endif
#define CLP_SOC_IFC_REG_FUSE_SOC_STEPPING_ID                                                        (0x30030348)
#ifndef SOC_IFC_REG_FUSE_SOC_STEPPING_ID
#define SOC_IFC_REG_FUSE_SOC_STEPPING_ID                                                            (0x348)
#define SOC_IFC_REG_FUSE_SOC_STEPPING_ID_SOC_STEPPING_ID_LOW                                        (0)
#define SOC_IFC_REG_FUSE_SOC_STEPPING_ID_SOC_STEPPING_ID_MASK                                       (0xffff)
#endif
#define CLP_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_0                                               (0x3003034c)
#ifndef SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_0
#define SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_0                                                   (0x34c)
#endif
#define CLP_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_1                                               (0x30030350)
#ifndef SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_1
#define SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_1                                                   (0x350)
#endif
#define CLP_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_2                                               (0x30030354)
#ifndef SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_2
#define SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_2                                                   (0x354)
#endif
#define CLP_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_3                                               (0x30030358)
#ifndef SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_3
#define SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_3                                                   (0x358)
#endif
#define CLP_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_4                                               (0x3003035c)
#ifndef SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_4
#define SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_4                                                   (0x35c)
#endif
#define CLP_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_5                                               (0x30030360)
#ifndef SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_5
#define SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_5                                                   (0x360)
#endif
#define CLP_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_6                                               (0x30030364)
#ifndef SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_6
#define SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_6                                                   (0x364)
#endif
#define CLP_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_7                                               (0x30030368)
#ifndef SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_7
#define SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_7                                                   (0x368)
#endif
#define CLP_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_8                                               (0x3003036c)
#ifndef SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_8
#define SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_8                                                   (0x36c)
#endif
#define CLP_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_9                                               (0x30030370)
#ifndef SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_9
#define SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_9                                                   (0x370)
#endif
#define CLP_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_10                                              (0x30030374)
#ifndef SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_10
#define SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_10                                                  (0x374)
#endif
#define CLP_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_11                                              (0x30030378)
#ifndef SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_11
#define SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_11                                                  (0x378)
#endif
#define CLP_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_12                                              (0x3003037c)
#ifndef SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_12
#define SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_12                                                  (0x37c)
#endif
#define CLP_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_13                                              (0x30030380)
#ifndef SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_13
#define SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_13                                                  (0x380)
#endif
#define CLP_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_14                                              (0x30030384)
#ifndef SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_14
#define SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_14                                                  (0x384)
#endif
#define CLP_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_15                                              (0x30030388)
#ifndef SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_15
#define SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_15                                                  (0x388)
#endif
#define CLP_SOC_IFC_REG_FUSE_PQC_KEY_TYPE                                                           (0x3003038c)
#ifndef SOC_IFC_REG_FUSE_PQC_KEY_TYPE
#define SOC_IFC_REG_FUSE_PQC_KEY_TYPE                                                               (0x38c)
#define SOC_IFC_REG_FUSE_PQC_KEY_TYPE_KEY_TYPE_LOW                                                  (0)
#define SOC_IFC_REG_FUSE_PQC_KEY_TYPE_KEY_TYPE_MASK                                                 (0x3)
#endif
#define CLP_SOC_IFC_REG_FUSE_SOC_MANIFEST_SVN_0                                                     (0x30030390)
#ifndef SOC_IFC_REG_FUSE_SOC_MANIFEST_SVN_0
#define SOC_IFC_REG_FUSE_SOC_MANIFEST_SVN_0                                                         (0x390)
#endif
#define CLP_SOC_IFC_REG_FUSE_SOC_MANIFEST_SVN_1                                                     (0x30030394)
#ifndef SOC_IFC_REG_FUSE_SOC_MANIFEST_SVN_1
#define SOC_IFC_REG_FUSE_SOC_MANIFEST_SVN_1                                                         (0x394)
#endif
#define CLP_SOC_IFC_REG_FUSE_SOC_MANIFEST_SVN_2                                                     (0x30030398)
#ifndef SOC_IFC_REG_FUSE_SOC_MANIFEST_SVN_2
#define SOC_IFC_REG_FUSE_SOC_MANIFEST_SVN_2                                                         (0x398)
#endif
#define CLP_SOC_IFC_REG_FUSE_SOC_MANIFEST_SVN_3                                                     (0x3003039c)
#ifndef SOC_IFC_REG_FUSE_SOC_MANIFEST_SVN_3
#define SOC_IFC_REG_FUSE_SOC_MANIFEST_SVN_3                                                         (0x39c)
#endif
#define CLP_SOC_IFC_REG_FUSE_SOC_MANIFEST_MAX_SVN                                                   (0x300303a0)
#ifndef SOC_IFC_REG_FUSE_SOC_MANIFEST_MAX_SVN
#define SOC_IFC_REG_FUSE_SOC_MANIFEST_MAX_SVN                                                       (0x3a0)
#define SOC_IFC_REG_FUSE_SOC_MANIFEST_MAX_SVN_SVN_LOW                                               (0)
#define SOC_IFC_REG_FUSE_SOC_MANIFEST_MAX_SVN_SVN_MASK                                              (0xff)
#endif
#define CLP_SOC_IFC_REG_SS_CALIPTRA_BASE_ADDR_L                                                     (0x30030500)
#ifndef SOC_IFC_REG_SS_CALIPTRA_BASE_ADDR_L
#define SOC_IFC_REG_SS_CALIPTRA_BASE_ADDR_L                                                         (0x500)
#endif
#define CLP_SOC_IFC_REG_SS_CALIPTRA_BASE_ADDR_H                                                     (0x30030504)
#ifndef SOC_IFC_REG_SS_CALIPTRA_BASE_ADDR_H
#define SOC_IFC_REG_SS_CALIPTRA_BASE_ADDR_H                                                         (0x504)
#endif
#define CLP_SOC_IFC_REG_SS_MCI_BASE_ADDR_L                                                          (0x30030508)
#ifndef SOC_IFC_REG_SS_MCI_BASE_ADDR_L
#define SOC_IFC_REG_SS_MCI_BASE_ADDR_L                                                              (0x508)
#endif
#define CLP_SOC_IFC_REG_SS_MCI_BASE_ADDR_H                                                          (0x3003050c)
#ifndef SOC_IFC_REG_SS_MCI_BASE_ADDR_H
#define SOC_IFC_REG_SS_MCI_BASE_ADDR_H                                                              (0x50c)
#endif
#define CLP_SOC_IFC_REG_SS_RECOVERY_IFC_BASE_ADDR_L                                                 (0x30030510)
#ifndef SOC_IFC_REG_SS_RECOVERY_IFC_BASE_ADDR_L
#define SOC_IFC_REG_SS_RECOVERY_IFC_BASE_ADDR_L                                                     (0x510)
#endif
#define CLP_SOC_IFC_REG_SS_RECOVERY_IFC_BASE_ADDR_H                                                 (0x30030514)
#ifndef SOC_IFC_REG_SS_RECOVERY_IFC_BASE_ADDR_H
#define SOC_IFC_REG_SS_RECOVERY_IFC_BASE_ADDR_H                                                     (0x514)
#endif
#define CLP_SOC_IFC_REG_SS_OTP_FC_BASE_ADDR_L                                                       (0x30030518)
#ifndef SOC_IFC_REG_SS_OTP_FC_BASE_ADDR_L
#define SOC_IFC_REG_SS_OTP_FC_BASE_ADDR_L                                                           (0x518)
#endif
#define CLP_SOC_IFC_REG_SS_OTP_FC_BASE_ADDR_H                                                       (0x3003051c)
#ifndef SOC_IFC_REG_SS_OTP_FC_BASE_ADDR_H
#define SOC_IFC_REG_SS_OTP_FC_BASE_ADDR_H                                                           (0x51c)
#endif
#define CLP_SOC_IFC_REG_SS_UDS_SEED_BASE_ADDR_L                                                     (0x30030520)
#ifndef SOC_IFC_REG_SS_UDS_SEED_BASE_ADDR_L
#define SOC_IFC_REG_SS_UDS_SEED_BASE_ADDR_L                                                         (0x520)
#endif
#define CLP_SOC_IFC_REG_SS_UDS_SEED_BASE_ADDR_H                                                     (0x30030524)
#ifndef SOC_IFC_REG_SS_UDS_SEED_BASE_ADDR_H
#define SOC_IFC_REG_SS_UDS_SEED_BASE_ADDR_H                                                         (0x524)
#endif
#define CLP_SOC_IFC_REG_SS_PROD_DEBUG_UNLOCK_AUTH_PK_HASH_REG_BANK_OFFSET                           (0x30030528)
#ifndef SOC_IFC_REG_SS_PROD_DEBUG_UNLOCK_AUTH_PK_HASH_REG_BANK_OFFSET
#define SOC_IFC_REG_SS_PROD_DEBUG_UNLOCK_AUTH_PK_HASH_REG_BANK_OFFSET                               (0x528)
#endif
#define CLP_SOC_IFC_REG_SS_NUM_OF_PROD_DEBUG_UNLOCK_AUTH_PK_HASHES                                  (0x3003052c)
#ifndef SOC_IFC_REG_SS_NUM_OF_PROD_DEBUG_UNLOCK_AUTH_PK_HASHES
#define SOC_IFC_REG_SS_NUM_OF_PROD_DEBUG_UNLOCK_AUTH_PK_HASHES                                      (0x52c)
#endif
#define CLP_SOC_IFC_REG_SS_DEBUG_INTENT                                                             (0x30030530)
#ifndef SOC_IFC_REG_SS_DEBUG_INTENT
#define SOC_IFC_REG_SS_DEBUG_INTENT                                                                 (0x530)
#define SOC_IFC_REG_SS_DEBUG_INTENT_DEBUG_INTENT_LOW                                                (0)
#define SOC_IFC_REG_SS_DEBUG_INTENT_DEBUG_INTENT_MASK                                               (0x1)
#endif
#define CLP_SOC_IFC_REG_SS_CALIPTRA_DMA_AXI_USER                                                    (0x30030534)
#ifndef SOC_IFC_REG_SS_CALIPTRA_DMA_AXI_USER
#define SOC_IFC_REG_SS_CALIPTRA_DMA_AXI_USER                                                        (0x534)
#endif
#define CLP_SOC_IFC_REG_SS_EXTERNAL_STAGING_AREA_BASE_ADDR_L                                        (0x30030538)
#ifndef SOC_IFC_REG_SS_EXTERNAL_STAGING_AREA_BASE_ADDR_L
#define SOC_IFC_REG_SS_EXTERNAL_STAGING_AREA_BASE_ADDR_L                                            (0x538)
#endif
#define CLP_SOC_IFC_REG_SS_EXTERNAL_STAGING_AREA_BASE_ADDR_H                                        (0x3003053c)
#ifndef SOC_IFC_REG_SS_EXTERNAL_STAGING_AREA_BASE_ADDR_H
#define SOC_IFC_REG_SS_EXTERNAL_STAGING_AREA_BASE_ADDR_H                                            (0x53c)
#endif
#define CLP_SOC_IFC_REG_SS_STRAP_GENERIC_0                                                          (0x300305a0)
#ifndef SOC_IFC_REG_SS_STRAP_GENERIC_0
#define SOC_IFC_REG_SS_STRAP_GENERIC_0                                                              (0x5a0)
#endif
#define CLP_SOC_IFC_REG_SS_STRAP_GENERIC_1                                                          (0x300305a4)
#ifndef SOC_IFC_REG_SS_STRAP_GENERIC_1
#define SOC_IFC_REG_SS_STRAP_GENERIC_1                                                              (0x5a4)
#endif
#define CLP_SOC_IFC_REG_SS_STRAP_GENERIC_2                                                          (0x300305a8)
#ifndef SOC_IFC_REG_SS_STRAP_GENERIC_2
#define SOC_IFC_REG_SS_STRAP_GENERIC_2                                                              (0x5a8)
#endif
#define CLP_SOC_IFC_REG_SS_STRAP_GENERIC_3                                                          (0x300305ac)
#ifndef SOC_IFC_REG_SS_STRAP_GENERIC_3
#define SOC_IFC_REG_SS_STRAP_GENERIC_3                                                              (0x5ac)
#endif
#define CLP_SOC_IFC_REG_SS_DBG_SERVICE_REG_REQ                                                      (0x300305c0)
#ifndef SOC_IFC_REG_SS_DBG_SERVICE_REG_REQ
#define SOC_IFC_REG_SS_DBG_SERVICE_REG_REQ                                                          (0x5c0)
#define SOC_IFC_REG_SS_DBG_SERVICE_REG_REQ_MANUF_DBG_UNLOCK_REQ_LOW                                 (0)
#define SOC_IFC_REG_SS_DBG_SERVICE_REG_REQ_MANUF_DBG_UNLOCK_REQ_MASK                                (0x1)
#define SOC_IFC_REG_SS_DBG_SERVICE_REG_REQ_PROD_DBG_UNLOCK_REQ_LOW                                  (1)
#define SOC_IFC_REG_SS_DBG_SERVICE_REG_REQ_PROD_DBG_UNLOCK_REQ_MASK                                 (0x2)
#define SOC_IFC_REG_SS_DBG_SERVICE_REG_REQ_UDS_PROGRAM_REQ_LOW                                      (2)
#define SOC_IFC_REG_SS_DBG_SERVICE_REG_REQ_UDS_PROGRAM_REQ_MASK                                     (0x4)
#define SOC_IFC_REG_SS_DBG_SERVICE_REG_REQ_RSVD_LOW                                                 (3)
#define SOC_IFC_REG_SS_DBG_SERVICE_REG_REQ_RSVD_MASK                                                (0xfffffff8)
#endif
#define CLP_SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP                                                      (0x300305c4)
#ifndef SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP
#define SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP                                                          (0x5c4)
#define SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_MANUF_DBG_UNLOCK_SUCCESS_LOW                             (0)
#define SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_MANUF_DBG_UNLOCK_SUCCESS_MASK                            (0x1)
#define SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_MANUF_DBG_UNLOCK_FAIL_LOW                                (1)
#define SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_MANUF_DBG_UNLOCK_FAIL_MASK                               (0x2)
#define SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_MANUF_DBG_UNLOCK_IN_PROGRESS_LOW                         (2)
#define SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_MANUF_DBG_UNLOCK_IN_PROGRESS_MASK                        (0x4)
#define SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_PROD_DBG_UNLOCK_SUCCESS_LOW                              (3)
#define SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_PROD_DBG_UNLOCK_SUCCESS_MASK                             (0x8)
#define SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_PROD_DBG_UNLOCK_FAIL_LOW                                 (4)
#define SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_PROD_DBG_UNLOCK_FAIL_MASK                                (0x10)
#define SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_PROD_DBG_UNLOCK_IN_PROGRESS_LOW                          (5)
#define SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_PROD_DBG_UNLOCK_IN_PROGRESS_MASK                         (0x20)
#define SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_UDS_PROGRAM_SUCCESS_LOW                                  (6)
#define SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_UDS_PROGRAM_SUCCESS_MASK                                 (0x40)
#define SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_UDS_PROGRAM_FAIL_LOW                                     (7)
#define SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_UDS_PROGRAM_FAIL_MASK                                    (0x80)
#define SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_UDS_PROGRAM_IN_PROGRESS_LOW                              (8)
#define SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_UDS_PROGRAM_IN_PROGRESS_MASK                             (0x100)
#define SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_TAP_MAILBOX_AVAILABLE_LOW                                (9)
#define SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_TAP_MAILBOX_AVAILABLE_MASK                               (0x200)
#define SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_RSVD_LOW                                                 (10)
#define SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_RSVD_MASK                                                (0xfffffc00)
#endif
#define CLP_SOC_IFC_REG_SS_SOC_DBG_UNLOCK_LEVEL_0                                                   (0x300305c8)
#ifndef SOC_IFC_REG_SS_SOC_DBG_UNLOCK_LEVEL_0
#define SOC_IFC_REG_SS_SOC_DBG_UNLOCK_LEVEL_0                                                       (0x5c8)
#endif
#define CLP_SOC_IFC_REG_SS_SOC_DBG_UNLOCK_LEVEL_1                                                   (0x300305cc)
#ifndef SOC_IFC_REG_SS_SOC_DBG_UNLOCK_LEVEL_1
#define SOC_IFC_REG_SS_SOC_DBG_UNLOCK_LEVEL_1                                                       (0x5cc)
#endif
#define CLP_SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_0                                                   (0x300305d0)
#ifndef SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_0
#define SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_0                                                       (0x5d0)
#endif
#define CLP_SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_1                                                   (0x300305d4)
#ifndef SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_1
#define SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_1                                                       (0x5d4)
#endif
#define CLP_SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_2                                                   (0x300305d8)
#ifndef SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_2
#define SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_2                                                       (0x5d8)
#endif
#define CLP_SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_3                                                   (0x300305dc)
#ifndef SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_3
#define SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_3                                                       (0x5dc)
#endif
#define CLP_SOC_IFC_REG_INTERNAL_OBF_KEY_0                                                          (0x30030600)
#ifndef SOC_IFC_REG_INTERNAL_OBF_KEY_0
#define SOC_IFC_REG_INTERNAL_OBF_KEY_0                                                              (0x600)
#endif
#define CLP_SOC_IFC_REG_INTERNAL_OBF_KEY_1                                                          (0x30030604)
#ifndef SOC_IFC_REG_INTERNAL_OBF_KEY_1
#define SOC_IFC_REG_INTERNAL_OBF_KEY_1                                                              (0x604)
#endif
#define CLP_SOC_IFC_REG_INTERNAL_OBF_KEY_2                                                          (0x30030608)
#ifndef SOC_IFC_REG_INTERNAL_OBF_KEY_2
#define SOC_IFC_REG_INTERNAL_OBF_KEY_2                                                              (0x608)
#endif
#define CLP_SOC_IFC_REG_INTERNAL_OBF_KEY_3                                                          (0x3003060c)
#ifndef SOC_IFC_REG_INTERNAL_OBF_KEY_3
#define SOC_IFC_REG_INTERNAL_OBF_KEY_3                                                              (0x60c)
#endif
#define CLP_SOC_IFC_REG_INTERNAL_OBF_KEY_4                                                          (0x30030610)
#ifndef SOC_IFC_REG_INTERNAL_OBF_KEY_4
#define SOC_IFC_REG_INTERNAL_OBF_KEY_4                                                              (0x610)
#endif
#define CLP_SOC_IFC_REG_INTERNAL_OBF_KEY_5                                                          (0x30030614)
#ifndef SOC_IFC_REG_INTERNAL_OBF_KEY_5
#define SOC_IFC_REG_INTERNAL_OBF_KEY_5                                                              (0x614)
#endif
#define CLP_SOC_IFC_REG_INTERNAL_OBF_KEY_6                                                          (0x30030618)
#ifndef SOC_IFC_REG_INTERNAL_OBF_KEY_6
#define SOC_IFC_REG_INTERNAL_OBF_KEY_6                                                              (0x618)
#endif
#define CLP_SOC_IFC_REG_INTERNAL_OBF_KEY_7                                                          (0x3003061c)
#ifndef SOC_IFC_REG_INTERNAL_OBF_KEY_7
#define SOC_IFC_REG_INTERNAL_OBF_KEY_7                                                              (0x61c)
#endif
#define CLP_SOC_IFC_REG_INTERNAL_ICCM_LOCK                                                          (0x30030620)
#ifndef SOC_IFC_REG_INTERNAL_ICCM_LOCK
#define SOC_IFC_REG_INTERNAL_ICCM_LOCK                                                              (0x620)
#define SOC_IFC_REG_INTERNAL_ICCM_LOCK_LOCK_LOW                                                     (0)
#define SOC_IFC_REG_INTERNAL_ICCM_LOCK_LOCK_MASK                                                    (0x1)
#endif
#define CLP_SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET                                                    (0x30030624)
#ifndef SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET
#define SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET                                                        (0x624)
#define SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET_CORE_RST_LOW                                           (0)
#define SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET_CORE_RST_MASK                                          (0x1)
#endif
#define CLP_SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET_WAIT_CYCLES                                        (0x30030628)
#ifndef SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET_WAIT_CYCLES
#define SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET_WAIT_CYCLES                                            (0x628)
#define SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET_WAIT_CYCLES_WAIT_CYCLES_LOW                            (0)
#define SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET_WAIT_CYCLES_WAIT_CYCLES_MASK                           (0xff)
#endif
#define CLP_SOC_IFC_REG_INTERNAL_NMI_VECTOR                                                         (0x3003062c)
#ifndef SOC_IFC_REG_INTERNAL_NMI_VECTOR
#define SOC_IFC_REG_INTERNAL_NMI_VECTOR                                                             (0x62c)
#endif
#define CLP_SOC_IFC_REG_INTERNAL_HW_ERROR_FATAL_MASK                                                (0x30030630)
#ifndef SOC_IFC_REG_INTERNAL_HW_ERROR_FATAL_MASK
#define SOC_IFC_REG_INTERNAL_HW_ERROR_FATAL_MASK                                                    (0x630)
#define SOC_IFC_REG_INTERNAL_HW_ERROR_FATAL_MASK_MASK_ICCM_ECC_UNC_LOW                              (0)
#define SOC_IFC_REG_INTERNAL_HW_ERROR_FATAL_MASK_MASK_ICCM_ECC_UNC_MASK                             (0x1)
#define SOC_IFC_REG_INTERNAL_HW_ERROR_FATAL_MASK_MASK_DCCM_ECC_UNC_LOW                              (1)
#define SOC_IFC_REG_INTERNAL_HW_ERROR_FATAL_MASK_MASK_DCCM_ECC_UNC_MASK                             (0x2)
#define SOC_IFC_REG_INTERNAL_HW_ERROR_FATAL_MASK_MASK_NMI_PIN_LOW                                   (2)
#define SOC_IFC_REG_INTERNAL_HW_ERROR_FATAL_MASK_MASK_NMI_PIN_MASK                                  (0x4)
#define SOC_IFC_REG_INTERNAL_HW_ERROR_FATAL_MASK_MASK_CRYPTO_ERR_LOW                                (3)
#define SOC_IFC_REG_INTERNAL_HW_ERROR_FATAL_MASK_MASK_CRYPTO_ERR_MASK                               (0x8)
#endif
#define CLP_SOC_IFC_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK                                            (0x30030634)
#ifndef SOC_IFC_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK
#define SOC_IFC_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK                                                (0x634)
#define SOC_IFC_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK_MASK_MBOX_PROT_NO_LOCK_LOW                     (0)
#define SOC_IFC_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK_MASK_MBOX_PROT_NO_LOCK_MASK                    (0x1)
#define SOC_IFC_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK_MASK_MBOX_PROT_OOO_LOW                         (1)
#define SOC_IFC_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK_MASK_MBOX_PROT_OOO_MASK                        (0x2)
#define SOC_IFC_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK_MASK_MBOX_ECC_UNC_LOW                          (2)
#define SOC_IFC_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK_MASK_MBOX_ECC_UNC_MASK                         (0x4)
#endif
#define CLP_SOC_IFC_REG_INTERNAL_FW_ERROR_FATAL_MASK                                                (0x30030638)
#ifndef SOC_IFC_REG_INTERNAL_FW_ERROR_FATAL_MASK
#define SOC_IFC_REG_INTERNAL_FW_ERROR_FATAL_MASK                                                    (0x638)
#endif
#define CLP_SOC_IFC_REG_INTERNAL_FW_ERROR_NON_FATAL_MASK                                            (0x3003063c)
#ifndef SOC_IFC_REG_INTERNAL_FW_ERROR_NON_FATAL_MASK
#define SOC_IFC_REG_INTERNAL_FW_ERROR_NON_FATAL_MASK                                                (0x63c)
#endif
#define CLP_SOC_IFC_REG_INTERNAL_RV_MTIME_L                                                         (0x30030640)
#ifndef SOC_IFC_REG_INTERNAL_RV_MTIME_L
#define SOC_IFC_REG_INTERNAL_RV_MTIME_L                                                             (0x640)
#endif
#define CLP_SOC_IFC_REG_INTERNAL_RV_MTIME_H                                                         (0x30030644)
#ifndef SOC_IFC_REG_INTERNAL_RV_MTIME_H
#define SOC_IFC_REG_INTERNAL_RV_MTIME_H                                                             (0x644)
#endif
#define CLP_SOC_IFC_REG_INTERNAL_RV_MTIMECMP_L                                                      (0x30030648)
#ifndef SOC_IFC_REG_INTERNAL_RV_MTIMECMP_L
#define SOC_IFC_REG_INTERNAL_RV_MTIMECMP_L                                                          (0x648)
#endif
#define CLP_SOC_IFC_REG_INTERNAL_RV_MTIMECMP_H                                                      (0x3003064c)
#ifndef SOC_IFC_REG_INTERNAL_RV_MTIMECMP_H
#define SOC_IFC_REG_INTERNAL_RV_MTIMECMP_H                                                          (0x64c)
#endif
#define CLP_SOC_IFC_REG_INTR_BLOCK_RF_START                                                         (0x30030800)
#define CLP_SOC_IFC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R                                              (0x30030800)
#ifndef SOC_IFC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R
#define SOC_IFC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R                                                  (0x800)
#define SOC_IFC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_LOW                                     (0)
#define SOC_IFC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_MASK                                    (0x1)
#define SOC_IFC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_LOW                                     (1)
#define SOC_IFC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_MASK                                    (0x2)
#endif
#define CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R                                               (0x30030804)
#ifndef SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R                                                   (0x804)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_INTERNAL_EN_LOW                             (0)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_INTERNAL_EN_MASK                            (0x1)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_INV_DEV_EN_LOW                              (1)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_INV_DEV_EN_MASK                             (0x2)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_CMD_FAIL_EN_LOW                             (2)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_CMD_FAIL_EN_MASK                            (0x4)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_BAD_FUSE_EN_LOW                             (3)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_BAD_FUSE_EN_MASK                            (0x8)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_ICCM_BLOCKED_EN_LOW                         (4)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_ICCM_BLOCKED_EN_MASK                        (0x10)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_MBOX_ECC_UNC_EN_LOW                         (5)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_MBOX_ECC_UNC_EN_MASK                        (0x20)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_WDT_TIMER1_TIMEOUT_EN_LOW                   (6)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_WDT_TIMER1_TIMEOUT_EN_MASK                  (0x40)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_WDT_TIMER2_TIMEOUT_EN_LOW                   (7)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_WDT_TIMER2_TIMEOUT_EN_MASK                  (0x80)
#endif
#define CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R                                               (0x30030808)
#ifndef SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R                                                   (0x808)
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_CMD_AVAIL_EN_LOW                            (0)
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_CMD_AVAIL_EN_MASK                           (0x1)
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_MBOX_ECC_COR_EN_LOW                         (1)
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_MBOX_ECC_COR_EN_MASK                        (0x2)
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_DEBUG_LOCKED_EN_LOW                         (2)
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_DEBUG_LOCKED_EN_MASK                        (0x4)
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_SCAN_MODE_EN_LOW                            (3)
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_SCAN_MODE_EN_MASK                           (0x8)
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_SOC_REQ_LOCK_EN_LOW                         (4)
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_SOC_REQ_LOCK_EN_MASK                        (0x10)
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_GEN_IN_TOGGLE_EN_LOW                        (5)
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_GEN_IN_TOGGLE_EN_MASK                       (0x20)
#endif
#define CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R                                           (0x3003080c)
#ifndef SOC_IFC_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R                                               (0x80c)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS_LOW                                   (0)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS_MASK                                  (0x1)
#endif
#define CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R                                           (0x30030810)
#ifndef SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R                                               (0x810)
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS_LOW                                   (0)
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS_MASK                                  (0x1)
#endif
#define CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R                                         (0x30030814)
#ifndef SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R                                             (0x814)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_INTERNAL_STS_LOW                      (0)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_INTERNAL_STS_MASK                     (0x1)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_INV_DEV_STS_LOW                       (1)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_INV_DEV_STS_MASK                      (0x2)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_CMD_FAIL_STS_LOW                      (2)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_CMD_FAIL_STS_MASK                     (0x4)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_BAD_FUSE_STS_LOW                      (3)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_BAD_FUSE_STS_MASK                     (0x8)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_ICCM_BLOCKED_STS_LOW                  (4)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_ICCM_BLOCKED_STS_MASK                 (0x10)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_MBOX_ECC_UNC_STS_LOW                  (5)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_MBOX_ECC_UNC_STS_MASK                 (0x20)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_WDT_TIMER1_TIMEOUT_STS_LOW            (6)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_WDT_TIMER1_TIMEOUT_STS_MASK           (0x40)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_WDT_TIMER2_TIMEOUT_STS_LOW            (7)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_WDT_TIMER2_TIMEOUT_STS_MASK           (0x80)
#endif
#define CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R                                         (0x30030818)
#ifndef SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R                                             (0x818)
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_AVAIL_STS_LOW                     (0)
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_AVAIL_STS_MASK                    (0x1)
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_MBOX_ECC_COR_STS_LOW                  (1)
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_MBOX_ECC_COR_STS_MASK                 (0x2)
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_DEBUG_LOCKED_STS_LOW                  (2)
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_DEBUG_LOCKED_STS_MASK                 (0x4)
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_SCAN_MODE_STS_LOW                     (3)
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_SCAN_MODE_STS_MASK                    (0x8)
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_SOC_REQ_LOCK_STS_LOW                  (4)
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_SOC_REQ_LOCK_STS_MASK                 (0x10)
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_GEN_IN_TOGGLE_STS_LOW                 (5)
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_GEN_IN_TOGGLE_STS_MASK                (0x20)
#endif
#define CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R                                             (0x3003081c)
#ifndef SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R                                                 (0x81c)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_INTERNAL_TRIG_LOW                         (0)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_INTERNAL_TRIG_MASK                        (0x1)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_INV_DEV_TRIG_LOW                          (1)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_INV_DEV_TRIG_MASK                         (0x2)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_CMD_FAIL_TRIG_LOW                         (2)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_CMD_FAIL_TRIG_MASK                        (0x4)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_BAD_FUSE_TRIG_LOW                         (3)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_BAD_FUSE_TRIG_MASK                        (0x8)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_ICCM_BLOCKED_TRIG_LOW                     (4)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_ICCM_BLOCKED_TRIG_MASK                    (0x10)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_MBOX_ECC_UNC_TRIG_LOW                     (5)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_MBOX_ECC_UNC_TRIG_MASK                    (0x20)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_WDT_TIMER1_TIMEOUT_TRIG_LOW               (6)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_WDT_TIMER1_TIMEOUT_TRIG_MASK              (0x40)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_WDT_TIMER2_TIMEOUT_TRIG_LOW               (7)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_WDT_TIMER2_TIMEOUT_TRIG_MASK              (0x80)
#endif
#define CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R                                             (0x30030820)
#ifndef SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R                                                 (0x820)
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_AVAIL_TRIG_LOW                        (0)
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_AVAIL_TRIG_MASK                       (0x1)
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_MBOX_ECC_COR_TRIG_LOW                     (1)
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_MBOX_ECC_COR_TRIG_MASK                    (0x2)
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_DEBUG_LOCKED_TRIG_LOW                     (2)
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_DEBUG_LOCKED_TRIG_MASK                    (0x4)
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_SCAN_MODE_TRIG_LOW                        (3)
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_SCAN_MODE_TRIG_MASK                       (0x8)
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_SOC_REQ_LOCK_TRIG_LOW                     (4)
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_SOC_REQ_LOCK_TRIG_MASK                    (0x10)
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_GEN_IN_TOGGLE_TRIG_LOW                    (5)
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_GEN_IN_TOGGLE_TRIG_MASK                   (0x20)
#endif
#define CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_R                                   (0x30030900)
#ifndef SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_R
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_R                                       (0x900)
#endif
#define CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INV_DEV_INTR_COUNT_R                                    (0x30030904)
#ifndef SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INV_DEV_INTR_COUNT_R
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INV_DEV_INTR_COUNT_R                                        (0x904)
#endif
#define CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_CMD_FAIL_INTR_COUNT_R                                   (0x30030908)
#ifndef SOC_IFC_REG_INTR_BLOCK_RF_ERROR_CMD_FAIL_INTR_COUNT_R
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_CMD_FAIL_INTR_COUNT_R                                       (0x908)
#endif
#define CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_BAD_FUSE_INTR_COUNT_R                                   (0x3003090c)
#ifndef SOC_IFC_REG_INTR_BLOCK_RF_ERROR_BAD_FUSE_INTR_COUNT_R
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_BAD_FUSE_INTR_COUNT_R                                       (0x90c)
#endif
#define CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_ICCM_BLOCKED_INTR_COUNT_R                               (0x30030910)
#ifndef SOC_IFC_REG_INTR_BLOCK_RF_ERROR_ICCM_BLOCKED_INTR_COUNT_R
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_ICCM_BLOCKED_INTR_COUNT_R                                   (0x910)
#endif
#define CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_MBOX_ECC_UNC_INTR_COUNT_R                               (0x30030914)
#ifndef SOC_IFC_REG_INTR_BLOCK_RF_ERROR_MBOX_ECC_UNC_INTR_COUNT_R
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_MBOX_ECC_UNC_INTR_COUNT_R                                   (0x914)
#endif
#define CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_R                         (0x30030918)
#ifndef SOC_IFC_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_R
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_R                             (0x918)
#endif
#define CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_R                         (0x3003091c)
#ifndef SOC_IFC_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_R
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_R                             (0x91c)
#endif
#define CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_CMD_AVAIL_INTR_COUNT_R                                  (0x30030980)
#ifndef SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_CMD_AVAIL_INTR_COUNT_R
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_CMD_AVAIL_INTR_COUNT_R                                      (0x980)
#endif
#define CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_MBOX_ECC_COR_INTR_COUNT_R                               (0x30030984)
#ifndef SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_MBOX_ECC_COR_INTR_COUNT_R
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_MBOX_ECC_COR_INTR_COUNT_R                                   (0x984)
#endif
#define CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_R                               (0x30030988)
#ifndef SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_R
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_R                                   (0x988)
#endif
#define CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_R                                  (0x3003098c)
#ifndef SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_R
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_R                                      (0x98c)
#endif
#define CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_SOC_REQ_LOCK_INTR_COUNT_R                               (0x30030990)
#ifndef SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_SOC_REQ_LOCK_INTR_COUNT_R
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_SOC_REQ_LOCK_INTR_COUNT_R                                   (0x990)
#endif
#define CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_R                              (0x30030994)
#ifndef SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_R
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_R                                  (0x994)
#endif
#define CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R                              (0x30030a00)
#ifndef SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R                                  (0xa00)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R_PULSE_LOW                        (0)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R_PULSE_MASK                       (0x1)
#endif
#define CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INV_DEV_INTR_COUNT_INCR_R                               (0x30030a04)
#ifndef SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INV_DEV_INTR_COUNT_INCR_R
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INV_DEV_INTR_COUNT_INCR_R                                   (0xa04)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INV_DEV_INTR_COUNT_INCR_R_PULSE_LOW                         (0)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INV_DEV_INTR_COUNT_INCR_R_PULSE_MASK                        (0x1)
#endif
#define CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_CMD_FAIL_INTR_COUNT_INCR_R                              (0x30030a08)
#ifndef SOC_IFC_REG_INTR_BLOCK_RF_ERROR_CMD_FAIL_INTR_COUNT_INCR_R
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_CMD_FAIL_INTR_COUNT_INCR_R                                  (0xa08)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_CMD_FAIL_INTR_COUNT_INCR_R_PULSE_LOW                        (0)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_CMD_FAIL_INTR_COUNT_INCR_R_PULSE_MASK                       (0x1)
#endif
#define CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_BAD_FUSE_INTR_COUNT_INCR_R                              (0x30030a0c)
#ifndef SOC_IFC_REG_INTR_BLOCK_RF_ERROR_BAD_FUSE_INTR_COUNT_INCR_R
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_BAD_FUSE_INTR_COUNT_INCR_R                                  (0xa0c)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_BAD_FUSE_INTR_COUNT_INCR_R_PULSE_LOW                        (0)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_BAD_FUSE_INTR_COUNT_INCR_R_PULSE_MASK                       (0x1)
#endif
#define CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_ICCM_BLOCKED_INTR_COUNT_INCR_R                          (0x30030a10)
#ifndef SOC_IFC_REG_INTR_BLOCK_RF_ERROR_ICCM_BLOCKED_INTR_COUNT_INCR_R
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_ICCM_BLOCKED_INTR_COUNT_INCR_R                              (0xa10)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_ICCM_BLOCKED_INTR_COUNT_INCR_R_PULSE_LOW                    (0)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_ICCM_BLOCKED_INTR_COUNT_INCR_R_PULSE_MASK                   (0x1)
#endif
#define CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_MBOX_ECC_UNC_INTR_COUNT_INCR_R                          (0x30030a14)
#ifndef SOC_IFC_REG_INTR_BLOCK_RF_ERROR_MBOX_ECC_UNC_INTR_COUNT_INCR_R
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_MBOX_ECC_UNC_INTR_COUNT_INCR_R                              (0xa14)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_MBOX_ECC_UNC_INTR_COUNT_INCR_R_PULSE_LOW                    (0)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_MBOX_ECC_UNC_INTR_COUNT_INCR_R_PULSE_MASK                   (0x1)
#endif
#define CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_INCR_R                    (0x30030a18)
#ifndef SOC_IFC_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_INCR_R
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_INCR_R                        (0xa18)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_INCR_R_PULSE_LOW              (0)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_INCR_R_PULSE_MASK             (0x1)
#endif
#define CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_INCR_R                    (0x30030a1c)
#ifndef SOC_IFC_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_INCR_R
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_INCR_R                        (0xa1c)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_INCR_R_PULSE_LOW              (0)
#define SOC_IFC_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_INCR_R_PULSE_MASK             (0x1)
#endif
#define CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_CMD_AVAIL_INTR_COUNT_INCR_R                             (0x30030a20)
#ifndef SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_CMD_AVAIL_INTR_COUNT_INCR_R
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_CMD_AVAIL_INTR_COUNT_INCR_R                                 (0xa20)
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_CMD_AVAIL_INTR_COUNT_INCR_R_PULSE_LOW                       (0)
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_CMD_AVAIL_INTR_COUNT_INCR_R_PULSE_MASK                      (0x1)
#endif
#define CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_MBOX_ECC_COR_INTR_COUNT_INCR_R                          (0x30030a24)
#ifndef SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_MBOX_ECC_COR_INTR_COUNT_INCR_R
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_MBOX_ECC_COR_INTR_COUNT_INCR_R                              (0xa24)
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_MBOX_ECC_COR_INTR_COUNT_INCR_R_PULSE_LOW                    (0)
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_MBOX_ECC_COR_INTR_COUNT_INCR_R_PULSE_MASK                   (0x1)
#endif
#define CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_INCR_R                          (0x30030a28)
#ifndef SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_INCR_R
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_INCR_R                              (0xa28)
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_INCR_R_PULSE_LOW                    (0)
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_INCR_R_PULSE_MASK                   (0x1)
#endif
#define CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_INCR_R                             (0x30030a2c)
#ifndef SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_INCR_R
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_INCR_R                                 (0xa2c)
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_INCR_R_PULSE_LOW                       (0)
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_INCR_R_PULSE_MASK                      (0x1)
#endif
#define CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_SOC_REQ_LOCK_INTR_COUNT_INCR_R                          (0x30030a30)
#ifndef SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_SOC_REQ_LOCK_INTR_COUNT_INCR_R
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_SOC_REQ_LOCK_INTR_COUNT_INCR_R                              (0xa30)
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_SOC_REQ_LOCK_INTR_COUNT_INCR_R_PULSE_LOW                    (0)
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_SOC_REQ_LOCK_INTR_COUNT_INCR_R_PULSE_MASK                   (0x1)
#endif
#define CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_INCR_R                         (0x30030a34)
#ifndef SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_INCR_R
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_INCR_R                             (0xa34)
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_INCR_R_PULSE_LOW                   (0)
#define SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_INCR_R_PULSE_MASK                  (0x1)
#endif
#define CLP_MBOX_SRAM_BASE_ADDR                                                                     (0x30040000)
#define CLP_MBOX_SRAM_END_ADDR                                                                      (0x3007ffff)


#endif
