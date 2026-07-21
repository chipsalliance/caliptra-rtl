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
#ifndef CALIPTRA_TOP_REG_HEADER
#define CALIPTRA_TOP_REG_HEADER


#define CALIPTRA_TOP_REG_BASE_ADDR                                                                  (0x0)
#define CALIPTRA_TOP_REG_MBOX_CSR_BASE_ADDR                                                         (0x20000)
#define CALIPTRA_TOP_REG_MBOX_CSR_MBOX_LOCK                                                         (0x20000)
#ifndef MBOX_CSR_MBOX_LOCK
#define MBOX_CSR_MBOX_LOCK                                                                          (0x0)
#define MBOX_CSR_MBOX_LOCK_LOCK_LOW                                                                 (0)
#define MBOX_CSR_MBOX_LOCK_LOCK_MASK                                                                (0x1)
#endif
#define CALIPTRA_TOP_REG_MBOX_CSR_MBOX_USER                                                         (0x20004)
#ifndef MBOX_CSR_MBOX_USER
#define MBOX_CSR_MBOX_USER                                                                          (0x4)
#endif
#define CALIPTRA_TOP_REG_MBOX_CSR_MBOX_CMD                                                          (0x20008)
#ifndef MBOX_CSR_MBOX_CMD
#define MBOX_CSR_MBOX_CMD                                                                           (0x8)
#endif
#define CALIPTRA_TOP_REG_MBOX_CSR_MBOX_DLEN                                                         (0x2000c)
#ifndef MBOX_CSR_MBOX_DLEN
#define MBOX_CSR_MBOX_DLEN                                                                          (0xc)
#endif
#define CALIPTRA_TOP_REG_MBOX_CSR_MBOX_DATAIN                                                       (0x20010)
#ifndef MBOX_CSR_MBOX_DATAIN
#define MBOX_CSR_MBOX_DATAIN                                                                        (0x10)
#endif
#define CALIPTRA_TOP_REG_MBOX_CSR_MBOX_DATAOUT                                                      (0x20014)
#ifndef MBOX_CSR_MBOX_DATAOUT
#define MBOX_CSR_MBOX_DATAOUT                                                                       (0x14)
#endif
#define CALIPTRA_TOP_REG_MBOX_CSR_MBOX_EXECUTE                                                      (0x20018)
#ifndef MBOX_CSR_MBOX_EXECUTE
#define MBOX_CSR_MBOX_EXECUTE                                                                       (0x18)
#define MBOX_CSR_MBOX_EXECUTE_EXECUTE_LOW                                                           (0)
#define MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK                                                          (0x1)
#endif
#define CALIPTRA_TOP_REG_MBOX_CSR_MBOX_STATUS                                                       (0x2001c)
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
#define CALIPTRA_TOP_REG_MBOX_CSR_MBOX_UNLOCK                                                       (0x20020)
#ifndef MBOX_CSR_MBOX_UNLOCK
#define MBOX_CSR_MBOX_UNLOCK                                                                        (0x20)
#define MBOX_CSR_MBOX_UNLOCK_UNLOCK_LOW                                                             (0)
#define MBOX_CSR_MBOX_UNLOCK_UNLOCK_MASK                                                            (0x1)
#endif
#define CALIPTRA_TOP_REG_MBOX_CSR_TAP_MODE                                                          (0x20024)
#ifndef MBOX_CSR_TAP_MODE
#define MBOX_CSR_TAP_MODE                                                                           (0x24)
#define MBOX_CSR_TAP_MODE_ENABLED_LOW                                                               (0)
#define MBOX_CSR_TAP_MODE_ENABLED_MASK                                                              (0x1)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_BASE_ADDR                                             (0x30000)
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_FATAL                                  (0x30000)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_FATAL
#define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_FATAL                                                   (0x0)
#define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_FATAL_ICCM_ECC_UNC_LOW                                  (0)
#define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_FATAL_ICCM_ECC_UNC_MASK                                 (0x1)
#define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_FATAL_DCCM_ECC_UNC_LOW                                  (1)
#define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_FATAL_DCCM_ECC_UNC_MASK                                 (0x2)
#define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_FATAL_NMI_PIN_LOW                                       (2)
#define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_FATAL_NMI_PIN_MASK                                      (0x4)
#define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_FATAL_CRYPTO_ERR_LOW                                    (3)
#define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_FATAL_CRYPTO_ERR_MASK                                   (0x8)
#define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_FATAL_KV_ERROR_LOW                                      (4)
#define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_FATAL_KV_ERROR_MASK                                     (0x10)
#define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_FATAL_SHADOW_STORAGE_ERR_LOW                            (5)
#define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_FATAL_SHADOW_STORAGE_ERR_MASK                           (0x20)
#define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_FATAL_RSVD_LOW                                          (6)
#define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_FATAL_RSVD_MASK                                         (0xffffffc0)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_NON_FATAL                              (0x30004)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_NON_FATAL
#define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_NON_FATAL                                               (0x4)
#define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_NON_FATAL_MBOX_PROT_NO_LOCK_LOW                         (0)
#define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_NON_FATAL_MBOX_PROT_NO_LOCK_MASK                        (0x1)
#define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_NON_FATAL_MBOX_PROT_OOO_LOW                             (1)
#define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_NON_FATAL_MBOX_PROT_OOO_MASK                            (0x2)
#define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_NON_FATAL_MBOX_ECC_UNC_LOW                              (2)
#define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_NON_FATAL_MBOX_ECC_UNC_MASK                             (0x4)
#define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_NON_FATAL_SHADOW_UPDATE_ERR_LOW                         (3)
#define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_NON_FATAL_SHADOW_UPDATE_ERR_MASK                        (0x8)
#define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_NON_FATAL_RSVD_LOW                                      (4)
#define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_NON_FATAL_RSVD_MASK                                     (0xfffffff0)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_FW_ERROR_FATAL                                  (0x30008)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_FW_ERROR_FATAL
#define GENERIC_AND_FUSE_REG_CPTRA_FW_ERROR_FATAL                                                   (0x8)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_FW_ERROR_NON_FATAL                              (0x3000c)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_FW_ERROR_NON_FATAL
#define GENERIC_AND_FUSE_REG_CPTRA_FW_ERROR_NON_FATAL                                               (0xc)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_ENC                                    (0x30010)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_ENC
#define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_ENC                                                     (0x10)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_FW_ERROR_ENC                                    (0x30014)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_FW_ERROR_ENC
#define GENERIC_AND_FUSE_REG_CPTRA_FW_ERROR_ENC                                                     (0x14)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_FW_EXTENDED_ERROR_INFO_0                        (0x30018)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_FW_EXTENDED_ERROR_INFO_0
#define GENERIC_AND_FUSE_REG_CPTRA_FW_EXTENDED_ERROR_INFO_0                                         (0x18)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_FW_EXTENDED_ERROR_INFO_1                        (0x3001c)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_FW_EXTENDED_ERROR_INFO_1
#define GENERIC_AND_FUSE_REG_CPTRA_FW_EXTENDED_ERROR_INFO_1                                         (0x1c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_FW_EXTENDED_ERROR_INFO_2                        (0x30020)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_FW_EXTENDED_ERROR_INFO_2
#define GENERIC_AND_FUSE_REG_CPTRA_FW_EXTENDED_ERROR_INFO_2                                         (0x20)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_FW_EXTENDED_ERROR_INFO_3                        (0x30024)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_FW_EXTENDED_ERROR_INFO_3
#define GENERIC_AND_FUSE_REG_CPTRA_FW_EXTENDED_ERROR_INFO_3                                         (0x24)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_FW_EXTENDED_ERROR_INFO_4                        (0x30028)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_FW_EXTENDED_ERROR_INFO_4
#define GENERIC_AND_FUSE_REG_CPTRA_FW_EXTENDED_ERROR_INFO_4                                         (0x28)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_FW_EXTENDED_ERROR_INFO_5                        (0x3002c)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_FW_EXTENDED_ERROR_INFO_5
#define GENERIC_AND_FUSE_REG_CPTRA_FW_EXTENDED_ERROR_INFO_5                                         (0x2c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_FW_EXTENDED_ERROR_INFO_6                        (0x30030)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_FW_EXTENDED_ERROR_INFO_6
#define GENERIC_AND_FUSE_REG_CPTRA_FW_EXTENDED_ERROR_INFO_6                                         (0x30)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_FW_EXTENDED_ERROR_INFO_7                        (0x30034)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_FW_EXTENDED_ERROR_INFO_7
#define GENERIC_AND_FUSE_REG_CPTRA_FW_EXTENDED_ERROR_INFO_7                                         (0x34)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_BOOT_STATUS                                     (0x30038)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_BOOT_STATUS
#define GENERIC_AND_FUSE_REG_CPTRA_BOOT_STATUS                                                      (0x38)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_FLOW_STATUS                                     (0x3003c)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_FLOW_STATUS
#define GENERIC_AND_FUSE_REG_CPTRA_FLOW_STATUS                                                      (0x3c)
#define GENERIC_AND_FUSE_REG_CPTRA_FLOW_STATUS_STATUS_LOW                                           (0)
#define GENERIC_AND_FUSE_REG_CPTRA_FLOW_STATUS_STATUS_MASK                                          (0xffffff)
#define GENERIC_AND_FUSE_REG_CPTRA_FLOW_STATUS_IDEVID_CSR_READY_LOW                                 (24)
#define GENERIC_AND_FUSE_REG_CPTRA_FLOW_STATUS_IDEVID_CSR_READY_MASK                                (0x1000000)
#define GENERIC_AND_FUSE_REG_CPTRA_FLOW_STATUS_BOOT_FSM_PS_LOW                                      (25)
#define GENERIC_AND_FUSE_REG_CPTRA_FLOW_STATUS_BOOT_FSM_PS_MASK                                     (0xe000000)
#define GENERIC_AND_FUSE_REG_CPTRA_FLOW_STATUS_READY_FOR_MB_PROCESSING_LOW                          (28)
#define GENERIC_AND_FUSE_REG_CPTRA_FLOW_STATUS_READY_FOR_MB_PROCESSING_MASK                         (0x10000000)
#define GENERIC_AND_FUSE_REG_CPTRA_FLOW_STATUS_READY_FOR_RUNTIME_LOW                                (29)
#define GENERIC_AND_FUSE_REG_CPTRA_FLOW_STATUS_READY_FOR_RUNTIME_MASK                               (0x20000000)
#define GENERIC_AND_FUSE_REG_CPTRA_FLOW_STATUS_READY_FOR_FUSES_LOW                                  (30)
#define GENERIC_AND_FUSE_REG_CPTRA_FLOW_STATUS_READY_FOR_FUSES_MASK                                 (0x40000000)
#define GENERIC_AND_FUSE_REG_CPTRA_FLOW_STATUS_MAILBOX_FLOW_DONE_LOW                                (31)
#define GENERIC_AND_FUSE_REG_CPTRA_FLOW_STATUS_MAILBOX_FLOW_DONE_MASK                               (0x80000000)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_RESET_REASON                                    (0x30040)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_RESET_REASON
#define GENERIC_AND_FUSE_REG_CPTRA_RESET_REASON                                                     (0x40)
#define GENERIC_AND_FUSE_REG_CPTRA_RESET_REASON_FW_UPD_RESET_LOW                                    (0)
#define GENERIC_AND_FUSE_REG_CPTRA_RESET_REASON_FW_UPD_RESET_MASK                                   (0x1)
#define GENERIC_AND_FUSE_REG_CPTRA_RESET_REASON_WARM_RESET_LOW                                      (1)
#define GENERIC_AND_FUSE_REG_CPTRA_RESET_REASON_WARM_RESET_MASK                                     (0x2)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_SECURITY_STATE                                  (0x30044)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_SECURITY_STATE
#define GENERIC_AND_FUSE_REG_CPTRA_SECURITY_STATE                                                   (0x44)
#define GENERIC_AND_FUSE_REG_CPTRA_SECURITY_STATE_DEVICE_LIFECYCLE_LOW                              (0)
#define GENERIC_AND_FUSE_REG_CPTRA_SECURITY_STATE_DEVICE_LIFECYCLE_MASK                             (0x3)
#define GENERIC_AND_FUSE_REG_CPTRA_SECURITY_STATE_DEBUG_LOCKED_LOW                                  (2)
#define GENERIC_AND_FUSE_REG_CPTRA_SECURITY_STATE_DEBUG_LOCKED_MASK                                 (0x4)
#define GENERIC_AND_FUSE_REG_CPTRA_SECURITY_STATE_SCAN_MODE_LOW                                     (3)
#define GENERIC_AND_FUSE_REG_CPTRA_SECURITY_STATE_SCAN_MODE_MASK                                    (0x8)
#define GENERIC_AND_FUSE_REG_CPTRA_SECURITY_STATE_RSVD_LOW                                          (4)
#define GENERIC_AND_FUSE_REG_CPTRA_SECURITY_STATE_RSVD_MASK                                         (0xfffffff0)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_MBOX_VALID_AXI_USER_0                           (0x30048)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_MBOX_VALID_AXI_USER_0
#define GENERIC_AND_FUSE_REG_CPTRA_MBOX_VALID_AXI_USER_0                                            (0x48)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_MBOX_VALID_AXI_USER_1                           (0x3004c)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_MBOX_VALID_AXI_USER_1
#define GENERIC_AND_FUSE_REG_CPTRA_MBOX_VALID_AXI_USER_1                                            (0x4c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_MBOX_VALID_AXI_USER_2                           (0x30050)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_MBOX_VALID_AXI_USER_2
#define GENERIC_AND_FUSE_REG_CPTRA_MBOX_VALID_AXI_USER_2                                            (0x50)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_MBOX_VALID_AXI_USER_3                           (0x30054)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_MBOX_VALID_AXI_USER_3
#define GENERIC_AND_FUSE_REG_CPTRA_MBOX_VALID_AXI_USER_3                                            (0x54)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_MBOX_VALID_AXI_USER_4                           (0x30058)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_MBOX_VALID_AXI_USER_4
#define GENERIC_AND_FUSE_REG_CPTRA_MBOX_VALID_AXI_USER_4                                            (0x58)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_MBOX_AXI_USER_LOCK_0                            (0x3005c)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_MBOX_AXI_USER_LOCK_0
#define GENERIC_AND_FUSE_REG_CPTRA_MBOX_AXI_USER_LOCK_0                                             (0x5c)
#define GENERIC_AND_FUSE_REG_CPTRA_MBOX_AXI_USER_LOCK_0_LOCK_LOW                                    (0)
#define GENERIC_AND_FUSE_REG_CPTRA_MBOX_AXI_USER_LOCK_0_LOCK_MASK                                   (0x1)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_MBOX_AXI_USER_LOCK_1                            (0x30060)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_MBOX_AXI_USER_LOCK_1
#define GENERIC_AND_FUSE_REG_CPTRA_MBOX_AXI_USER_LOCK_1                                             (0x60)
#define GENERIC_AND_FUSE_REG_CPTRA_MBOX_AXI_USER_LOCK_1_LOCK_LOW                                    (0)
#define GENERIC_AND_FUSE_REG_CPTRA_MBOX_AXI_USER_LOCK_1_LOCK_MASK                                   (0x1)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_MBOX_AXI_USER_LOCK_2                            (0x30064)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_MBOX_AXI_USER_LOCK_2
#define GENERIC_AND_FUSE_REG_CPTRA_MBOX_AXI_USER_LOCK_2                                             (0x64)
#define GENERIC_AND_FUSE_REG_CPTRA_MBOX_AXI_USER_LOCK_2_LOCK_LOW                                    (0)
#define GENERIC_AND_FUSE_REG_CPTRA_MBOX_AXI_USER_LOCK_2_LOCK_MASK                                   (0x1)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_MBOX_AXI_USER_LOCK_3                            (0x30068)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_MBOX_AXI_USER_LOCK_3
#define GENERIC_AND_FUSE_REG_CPTRA_MBOX_AXI_USER_LOCK_3                                             (0x68)
#define GENERIC_AND_FUSE_REG_CPTRA_MBOX_AXI_USER_LOCK_3_LOCK_LOW                                    (0)
#define GENERIC_AND_FUSE_REG_CPTRA_MBOX_AXI_USER_LOCK_3_LOCK_MASK                                   (0x1)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_MBOX_AXI_USER_LOCK_4                            (0x3006c)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_MBOX_AXI_USER_LOCK_4
#define GENERIC_AND_FUSE_REG_CPTRA_MBOX_AXI_USER_LOCK_4                                             (0x6c)
#define GENERIC_AND_FUSE_REG_CPTRA_MBOX_AXI_USER_LOCK_4_LOCK_LOW                                    (0)
#define GENERIC_AND_FUSE_REG_CPTRA_MBOX_AXI_USER_LOCK_4_LOCK_MASK                                   (0x1)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_TRNG_VALID_AXI_USER                             (0x30070)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_TRNG_VALID_AXI_USER
#define GENERIC_AND_FUSE_REG_CPTRA_TRNG_VALID_AXI_USER                                              (0x70)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_TRNG_AXI_USER_LOCK                              (0x30074)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_TRNG_AXI_USER_LOCK
#define GENERIC_AND_FUSE_REG_CPTRA_TRNG_AXI_USER_LOCK                                               (0x74)
#define GENERIC_AND_FUSE_REG_CPTRA_TRNG_AXI_USER_LOCK_LOCK_LOW                                      (0)
#define GENERIC_AND_FUSE_REG_CPTRA_TRNG_AXI_USER_LOCK_LOCK_MASK                                     (0x1)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_0                                     (0x30078)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_0
#define GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_0                                                      (0x78)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_1                                     (0x3007c)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_1
#define GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_1                                                      (0x7c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_2                                     (0x30080)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_2
#define GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_2                                                      (0x80)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_3                                     (0x30084)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_3
#define GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_3                                                      (0x84)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_4                                     (0x30088)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_4
#define GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_4                                                      (0x88)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_5                                     (0x3008c)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_5
#define GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_5                                                      (0x8c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_6                                     (0x30090)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_6
#define GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_6                                                      (0x90)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_7                                     (0x30094)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_7
#define GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_7                                                      (0x94)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_8                                     (0x30098)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_8
#define GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_8                                                      (0x98)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_9                                     (0x3009c)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_9
#define GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_9                                                      (0x9c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_10                                    (0x300a0)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_10
#define GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_10                                                     (0xa0)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_11                                    (0x300a4)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_11
#define GENERIC_AND_FUSE_REG_CPTRA_TRNG_DATA_11                                                     (0xa4)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_TRNG_CTRL                                       (0x300a8)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_TRNG_CTRL
#define GENERIC_AND_FUSE_REG_CPTRA_TRNG_CTRL                                                        (0xa8)
#define GENERIC_AND_FUSE_REG_CPTRA_TRNG_CTRL_CLEAR_LOW                                              (0)
#define GENERIC_AND_FUSE_REG_CPTRA_TRNG_CTRL_CLEAR_MASK                                             (0x1)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_TRNG_STATUS                                     (0x300ac)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_TRNG_STATUS
#define GENERIC_AND_FUSE_REG_CPTRA_TRNG_STATUS                                                      (0xac)
#define GENERIC_AND_FUSE_REG_CPTRA_TRNG_STATUS_DATA_REQ_LOW                                         (0)
#define GENERIC_AND_FUSE_REG_CPTRA_TRNG_STATUS_DATA_REQ_MASK                                        (0x1)
#define GENERIC_AND_FUSE_REG_CPTRA_TRNG_STATUS_DATA_WR_DONE_LOW                                     (1)
#define GENERIC_AND_FUSE_REG_CPTRA_TRNG_STATUS_DATA_WR_DONE_MASK                                    (0x2)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_FUSE_WR_DONE                                    (0x300b0)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_FUSE_WR_DONE
#define GENERIC_AND_FUSE_REG_CPTRA_FUSE_WR_DONE                                                     (0xb0)
#define GENERIC_AND_FUSE_REG_CPTRA_FUSE_WR_DONE_DONE_LOW                                            (0)
#define GENERIC_AND_FUSE_REG_CPTRA_FUSE_WR_DONE_DONE_MASK                                           (0x1)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_TIMER_CONFIG                                    (0x300b4)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_TIMER_CONFIG
#define GENERIC_AND_FUSE_REG_CPTRA_TIMER_CONFIG                                                     (0xb4)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_BOOTFSM_GO                                      (0x300b8)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_BOOTFSM_GO
#define GENERIC_AND_FUSE_REG_CPTRA_BOOTFSM_GO                                                       (0xb8)
#define GENERIC_AND_FUSE_REG_CPTRA_BOOTFSM_GO_GO_LOW                                                (0)
#define GENERIC_AND_FUSE_REG_CPTRA_BOOTFSM_GO_GO_MASK                                               (0x1)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_DBG_MANUF_SERVICE_REG                           (0x300bc)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_DBG_MANUF_SERVICE_REG
#define GENERIC_AND_FUSE_REG_CPTRA_DBG_MANUF_SERVICE_REG                                            (0xbc)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_CLK_GATING_EN                                   (0x300c0)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_CLK_GATING_EN
#define GENERIC_AND_FUSE_REG_CPTRA_CLK_GATING_EN                                                    (0xc0)
#define GENERIC_AND_FUSE_REG_CPTRA_CLK_GATING_EN_CLK_GATING_EN_LOW                                  (0)
#define GENERIC_AND_FUSE_REG_CPTRA_CLK_GATING_EN_CLK_GATING_EN_MASK                                 (0x1)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_GENERIC_INPUT_WIRES_0                           (0x300c4)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_GENERIC_INPUT_WIRES_0
#define GENERIC_AND_FUSE_REG_CPTRA_GENERIC_INPUT_WIRES_0                                            (0xc4)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_GENERIC_INPUT_WIRES_1                           (0x300c8)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_GENERIC_INPUT_WIRES_1
#define GENERIC_AND_FUSE_REG_CPTRA_GENERIC_INPUT_WIRES_1                                            (0xc8)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_GENERIC_OUTPUT_WIRES_0                          (0x300cc)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_GENERIC_OUTPUT_WIRES_0
#define GENERIC_AND_FUSE_REG_CPTRA_GENERIC_OUTPUT_WIRES_0                                           (0xcc)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_GENERIC_OUTPUT_WIRES_1                          (0x300d0)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_GENERIC_OUTPUT_WIRES_1
#define GENERIC_AND_FUSE_REG_CPTRA_GENERIC_OUTPUT_WIRES_1                                           (0xd0)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_HW_REV_ID                                       (0x300d4)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_HW_REV_ID
#define GENERIC_AND_FUSE_REG_CPTRA_HW_REV_ID                                                        (0xd4)
#define GENERIC_AND_FUSE_REG_CPTRA_HW_REV_ID_CPTRA_GENERATION_LOW                                   (0)
#define GENERIC_AND_FUSE_REG_CPTRA_HW_REV_ID_CPTRA_GENERATION_MASK                                  (0xffff)
#define GENERIC_AND_FUSE_REG_CPTRA_HW_REV_ID_SOC_STEPPING_ID_LOW                                    (16)
#define GENERIC_AND_FUSE_REG_CPTRA_HW_REV_ID_SOC_STEPPING_ID_MASK                                   (0xffff0000)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_FW_REV_ID_0                                     (0x300d8)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_FW_REV_ID_0
#define GENERIC_AND_FUSE_REG_CPTRA_FW_REV_ID_0                                                      (0xd8)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_FW_REV_ID_1                                     (0x300dc)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_FW_REV_ID_1
#define GENERIC_AND_FUSE_REG_CPTRA_FW_REV_ID_1                                                      (0xdc)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_HW_CONFIG                                       (0x300e0)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_HW_CONFIG
#define GENERIC_AND_FUSE_REG_CPTRA_HW_CONFIG                                                        (0xe0)
#define GENERIC_AND_FUSE_REG_CPTRA_HW_CONFIG_ITRNG_EN_LOW                                           (0)
#define GENERIC_AND_FUSE_REG_CPTRA_HW_CONFIG_ITRNG_EN_MASK                                          (0x1)
#define GENERIC_AND_FUSE_REG_CPTRA_HW_CONFIG_FUSE_GRANULARITY_LOW                                   (1)
#define GENERIC_AND_FUSE_REG_CPTRA_HW_CONFIG_FUSE_GRANULARITY_MASK                                  (0x2)
#define GENERIC_AND_FUSE_REG_CPTRA_HW_CONFIG_RSVD_EN_LOW                                            (2)
#define GENERIC_AND_FUSE_REG_CPTRA_HW_CONFIG_RSVD_EN_MASK                                           (0xc)
#define GENERIC_AND_FUSE_REG_CPTRA_HW_CONFIG_LMS_ACC_EN_LOW                                         (4)
#define GENERIC_AND_FUSE_REG_CPTRA_HW_CONFIG_LMS_ACC_EN_MASK                                        (0x10)
#define GENERIC_AND_FUSE_REG_CPTRA_HW_CONFIG_SUBSYSTEM_MODE_EN_LOW                                  (5)
#define GENERIC_AND_FUSE_REG_CPTRA_HW_CONFIG_SUBSYSTEM_MODE_EN_MASK                                 (0x20)
#define GENERIC_AND_FUSE_REG_CPTRA_HW_CONFIG_OCP_LOCK_MODE_EN_LOW                                   (6)
#define GENERIC_AND_FUSE_REG_CPTRA_HW_CONFIG_OCP_LOCK_MODE_EN_MASK                                  (0x40)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_WDT_TIMER1_EN                                   (0x300e4)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_WDT_TIMER1_EN
#define GENERIC_AND_FUSE_REG_CPTRA_WDT_TIMER1_EN                                                    (0xe4)
#define GENERIC_AND_FUSE_REG_CPTRA_WDT_TIMER1_EN_TIMER1_EN_LOW                                      (0)
#define GENERIC_AND_FUSE_REG_CPTRA_WDT_TIMER1_EN_TIMER1_EN_MASK                                     (0x1)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_WDT_TIMER1_CTRL                                 (0x300e8)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_WDT_TIMER1_CTRL
#define GENERIC_AND_FUSE_REG_CPTRA_WDT_TIMER1_CTRL                                                  (0xe8)
#define GENERIC_AND_FUSE_REG_CPTRA_WDT_TIMER1_CTRL_TIMER1_RESTART_LOW                               (0)
#define GENERIC_AND_FUSE_REG_CPTRA_WDT_TIMER1_CTRL_TIMER1_RESTART_MASK                              (0x1)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD_0                     (0x300ec)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD_0
#define GENERIC_AND_FUSE_REG_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD_0                                      (0xec)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD_1                     (0x300f0)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD_1
#define GENERIC_AND_FUSE_REG_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD_1                                      (0xf0)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_WDT_TIMER2_EN                                   (0x300f4)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_WDT_TIMER2_EN
#define GENERIC_AND_FUSE_REG_CPTRA_WDT_TIMER2_EN                                                    (0xf4)
#define GENERIC_AND_FUSE_REG_CPTRA_WDT_TIMER2_EN_TIMER2_EN_LOW                                      (0)
#define GENERIC_AND_FUSE_REG_CPTRA_WDT_TIMER2_EN_TIMER2_EN_MASK                                     (0x1)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_WDT_TIMER2_CTRL                                 (0x300f8)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_WDT_TIMER2_CTRL
#define GENERIC_AND_FUSE_REG_CPTRA_WDT_TIMER2_CTRL                                                  (0xf8)
#define GENERIC_AND_FUSE_REG_CPTRA_WDT_TIMER2_CTRL_TIMER2_RESTART_LOW                               (0)
#define GENERIC_AND_FUSE_REG_CPTRA_WDT_TIMER2_CTRL_TIMER2_RESTART_MASK                              (0x1)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD_0                     (0x300fc)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD_0
#define GENERIC_AND_FUSE_REG_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD_0                                      (0xfc)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD_1                     (0x30100)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD_1
#define GENERIC_AND_FUSE_REG_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD_1                                      (0x100)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_WDT_STATUS                                      (0x30104)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_WDT_STATUS
#define GENERIC_AND_FUSE_REG_CPTRA_WDT_STATUS                                                       (0x104)
#define GENERIC_AND_FUSE_REG_CPTRA_WDT_STATUS_T1_TIMEOUT_LOW                                        (0)
#define GENERIC_AND_FUSE_REG_CPTRA_WDT_STATUS_T1_TIMEOUT_MASK                                       (0x1)
#define GENERIC_AND_FUSE_REG_CPTRA_WDT_STATUS_T2_TIMEOUT_LOW                                        (1)
#define GENERIC_AND_FUSE_REG_CPTRA_WDT_STATUS_T2_TIMEOUT_MASK                                       (0x2)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_FUSE_VALID_AXI_USER                             (0x30108)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_FUSE_VALID_AXI_USER
#define GENERIC_AND_FUSE_REG_CPTRA_FUSE_VALID_AXI_USER                                              (0x108)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_FUSE_AXI_USER_LOCK                              (0x3010c)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_FUSE_AXI_USER_LOCK
#define GENERIC_AND_FUSE_REG_CPTRA_FUSE_AXI_USER_LOCK                                               (0x10c)
#define GENERIC_AND_FUSE_REG_CPTRA_FUSE_AXI_USER_LOCK_LOCK_LOW                                      (0)
#define GENERIC_AND_FUSE_REG_CPTRA_FUSE_AXI_USER_LOCK_LOCK_MASK                                     (0x1)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_WDT_CFG_0                                       (0x30110)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_WDT_CFG_0
#define GENERIC_AND_FUSE_REG_CPTRA_WDT_CFG_0                                                        (0x110)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_WDT_CFG_1                                       (0x30114)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_WDT_CFG_1
#define GENERIC_AND_FUSE_REG_CPTRA_WDT_CFG_1                                                        (0x114)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_ITRNG_ENTROPY_CONFIG_0                          (0x30118)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_ITRNG_ENTROPY_CONFIG_0
#define GENERIC_AND_FUSE_REG_CPTRA_ITRNG_ENTROPY_CONFIG_0                                           (0x118)
#define GENERIC_AND_FUSE_REG_CPTRA_ITRNG_ENTROPY_CONFIG_0_LOW_THRESHOLD_LOW                         (0)
#define GENERIC_AND_FUSE_REG_CPTRA_ITRNG_ENTROPY_CONFIG_0_LOW_THRESHOLD_MASK                        (0xffff)
#define GENERIC_AND_FUSE_REG_CPTRA_ITRNG_ENTROPY_CONFIG_0_HIGH_THRESHOLD_LOW                        (16)
#define GENERIC_AND_FUSE_REG_CPTRA_ITRNG_ENTROPY_CONFIG_0_HIGH_THRESHOLD_MASK                       (0xffff0000)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_ITRNG_ENTROPY_CONFIG_1                          (0x3011c)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_ITRNG_ENTROPY_CONFIG_1
#define GENERIC_AND_FUSE_REG_CPTRA_ITRNG_ENTROPY_CONFIG_1                                           (0x11c)
#define GENERIC_AND_FUSE_REG_CPTRA_ITRNG_ENTROPY_CONFIG_1_REPETITION_COUNT_LOW                      (0)
#define GENERIC_AND_FUSE_REG_CPTRA_ITRNG_ENTROPY_CONFIG_1_REPETITION_COUNT_MASK                     (0xffff)
#define GENERIC_AND_FUSE_REG_CPTRA_ITRNG_ENTROPY_CONFIG_1_RSVD_LOW                                  (16)
#define GENERIC_AND_FUSE_REG_CPTRA_ITRNG_ENTROPY_CONFIG_1_RSVD_MASK                                 (0xffff0000)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_RSVD_REG_0                                      (0x30120)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_RSVD_REG_0
#define GENERIC_AND_FUSE_REG_CPTRA_RSVD_REG_0                                                       (0x120)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_RSVD_REG_1                                      (0x30124)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_RSVD_REG_1
#define GENERIC_AND_FUSE_REG_CPTRA_RSVD_REG_1                                                       (0x124)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_HW_CAPABILITIES                                 (0x30128)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_HW_CAPABILITIES
#define GENERIC_AND_FUSE_REG_CPTRA_HW_CAPABILITIES                                                  (0x128)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_FW_CAPABILITIES                                 (0x3012c)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_FW_CAPABILITIES
#define GENERIC_AND_FUSE_REG_CPTRA_FW_CAPABILITIES                                                  (0x12c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_CAP_LOCK                                        (0x30130)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_CAP_LOCK
#define GENERIC_AND_FUSE_REG_CPTRA_CAP_LOCK                                                         (0x130)
#define GENERIC_AND_FUSE_REG_CPTRA_CAP_LOCK_LOCK_LOW                                                (0)
#define GENERIC_AND_FUSE_REG_CPTRA_CAP_LOCK_LOCK_MASK                                               (0x1)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_0                                 (0x30140)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_0
#define GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_0                                                  (0x140)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_1                                 (0x30144)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_1
#define GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_1                                                  (0x144)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_2                                 (0x30148)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_2
#define GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_2                                                  (0x148)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_3                                 (0x3014c)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_3
#define GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_3                                                  (0x14c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_4                                 (0x30150)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_4
#define GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_4                                                  (0x150)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_5                                 (0x30154)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_5
#define GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_5                                                  (0x154)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_6                                 (0x30158)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_6
#define GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_6                                                  (0x158)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_7                                 (0x3015c)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_7
#define GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_7                                                  (0x15c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_8                                 (0x30160)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_8
#define GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_8                                                  (0x160)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_9                                 (0x30164)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_9
#define GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_9                                                  (0x164)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_10                                (0x30168)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_10
#define GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_10                                                 (0x168)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_11                                (0x3016c)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_11
#define GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_11                                                 (0x16c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_LOCK                              (0x30170)
#ifndef GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_LOCK
#define GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_LOCK                                               (0x170)
#define GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_LOCK_LOCK_LOW                                      (0)
#define GENERIC_AND_FUSE_REG_CPTRA_OWNER_PK_HASH_LOCK_LOCK_MASK                                     (0x1)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_0                                       (0x30200)
#ifndef GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_0
#define GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_0                                                        (0x200)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_1                                       (0x30204)
#ifndef GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_1
#define GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_1                                                        (0x204)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_2                                       (0x30208)
#ifndef GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_2
#define GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_2                                                        (0x208)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_3                                       (0x3020c)
#ifndef GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_3
#define GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_3                                                        (0x20c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_4                                       (0x30210)
#ifndef GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_4
#define GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_4                                                        (0x210)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_5                                       (0x30214)
#ifndef GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_5
#define GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_5                                                        (0x214)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_6                                       (0x30218)
#ifndef GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_6
#define GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_6                                                        (0x218)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_7                                       (0x3021c)
#ifndef GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_7
#define GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_7                                                        (0x21c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_8                                       (0x30220)
#ifndef GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_8
#define GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_8                                                        (0x220)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_9                                       (0x30224)
#ifndef GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_9
#define GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_9                                                        (0x224)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_10                                      (0x30228)
#ifndef GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_10
#define GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_10                                                       (0x228)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_11                                      (0x3022c)
#ifndef GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_11
#define GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_11                                                       (0x22c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_12                                      (0x30230)
#ifndef GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_12
#define GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_12                                                       (0x230)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_13                                      (0x30234)
#ifndef GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_13
#define GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_13                                                       (0x234)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_14                                      (0x30238)
#ifndef GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_14
#define GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_14                                                       (0x238)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_15                                      (0x3023c)
#ifndef GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_15
#define GENERIC_AND_FUSE_REG_FUSE_UDS_SEED_15                                                       (0x23c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_FIELD_ENTROPY_0                                  (0x30240)
#ifndef GENERIC_AND_FUSE_REG_FUSE_FIELD_ENTROPY_0
#define GENERIC_AND_FUSE_REG_FUSE_FIELD_ENTROPY_0                                                   (0x240)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_FIELD_ENTROPY_1                                  (0x30244)
#ifndef GENERIC_AND_FUSE_REG_FUSE_FIELD_ENTROPY_1
#define GENERIC_AND_FUSE_REG_FUSE_FIELD_ENTROPY_1                                                   (0x244)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_FIELD_ENTROPY_2                                  (0x30248)
#ifndef GENERIC_AND_FUSE_REG_FUSE_FIELD_ENTROPY_2
#define GENERIC_AND_FUSE_REG_FUSE_FIELD_ENTROPY_2                                                   (0x248)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_FIELD_ENTROPY_3                                  (0x3024c)
#ifndef GENERIC_AND_FUSE_REG_FUSE_FIELD_ENTROPY_3
#define GENERIC_AND_FUSE_REG_FUSE_FIELD_ENTROPY_3                                                   (0x24c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_FIELD_ENTROPY_4                                  (0x30250)
#ifndef GENERIC_AND_FUSE_REG_FUSE_FIELD_ENTROPY_4
#define GENERIC_AND_FUSE_REG_FUSE_FIELD_ENTROPY_4                                                   (0x250)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_FIELD_ENTROPY_5                                  (0x30254)
#ifndef GENERIC_AND_FUSE_REG_FUSE_FIELD_ENTROPY_5
#define GENERIC_AND_FUSE_REG_FUSE_FIELD_ENTROPY_5                                                   (0x254)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_FIELD_ENTROPY_6                                  (0x30258)
#ifndef GENERIC_AND_FUSE_REG_FUSE_FIELD_ENTROPY_6
#define GENERIC_AND_FUSE_REG_FUSE_FIELD_ENTROPY_6                                                   (0x258)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_FIELD_ENTROPY_7                                  (0x3025c)
#ifndef GENERIC_AND_FUSE_REG_FUSE_FIELD_ENTROPY_7
#define GENERIC_AND_FUSE_REG_FUSE_FIELD_ENTROPY_7                                                   (0x25c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_0                                 (0x30260)
#ifndef GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_0
#define GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_0                                                  (0x260)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_1                                 (0x30264)
#ifndef GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_1
#define GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_1                                                  (0x264)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_2                                 (0x30268)
#ifndef GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_2
#define GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_2                                                  (0x268)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_3                                 (0x3026c)
#ifndef GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_3
#define GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_3                                                  (0x26c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_4                                 (0x30270)
#ifndef GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_4
#define GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_4                                                  (0x270)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_5                                 (0x30274)
#ifndef GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_5
#define GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_5                                                  (0x274)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_6                                 (0x30278)
#ifndef GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_6
#define GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_6                                                  (0x278)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_7                                 (0x3027c)
#ifndef GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_7
#define GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_7                                                  (0x27c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_8                                 (0x30280)
#ifndef GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_8
#define GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_8                                                  (0x280)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_9                                 (0x30284)
#ifndef GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_9
#define GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_9                                                  (0x284)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_10                                (0x30288)
#ifndef GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_10
#define GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_10                                                 (0x288)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_11                                (0x3028c)
#ifndef GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_11
#define GENERIC_AND_FUSE_REG_FUSE_VENDOR_PK_HASH_11                                                 (0x28c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_ECC_REVOCATION                                   (0x30290)
#ifndef GENERIC_AND_FUSE_REG_FUSE_ECC_REVOCATION
#define GENERIC_AND_FUSE_REG_FUSE_ECC_REVOCATION                                                    (0x290)
#define GENERIC_AND_FUSE_REG_FUSE_ECC_REVOCATION_ECC_REVOCATION_LOW                                 (0)
#define GENERIC_AND_FUSE_REG_FUSE_ECC_REVOCATION_ECC_REVOCATION_MASK                                (0xf)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_FMC_KEY_MANIFEST_SVN                             (0x302b4)
#ifndef GENERIC_AND_FUSE_REG_FUSE_FMC_KEY_MANIFEST_SVN
#define GENERIC_AND_FUSE_REG_FUSE_FMC_KEY_MANIFEST_SVN                                              (0x2b4)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_RUNTIME_SVN_0                                    (0x302b8)
#ifndef GENERIC_AND_FUSE_REG_FUSE_RUNTIME_SVN_0
#define GENERIC_AND_FUSE_REG_FUSE_RUNTIME_SVN_0                                                     (0x2b8)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_RUNTIME_SVN_1                                    (0x302bc)
#ifndef GENERIC_AND_FUSE_REG_FUSE_RUNTIME_SVN_1
#define GENERIC_AND_FUSE_REG_FUSE_RUNTIME_SVN_1                                                     (0x2bc)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_RUNTIME_SVN_2                                    (0x302c0)
#ifndef GENERIC_AND_FUSE_REG_FUSE_RUNTIME_SVN_2
#define GENERIC_AND_FUSE_REG_FUSE_RUNTIME_SVN_2                                                     (0x2c0)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_RUNTIME_SVN_3                                    (0x302c4)
#ifndef GENERIC_AND_FUSE_REG_FUSE_RUNTIME_SVN_3
#define GENERIC_AND_FUSE_REG_FUSE_RUNTIME_SVN_3                                                     (0x2c4)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_ANTI_ROLLBACK_DISABLE                            (0x302c8)
#ifndef GENERIC_AND_FUSE_REG_FUSE_ANTI_ROLLBACK_DISABLE
#define GENERIC_AND_FUSE_REG_FUSE_ANTI_ROLLBACK_DISABLE                                             (0x2c8)
#define GENERIC_AND_FUSE_REG_FUSE_ANTI_ROLLBACK_DISABLE_DIS_LOW                                     (0)
#define GENERIC_AND_FUSE_REG_FUSE_ANTI_ROLLBACK_DISABLE_DIS_MASK                                    (0x1)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_0                               (0x302cc)
#ifndef GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_0
#define GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_0                                                (0x2cc)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_1                               (0x302d0)
#ifndef GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_1
#define GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_1                                                (0x2d0)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_2                               (0x302d4)
#ifndef GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_2
#define GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_2                                                (0x2d4)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_3                               (0x302d8)
#ifndef GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_3
#define GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_3                                                (0x2d8)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_4                               (0x302dc)
#ifndef GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_4
#define GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_4                                                (0x2dc)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_5                               (0x302e0)
#ifndef GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_5
#define GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_5                                                (0x2e0)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_6                               (0x302e4)
#ifndef GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_6
#define GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_6                                                (0x2e4)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_7                               (0x302e8)
#ifndef GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_7
#define GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_7                                                (0x2e8)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_8                               (0x302ec)
#ifndef GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_8
#define GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_8                                                (0x2ec)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_9                               (0x302f0)
#ifndef GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_9
#define GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_9                                                (0x2f0)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_10                              (0x302f4)
#ifndef GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_10
#define GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_10                                               (0x2f4)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_11                              (0x302f8)
#ifndef GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_11
#define GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_11                                               (0x2f8)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_12                              (0x302fc)
#ifndef GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_12
#define GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_12                                               (0x2fc)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_13                              (0x30300)
#ifndef GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_13
#define GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_13                                               (0x300)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_14                              (0x30304)
#ifndef GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_14
#define GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_14                                               (0x304)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_15                              (0x30308)
#ifndef GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_15
#define GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_15                                               (0x308)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_16                              (0x3030c)
#ifndef GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_16
#define GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_16                                               (0x30c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_17                              (0x30310)
#ifndef GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_17
#define GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_17                                               (0x310)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_18                              (0x30314)
#ifndef GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_18
#define GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_18                                               (0x314)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_19                              (0x30318)
#ifndef GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_19
#define GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_19                                               (0x318)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_20                              (0x3031c)
#ifndef GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_20
#define GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_20                                               (0x31c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_21                              (0x30320)
#ifndef GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_21
#define GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_21                                               (0x320)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_22                              (0x30324)
#ifndef GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_22
#define GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_22                                               (0x324)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_23                              (0x30328)
#ifndef GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_23
#define GENERIC_AND_FUSE_REG_FUSE_IDEVID_CERT_ATTR_23                                               (0x328)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_IDEVID_MANUF_HSM_ID_0                            (0x3032c)
#ifndef GENERIC_AND_FUSE_REG_FUSE_IDEVID_MANUF_HSM_ID_0
#define GENERIC_AND_FUSE_REG_FUSE_IDEVID_MANUF_HSM_ID_0                                             (0x32c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_IDEVID_MANUF_HSM_ID_1                            (0x30330)
#ifndef GENERIC_AND_FUSE_REG_FUSE_IDEVID_MANUF_HSM_ID_1
#define GENERIC_AND_FUSE_REG_FUSE_IDEVID_MANUF_HSM_ID_1                                             (0x330)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_IDEVID_MANUF_HSM_ID_2                            (0x30334)
#ifndef GENERIC_AND_FUSE_REG_FUSE_IDEVID_MANUF_HSM_ID_2
#define GENERIC_AND_FUSE_REG_FUSE_IDEVID_MANUF_HSM_ID_2                                             (0x334)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_IDEVID_MANUF_HSM_ID_3                            (0x30338)
#ifndef GENERIC_AND_FUSE_REG_FUSE_IDEVID_MANUF_HSM_ID_3
#define GENERIC_AND_FUSE_REG_FUSE_IDEVID_MANUF_HSM_ID_3                                             (0x338)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_LMS_REVOCATION                                   (0x30340)
#ifndef GENERIC_AND_FUSE_REG_FUSE_LMS_REVOCATION
#define GENERIC_AND_FUSE_REG_FUSE_LMS_REVOCATION                                                    (0x340)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_MLDSA_REVOCATION                                 (0x30344)
#ifndef GENERIC_AND_FUSE_REG_FUSE_MLDSA_REVOCATION
#define GENERIC_AND_FUSE_REG_FUSE_MLDSA_REVOCATION                                                  (0x344)
#define GENERIC_AND_FUSE_REG_FUSE_MLDSA_REVOCATION_MLDSA_REVOCATION_LOW                             (0)
#define GENERIC_AND_FUSE_REG_FUSE_MLDSA_REVOCATION_MLDSA_REVOCATION_MASK                            (0xf)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_SOC_STEPPING_ID                                  (0x30348)
#ifndef GENERIC_AND_FUSE_REG_FUSE_SOC_STEPPING_ID
#define GENERIC_AND_FUSE_REG_FUSE_SOC_STEPPING_ID                                                   (0x348)
#define GENERIC_AND_FUSE_REG_FUSE_SOC_STEPPING_ID_SOC_STEPPING_ID_LOW                               (0)
#define GENERIC_AND_FUSE_REG_FUSE_SOC_STEPPING_ID_SOC_STEPPING_ID_MASK                              (0xffff)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_0                         (0x3034c)
#ifndef GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_0
#define GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_0                                          (0x34c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_1                         (0x30350)
#ifndef GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_1
#define GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_1                                          (0x350)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_2                         (0x30354)
#ifndef GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_2
#define GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_2                                          (0x354)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_3                         (0x30358)
#ifndef GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_3
#define GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_3                                          (0x358)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_4                         (0x3035c)
#ifndef GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_4
#define GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_4                                          (0x35c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_5                         (0x30360)
#ifndef GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_5
#define GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_5                                          (0x360)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_6                         (0x30364)
#ifndef GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_6
#define GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_6                                          (0x364)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_7                         (0x30368)
#ifndef GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_7
#define GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_7                                          (0x368)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_8                         (0x3036c)
#ifndef GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_8
#define GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_8                                          (0x36c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_9                         (0x30370)
#ifndef GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_9
#define GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_9                                          (0x370)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_10                        (0x30374)
#ifndef GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_10
#define GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_10                                         (0x374)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_11                        (0x30378)
#ifndef GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_11
#define GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_11                                         (0x378)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_12                        (0x3037c)
#ifndef GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_12
#define GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_12                                         (0x37c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_13                        (0x30380)
#ifndef GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_13
#define GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_13                                         (0x380)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_14                        (0x30384)
#ifndef GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_14
#define GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_14                                         (0x384)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_15                        (0x30388)
#ifndef GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_15
#define GENERIC_AND_FUSE_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_15                                         (0x388)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_PQC_KEY_TYPE                                     (0x3038c)
#ifndef GENERIC_AND_FUSE_REG_FUSE_PQC_KEY_TYPE
#define GENERIC_AND_FUSE_REG_FUSE_PQC_KEY_TYPE                                                      (0x38c)
#define GENERIC_AND_FUSE_REG_FUSE_PQC_KEY_TYPE_KEY_TYPE_LOW                                         (0)
#define GENERIC_AND_FUSE_REG_FUSE_PQC_KEY_TYPE_KEY_TYPE_MASK                                        (0x3)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_SOC_MANIFEST_SVN_0                               (0x30390)
#ifndef GENERIC_AND_FUSE_REG_FUSE_SOC_MANIFEST_SVN_0
#define GENERIC_AND_FUSE_REG_FUSE_SOC_MANIFEST_SVN_0                                                (0x390)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_SOC_MANIFEST_SVN_1                               (0x30394)
#ifndef GENERIC_AND_FUSE_REG_FUSE_SOC_MANIFEST_SVN_1
#define GENERIC_AND_FUSE_REG_FUSE_SOC_MANIFEST_SVN_1                                                (0x394)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_SOC_MANIFEST_SVN_2                               (0x30398)
#ifndef GENERIC_AND_FUSE_REG_FUSE_SOC_MANIFEST_SVN_2
#define GENERIC_AND_FUSE_REG_FUSE_SOC_MANIFEST_SVN_2                                                (0x398)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_SOC_MANIFEST_SVN_3                               (0x3039c)
#ifndef GENERIC_AND_FUSE_REG_FUSE_SOC_MANIFEST_SVN_3
#define GENERIC_AND_FUSE_REG_FUSE_SOC_MANIFEST_SVN_3                                                (0x39c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_SOC_MANIFEST_MAX_SVN                             (0x303a0)
#ifndef GENERIC_AND_FUSE_REG_FUSE_SOC_MANIFEST_MAX_SVN
#define GENERIC_AND_FUSE_REG_FUSE_SOC_MANIFEST_MAX_SVN                                              (0x3a0)
#define GENERIC_AND_FUSE_REG_FUSE_SOC_MANIFEST_MAX_SVN_SVN_LOW                                      (0)
#define GENERIC_AND_FUSE_REG_FUSE_SOC_MANIFEST_MAX_SVN_SVN_MASK                                     (0xff)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_HEK_SEED_0                                       (0x303c0)
#ifndef GENERIC_AND_FUSE_REG_FUSE_HEK_SEED_0
#define GENERIC_AND_FUSE_REG_FUSE_HEK_SEED_0                                                        (0x3c0)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_HEK_SEED_1                                       (0x303c4)
#ifndef GENERIC_AND_FUSE_REG_FUSE_HEK_SEED_1
#define GENERIC_AND_FUSE_REG_FUSE_HEK_SEED_1                                                        (0x3c4)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_HEK_SEED_2                                       (0x303c8)
#ifndef GENERIC_AND_FUSE_REG_FUSE_HEK_SEED_2
#define GENERIC_AND_FUSE_REG_FUSE_HEK_SEED_2                                                        (0x3c8)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_HEK_SEED_3                                       (0x303cc)
#ifndef GENERIC_AND_FUSE_REG_FUSE_HEK_SEED_3
#define GENERIC_AND_FUSE_REG_FUSE_HEK_SEED_3                                                        (0x3cc)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_HEK_SEED_4                                       (0x303d0)
#ifndef GENERIC_AND_FUSE_REG_FUSE_HEK_SEED_4
#define GENERIC_AND_FUSE_REG_FUSE_HEK_SEED_4                                                        (0x3d0)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_HEK_SEED_5                                       (0x303d4)
#ifndef GENERIC_AND_FUSE_REG_FUSE_HEK_SEED_5
#define GENERIC_AND_FUSE_REG_FUSE_HEK_SEED_5                                                        (0x3d4)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_HEK_SEED_6                                       (0x303d8)
#ifndef GENERIC_AND_FUSE_REG_FUSE_HEK_SEED_6
#define GENERIC_AND_FUSE_REG_FUSE_HEK_SEED_6                                                        (0x3d8)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_FUSE_HEK_SEED_7                                       (0x303dc)
#ifndef GENERIC_AND_FUSE_REG_FUSE_HEK_SEED_7
#define GENERIC_AND_FUSE_REG_FUSE_HEK_SEED_7                                                        (0x3dc)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_SS_CALIPTRA_BASE_ADDR_L                               (0x30500)
#ifndef GENERIC_AND_FUSE_REG_SS_CALIPTRA_BASE_ADDR_L
#define GENERIC_AND_FUSE_REG_SS_CALIPTRA_BASE_ADDR_L                                                (0x500)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_SS_CALIPTRA_BASE_ADDR_H                               (0x30504)
#ifndef GENERIC_AND_FUSE_REG_SS_CALIPTRA_BASE_ADDR_H
#define GENERIC_AND_FUSE_REG_SS_CALIPTRA_BASE_ADDR_H                                                (0x504)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_SS_MCI_BASE_ADDR_L                                    (0x30508)
#ifndef GENERIC_AND_FUSE_REG_SS_MCI_BASE_ADDR_L
#define GENERIC_AND_FUSE_REG_SS_MCI_BASE_ADDR_L                                                     (0x508)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_SS_MCI_BASE_ADDR_H                                    (0x3050c)
#ifndef GENERIC_AND_FUSE_REG_SS_MCI_BASE_ADDR_H
#define GENERIC_AND_FUSE_REG_SS_MCI_BASE_ADDR_H                                                     (0x50c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_SS_RECOVERY_IFC_BASE_ADDR_L                           (0x30510)
#ifndef GENERIC_AND_FUSE_REG_SS_RECOVERY_IFC_BASE_ADDR_L
#define GENERIC_AND_FUSE_REG_SS_RECOVERY_IFC_BASE_ADDR_L                                            (0x510)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_SS_RECOVERY_IFC_BASE_ADDR_H                           (0x30514)
#ifndef GENERIC_AND_FUSE_REG_SS_RECOVERY_IFC_BASE_ADDR_H
#define GENERIC_AND_FUSE_REG_SS_RECOVERY_IFC_BASE_ADDR_H                                            (0x514)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_SS_OTP_FC_BASE_ADDR_L                                 (0x30518)
#ifndef GENERIC_AND_FUSE_REG_SS_OTP_FC_BASE_ADDR_L
#define GENERIC_AND_FUSE_REG_SS_OTP_FC_BASE_ADDR_L                                                  (0x518)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_SS_OTP_FC_BASE_ADDR_H                                 (0x3051c)
#ifndef GENERIC_AND_FUSE_REG_SS_OTP_FC_BASE_ADDR_H
#define GENERIC_AND_FUSE_REG_SS_OTP_FC_BASE_ADDR_H                                                  (0x51c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_SS_UDS_SEED_BASE_ADDR_L                               (0x30520)
#ifndef GENERIC_AND_FUSE_REG_SS_UDS_SEED_BASE_ADDR_L
#define GENERIC_AND_FUSE_REG_SS_UDS_SEED_BASE_ADDR_L                                                (0x520)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_SS_UDS_SEED_BASE_ADDR_H                               (0x30524)
#ifndef GENERIC_AND_FUSE_REG_SS_UDS_SEED_BASE_ADDR_H
#define GENERIC_AND_FUSE_REG_SS_UDS_SEED_BASE_ADDR_H                                                (0x524)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_SS_PROD_DEBUG_UNLOCK_AUTH_PK_HASH_REG_BANK_OFFSET     (0x30528)
#ifndef GENERIC_AND_FUSE_REG_SS_PROD_DEBUG_UNLOCK_AUTH_PK_HASH_REG_BANK_OFFSET
#define GENERIC_AND_FUSE_REG_SS_PROD_DEBUG_UNLOCK_AUTH_PK_HASH_REG_BANK_OFFSET                      (0x528)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_SS_NUM_OF_PROD_DEBUG_UNLOCK_AUTH_PK_HASHES            (0x3052c)
#ifndef GENERIC_AND_FUSE_REG_SS_NUM_OF_PROD_DEBUG_UNLOCK_AUTH_PK_HASHES
#define GENERIC_AND_FUSE_REG_SS_NUM_OF_PROD_DEBUG_UNLOCK_AUTH_PK_HASHES                             (0x52c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_SS_DEBUG_INTENT                                       (0x30530)
#ifndef GENERIC_AND_FUSE_REG_SS_DEBUG_INTENT
#define GENERIC_AND_FUSE_REG_SS_DEBUG_INTENT                                                        (0x530)
#define GENERIC_AND_FUSE_REG_SS_DEBUG_INTENT_DEBUG_INTENT_LOW                                       (0)
#define GENERIC_AND_FUSE_REG_SS_DEBUG_INTENT_DEBUG_INTENT_MASK                                      (0x1)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_SS_CALIPTRA_DMA_AXI_USER                              (0x30534)
#ifndef GENERIC_AND_FUSE_REG_SS_CALIPTRA_DMA_AXI_USER
#define GENERIC_AND_FUSE_REG_SS_CALIPTRA_DMA_AXI_USER                                               (0x534)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_SS_EXTERNAL_STAGING_AREA_BASE_ADDR_L                  (0x30538)
#ifndef GENERIC_AND_FUSE_REG_SS_EXTERNAL_STAGING_AREA_BASE_ADDR_L
#define GENERIC_AND_FUSE_REG_SS_EXTERNAL_STAGING_AREA_BASE_ADDR_L                                   (0x538)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_SS_EXTERNAL_STAGING_AREA_BASE_ADDR_H                  (0x3053c)
#ifndef GENERIC_AND_FUSE_REG_SS_EXTERNAL_STAGING_AREA_BASE_ADDR_H
#define GENERIC_AND_FUSE_REG_SS_EXTERNAL_STAGING_AREA_BASE_ADDR_H                                   (0x53c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_SS_KEY_RELEASE_BASE_ADDR_L                            (0x30540)
#ifndef GENERIC_AND_FUSE_REG_SS_KEY_RELEASE_BASE_ADDR_L
#define GENERIC_AND_FUSE_REG_SS_KEY_RELEASE_BASE_ADDR_L                                             (0x540)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_SS_KEY_RELEASE_BASE_ADDR_H                            (0x30544)
#ifndef GENERIC_AND_FUSE_REG_SS_KEY_RELEASE_BASE_ADDR_H
#define GENERIC_AND_FUSE_REG_SS_KEY_RELEASE_BASE_ADDR_H                                             (0x544)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_SS_KEY_RELEASE_SIZE                                   (0x30548)
#ifndef GENERIC_AND_FUSE_REG_SS_KEY_RELEASE_SIZE
#define GENERIC_AND_FUSE_REG_SS_KEY_RELEASE_SIZE                                                    (0x548)
#define GENERIC_AND_FUSE_REG_SS_KEY_RELEASE_SIZE_SIZE_LOW                                           (0)
#define GENERIC_AND_FUSE_REG_SS_KEY_RELEASE_SIZE_SIZE_MASK                                          (0xffff)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_SS_OCP_LOCK_CTRL                                      (0x3054c)
#ifndef GENERIC_AND_FUSE_REG_SS_OCP_LOCK_CTRL
#define GENERIC_AND_FUSE_REG_SS_OCP_LOCK_CTRL                                                       (0x54c)
#define GENERIC_AND_FUSE_REG_SS_OCP_LOCK_CTRL_LOCK_IN_PROGRESS_LOW                                  (0)
#define GENERIC_AND_FUSE_REG_SS_OCP_LOCK_CTRL_LOCK_IN_PROGRESS_MASK                                 (0x1)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_SS_STRAP_GENERIC_0                                    (0x305a0)
#ifndef GENERIC_AND_FUSE_REG_SS_STRAP_GENERIC_0
#define GENERIC_AND_FUSE_REG_SS_STRAP_GENERIC_0                                                     (0x5a0)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_SS_STRAP_GENERIC_1                                    (0x305a4)
#ifndef GENERIC_AND_FUSE_REG_SS_STRAP_GENERIC_1
#define GENERIC_AND_FUSE_REG_SS_STRAP_GENERIC_1                                                     (0x5a4)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_SS_STRAP_GENERIC_2                                    (0x305a8)
#ifndef GENERIC_AND_FUSE_REG_SS_STRAP_GENERIC_2
#define GENERIC_AND_FUSE_REG_SS_STRAP_GENERIC_2                                                     (0x5a8)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_SS_STRAP_GENERIC_3                                    (0x305ac)
#ifndef GENERIC_AND_FUSE_REG_SS_STRAP_GENERIC_3
#define GENERIC_AND_FUSE_REG_SS_STRAP_GENERIC_3                                                     (0x5ac)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_REQ                                (0x305c0)
#ifndef GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_REQ
#define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_REQ                                                 (0x5c0)
#define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_REQ_MANUF_DBG_UNLOCK_REQ_LOW                        (0)
#define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_REQ_MANUF_DBG_UNLOCK_REQ_MASK                       (0x1)
#define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_REQ_PROD_DBG_UNLOCK_REQ_LOW                         (1)
#define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_REQ_PROD_DBG_UNLOCK_REQ_MASK                        (0x2)
#define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_REQ_UDS_PROGRAM_REQ_LOW                             (2)
#define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_REQ_UDS_PROGRAM_REQ_MASK                            (0x4)
#define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_REQ_RSVD_LOW                                        (3)
#define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_REQ_RSVD_MASK                                       (0xfffffff8)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_RSP                                (0x305c4)
#ifndef GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_RSP
#define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_RSP                                                 (0x5c4)
#define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_RSP_MANUF_DBG_UNLOCK_SUCCESS_LOW                    (0)
#define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_RSP_MANUF_DBG_UNLOCK_SUCCESS_MASK                   (0x1)
#define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_RSP_MANUF_DBG_UNLOCK_FAIL_LOW                       (1)
#define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_RSP_MANUF_DBG_UNLOCK_FAIL_MASK                      (0x2)
#define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_RSP_MANUF_DBG_UNLOCK_IN_PROGRESS_LOW                (2)
#define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_RSP_MANUF_DBG_UNLOCK_IN_PROGRESS_MASK               (0x4)
#define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_RSP_PROD_DBG_UNLOCK_SUCCESS_LOW                     (3)
#define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_RSP_PROD_DBG_UNLOCK_SUCCESS_MASK                    (0x8)
#define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_RSP_PROD_DBG_UNLOCK_FAIL_LOW                        (4)
#define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_RSP_PROD_DBG_UNLOCK_FAIL_MASK                       (0x10)
#define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_RSP_PROD_DBG_UNLOCK_IN_PROGRESS_LOW                 (5)
#define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_RSP_PROD_DBG_UNLOCK_IN_PROGRESS_MASK                (0x20)
#define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_RSP_UDS_PROGRAM_SUCCESS_LOW                         (6)
#define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_RSP_UDS_PROGRAM_SUCCESS_MASK                        (0x40)
#define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_RSP_UDS_PROGRAM_FAIL_LOW                            (7)
#define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_RSP_UDS_PROGRAM_FAIL_MASK                           (0x80)
#define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_RSP_UDS_PROGRAM_IN_PROGRESS_LOW                     (8)
#define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_RSP_UDS_PROGRAM_IN_PROGRESS_MASK                    (0x100)
#define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_RSP_TAP_MAILBOX_AVAILABLE_LOW                       (9)
#define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_RSP_TAP_MAILBOX_AVAILABLE_MASK                      (0x200)
#define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_RSP_RSVD_LOW                                        (10)
#define GENERIC_AND_FUSE_REG_SS_DBG_SERVICE_REG_RSP_RSVD_MASK                                       (0xfffffc00)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_SS_SOC_DBG_UNLOCK_LEVEL_0                             (0x305c8)
#ifndef GENERIC_AND_FUSE_REG_SS_SOC_DBG_UNLOCK_LEVEL_0
#define GENERIC_AND_FUSE_REG_SS_SOC_DBG_UNLOCK_LEVEL_0                                              (0x5c8)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_SS_SOC_DBG_UNLOCK_LEVEL_1                             (0x305cc)
#ifndef GENERIC_AND_FUSE_REG_SS_SOC_DBG_UNLOCK_LEVEL_1
#define GENERIC_AND_FUSE_REG_SS_SOC_DBG_UNLOCK_LEVEL_1                                              (0x5cc)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_SS_GENERIC_FW_EXEC_CTRL_0                             (0x305d0)
#ifndef GENERIC_AND_FUSE_REG_SS_GENERIC_FW_EXEC_CTRL_0
#define GENERIC_AND_FUSE_REG_SS_GENERIC_FW_EXEC_CTRL_0                                              (0x5d0)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_SS_GENERIC_FW_EXEC_CTRL_1                             (0x305d4)
#ifndef GENERIC_AND_FUSE_REG_SS_GENERIC_FW_EXEC_CTRL_1
#define GENERIC_AND_FUSE_REG_SS_GENERIC_FW_EXEC_CTRL_1                                              (0x5d4)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_SS_GENERIC_FW_EXEC_CTRL_2                             (0x305d8)
#ifndef GENERIC_AND_FUSE_REG_SS_GENERIC_FW_EXEC_CTRL_2
#define GENERIC_AND_FUSE_REG_SS_GENERIC_FW_EXEC_CTRL_2                                              (0x5d8)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_SS_GENERIC_FW_EXEC_CTRL_3                             (0x305dc)
#ifndef GENERIC_AND_FUSE_REG_SS_GENERIC_FW_EXEC_CTRL_3
#define GENERIC_AND_FUSE_REG_SS_GENERIC_FW_EXEC_CTRL_3                                              (0x5dc)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_0                                (0x30c00)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_0
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_0                                                 (0xc00)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_1                                (0x30c04)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_1
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_1                                                 (0xc04)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_2                                (0x30c08)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_2
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_2                                                 (0xc08)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_3                                (0x30c0c)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_3
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_3                                                 (0xc0c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_4                                (0x30c10)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_4
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_4                                                 (0xc10)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_5                                (0x30c14)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_5
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_5                                                 (0xc14)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_6                                (0x30c18)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_6
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_6                                                 (0xc18)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_7                                (0x30c1c)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_7
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_7                                                 (0xc1c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_8                                (0x30c20)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_8
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_8                                                 (0xc20)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_9                                (0x30c24)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_9
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_9                                                 (0xc24)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_10                               (0x30c28)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_10
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_10                                                (0xc28)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_11                               (0x30c2c)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_11
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_11                                                (0xc2c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_12                               (0x30c30)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_12
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_12                                                (0xc30)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_13                               (0x30c34)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_13
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_13                                                (0xc34)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_14                               (0x30c38)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_14
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_14                                                (0xc38)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_15                               (0x30c3c)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_15
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_15                                                (0xc3c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_16                               (0x30c40)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_16
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_16                                                (0xc40)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_17                               (0x30c44)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_17
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_17                                                (0xc44)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_18                               (0x30c48)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_18
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_18                                                (0xc48)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_19                               (0x30c4c)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_19
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_19                                                (0xc4c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_20                               (0x30c50)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_20
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_20                                                (0xc50)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_21                               (0x30c54)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_21
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_21                                                (0xc54)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_22                               (0x30c58)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_22
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_22                                                (0xc58)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_23                               (0x30c5c)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_23
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_23                                                (0xc5c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_24                               (0x30c60)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_24
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_24                                                (0xc60)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_25                               (0x30c64)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_25
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_25                                                (0xc64)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_26                               (0x30c68)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_26
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_26                                                (0xc68)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_27                               (0x30c6c)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_27
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_27                                                (0xc6c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_28                               (0x30c70)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_28
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_28                                                (0xc70)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_29                               (0x30c74)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_29
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_29                                                (0xc74)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_30                               (0x30c78)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_30
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_30                                                (0xc78)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_31                               (0x30c7c)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_31
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_31                                                (0xc7c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_32                               (0x30c80)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_32
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_32                                                (0xc80)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_33                               (0x30c84)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_33
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_33                                                (0xc84)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_34                               (0x30c88)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_34
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_34                                                (0xc88)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_35                               (0x30c8c)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_35
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_35                                                (0xc8c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_36                               (0x30c90)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_36
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_36                                                (0xc90)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_37                               (0x30c94)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_37
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_37                                                (0xc94)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_38                               (0x30c98)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_38
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_38                                                (0xc98)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_39                               (0x30c9c)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_39
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_39                                                (0xc9c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_40                               (0x30ca0)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_40
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_40                                                (0xca0)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_41                               (0x30ca4)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_41
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_41                                                (0xca4)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_42                               (0x30ca8)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_42
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_42                                                (0xca8)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_43                               (0x30cac)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_43
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_43                                                (0xcac)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_44                               (0x30cb0)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_44
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_44                                                (0xcb0)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_45                               (0x30cb4)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_45
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_45                                                (0xcb4)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_46                               (0x30cb8)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_46
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_46                                                (0xcb8)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_47                               (0x30cbc)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_47
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_47                                                (0xcbc)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_48                               (0x30cc0)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_48
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_48                                                (0xcc0)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_49                               (0x30cc4)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_49
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_49                                                (0xcc4)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_50                               (0x30cc8)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_50
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_50                                                (0xcc8)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_51                               (0x30ccc)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_51
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_51                                                (0xccc)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_52                               (0x30cd0)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_52
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_52                                                (0xcd0)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_53                               (0x30cd4)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_53
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_53                                                (0xcd4)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_54                               (0x30cd8)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_54
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_54                                                (0xcd8)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_55                               (0x30cdc)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_55
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_55                                                (0xcdc)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_56                               (0x30ce0)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_56
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_56                                                (0xce0)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_57                               (0x30ce4)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_57
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_57                                                (0xce4)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_58                               (0x30ce8)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_58
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_58                                                (0xce8)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_59                               (0x30cec)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_59
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_59                                                (0xcec)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_60                               (0x30cf0)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_60
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_60                                                (0xcf0)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_61                               (0x30cf4)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_61
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_61                                                (0xcf4)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_62                               (0x30cf8)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_62
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_62                                                (0xcf8)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_63                               (0x30cfc)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_63
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_63                                                (0xcfc)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_64                               (0x30d00)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_64
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_64                                                (0xd00)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_65                               (0x30d04)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_65
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_65                                                (0xd04)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_66                               (0x30d08)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_66
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_66                                                (0xd08)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_67                               (0x30d0c)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_67
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_67                                                (0xd0c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_68                               (0x30d10)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_68
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_68                                                (0xd10)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_69                               (0x30d14)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_69
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_69                                                (0xd14)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_70                               (0x30d18)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_70
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_70                                                (0xd18)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_71                               (0x30d1c)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_71
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_71                                                (0xd1c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_72                               (0x30d20)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_72
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_72                                                (0xd20)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_73                               (0x30d24)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_73
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_73                                                (0xd24)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_74                               (0x30d28)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_74
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_74                                                (0xd28)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_75                               (0x30d2c)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_75
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_75                                                (0xd2c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_76                               (0x30d30)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_76
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_76                                                (0xd30)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_77                               (0x30d34)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_77
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_77                                                (0xd34)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_78                               (0x30d38)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_78
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_78                                                (0xd38)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_79                               (0x30d3c)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_79
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_79                                                (0xd3c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_80                               (0x30d40)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_80
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_80                                                (0xd40)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_81                               (0x30d44)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_81
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_81                                                (0xd44)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_82                               (0x30d48)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_82
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_82                                                (0xd48)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_83                               (0x30d4c)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_83
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_83                                                (0xd4c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_84                               (0x30d50)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_84
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_84                                                (0xd50)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_85                               (0x30d54)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_85
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_85                                                (0xd54)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_86                               (0x30d58)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_86
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_86                                                (0xd58)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_87                               (0x30d5c)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_87
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_87                                                (0xd5c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_88                               (0x30d60)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_88
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_88                                                (0xd60)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_89                               (0x30d64)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_89
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_89                                                (0xd64)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_90                               (0x30d68)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_90
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_90                                                (0xd68)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_91                               (0x30d6c)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_91
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_91                                                (0xd6c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_92                               (0x30d70)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_92
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_92                                                (0xd70)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_93                               (0x30d74)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_93
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_93                                                (0xd74)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_94                               (0x30d78)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_94
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_94                                                (0xd78)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_95                               (0x30d7c)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_95
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_95                                                (0xd7c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_96                               (0x30d80)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_96
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_96                                                (0xd80)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_97                               (0x30d84)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_97
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_97                                                (0xd84)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_98                               (0x30d88)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_98
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_98                                                (0xd88)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_99                               (0x30d8c)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_99
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_99                                                (0xd8c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_100                              (0x30d90)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_100
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_100                                               (0xd90)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_101                              (0x30d94)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_101
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_101                                               (0xd94)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_102                              (0x30d98)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_102
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_102                                               (0xd98)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_103                              (0x30d9c)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_103
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_103                                               (0xd9c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_104                              (0x30da0)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_104
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_104                                               (0xda0)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_105                              (0x30da4)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_105
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_105                                               (0xda4)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_106                              (0x30da8)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_106
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_106                                               (0xda8)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_107                              (0x30dac)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_107
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_107                                               (0xdac)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_108                              (0x30db0)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_108
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_108                                               (0xdb0)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_109                              (0x30db4)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_109
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_109                                               (0xdb4)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_110                              (0x30db8)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_110
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_110                                               (0xdb8)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_111                              (0x30dbc)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_111
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_111                                               (0xdbc)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_112                              (0x30dc0)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_112
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_112                                               (0xdc0)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_113                              (0x30dc4)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_113
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_113                                               (0xdc4)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_114                              (0x30dc8)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_114
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_114                                               (0xdc8)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_115                              (0x30dcc)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_115
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_115                                               (0xdcc)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_116                              (0x30dd0)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_116
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_116                                               (0xdd0)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_117                              (0x30dd4)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_117
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_117                                               (0xdd4)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_118                              (0x30dd8)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_118
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_118                                               (0xdd8)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_119                              (0x30ddc)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_119
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_119                                               (0xddc)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_120                              (0x30de0)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_120
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_120                                               (0xde0)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_121                              (0x30de4)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_121
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_121                                               (0xde4)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_122                              (0x30de8)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_122
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_122                                               (0xde8)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_123                              (0x30dec)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_123
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_123                                               (0xdec)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_124                              (0x30df0)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_124
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_124                                               (0xdf0)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_125                              (0x30df4)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_125
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_125                                               (0xdf4)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_126                              (0x30df8)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_126
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_126                                               (0xdf8)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_127                              (0x30dfc)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_127
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_127                                               (0xdfc)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_128                              (0x30e00)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_128
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_128                                               (0xe00)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_129                              (0x30e04)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_129
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_129                                               (0xe04)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_130                              (0x30e08)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_130
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_130                                               (0xe08)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_131                              (0x30e0c)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_131
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_131                                               (0xe0c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_132                              (0x30e10)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_132
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_132                                               (0xe10)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_133                              (0x30e14)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_133
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_133                                               (0xe14)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_134                              (0x30e18)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_134
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_134                                               (0xe18)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_135                              (0x30e1c)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_135
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_135                                               (0xe1c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_136                              (0x30e20)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_136
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_136                                               (0xe20)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_137                              (0x30e24)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_137
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_137                                               (0xe24)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_138                              (0x30e28)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_138
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_138                                               (0xe28)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_139                              (0x30e2c)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_139
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_139                                               (0xe2c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_140                              (0x30e30)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_140
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_140                                               (0xe30)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_141                              (0x30e34)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_141
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_141                                               (0xe34)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_142                              (0x30e38)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_142
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_142                                               (0xe38)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_143                              (0x30e3c)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_143
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_143                                               (0xe3c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_144                              (0x30e40)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_144
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_144                                               (0xe40)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_145                              (0x30e44)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_145
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_145                                               (0xe44)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_146                              (0x30e48)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_146
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_146                                               (0xe48)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_147                              (0x30e4c)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_147
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_147                                               (0xe4c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_148                              (0x30e50)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_148
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_148                                               (0xe50)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_149                              (0x30e54)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_149
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_149                                               (0xe54)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_150                              (0x30e58)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_150
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_150                                               (0xe58)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_151                              (0x30e5c)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_151
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_151                                               (0xe5c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_152                              (0x30e60)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_152
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_152                                               (0xe60)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_153                              (0x30e64)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_153
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_153                                               (0xe64)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_154                              (0x30e68)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_154
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_154                                               (0xe68)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_155                              (0x30e6c)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_155
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_155                                               (0xe6c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_156                              (0x30e70)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_156
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_156                                               (0xe70)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_157                              (0x30e74)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_157
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_157                                               (0xe74)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_158                              (0x30e78)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_158
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_158                                               (0xe78)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_159                              (0x30e7c)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_159
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_159                                               (0xe7c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_160                              (0x30e80)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_160
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_160                                               (0xe80)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_161                              (0x30e84)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_161
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_161                                               (0xe84)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_162                              (0x30e88)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_162
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_162                                               (0xe88)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_163                              (0x30e8c)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_163
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_163                                               (0xe8c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_164                              (0x30e90)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_164
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_164                                               (0xe90)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_165                              (0x30e94)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_165
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_165                                               (0xe94)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_166                              (0x30e98)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_166
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_166                                               (0xe98)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_167                              (0x30e9c)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_167
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_167                                               (0xe9c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_168                              (0x30ea0)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_168
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_168                                               (0xea0)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_169                              (0x30ea4)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_169
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_169                                               (0xea4)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_170                              (0x30ea8)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_170
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_170                                               (0xea8)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_171                              (0x30eac)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_171
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_171                                               (0xeac)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_172                              (0x30eb0)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_172
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_172                                               (0xeb0)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_173                              (0x30eb4)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_173
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_173                                               (0xeb4)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_174                              (0x30eb8)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_174
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_174                                               (0xeb8)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_175                              (0x30ebc)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_175
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_175                                               (0xebc)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_176                              (0x30ec0)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_176
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_176                                               (0xec0)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_177                              (0x30ec4)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_177
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_177                                               (0xec4)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_178                              (0x30ec8)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_178
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_178                                               (0xec8)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_179                              (0x30ecc)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_179
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_179                                               (0xecc)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_180                              (0x30ed0)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_180
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_180                                               (0xed0)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_181                              (0x30ed4)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_181
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_181                                               (0xed4)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_182                              (0x30ed8)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_182
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_182                                               (0xed8)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_183                              (0x30edc)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_183
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_183                                               (0xedc)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_184                              (0x30ee0)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_184
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_184                                               (0xee0)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_185                              (0x30ee4)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_185
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_185                                               (0xee4)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_186                              (0x30ee8)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_186
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_186                                               (0xee8)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_187                              (0x30eec)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_187
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_187                                               (0xeec)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_188                              (0x30ef0)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_188
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_188                                               (0xef0)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_189                              (0x30ef4)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_189
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_189                                               (0xef4)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_190                              (0x30ef8)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_190
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_190                                               (0xef8)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_191                              (0x30efc)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_191
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_191                                               (0xefc)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_192                              (0x30f00)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_192
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_192                                               (0xf00)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_193                              (0x30f04)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_193
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_193                                               (0xf04)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_194                              (0x30f08)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_194
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_194                                               (0xf08)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_195                              (0x30f0c)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_195
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_195                                               (0xf0c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_196                              (0x30f10)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_196
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_196                                               (0xf10)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_197                              (0x30f14)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_197
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_197                                               (0xf14)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_198                              (0x30f18)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_198
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_198                                               (0xf18)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_199                              (0x30f1c)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_199
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_199                                               (0xf1c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_200                              (0x30f20)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_200
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_200                                               (0xf20)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_201                              (0x30f24)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_201
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_201                                               (0xf24)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_202                              (0x30f28)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_202
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_202                                               (0xf28)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_203                              (0x30f2c)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_203
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_203                                               (0xf2c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_204                              (0x30f30)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_204
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_204                                               (0xf30)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_205                              (0x30f34)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_205
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_205                                               (0xf34)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_206                              (0x30f38)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_206
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_206                                               (0xf38)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_207                              (0x30f3c)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_207
#define GENERIC_AND_FUSE_REG_STASH_BANK_SLOT_DATA_207                                               (0xf3c)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_SOC_LOCK                                   (0x30f40)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_SOC_LOCK
#define GENERIC_AND_FUSE_REG_STASH_BANK_SOC_LOCK                                                    (0xf40)
#define GENERIC_AND_FUSE_REG_STASH_BANK_SOC_LOCK_LOCK_LOW                                           (0)
#define GENERIC_AND_FUSE_REG_STASH_BANK_SOC_LOCK_LOCK_MASK                                          (0xff)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_END_STASH                                       (0x30f44)
#ifndef GENERIC_AND_FUSE_REG_STASH_END_STASH
#define GENERIC_AND_FUSE_REG_STASH_END_STASH                                                        (0xf44)
#define GENERIC_AND_FUSE_REG_STASH_END_STASH_END_STASH_LOW                                          (0)
#define GENERIC_AND_FUSE_REG_STASH_END_STASH_END_STASH_MASK                                         (0x1)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_CPTRA_LOCK                                 (0x30f48)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_CPTRA_LOCK
#define GENERIC_AND_FUSE_REG_STASH_BANK_CPTRA_LOCK                                                  (0xf48)
#define GENERIC_AND_FUSE_REG_STASH_BANK_CPTRA_LOCK_CPTRA_LOCK_LOW                                   (0)
#define GENERIC_AND_FUSE_REG_STASH_BANK_CPTRA_LOCK_CPTRA_LOCK_MASK                                  (0x1)
#endif
#define CALIPTRA_TOP_REG_GENERIC_AND_FUSE_REG_STASH_BANK_STATUS                                     (0x30f4c)
#ifndef GENERIC_AND_FUSE_REG_STASH_BANK_STATUS
#define GENERIC_AND_FUSE_REG_STASH_BANK_STATUS                                                      (0xf4c)
#define GENERIC_AND_FUSE_REG_STASH_BANK_STATUS_SLOT_LOCKED_LOW                                      (0)
#define GENERIC_AND_FUSE_REG_STASH_BANK_STATUS_SLOT_LOCKED_MASK                                     (0xff)
#define GENERIC_AND_FUSE_REG_STASH_BANK_STATUS_END_STASH_LOW                                        (8)
#define GENERIC_AND_FUSE_REG_STASH_BANK_STATUS_END_STASH_MASK                                       (0x100)
#define GENERIC_AND_FUSE_REG_STASH_BANK_STATUS_CPTRA_LOCK_LOW                                       (9)
#define GENERIC_AND_FUSE_REG_STASH_BANK_STATUS_CPTRA_LOCK_MASK                                      (0x200)
#endif


#endif