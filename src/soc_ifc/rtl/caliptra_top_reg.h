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
#define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_FATAL_DCLS_ERROR_LOW                                    (4)
#define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_FATAL_DCLS_ERROR_MASK                                   (0x10)
#define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_FATAL_RSVD_LOW                                          (5)
#define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_FATAL_RSVD_MASK                                         (0xffffffe0)
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
#define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_NON_FATAL_RSVD_LOW                                      (3)
#define GENERIC_AND_FUSE_REG_CPTRA_HW_ERROR_NON_FATAL_RSVD_MASK                                     (0xfffffff8)
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


#endif