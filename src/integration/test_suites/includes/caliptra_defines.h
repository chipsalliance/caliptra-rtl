/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
// Separating these defines from 'defines.h' since that file is auto-generated
// when building the SweRV EL2 from the configuration script, and clobbers
// these manual additions.

#ifndef CALIPTRA_DEFINES_H
  #define CALIPTRA_DEFINES_H

#include "defines.h"


/* ---- Key Vault ---- */
#define KV_BASE_ADDR              0x10018000
#define KV_KEY_CTRL_ADDR          0x10018200
#define KV_PCR_CTRL_ADDR          0x10018220

#define KV_NUM_PCR                0x00000008
#define KV_NUM_DWORDS             0x00000010


/* ---- AES ---- */
#define AES_ADDR_NAME0            0x10000000
#define AES_ADDR_NAME1            0x10000004
#define AES_ADDR_VER0             0x10000008
#define AES_ADDR_VER1             0x1000000c
#define AES_ADDR_CNTRL            0x10000010
#define AES_ADDR_STATUS           0x10000018
#define AES_ADDR_KEY_START        0x10000040
#define AES_ADDR_KEY_END          0x1000005f
#define AES_ADDR_BLOCK_START      0x10000080
#define AES_ADDR_BLOCK_END        0x1000008f
#define AES_ADDR_RESULT_START     0x10000100
#define AES_ADDR_RESULT_END       0x1000010f
#define AES_ADDR_CONFIG           0x10000020
#define AES_ADDR_IV_START         0x10000110
#define AES_ADDR_IV_END           0x1000011f
#define AES_ADDR_KV_CTRL          0x10000200

#define AES_INIT                  0x0000000D
#define AES_NEXT                  0x0000000E
#define AES_VALID                 0x00000003


/* ---- HMAC ---- */
#define HMAC_ADDR_NAME            0x10010000
#define HMAC_ADDR_VER             0x10010008
#define HMAC_ADDR_CNTRL           0x10010010
#define HMAC_ADDR_STATUS          0x10010018
#define HMAC_ADDR_KEY_START       0x10010040
#define HMAC_ADDR_KEY_END         0x1001006c
#define HMAC_ADDR_BLOCK_START     0x10010080
#define HMAC_ADDR_BLOCK_END       0x100100fc
#define HMAC_ADDR_TAG_START       0x10010100
#define HMAC_ADDR_TAG_END         0x1001012c
#define HMAC_ADDR_KV_CTRL         0x10010200

#define HMAC_INIT                 0x0000000D
#define HMAC_NEXT                 0x0000000E
#define HMAC_VALID                0x00000003

#define HMAC_KEY_NUM_DWORDS       0x0000000C


/* ---- SHA512 ---- */
#define SHA512_ADDR_NAME            0x10020000
#define SHA512_ADDR_VER             0x10020008
#define SHA512_ADDR_CNTRL           0x10020010
#define SHA512_ADDR_STATUS          0x10020018
#define SHA512_ADDR_BLOCK_START     0x10020080
#define SHA512_ADDR_BLOCK_END       0x100200ff
#define SHA512_ADDR_DIGEST_START    0x10020100
#define SHA512_ADDR_DIGEST_END      0x1002013f

#define SHA512_INIT                 0x0000000D
#define SHA512_NEXT                 0x0000000E
#define SHA512_VALID                0x00000003


/* ---- Mailbox ---- */
#define MBOX_REG_BASE             0x30030000
#define MBOX_FLOW_STATUS          (MBOX_REG_BASE + 0x1c)
#define MBOX_CLEAR_SECRETS        (MBOX_REG_BASE + 0x20)
#define STDOUT                    (MBOX_REG_BASE + 0x2c)

#define MBOX_ADDR_BASE            0x30020000
#define MBOX_ADDR_LOCK            (MBOX_ADDR_BASE + 0x00)
#define MBOX_ADDR_CMD             (MBOX_ADDR_BASE + 0x08)
#define MBOX_ADDR_DLEN            (MBOX_ADDR_BASE + 0x0C)
#define MBOX_ADDR_DATAIN          (MBOX_ADDR_BASE + 0x10)
#define MBOX_ADDR_DATAOUT         (MBOX_ADDR_BASE + 0x14)
#define MBOX_ADDR_EXECUTE         (MBOX_ADDR_BASE + 0x18)

#define MBOX_DLEN_VAL             0x0000001C

/* ---- ECC ----*/
#define ECC_BASE_ADDR             0x10008000
#define ECC_ADDR_NAME0            0x10008000
#define ECC_ADDR_NAME1            0x10008004
#define ECC_ADDR_VERSION0         0x10008008
#define ECC_ADDR_VERSION1         0x1000800C
#define ECC_ADDR_CTRL             0x10008010
#define ECC_CMD_KEYGEN            0x1
#define ECC_CMD_KEYSIGN           0x2
#define ECC_CMD_KEYVERIFY         0x3
#define ECC_ADDR_STATUS           0x10008018
#define STATUS_READY_BIT          0x0
#define STATUS_VALID_BIT          0x1
#define ECC_ADDR_SEED0            0x10008080
#define ECC_ADDR_SEED11           0x100080AC
#define ECC_ADDR_MSG0             0x10008100
#define ECC_ADDR_MSG11            0x1000812C
#define ECC_ADDR_PRIVKEY0         0x10008180
#define ECC_ADDR_PRIVKEY11        0x100081AC
#define ECC_ADDR_PUBKEYX0         0x10008200
#define ECC_ADDR_PUBKEYX11        0x1000822C
#define ECC_ADDR_PUBKEYY0         0x10008280
#define AECC_DDR_PUBKEYY11        0x100082AC
#define ECC_ADDR_SIGNR0           0x10008300
#define ECC_ADDR_SIGNR11          0x1000832C
#define ECC_ADDR_SIGNS0           0x10008380
#define ECC_ADDR_SIGNS11          0x100083AC
#define ECC_ADDR_VERIFYR0         0x10008400
#define ECC_ADDR_VERIFYR11        0x1000842C
#define ECC_ADDR_IV0              0x10008480
#define ECC_ADDR_IV11             0x100084AC





/* ---- Interrupts ---- */
#define SWERV_INTR_VEC_AES_ERROR    1
#define SWERV_INTR_VEC_AES_NOTIF    2
#define SWERV_INTR_VEC_ECC_ERROR    3
#define SWERV_INTR_VEC_ECC_NOTIF    4
#define SWERV_INTR_VEC_HMAC_ERROR   5
#define SWERV_INTR_VEC_HMAC_NOTIF   6
#define SWERV_INTR_VEC_KV_ERROR     7
#define SWERV_INTR_VEC_KV_NOTIF     8
#define SWERV_INTR_VEC_SHA512_ERROR 9
#define SWERV_INTR_VEC_SHA512_NOTIF 10
#define SWERV_INTR_VEC_SHA256_ERROR 11
#define SWERV_INTR_VEC_SHA256_NOTIF 12
#define SWERV_INTR_VEC_QSPI_ERROR   13
#define SWERV_INTR_VEC_QSPI_NOTIF   14
#define SWERV_INTR_VEC_UART_ERROR   15
#define SWERV_INTR_VEC_UART_NOTIF   16
#define SWERV_INTR_VEC_I3C_ERROR    17
#define SWERV_INTR_VEC_I3C_NOTIF    18
#define SWERV_INTR_VEC_MBOX_ERROR   19
#define SWERV_INTR_VEC_MBOX_NOTIF   20
// Used to tie-off unused upper intr bits
#define SWERV_INTR_VEC_MAX_ASSIGNED SWERV_INTR_VEC_MBOX_NOTIF

#define SWERV_INTR_PRIO_AES_ERROR    8
#define SWERV_INTR_PRIO_AES_NOTIF    7
#define SWERV_INTR_PRIO_ECC_ERROR    8
#define SWERV_INTR_PRIO_ECC_NOTIF    7
#define SWERV_INTR_PRIO_HMAC_ERROR   8
#define SWERV_INTR_PRIO_HMAC_NOTIF   7
#define SWERV_INTR_PRIO_KV_ERROR     8
#define SWERV_INTR_PRIO_KV_NOTIF     7
#define SWERV_INTR_PRIO_SHA512_ERROR 8
#define SWERV_INTR_PRIO_SHA512_NOTIF 7
#define SWERV_INTR_PRIO_SHA256_ERROR 8
#define SWERV_INTR_PRIO_SHA256_NOTIF 7
#define SWERV_INTR_PRIO_QSPI_ERROR   4
#define SWERV_INTR_PRIO_QSPI_NOTIF   3
#define SWERV_INTR_PRIO_UART_ERROR   4
#define SWERV_INTR_PRIO_UART_NOTIF   3
#define SWERV_INTR_PRIO_I3C_ERROR    4
#define SWERV_INTR_PRIO_I3C_NOTIF    3
#define SWERV_INTR_PRIO_MBOX_ERROR   8
#define SWERV_INTR_PRIO_MBOX_NOTIF   7


#endif // CALIPTRA_DEFINES_H
