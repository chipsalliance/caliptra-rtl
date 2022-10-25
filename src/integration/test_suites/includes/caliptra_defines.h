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
#include "caliptra_reg.h"


/* ---- Key Vault ---- */
#define KV_BASE_ADDR              0x10018000
#define KV_KEY_CTRL_ADDR          0x10018200
#define KV_PCR_CTRL_ADDR          0x10018220

#define KV_NUM_PCR                0x00000008
#define KV_NUM_DWORDS             0x00000010


/* ---- AES ---- */
#define AES_BASE_ADDR             0x10000000
#define AES_ADDR_NAME0            (AES_BASE_ADDR + 0x0000)
#define AES_ADDR_NAME1            (AES_BASE_ADDR + 0x0004)
#define AES_ADDR_VER0             (AES_BASE_ADDR + 0x0008)
#define AES_ADDR_VER1             (AES_BASE_ADDR + 0x000c)
#define AES_ADDR_CNTRL            (AES_BASE_ADDR + 0x0010)
#define AES_ADDR_STATUS           (AES_BASE_ADDR + 0x0018)
#define AES_ADDR_KEY_START        (AES_BASE_ADDR + 0x0040)
#define AES_ADDR_KEY_END          (AES_BASE_ADDR + 0x005f)
#define AES_ADDR_BLOCK_START      (AES_BASE_ADDR + 0x0080)
#define AES_ADDR_BLOCK_END        (AES_BASE_ADDR + 0x008f)
#define AES_ADDR_RESULT_START     (AES_BASE_ADDR + 0x0100)
#define AES_ADDR_RESULT_END       (AES_BASE_ADDR + 0x010f)
#define AES_ADDR_CONFIG           (AES_BASE_ADDR + 0x0020)
#define AES_ADDR_IV_START         (AES_BASE_ADDR + 0x0110)
#define AES_ADDR_IV_END           (AES_BASE_ADDR + 0x011f)
#define AES_ADDR_KV_CTRL          (AES_BASE_ADDR + 0x0200)
#define AES_ADDR_INTR_START       (AES_BASE_ADDR + 0x0800)

#define AES_INIT                  0x0000000D
#define AES_NEXT                  0x0000000E
#define AES_VALID                 0x00000003


/* ---- HMAC ---- */
#define HMAC_BASE_ADDR            0x10010000
#define HMAC_ADDR_NAME            (HMAC_BASE_ADDR + 0x0000)
#define HMAC_ADDR_VER             (HMAC_BASE_ADDR + 0x0008)
#define HMAC_ADDR_CNTRL           (HMAC_BASE_ADDR + 0x0010)
#define HMAC_ADDR_STATUS          (HMAC_BASE_ADDR + 0x0018)
#define HMAC_ADDR_KEY_START       (HMAC_BASE_ADDR + 0x0040)
#define HMAC_ADDR_KEY_END         (HMAC_BASE_ADDR + 0x006c)
#define HMAC_ADDR_BLOCK_START     (HMAC_BASE_ADDR + 0x0080)
#define HMAC_ADDR_BLOCK_END       (HMAC_BASE_ADDR + 0x00fc)
#define HMAC_ADDR_TAG_START       (HMAC_BASE_ADDR + 0x0100)
#define HMAC_ADDR_TAG_END         (HMAC_BASE_ADDR + 0x012c)
#define HMAC_ADDR_KV_CTRL         (HMAC_BASE_ADDR + 0x0200)
#define HMAC_ADDR_INTR_START      (HMAC_BASE_ADDR + 0x0800)

#define HMAC_INIT                 0x0000000D
#define HMAC_NEXT                 0x0000000E
#define HMAC_VALID                0x00000003

#define HMAC_KEY_NUM_DWORDS       0x0000000C


/* ---- SHA512 ---- */
#define SHA512_BASE_ADDR            0x10020000
#define SHA512_ADDR_NAME            (SHA512_BASE_ADDR + 0x0000)
#define SHA512_ADDR_VER             (SHA512_BASE_ADDR + 0x0008)
#define SHA512_ADDR_CNTRL           (SHA512_BASE_ADDR + 0x0010)
#define SHA512_ADDR_STATUS          (SHA512_BASE_ADDR + 0x0018)
#define SHA512_ADDR_BLOCK_START     (SHA512_BASE_ADDR + 0x0080)
#define SHA512_ADDR_BLOCK_END       (SHA512_BASE_ADDR + 0x00ff)
#define SHA512_ADDR_DIGEST_START    (SHA512_BASE_ADDR + 0x0100)
#define SHA512_ADDR_DIGEST_END      (SHA512_BASE_ADDR + 0x013f)
#define SHA512_ADDR_INTR_START      (SHA512_BASE_ADDR + 0x0800)

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
#define ECC_ADDR_NAME0            (ECC_BASE_ADDR + ECC_REG_ECC_NAME_0   )
#define ECC_ADDR_NAME1            (ECC_BASE_ADDR + ECC_REG_ECC_NAME_1   )
#define ECC_ADDR_VERSION0         (ECC_BASE_ADDR + ECC_REG_ECC_VERSION_0)
#define ECC_ADDR_VERSION1         (ECC_BASE_ADDR + ECC_REG_ECC_VERSION_1)
#define ECC_ADDR_CTRL             (ECC_BASE_ADDR + ECC_REG_ECC_CTRL     )
#define ECC_CMD_KEYGEN            0x1
#define ECC_CMD_KEYSIGN           0x2
#define ECC_CMD_KEYVERIFY         0x3
#define ECC_ADDR_STATUS           (ECC_BASE_ADDR + ECC_REG_ECC_STATUS)
#define STATUS_READY_BIT          0x0
#define STATUS_VALID_BIT          0x1
#define ECC_ADDR_SEED0            (ECC_BASE_ADDR + 0x080)
#define ECC_ADDR_SEED11           (ECC_BASE_ADDR + 0x0AC)
#define ECC_ADDR_MSG0             (ECC_BASE_ADDR + 0x100)
#define ECC_ADDR_MSG11            (ECC_BASE_ADDR + 0x12C)
#define ECC_ADDR_PRIVKEY0         (ECC_BASE_ADDR + 0x180)
#define ECC_ADDR_PRIVKEY11        (ECC_BASE_ADDR + 0x1AC)
#define ECC_ADDR_PUBKEYX0         (ECC_BASE_ADDR + 0x200)
#define ECC_ADDR_PUBKEYX11        (ECC_BASE_ADDR + 0x22C)
#define ECC_ADDR_PUBKEYY0         (ECC_BASE_ADDR + 0x280)
#define AECC_DDR_PUBKEYY11        (ECC_BASE_ADDR + 0x2AC)
#define ECC_ADDR_SIGNR0           (ECC_BASE_ADDR + 0x300)
#define ECC_ADDR_SIGNR11          (ECC_BASE_ADDR + 0x32C)
#define ECC_ADDR_SIGNS0           (ECC_BASE_ADDR + 0x380)
#define ECC_ADDR_SIGNS11          (ECC_BASE_ADDR + 0x3AC)
#define ECC_ADDR_VERIFYR0         (ECC_BASE_ADDR + 0x400)
#define ECC_ADDR_VERIFYR11        (ECC_BASE_ADDR + 0x42C)
#define ECC_ADDR_IV0              (ECC_BASE_ADDR + 0x480)
#define ECC_ADDR_IV11             (ECC_BASE_ADDR + 0x4AC)





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
