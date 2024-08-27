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
// when building the VeeR EL2 from the configuration script, and clobbers
// these manual additions.

#ifndef CALIPTRA_DEFINES_H
  #define CALIPTRA_DEFINES_H

#include "defines.h"
#include "caliptra_reg.h"


/* ---- Key Vault ---- */

#define KV_NUM_PCR                0x00000008
#define KV_NUM_DWORDS             0x00000010


/* ---- DOE ---- */

#define DOE_INIT                  0x0000000D
#define DOE_NEXT                  0x0000000E
#define DOE_VALID                 0x00000003


/* ---- HMAC ---- */
#define HMAC_BASE_ADDR            CLP_HMAC_REG_BASE_ADDR

#define HMAC_INIT                 0x00000001
#define HMAC_NEXT                 0x00000002
#define HMAC_ZEROIZ               0x00000004
#define HMAC_VALID                0x00000003

#define HMAC_KEY_NUM_DWORDS       0x0000000C


/* ---- SHA512 ---- */

#define SHA512_INIT                 0x0000000D
#define SHA512_NEXT                 0x0000000E
#define SHA512_VALID                0x00000003
#define MODE_SHA_512_224            0x0
#define MODE_SHA_512_256            0x1
#define MODE_SHA_384                0x2
#define MODE_SHA_512                0x3


/* ---- SHA256 ---- */

#define SHA256_INIT                 (SHA256_REG_SHA256_CTRL_INIT_MASK | SHA256_REG_SHA256_CTRL_MODE_MASK)
#define SHA256_NEXT                 (SHA256_REG_SHA256_CTRL_NEXT_MASK | SHA256_REG_SHA256_CTRL_MODE_MASK)
#define SHA256_VALID                (SHA256_REG_SHA256_STATUS_READY_MASK | SHA256_REG_SHA256_STATUS_VALID_MASK)
#define SHA256_MODE_SHA_224         0x0
#define SHA256_MODE_SHA_256         0x1

/* ---- Mailbox ---- */
#define MBOX_DIR_BASE_ADDR        0x30000000
#define MBOX_DIR_SPAN             0x00020000 /* 128 KiB */
#define STDOUT                    CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0

/* ---- ECC ----*/
#define ECC_CMD_KEYGEN            0x1
#define ECC_CMD_SIGNING           0x2
#define ECC_CMD_VERIFYING         0x3
#define ECC_CMD_SHAREDKEY         0x4
#define STATUS_READY_BIT          0x0
#define STATUS_VALID_BIT          0x1

/* ---- Interrupts ---- */
#define VEER_INTR_VEC_DOE_ERROR        1
#define VEER_INTR_VEC_DOE_NOTIF        2
#define VEER_INTR_VEC_ECC_ERROR        3
#define VEER_INTR_VEC_ECC_NOTIF        4
#define VEER_INTR_VEC_HMAC_ERROR       5
#define VEER_INTR_VEC_HMAC_NOTIF       6
#define VEER_INTR_VEC_KV_ERROR         7
#define VEER_INTR_VEC_KV_NOTIF         8
#define VEER_INTR_VEC_SHA512_ERROR     9
#define VEER_INTR_VEC_SHA512_NOTIF     10
#define VEER_INTR_VEC_SHA256_ERROR     11
#define VEER_INTR_VEC_SHA256_NOTIF     12
#define VEER_INTR_VEC_QSPI_ERROR       13
#define VEER_INTR_VEC_QSPI_NOTIF       14
#define VEER_INTR_VEC_UART_ERROR       15
#define VEER_INTR_VEC_UART_NOTIF       16
#define VEER_INTR_VEC_I3C_ERROR        17
#define VEER_INTR_VEC_I3C_NOTIF        18
#define VEER_INTR_VEC_SOC_IFC_ERROR    19
#define VEER_INTR_VEC_SOC_IFC_NOTIF    20
#define VEER_INTR_VEC_SHA512_ACC_ERROR 21
#define VEER_INTR_VEC_SHA512_ACC_NOTIF 22
// Used to tie-off unused upper intr bits
#define VEER_INTR_VEC_MAX_ASSIGNED VEER_INTR_VEC_SHA512_ACC_NOTIF

#define VEER_INTR_PRIO_DOE_ERROR        8
#define VEER_INTR_PRIO_DOE_NOTIF        7
#define VEER_INTR_PRIO_ECC_ERROR        8
#define VEER_INTR_PRIO_ECC_NOTIF        7
#define VEER_INTR_PRIO_HMAC_ERROR       8
#define VEER_INTR_PRIO_HMAC_NOTIF       7
#define VEER_INTR_PRIO_KV_ERROR         8
#define VEER_INTR_PRIO_KV_NOTIF         7
#define VEER_INTR_PRIO_SHA512_ERROR     8
#define VEER_INTR_PRIO_SHA512_NOTIF     7
#define VEER_INTR_PRIO_SHA256_ERROR     8
#define VEER_INTR_PRIO_SHA256_NOTIF     7
#define VEER_INTR_PRIO_SHA512_ACC_ERROR 8
#define VEER_INTR_PRIO_SHA512_ACC_NOTIF 7
#define VEER_INTR_PRIO_QSPI_ERROR       4
#define VEER_INTR_PRIO_QSPI_NOTIF       3
#define VEER_INTR_PRIO_UART_ERROR       4
#define VEER_INTR_PRIO_UART_NOTIF       3
#define VEER_INTR_PRIO_I3C_ERROR        4
#define VEER_INTR_PRIO_I3C_NOTIF        3
#define VEER_INTR_PRIO_SOC_IFC_ERROR    8
#define VEER_INTR_PRIO_SOC_IFC_NOTIF    7


#endif // CALIPTRA_DEFINES_H
