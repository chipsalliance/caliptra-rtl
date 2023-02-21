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
// ---------------------------------------------------------------------
// File: caliptra_isr.h
// Description:
//     Provides function declarations for use by external test files, so
//     that the ISR functionality may behave like a library.
//     TODO:
//     This header file includes inline function definitions for event and
//     test specific interrupt service behavior, so it should be copied and
//     modified for each test.
// ---------------------------------------------------------------------

#ifndef CALIPTRA_ISR_H
    #define CALIPTRA_ISR_H

#define EN_ISR_PRINTS 0

#include "caliptra_reg.h"
#include <stdint.h>
#include "printf.h"

//////////////////////////////////////////////////////////////////////////////
// Function Declarations
//

// Performs all the CSR setup to configure and enable vectored external interrupts
void init_interrupts(void);

// These inline functions are used to insert event-specific functionality into the
// otherwise generic ISR that gets laid down by the parameterized macro "nonstd_veer_isr"
inline void service_doe_error_intr() {return;}
inline void service_doe_notif_intr() {
    uint32_t * reg = (uint32_t *) (CLP_DOE_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R);
    uint32_t sts = *reg;
    /* Write 1 to Clear the pending interrupt */
    if (sts & DOE_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK) {
        *reg = DOE_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK;
    }
    if (sts == 0) {
        printf("bad doe_notif_intr sts:%x\n", sts);
        printf("%c", 0x1);
    }
}

inline void service_ecc_error_intr() {return;}
inline void service_ecc_notif_intr() {
    uint32_t * reg = (uint32_t *) (CLP_ECC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R);
    uint32_t sts = *reg;
    /* Write 1 to Clear the pending interrupt */
    if (sts & ECC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK) {
        *reg = ECC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK;
    }
    if (sts == 0) {
        printf("bad ecc_notif_intr sts:%x\n", sts);
        printf("%c", 0x1);
    }
}

inline void service_hmac_error_intr() {return;}
inline void service_hmac_notif_intr() {
    uint32_t * reg = (uint32_t *) (CLP_HMAC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R);
    uint32_t sts = *reg;
    /* Write 1 to Clear the pending interrupt */
    if (sts & HMAC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK) {
        *reg = HMAC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK;
    }
    if (sts == 0) {
        printf("bad hmac_notif_intr sts:%x\n", sts);
        printf("%c", 0x1);
    }
}

inline void service_kv_error_intr() {return;}
inline void service_kv_notif_intr() {return;}
inline void service_sha512_error_intr() {return;}
inline void service_sha512_notif_intr() {
    uint32_t * reg = (uint32_t *) (CLP_SHA512_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R);
    uint32_t sts = *reg;
    /* Write 1 to Clear the pending interrupt */
    if (sts & SHA512_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK) {
        *reg = SHA512_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK;
    }
    if (sts == 0) {
        printf("bad sha512_notif_intr sts:%x\n", sts);
        printf("%c", 0x1);
    }
}

inline void service_sha256_error_intr() {return;}
inline void service_sha256_notif_intr() {
    uint32_t * reg = (uint32_t *) (CLP_SHA256_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R);
    uint32_t sts = *reg;
    /* Write 1 to Clear the pending interrupt */
    if (sts & SHA256_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK) {
        *reg = SHA256_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK;
    }
    if (sts == 0) {
        printf("bad sha256_notif_intr sts:%x\n", sts);
        printf("%c", 0x1);
    }
}

inline void service_qspi_error_intr() {return;}
inline void service_qspi_notif_intr() {return;}
inline void service_uart_error_intr() {return;}
inline void service_uart_notif_intr() {return;}
inline void service_i3c_error_intr() {return;}
inline void service_i3c_notif_intr() {return;}
inline void service_soc_ifc_error_intr() {
    uint32_t * reg = (uint32_t *) (CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R);
    uint32_t sts = *reg;
    /* Write 1 to Clear the pending interrupt */
    if (sts & SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_INTERNAL_STS_MASK) {
        *reg = SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_INTERNAL_STS_MASK;
    }
    if (sts & SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_INV_DEV_STS_MASK) {
        *reg = SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_INV_DEV_STS_MASK;
    }
    if (sts & SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_CMD_FAIL_STS_MASK) {
        *reg = SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_CMD_FAIL_STS_MASK;
    }
    if (sts & SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_BAD_FUSE_STS_MASK) {
        *reg = SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_BAD_FUSE_STS_MASK;
    }
    if (sts & SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_ICCM_BLOCKED_STS_MASK) {
        *reg = SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_ICCM_BLOCKED_STS_MASK;
    }
    if (sts & SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_MBOX_ECC_UNC_STS_MASK) {
        *reg = SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_MBOX_ECC_UNC_STS_MASK;
    }
    if (sts == 0) {
        printf("bad soc_ifc_error_intr sts:%x\n", sts);
        printf("%c", 0x1);
    }
}

inline void service_soc_ifc_notif_intr () {
    uint32_t * reg = (uint32_t *) (CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R);
    uint32_t sts = *reg;
    /* Write 1 to Clear the pending interrupt */
    if (sts & SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_AVAIL_STS_MASK) {
        *reg = SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_AVAIL_STS_MASK;
    }
    if (sts & SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_MBOX_ECC_COR_STS_MASK) {
        *reg = SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_MBOX_ECC_COR_STS_MASK;
    }
    if (sts & SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_DEBUG_LOCKED_STS_MASK) {
        *reg = SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_DEBUG_LOCKED_STS_MASK;
    }
    if (sts == 0) {
        printf("bad soc_ifc_notif_intr sts:%x\n", sts);
        printf("%c", 0x1);
    }
}

inline void service_sha512_acc_error_intr() {printf("ERROR");}
inline void service_sha512_acc_notif_intr() {
    uint32_t * reg = (uint32_t *) (CLP_SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R);
    uint32_t sts = *reg;
    /* Write 1 to Clear the pending interrupt */
    if (sts & SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK) {
        *reg = SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK;
    }
    if (sts == 0) {
        printf("bad sha512_acc_notif_intr sts:%x\n", sts);
        printf("%c", 0x1);
    }
}

#endif //CALIPTRA_ISR_H
