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
// File: caliptra_isr.h  (COMMON / default)
// Description:
//     Shared interrupt-service header used by the vast majority of tests.
//     It provides the cptra_intr_rcv bookkeeping struct plus a generic
//     "clear and log" service routine for every interrupt block: read the
//     block's INTERNAL_INTR status, write-1-to-clear every asserted source,
//     record the observed status into cptra_intr_rcv, and log a warning if
//     the ISR was entered with no status bit set.
//
//     A test only needs a *local* copy of caliptra_isr.h when its handler
//     must do something more than clear+record (e.g. poke another register,
//     drive a test-specific global, or intentionally fail). If a test dir
//     contains its own caliptra_isr.h the build uses that instead of this
//     one (see tools/scripts/Makefile: the test-dir copy overwrites the
//     shared copy in the build directory).
// ---------------------------------------------------------------------

#ifndef CALIPTRA_ISR_H
    #define CALIPTRA_ISR_H

#define EN_ISR_PRINTS 1

#include "caliptra_reg.h"
#include <stdint.h>
#include "printf.h"

/* --------------- symbols/typedefs --------------- */
typedef struct {
    uint32_t doe_error;
    uint32_t doe_notif;
    uint32_t ecc_error;
    uint32_t ecc_notif;
    uint32_t hmac_error;
    uint32_t hmac_notif;
    uint32_t kv_error;
    uint32_t kv_notif;
    uint32_t sha512_error;
    uint32_t sha512_notif;
    uint32_t sha256_error;
    uint32_t sha256_notif;
    uint32_t sha3_error;
    uint32_t sha3_notif;
    uint32_t soc_ifc_error;
    uint32_t soc_ifc_notif;
    uint32_t sha512_acc_error;
    uint32_t sha512_acc_notif;
    uint32_t abr_error;
    uint32_t abr_notif;
    uint32_t axi_dma_error;
    uint32_t axi_dma_notif;
    uint32_t aes_error;
    uint32_t aes_notif;
} caliptra_intr_received_s;
extern volatile caliptra_intr_received_s cptra_intr_rcv;

// Optional RISC-V exception bookkeeping. A test opts in by compiling with
// -DRV_EXCEPTION_STRUCT (e.g. via its <test>.mk) and defining a storage
// instance of exc_flag; the shared trap handler in caliptra_isr.c then records
// mcause/mscause into it. The typedef lives here so both the test and
// caliptra_isr.c see the same type.
#ifdef RV_EXCEPTION_STRUCT
typedef struct {
    uint8_t  exception_hit;
    uint32_t mcause;
    uint32_t mscause;
} rv_exception_struct_s;
#endif

//////////////////////////////////////////////////////////////////////////////
// Function Declarations
//

// Performs all the CSR setup to configure and enable vectored external interrupts
void init_interrupts(void);

// Generic "clear and log" body shared by every block that owns an
// INTR_BLOCK_RF. Reads the INTERNAL_INTR status register, write-1-to-clears
// every asserted source, records the status into cptra_intr_rcv for tests
// that poll it, and warns if the ISR fired with no source set.
// NOTE: reg MUST be volatile. sts is read from *reg and then written back to
// W1C-clear the asserted sources; with a non-volatile pointer the compiler
// treats "write back the value just read" as a redundant store and deletes it
// at -O3, so the interrupt is never cleared and the ISR re-enters forever.
#define CALIPTRA_SERVICE_INTR(field, intr_reg)                        \
    do {                                                              \
        volatile uint32_t * reg = (volatile uint32_t *) (intr_reg);   \
        uint32_t sts = *reg;                                          \
        *reg = sts;                                                   \
        cptra_intr_rcv.field |= sts;                                  \
        if (sts == 0) {                                               \
            VPRINTF(ERROR, "spurious " #field " intr, sts:%x\n", sts);\
        }                                                             \
    } while (0)

// These inline functions are used to insert event-specific functionality into
// the otherwise generic ISR that gets laid down by the parameterized macro
// "nonstd_veer_isr". Every service_* symbol referenced by caliptra_isr.c must
// be defined here so the shared ISR compiles against this default header.
inline void service_doe_error_intr()        { CALIPTRA_SERVICE_INTR(doe_error,        CLP_DOE_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R); }
inline void service_doe_notif_intr()        { CALIPTRA_SERVICE_INTR(doe_notif,        CLP_DOE_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R); }

inline void service_ecc_error_intr()        { CALIPTRA_SERVICE_INTR(ecc_error,        CLP_ECC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R); }
inline void service_ecc_notif_intr()        { CALIPTRA_SERVICE_INTR(ecc_notif,        CLP_ECC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R); }

inline void service_hmac_error_intr()       { CALIPTRA_SERVICE_INTR(hmac_error,       CLP_HMAC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R); }
inline void service_hmac_notif_intr()       { CALIPTRA_SERVICE_INTR(hmac_notif,       CLP_HMAC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R); }

// Key Vault has no INTR_BLOCK_RF; its interrupts are unused, so the handlers
// are stubs.
inline void service_kv_error_intr()         { return; }
inline void service_kv_notif_intr()         { return; }

inline void service_sha512_error_intr()     { CALIPTRA_SERVICE_INTR(sha512_error,     CLP_SHA512_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R); }
inline void service_sha512_notif_intr()     { CALIPTRA_SERVICE_INTR(sha512_notif,     CLP_SHA512_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R); }

inline void service_sha256_error_intr()     { CALIPTRA_SERVICE_INTR(sha256_error,     CLP_SHA256_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R); }
inline void service_sha256_notif_intr()     { CALIPTRA_SERVICE_INTR(sha256_notif,     CLP_SHA256_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R); }

// SHA3 uses the CLP_SHA3_INTR_BLOCK_RF_ prefix (no _REG_) unlike the others.
inline void service_sha3_error_intr()       { CALIPTRA_SERVICE_INTR(sha3_error,       CLP_SHA3_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R); }
inline void service_sha3_notif_intr()       { CALIPTRA_SERVICE_INTR(sha3_notif,       CLP_SHA3_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R); }

inline void service_soc_ifc_error_intr()    { CALIPTRA_SERVICE_INTR(soc_ifc_error,    CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R); }
inline void service_soc_ifc_notif_intr()    { CALIPTRA_SERVICE_INTR(soc_ifc_notif,    CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R); }

inline void service_sha512_acc_error_intr() { CALIPTRA_SERVICE_INTR(sha512_acc_error, CLP_SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R); }
inline void service_sha512_acc_notif_intr() { CALIPTRA_SERVICE_INTR(sha512_acc_notif, CLP_SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R); }

inline void service_abr_error_intr()        { CALIPTRA_SERVICE_INTR(abr_error,        CLP_ABR_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R); }
inline void service_abr_notif_intr()        { CALIPTRA_SERVICE_INTR(abr_notif,        CLP_ABR_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R); }

// AXI_DMA names its primary notif source NOTIF_TXN_DONE (not NOTIF_CMD_DONE),
// but the generic clear-all body covers every source regardless of name.
inline void service_axi_dma_error_intr()    { CALIPTRA_SERVICE_INTR(axi_dma_error,    CLP_AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R); }
inline void service_axi_dma_notif_intr()    { CALIPTRA_SERVICE_INTR(axi_dma_notif,    CLP_AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R); }

inline void service_aes_error_intr()        { CALIPTRA_SERVICE_INTR(aes_error,        CLP_AES_CLP_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R); }
inline void service_aes_notif_intr()        { CALIPTRA_SERVICE_INTR(aes_notif,        CLP_AES_CLP_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R); }

#endif //CALIPTRA_ISR_H
