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
//     Dummy ISRs
// ---------------------------------------------------------------------

#ifndef CALIPTRA_ISR_H
#define CALIPTRA_ISR_H

#include "caliptra_defines.h"
#include <stdint.h>

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
    uint32_t qspi_error;
    uint32_t qspi_notif;
    uint32_t uart_error;
    uint32_t uart_notif;
    uint32_t i3c_error;
    uint32_t i3c_notif;
    uint32_t soc_ifc_error;
    uint32_t soc_ifc_notif;
    uint32_t sha512_acc_error;
    uint32_t sha512_acc_notif;
} caliptra_intr_received_s;

//////////////////////////////////////////////////////////////////////////////
// Function Declarations

inline void service_doe_error_intr() {return;}
inline void service_doe_notif_intr() {return;}

inline void service_ecc_error_intr() {return;}
inline void service_ecc_notif_intr() {return;}

inline void service_hmac_error_intr() {return;}
inline void service_hmac_notif_intr() {return;}

inline void service_kv_error_intr() {return;}
inline void service_kv_notif_intr() {return;}

inline void service_sha512_error_intr() {return;}
inline void service_sha512_notif_intr() {return;}

inline void service_sha256_error_intr() {return;}
inline void service_sha256_notif_intr() {return;}

inline void service_qspi_error_intr() {return;}
inline void service_qspi_notif_intr() {return;}

inline void service_uart_error_intr() {return;}
inline void service_uart_notif_intr() {return;}

inline void service_i3c_error_intr() {return;}
inline void service_i3c_notif_intr() {return;}

inline void service_soc_ifc_error_intr() {return;}
inline void service_soc_ifc_notif_intr () {return;}

inline void service_sha512_acc_error_intr() {return;}
inline void service_sha512_acc_notif_intr() {return;}

#endif //CALIPTRA_ISR_H
