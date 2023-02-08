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

#define EN_ISR_PRINTS 1

#include "caliptra_defines.h"
#include <stdint.h>
#include "printf.h"

//extern volatile uint32_t hmac_intr_status;

//////////////////////////////////////////////////////////////////////////////
// Function Declarations
//
// Performs all the CSR setup to configure and enable vectored external interrupts
void init_interrupts(void);

// These inline functions are used to insert event-specific functionality into the
// otherwise generic ISR that gets laid down by the parameterized macro "nonstd_swerv_isr"
inline void service_doe_error_intr() {printf("ERROR");}
inline void service_doe_notif_intr() {printf("ERROR");}
inline void service_ecc_error_intr   () {printf("ERROR");}
inline void service_ecc_notif_intr   () {printf("ERROR");}
inline void service_hmac_error_intr  () {printf("ERROR");}
inline void service_hmac_notif_intr  () {printf("ERROR");}

inline void service_kv_error_intr    () {printf("ERROR");}
inline void service_kv_notif_intr    () {printf("ERROR");}
inline void service_sha512_error_intr() {printf("ERROR");}
inline void service_sha512_notif_intr() {printf("ERROR");}
inline void service_sha256_error_intr() {printf("ERROR");}
inline void service_sha256_notif_intr() {printf("ERROR");}
inline void service_qspi_error_intr  () {printf("ERROR");}
inline void service_qspi_notif_intr  () {printf("ERROR");}
inline void service_uart_error_intr  () {printf("ERROR");}
inline void service_uart_notif_intr  () {printf("ERROR");}
inline void service_i3c_error_intr   () {printf("ERROR");}
inline void service_i3c_notif_intr   () {printf("ERROR");}
inline void service_soc_ifc_error_intr  () {printf("ERROR");}
inline void service_soc_ifc_notif_intr  () {printf("ERROR");}
inline void service_sha512_acc_error_intr() {printf("ERROR");}
inline void service_sha512_acc_notif_intr() {printf("ERROR");}


#endif //CALIPTRA_ISR_H
