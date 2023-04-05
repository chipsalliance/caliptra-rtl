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

#ifndef VEER_CSR_H
#define VEER_CSR_H

#include "caliptra_defines.h"
#include "riscv-csr.h" /* for __riscv_xlen */

//////////////////////////////////////////////////////////////////////////////
// Non-Standard VeeR CSR offset macros
//
#define VEER_CSR_MEIVT    0xBC8
#define VEER_CSR_MEIPT    0xBC9
#define VEER_CSR_MEICPCT  0xBCA
#define VEER_CSR_MEICIDPL 0xBCB
#define VEER_CSR_MEICURPL 0xBCC
#define VEER_CSR_MEIHAP   0xFC8


//////////////////////////////////////////////////////////////////////////////
// VeeR PIC Memory Mapped register offset macros
//
// Per the VeeR PRM:
//   Suffix 'S' indicates a discrete register for each unique interrupt source
//              i.e. 64 interrupts = 64 registers
//   Suffix 'X' indicates a single bit within a range of registers for each interrupt source
//              i.e. 64 interrupts = 2 registers (32-bits each)
#define VEER_MM_PIC_MEIPLS       (RV_PIC_BASE_ADDR + RV_PIC_MEIPL_OFFSET)
#define VEER_MM_PIC_MEIPL(S)     (RV_PIC_BASE_ADDR + RV_PIC_MEIPL_OFFSET + S*4) /* S is 1:255 */
#define VEER_MM_PIC_MEIPX        (RV_PIC_BASE_ADDR + RV_PIC_MEIP_OFFSET)
#define VEER_MM_PIC_MEIP(X)      (RV_PIC_BASE_ADDR + RV_PIC_MEIP_OFFSET + (X>>5)*4) /* X is 1:255 */
#define VEER_MM_PIC_MEIES        (RV_PIC_BASE_ADDR + RV_PIC_MEIE_OFFSET)
#define VEER_MM_PIC_MEIE(S)      (RV_PIC_BASE_ADDR + RV_PIC_MEIE_OFFSET + S*4) /* S is 1:255 */
#define VEER_MM_PIC_MPICCFG      (RV_PIC_BASE_ADDR + RV_PIC_MPICCFG_OFFSET)
#define VEER_MM_PIC_MEIGWCTRLS   (RV_PIC_BASE_ADDR + RV_PIC_MEIGWCTRL_OFFSET)
#define VEER_MM_PIC_MEIGWCTRL(S) (RV_PIC_BASE_ADDR + RV_PIC_MEIGWCTRL_OFFSET + S*4) /* S is 1:255 */
#define VEER_MM_PIC_MEIGWCLRS    (RV_PIC_BASE_ADDR + RV_PIC_MEIGWCLR_OFFSET)
#define VEER_MM_PIC_MEIGWCLR(S)  (RV_PIC_BASE_ADDR + RV_PIC_MEIGWCLR_OFFSET + S*4) /* S is 1:255 */


//////////////////////////////////////////////////////////////////////////////
// VeeR PIC Gateway Configuration bits
//
enum {
  VEER_MEIGWCTRL_ACTIVE_HI_LEVEL = 0x00000000,
  VEER_MEIGWCTRL_ACTIVE_LO_LEVEL = 0x00000001,
  VEER_MEIGWCTRL_ACTIVE_HI_EDGE  = 0x00000002,
  VEER_MEIGWCTRL_ACTIVE_LO_EDGE  = 0x00000003,
};


//////////////////////////////////////////////////////////////////////////////
// VeeR Core-Specific MCAUSE values
//
#define MCAUSE_NMI_BIT_MASK                     (0xFUL << ((__riscv_xlen-4)))
#define MCAUSE_NMI_CODE_DBUS_STORE_VALUE        (MCAUSE_NMI_BIT_MASK | 0x0000)
#define MCAUSE_NMI_CODE_DBUS_LOAD_VALUE         (MCAUSE_NMI_BIT_MASK | 0x0001)
#define MCAUSE_NMI_CODE_FAST_INT_ECC_VALUE      (MCAUSE_NMI_BIT_MASK | 0x1000)
#define MCAUSE_NMI_CODE_FAST_INT_DCCM_VALUE     (MCAUSE_NMI_BIT_MASK | 0x1001)
#define MCAUSE_NMI_CODE_FAST_INT_NONDCCM_VALUE  (MCAUSE_NMI_BIT_MASK | 0x1002)

/*******************************************
 * mdeau - MRW - Data base register.
 */
static inline uint_xlen_t csr_read_mdeau(void) {
    uint_xlen_t value;
    __asm__ volatile ("csrr    %0, 0xbc0"
                      : "=r" (value)  /* output : register */
                      : /* input : none */
                      : /* clobbers: none */);
    return value;
}
static inline void csr_write_mdeau(uint_xlen_t value) {
    __asm__ volatile ("csrw    0xbc0, %0"
                      : /* output: none */
                      : "r" (value) /* input : from register */
                      : /* clobbers: none */);
}
static inline uint_xlen_t csr_read_write_mdeau(uint_xlen_t new_value) {
    uint_xlen_t prev_value;
    __asm__ volatile ("csrrw    %0, 0xbc0, %1"
                      : "=r" (prev_value) /* output: register %0 */
                      : "r" (new_value)  /* input : register */
                      : /* clobbers: none */);
    return prev_value;
}


#endif // #define VEER_CSR_H
