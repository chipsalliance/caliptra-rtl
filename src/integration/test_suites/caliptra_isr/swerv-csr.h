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

#ifndef SWERV_CSR_H
#define SWERV_CSR_H

#include "caliptra_defines.h"

//////////////////////////////////////////////////////////////////////////////
// Non-Standard SweRV CSR offset macros
//
#define SWERV_CSR_MEIVT    0xBC8
#define SWERV_CSR_MEIPT    0xBC9
#define SWERV_CSR_MEICPCT  0xBCA
#define SWERV_CSR_MEICIDPL 0xBCB
#define SWERV_CSR_MEICURPL 0xBCC
#define SWERV_CSR_MEIHAP   0xFC8


//////////////////////////////////////////////////////////////////////////////
// SweRV PIC Memory Mapped register offset macros
//
// Per the SweRV PRM:
//   Suffix 'S' indicates a discrete register for each unique interrupt source
//              i.e. 64 interrupts = 64 registers
//   Suffix 'X' indicates a single bit within a range of registers for each interrupt source
//              i.e. 64 interrupts = 2 registers (32-bits each)
#define SWERV_MM_PIC_MEIPLS       (RV_PIC_BASE_ADDR + RV_PIC_MEIPL_OFFSET)
#define SWERV_MM_PIC_MEIPL(S)     (RV_PIC_BASE_ADDR + RV_PIC_MEIPL_OFFSET + S*4) /* S is 1:255 */
#define SWERV_MM_PIC_MEIPX        (RV_PIC_BASE_ADDR + RV_PIC_MEIP_OFFSET)
#define SWERV_MM_PIC_MEIP(X)      (RV_PIC_BASE_ADDR + RV_PIC_MEIP_OFFSET + (X>>5)*4) /* X is 1:255 */
#define SWERV_MM_PIC_MEIES        (RV_PIC_BASE_ADDR + RV_PIC_MEIE_OFFSET)
#define SWERV_MM_PIC_MEIE(S)      (RV_PIC_BASE_ADDR + RV_PIC_MEIE_OFFSET + S*4) /* S is 1:255 */
#define SWERV_MM_PIC_MPICCFG      (RV_PIC_BASE_ADDR + RV_PIC_MPICCFG_OFFSET)
#define SWERV_MM_PIC_MEIGWCTRLS   (RV_PIC_BASE_ADDR + RV_PIC_MEIGWCTRL_OFFSET)
#define SWERV_MM_PIC_MEIGWCTRL(S) (RV_PIC_BASE_ADDR + RV_PIC_MEIGWCTRL_OFFSET + S*4) /* S is 1:255 */
#define SWERV_MM_PIC_MEIGWCLRS    (RV_PIC_BASE_ADDR + RV_PIC_MEIGWCLR_OFFSET)
#define SWERV_MM_PIC_MEIGWCLR(S)  (RV_PIC_BASE_ADDR + RV_PIC_MEIGWCLR_OFFSET + S*4) /* S is 1:255 */


//////////////////////////////////////////////////////////////////////////////
// SweRV PIC Gateway Configuration bits
//
enum {
  SWERV_MEIGWCTRL_ACTIVE_HI_LEVEL = 0x00000000,
  SWERV_MEIGWCTRL_ACTIVE_LO_LEVEL = 0x00000001,
  SWERV_MEIGWCTRL_ACTIVE_HI_EDGE  = 0x00000002,
  SWERV_MEIGWCTRL_ACTIVE_LO_EDGE  = 0x00000003,
};


#endif // #define SWERV_CSR_H
