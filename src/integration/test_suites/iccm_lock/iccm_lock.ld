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
OUTPUT_ARCH( "riscv" )
ENTRY(_start)

SECTIONS {
  . = 0x0;
  .text   : { *(.text*) }
  _end = .;
  . = 0x00007ff0;
  .iccm.ctl : { LONG(0x40000000); LONG(0x40020000) }
  . = 0x00007ff8;
  .data.ctl : { LONG(0x50000000); LONG(0x50020000) }
  . = 0x50000000;
  .data  :  { *(.*data) *(.rodata*) *(.sbss) }
  .bss : { *(.bss) }
  .dccm : { *(.dccm*) }
  . = ALIGN(4);
  iccm_code0_start = .;
  /* ICCM as VMA */
  .data_iccm0 0x40000000 : AT(iccm_code0_start) {*(.data_iccm0) ; . = ALIGN(4); } =0x0000, /* iccm_code0_start, after .data, as LMA */
  iccm_code0_end = iccm_code0_start + SIZEOF(.data_iccm0);
  iccm_code1_start = ALIGN(iccm_code0_end,4);
  .data_iccm1 0x40000000 : AT(iccm_code1_start) {*(.data_iccm1) ; . = ALIGN(4); } =0x0000, /* iccm_code1_start, after .data, as LMA */
  iccm_code1_end = iccm_code1_start + SIZEOF(.data_iccm1);
  iccm_code2_start = ALIGN(iccm_code1_end,4);
  .data_iccm2 0x40000000 : AT(iccm_code2_start) {*(.data_iccm2) ; . = ALIGN(4); } =0x0000, /* iccm_code2_start, after .data, as LMA */
  iccm_code2_end = iccm_code2_start + SIZEOF(.data_iccm2);
  . = ALIGN(iccm_code2_end,16);
  STACK = ALIGN(16) + 0x4000;
}
