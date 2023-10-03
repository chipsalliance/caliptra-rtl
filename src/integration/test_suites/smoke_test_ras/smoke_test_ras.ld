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

  .eh_frame : { *(.eh_frame) }
  /* DCCM as VMA */
  /* Data is bundled with ROM image in iMem */
  /* Align data to 4-bytes to allow LSU access to work
   * when copying to DCCM */
  /* Only upper half of DCCM is used for ROM image */
  _data_lma_start = ALIGN(4);
  _data_vma_start = 0x50010000;
  .data _data_vma_start : AT(_data_lma_start) {  *(.srodata*) ; . = ALIGN(4);} =0x0000,
  _data_lma_end = _data_lma_start + SIZEOF(.data);
  _data_vma_end = _data_vma_start + SIZEOF(.data);

  _bss_lma_start = _data_lma_end;
  _bss_vma_start = _data_vma_end;
  .bss _bss_vma_start : AT(_bss_lma_start) { *(.sbss) *(.bss) ; . = ALIGN(4);} =0x0000,
  _bss_lma_end = _bss_lma_start + SIZEOF(.bss);
  _bss_vma_end = _bss_vma_start + SIZEOF(.bss);

  _end = _bss_lma_end;
  ASSERT( _end < 0x0000C000, "ERROR: ROM size exceeds 48KiB")

  /* DCCM as VMA and LMA */
  . = _bss_vma_end;
  _dccm_lma_start = _bss_vma_end; /* ----\___ SAME */
  _dccm_vma_start = _bss_vma_end; /* ----/         */
  .dccm _dccm_vma_start : AT(_dccm_lma_start) { *(.*data) *(.rodata*) *(.dccm*) . = ALIGN(4); } =0x0000,
  iccm_code0_start = .;

  /* ICCM as VMA */
  /* All of these sections start at the base address of ICCM, and cannot coexist */
  /* The code in these sections will be loaded to DCCM alongside .data and later
   * copied into ICCM for execution.
   * NOTE: none of these sections will be used by the val image/FMC/RT flows */
  .data_iccm0 0x40000000 : AT(iccm_code0_start) {*(.data_iccm0) ; . = ALIGN(4); } =0x0000, /* iccm_code0_start, after .data, as LMA */
  iccm_code0_end = iccm_code0_start + SIZEOF(.data_iccm0);
  iccm_code1_start = ALIGN(iccm_code0_end,4);
  .data_iccm1 0x40000000 : AT(iccm_code1_start) {*(.data_iccm1) ; . = ALIGN(4); } =0x0000, /* iccm_code1_start, after .data, as LMA */
  iccm_code1_end = iccm_code1_start + SIZEOF(.data_iccm1);
  iccm_code2_start = ALIGN(iccm_code1_end,4);
  .data_iccm2 0x40000000 : AT(iccm_code2_start) {*(.data_iccm2) ; . = ALIGN(4); } =0x0000, /* iccm_code2_start, after .data, as LMA */
  iccm_code2_end = iccm_code2_start + SIZEOF(.data_iccm2);

  /* Stack is at the end of DCCM after .data_iccm2 */
  . = ALIGN(iccm_code2_end,16);
  STACK = ALIGN(16) + 0x4000;
  ASSERT( (STACK < 0x50020000), "ERROR: Stack overflows the DCCM -- note: lower half of DCCM is allocated in the validation image for remote firmware images")
}
