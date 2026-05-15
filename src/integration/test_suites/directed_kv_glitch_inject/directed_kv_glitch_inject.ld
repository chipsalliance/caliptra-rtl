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

/* Custom linker script for KV glitch injection test.
 * Places .data_iccm0 (FMC) at VMA 0x40000000 so that PC-relative
 * addressing works correctly when fmc_entry executes from ICCM. */

OUTPUT_ARCH( "riscv" )
ENTRY(_start)

SECTIONS {
  . = 0x0;
  .text   : { *(.text*) }

  .eh_frame : { *(.eh_frame) }
  _data_lma_start = ALIGN(4);
  _data_vma_start = 0x50020000;
  .data _data_vma_start : AT(_data_lma_start) { *(.*data) *(.*data.*) *(.rodata*) *(.srodata*) ; . = ALIGN(4);} =0x0000,
  _data_lma_end = _data_lma_start + SIZEOF(.data);
  _data_vma_end = _data_vma_start + SIZEOF(.data);

  _bss_lma_start = _data_lma_end;
  _bss_vma_start = _data_vma_end;
  .bss _bss_vma_start : AT(_bss_lma_start) { *(.sbss) *(.bss) ; . = ALIGN(4);} =0x0000,
  _bss_lma_end = _bss_lma_start + SIZEOF(.bss);
  _bss_vma_end = _bss_vma_start + SIZEOF(.bss);

  _end = _bss_lma_end;
  ASSERT( _end < 0x00018000, "ERROR: ROM size exceeds 96KiB")

  /* DCCM as VMA and LMA */
  . = _bss_vma_end;
  _dccm_lma_start = _bss_vma_end;
  _dccm_vma_start = _bss_vma_end;
  .dccm _dccm_vma_start : AT(_dccm_lma_start) { *(.dccm*) . = ALIGN(4); } =0x0000,

  /* ICCM section for FMC code */
  iccm_code0_start = _dccm_lma_start + SIZEOF(.dccm);
  .data_iccm0 0x40000000 : AT(iccm_code0_start) {*(.data_iccm0) ; . = ALIGN(4); } =0x0000,
  iccm_code0_end = iccm_code0_start + SIZEOF(.data_iccm0);

  /* Stack at end of DCCM */
  . = ALIGN(iccm_code0_end, 16);
  STACK = ALIGN(16) + 0x4000;
  ASSERT( (STACK < 0x50040000), "ERROR: Stack overflows the DCCM")
}
