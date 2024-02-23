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
  _data_lma_start = ALIGN(4);
  _data_vma_start = 0x50000000;
  .data _data_vma_start : AT(_data_lma_start) {  *(.srodata*) ; . = ALIGN(4);} =0x0000,
  _data_lma_end = _data_lma_start + SIZEOF(.data);
  _data_vma_end = _data_vma_start + SIZEOF(.data);

  _bss_lma_start = _data_lma_end;
  _bss_vma_start = _data_vma_end;
  .bss _bss_vma_start : AT(_bss_lma_start) { *(.sbss) *(.bss) ; . = ALIGN(4);} =0x0000,
  _bss_lma_end = _bss_lma_start + SIZEOF(.bss);
  _bss_vma_end = _bss_vma_start + SIZEOF(.bss);

  _end = _bss_lma_end;
  ASSERT( _end < 0x00010000, "ERROR: ROM size exceeds 64KiB")

  /* DCCM as VMA and LMA */
  . = _bss_vma_end;
  _dccm_lma_start = _bss_vma_end; /* ----\___ SAME */
  _dccm_vma_start = _bss_vma_end; /* ----/         */
  .dccm _dccm_vma_start : AT(_dccm_lma_start) { *(.*data) *(.*data.*) *(.rodata*) *(.dccm*) . = ALIGN(4); } =0x0000,
  _dccm_end = _dccm_vma_start + SIZEOF(.dccm);

  /* NO ICCM */

  /* Stack is at the end of DCCM */
  . = ALIGN(_dccm_end,16);
  stack_start = .;
  STACK = ALIGN(16) + 0x2000;
  ASSERT( (STACK < 0x50004000), "ERROR: Stack overflows the DCCM")
}
