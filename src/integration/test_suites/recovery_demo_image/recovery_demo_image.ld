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
  . = 0x40000000;
  .text   : { *(.text*) }

  .eh_frame : { *(.eh_frame) }
  /* DCCM as VMA */
  /* Data is bundled with ROM image in iMem */
  /* Align data to 4-bytes to allow LSU access to work
   * when copying to DCCM */
  /* Only upper half of DCCM is used for ROM image */
  _data_lma_start = ALIGN(256);
  _data_vma_start = 0x50000000;
  .data _data_vma_start : AT(_data_lma_start) { *(.*data) *(.*data.*) *(.rodata*) *(.srodata*) ; . = ALIGN(4);} =0x0000,
  _data_lma_end = _data_lma_start + SIZEOF(.data);
  _data_vma_end = _data_vma_start + SIZEOF(.data);

  _bss_lma_start = _data_lma_end;
  _bss_vma_start = _data_vma_end;
  .bss _bss_vma_start : AT(_bss_lma_start) { *(.sbss) *(.bss) ; . = ALIGN(4);} =0x0000,
  _bss_lma_end = _bss_lma_start + SIZEOF(.bss);
  _bss_vma_end = _bss_vma_start + SIZEOF(.bss);

  _end = _bss_lma_end;
  /*ASSERT( _end < 0x0000C000, "ERROR: ROM size exceeds 48KiB")*/


  /* Stack is at the end of DCCM after .data_iccm2 */
  . = ALIGN(_bss_vma_end,16);
  STACK = ALIGN(16) + 0x2000;
  ASSERT( (STACK < 0x50010000), "ERROR: Stack overflows the DCCM -- note: lower half of DCCM is allocated in the demo image for ROM code")
}
