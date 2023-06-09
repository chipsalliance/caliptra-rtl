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
ENTRY(caliptra_rt)

SECTIONS {
  . = 0x10;
  _text_lma_start = .;
  /* ---------------------
   * Upper half of ICCM as VMA for Runtime
   * --------------------- */
  .text 0x40010000 : AT(_text_lma_start) { *(.text*) ; . = ALIGN(16); } =0x0000,
  /* Insert a unique value in memory (LMA) at the boundary between ICCM/DCCM
   * Dword of 0's is not a legal instruction, but could be a valid 'const'
   * data element in the instructions. This full 4-dword value should be
   * unique enough for ROM to identify the boundary between ICCM and DCCM contents */
  _text_lma_end = _text_lma_start + SIZEOF(.text);
  ASSERT(( _text_lma_end < 0x00010000), "ERROR: .text section overflows ICCM size -- RT loaded to upper half of ICCM")

  /* Now, knowing the size of .text section, put that at address 0 for ROM to check */
  .text.pre 0x0 : AT(0x0) { LONG(_text_lma_end - 0x10); LONG(0x00000000); LONG(0x00000000); LONG(0x00000000); }

  /* ---------------------
   * DCCM as VMA
   * --------------------- */
  /* Upper half of DCCM allocated (in val image) for remote RT FW */
  . = _text_lma_end + 0x10; /* . (location counter) points to 0x0, force it back to next LMA here */
  _data_vma_start = 0x50010000;
  _data_lma_start = .; /* After this, . (location counter) goes back to holding VMA value */
  .data _data_vma_start :  AT(_data_lma_start) { *(.*data) *(.sdata*) *(.rodata*) *(.srodata*) ; . = ALIGN(4); } =0x0000,
  _data_lma_end = _data_lma_start + SIZEOF(.data);

  _bss_vma_start = ALIGN(4);
  _bss_lma_start = _data_lma_end;
  .bss _bss_vma_start : AT(_bss_lma_start) { *(.bss) *(.sbss) ; . = ALIGN(4); } =0x0000,
  _bss_lma_end = _bss_lma_start + SIZEOF(.bss);

  _dccm_vma_start = ALIGN(4);
  _dccm_lma_start = _bss_lma_end;
  .dccm _dccm_vma_start : AT(_dccm_lma_start) { *(.dccm*) ; . = ALIGN(4); } =0x0000,
  _dccm_vma_end = .;
  _dccm_lma_end = _dccm_lma_start + SIZEOF(.dccm);

  ASSERT(( _dccm_lma_end < 0x00020000), "ERROR: RT firmware image overflows size of mailbox")

  /* Now, knowing the size of .dccm etc. sections, put that at next aligned address after .text for ROM to check */
  .data.pre _text_lma_end : AT(_text_lma_end) { LONG(_dccm_lma_end - _data_lma_start); LONG(0x00000000); LONG(0x00000000); LONG(0x00000000); }

  /* ---------------------
   * Stack is at the end of DCCM after .data
   * --------------------- */
  STACK = ALIGN(_dccm_vma_end,16) + 0x4000;

  ASSERT( (STACK > 0x50010000), "ERROR: Stack not in the expected address range")
  ASSERT( (STACK < 0x50020000), "ERROR: Stack overflows the DCCM in runtime image -- note: lower half of DCCM is used by FMC code")
}
