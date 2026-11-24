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

/*
 * Linker script for the caliptra_top validation ROM image. The Makefile picks it
 * up because it is named $(TESTNAME).ld. Derived from libs/riscv_hw_if/link.ld,
 * keep the two in sync.
 *
 * Difference from link.ld: the ROM's RW data, read-only data, .bss and ISR
 * vector table are stored in the ROM image (LMA right after .text) and run from
 * DCCM (VMA 0x5002_0000). The local crt0.s copies them into DCCM on every reset.
 * dccm.hex preloading alone is not enough for this image, because the RT
 * firmware it loads links its own .data/.bss/stack at 0x5002_0000 as well
 * (caliptra_rt/caliptra_rt.ld). After a warm or FW update reset the ROM must
 * re-initialize that region rather than run with RT's leftover values.
 *
 * The output section is deliberately not named .data. The Makefile strips .data
 * from program.hex and emits it into dccm.hex only. As .rom_data it stays in
 * program.hex at its ROM LMA, and dccm.hex ends up empty.
 */
SECTIONS {
  /* ------------------- ROM / imem ------------------- */
  . = 0x0;
  .text     : { *(.text*) }
  .eh_frame : { *(.eh_frame) }
  _rom_end = .;

  /* ------- RW data + BSS: LMA in ROM, VMA in DCCM, copied by crt0 -------
   * Same input sections as link.ld. .bss/.sbss are folded in with zero fill,
   * so the single crt0 copy loop also clears them. *(.dccm*) comes first so
   * the 1 KiB-aligned ISR vector table stays at 0x5002_0000.
   *
   * Data stays in the UPPER half of DCCM. The LOWER half
   * (0x5000_0000..0x5001_ffff) is left free for the FMC image, whose .data is
   * linked at 0x5000_0000 (caliptra_fmc/caliptra_fmc.ld) and which this ROM
   * copies in through the mailbox FW flow. */
  _data_lma_start = ALIGN(_rom_end, 4);
  _data_vma_start = 0x50020000;
  .rom_data _data_vma_start : AT(_data_lma_start) {
      *(.dccm*)
      *(.*data) *(.*data.*)
      *(.rodata*) *(.srodata*)
      *(.sbss) *(.bss)
      . = ALIGN(4);
  } =0x0000
  _data_vma_end = .;
  _data_lma_end = _data_lma_start + SIZEOF(.rom_data);
  ASSERT( _data_lma_end <= 0x00018000, "ERROR: ROM (.text + data load image) size exceeds 96KiB")

  /* ------------------- ICCM code images -------------------
   * VMA is in ICCM; LMA is staged in DCCM (loaded via dccm.hex) and copied into
   * ICCM by the test at runtime. All three share the ICCM base address and
   * cannot coexist in a single image: a test loads ONE of them to the base and
   * runs it (e.g. iccm_lock copies iccm0, then after a reset copies iccm1 to the
   * SAME base to verify the rewrite took effect). Tests that need to load
   * multiple ICCM images simultaneously at distinct offsets provide their own
   * linker script (e.g. the directed_kv_* tests place iccm1 at 0x4000_8000). */
  iccm_code0_start = .;
  .data_iccm0 0x40000000 : AT(iccm_code0_start) { *(.data_iccm0) ; . = ALIGN(4); } =0x0000
  iccm_code0_end = iccm_code0_start + SIZEOF(.data_iccm0);
  iccm_code1_start = ALIGN(iccm_code0_end,4);
  .data_iccm1 0x40000000 : AT(iccm_code1_start) { *(.data_iccm1) ; . = ALIGN(4); } =0x0000
  iccm_code1_end = iccm_code1_start + SIZEOF(.data_iccm1);
  iccm_code2_start = ALIGN(iccm_code1_end,4);
  .data_iccm2 0x40000000 : AT(iccm_code2_start) { *(.data_iccm2) ; . = ALIGN(4); } =0x0000
  iccm_code2_end = iccm_code2_start + SIZEOF(.data_iccm2);

  /* ------------------- Stack ------------------- */
  . = ALIGN(iccm_code2_end,16);
  STACK = ALIGN(16) + 0x8000;
  ASSERT( (STACK < 0x50040000), "ERROR: Stack overflows the DCCM")
}
