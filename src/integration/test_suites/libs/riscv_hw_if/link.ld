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
 * Unified simulation linker script.
 *
 * All read/write data (.data/.rodata/.sdata) AND .bss live directly in DCCM
 * (VMA == LMA) and are backdoor-loaded into DCCM via dccm.hex. crt0 performs NO
 * ROM->DCCM copy of either .data or .bss (these benches are simulation-only and
 * DCCM is always preloaded). Only .text remains in the ROM/imem program image.
 *
 * Data is placed at the DCCM base (0x5000_0000) so a test has the full 256 KiB
 * of DCCM available. (Previously .data started at 0x5002_0000 and the lower half
 * was nominally reserved for remote-firmware images; that reservation is unused
 * in these benches, and many tests already relocated data to the lower half.)
 */
SECTIONS {
  /* ------------------- ROM / imem ------------------- */
  . = 0x0;
  .text     : { *(.text*) }
  .eh_frame : { *(.eh_frame) }
  _rom_end = .;
  ASSERT( _rom_end < 0x00018000, "ERROR: ROM (.text) size exceeds 96KiB")

  /* ------- DCCM-resident RW data + BSS (VMA == LMA) -------
   * Backdoor-loaded via dccm.hex; no crt0 copy. The .bss/.sbss inputs are
   * folded in here (with =0x0000 fill) so they are zero-initialized by the
   * DCCM preload rather than copied from ROM at reset.
   *
   * Data starts at 0x5002_0000 (the UPPER half of DCCM). The LOWER half
   * (0x5000_0000..0x5001_ffff) is deliberately left free: the integration /
   * validation ROM copies remote firmware images (FMC/RT, whose own .data is
   * linked at 0x5000_0000) into the lower half via the mailbox FW flow. Placing
   * this firmware's data/stack in the lower half would be overwritten by that
   * copy and corrupt the ROM mid-transfer. Do not move this below 0x5002_0000. */
  _data_vma_start = 0x50020000;
  .data _data_vma_start : AT(_data_vma_start) {
      *(.dccm*)
      *(.*data) *(.*data.*)
      *(.rodata*) *(.srodata*)
      *(.sbss) *(.bss)
      . = ALIGN(4);
  } =0x0000
  _data_vma_end = .;

  /* ------------------- ICCM code images -------------------
   * VMA is in ICCM; LMA is staged in DCCM (loaded via dccm.hex) and copied into
   * ICCM by the test at runtime. iccm0 sits at the ICCM base; iccm1/iccm2 are
   * placed at distinct ICCM offsets so a test may load them to COEXIST with
   * iccm0 (e.g. a ROM image at the base plus an RT image at 0x8000). Tests that
   * use only one image leave the others empty (zero size), so these fixed
   * offsets are harmless for them. A test that loads an image must copy it to,
   * execute it at, and vector NMIs to that image's linked VMA. */
  iccm_code0_start = .;
  .data_iccm0 0x40000000 : AT(iccm_code0_start) { *(.data_iccm0) ; . = ALIGN(4); } =0x0000
  iccm_code0_end = iccm_code0_start + SIZEOF(.data_iccm0);
  iccm_code1_start = ALIGN(iccm_code0_end,4);
  .data_iccm1 0x40008000 : AT(iccm_code1_start) { *(.data_iccm1) ; . = ALIGN(4); } =0x0000
  iccm_code1_end = iccm_code1_start + SIZEOF(.data_iccm1);
  iccm_code2_start = ALIGN(iccm_code1_end,4);
  .data_iccm2 0x4003D000 : AT(iccm_code2_start) { *(.data_iccm2) ; . = ALIGN(4); } =0x0000
  iccm_code2_end = iccm_code2_start + SIZEOF(.data_iccm2);

  /* ------------------- Stack ------------------- */
  . = ALIGN(iccm_code2_end,16);
  STACK = ALIGN(16) + 0x8000;
  ASSERT( (STACK < 0x50040000), "ERROR: Stack overflows the DCCM")
}
