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
  . = 0x30000000;
  .data  :  { *(.*data) *(.rodata*) *(.sbss) STACK = ALIGN(16) + 0x1000;}
  .bss : { *(.bss) }
  /*. = 0xd0580000;*/
  /*.data.io .  : { *(.data.io) }*/
}
