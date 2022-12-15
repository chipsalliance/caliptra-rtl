//********************************************************************************
// SPDX-License-Identifier: Apache-2.0
// Copyright 2020 Western Digital Corporation or its affiliates.
//
// Licensed under the Apache License, Version 2.0 (the \"License\");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an \"AS IS\" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//********************************************************************************

OUTPUT_ARCH( "riscv" )
ENTRY(_start)

SECTIONS {
  . = 0x80000000;
  .text   : { *(.text*) }
 _end = .;
  . = 0xf004ff00;
  .data.io .  : { *(.data.io) }
  . = 0xf0040000;
  .data  :  { *(.*data) *(.rodata*) *(.sbss) STACK = ALIGN(16) + 0x1000;}
  .bss : { *(.bss) }
  . = 0xfffffff8;
  .data.ctl : { LONG(0xf0040000); LONG(STACK) }
}
