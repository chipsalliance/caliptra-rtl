OUTPUT_ARCH( "riscv" )
ENTRY(_start)

SECTIONS {
  . = 0x0;
  .text   : { *(.text*) }
  _end = .;
  . = 0x00007ff0;
  .iccm.ctl : { LONG(0xee000000); LONG(0xee008000) }
  . = 0x00007ff8;
  .data.ctl : { LONG(0x30000000); LONG(STACK) }
  . = 0x30000000;
  .data  :  { *(.*data) *(.rodata*) *(.sbss) STACK = ALIGN(16) + 0x1000;}
  .bss : { *(.bss) }
  . = 0xf0040001;
  .data.io .  : { *(.data.io) }
}
