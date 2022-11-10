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
