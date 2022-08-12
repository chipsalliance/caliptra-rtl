OUTPUT_ARCH( "riscv" )
ENTRY(_start)

SECTIONS {
  . = 0x0;
  .text   : { crt0.o (.text*) }
  _end = .;
  . = 0x00007ff0;
  .iccm.ctl : { LONG(0xee000000); LONG(0xee008000) }
  . = 0x00007ff8;
  .data.ctl : { LONG(0x30000000); LONG(STACK) }
  . = 0x30000000;
  .data  :  { *(.*data) *(.rodata*) *(.sbss) STACK = ALIGN(16) + 0x1000;}
  .bss : { *(.bss) }
  . = 0xee000000 ;
  .text.init   : { cmark.o (.text*) }
  /*. = 0xd0580000;*/
  /*.data.io .  : { *(.data.io) }*/
}
