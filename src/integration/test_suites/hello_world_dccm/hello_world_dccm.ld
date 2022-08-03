OUTPUT_ARCH( "riscv" )
ENTRY(_start)

SECTIONS {
  . = 0x30000000;
  .data : { *(.*data) *(.rodata*) *(.sbss)  STACK = ALIGN(16) + 0x1000;}
  . = 0x80000000;
  .text   : { *(.text*) }
 _end = .;
  . = 0xd0580000;
  .data.io .  : { *(.data.io) }
  . = 0xf0040000;
  .bss : { *(.bss) }
  . = 0xfffffff8;
  .data.ctl : { LONG(0x30000000); LONG(STACK) }
}
