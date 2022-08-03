OUTPUT_ARCH( "riscv" )
ENTRY(_start)

SECTIONS {
  . = 0x30000000;
  .data : { *(.*data) *(.rodata*) *(.sbss) }
  .text   : { *(.text*) }
 _end = .;
  . = 0xd0580000;
  .data.io .  : { *(.data.io) }
  . = 0xf0040000;
  .bss : { *(.bss) }
  . = 0xfffffff8;
  .data.ctl : { LONG(0xf0040000); LONG(STACK) }
}
