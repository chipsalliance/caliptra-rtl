OUTPUT_ARCH( "riscv" )
ENTRY(_start)

SECTIONS {
  . = 0x30000000;
  .data : { *(.*data) *(.rodata*) *(.sbss) }
  . = 0x80000000;
  .text   : { *(.text*) }
  _end = .;
  .bss : { *(.bss) }
  . = 0xee000000;
  .data.io .  : { *(.data.io) }
}
