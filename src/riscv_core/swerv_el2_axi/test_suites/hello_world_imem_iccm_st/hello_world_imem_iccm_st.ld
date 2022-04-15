OUTPUT_ARCH( "riscv" )
ENTRY(_start)

SECTIONS {
    . = 0x80000000;
  .text   : { *(.text*) }
 _end = .;
  .data  :  { *(.*data) *(.rodata*) *(.sbss) STACK = ALIGN(16) + 0x1000;}
  .bss : { *(.bss) }
  . = 0xee000000;
  .data.io .  : { *(.data.io) }
}
