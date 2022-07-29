OUTPUT_ARCH( "riscv" )
ENTRY(_start)

SECTIONS {
    . = 0x80000000;
  .text   : { *(.text*) }
 _end = .;
  .data  :  { *(.*data) *(.rodata*) *(.sbss) STACK = ALIGN(16) + 0x1000;}
  .bss : { *(.bss) }
  . = 0x60000008;
  .data.io .  : { *(.data.io) }
}
