OUTPUT_ARCH( "riscv" )
ENTRY(_start)

SECTIONS {
  . = 0x30000000;
  .data : { *(.*data) *(.rodata*) *(.sbss) }
  . = 0x80000000;
  .text  :  { *(.text*) }
  . = 0x10000;
  . = ALIGN(4);
  printf_start = .;
  . = 0xee000000;
  .data_load : AT(printf_start) {*(.data_text)}
  printf_end = printf_start + SIZEOF(.data_load);
}
