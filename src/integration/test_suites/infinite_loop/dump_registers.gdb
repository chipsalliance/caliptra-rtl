echo Connecting to OpenOCD...\n
set architecture riscv:rv32
set remotetimeout 30
target extended-remote :3333

echo Dumping registers...\n
info registers

echo Writing data to DCCM...\n
monitor write_memory 0x50000000 32 0xdeadbeef
monitor read_memory 0x50000000 32 1
print/x *(0x50000000)
