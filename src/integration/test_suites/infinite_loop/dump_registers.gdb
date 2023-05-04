echo Connecting to OpenOCD...\n
set architecture riscv:rv32
target extended-remote :3333

echo Dumping registers...\n
info registers
