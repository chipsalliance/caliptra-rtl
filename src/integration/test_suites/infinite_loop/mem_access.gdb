echo Connecting to OpenOCD...\n
set architecture riscv:rv32
set remotetimeout 30
target extended-remote :3333

echo Connected, waiting...\n
shell sleep 5s

echo Accessing DCCM...\n
set *(0x50000000) = 0xCAFEBABA
set *(0x50000004) = 0xDEADBEEF
set *(0x50000008) = 0xFEEDBACA
set *(0x5000000C) = 0xA5A5A5A5
print/x *0x50000000@4

echo Accessing ICCM...\n
set *(0x40000100) = 0x01234567
set *(0x40000104) = 0x89ABCDEF
set *(0x40000108) = 0x55555555
set *(0x4000010C) = 0xAAAAAAAA
print/x *0x40000100@4

echo Accessing ROM...\n
print/x *0x00000000@8
