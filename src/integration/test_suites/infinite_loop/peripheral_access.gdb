echo Connecting to OpenOCD...\n
set architecture riscv:rv32
set remotetimeout 30
target extended-remote :3333

echo Connected, waiting...\n
shell sleep 5s

echo Accessing ECC...\n
print/x *0x10008000@2
print/x *0x10008008@2

echo Accessing HMAC...\n
print/x *0x10010000@2
print/x *0x10010008@2

echo Accessing SHA512...\n
print/x *0x10020000@2
print/x *0x10020008@2

echo Accessing SHA256...\n
print/x *0x10028000@2
print/x *0x10028008@2

echo Writing and reading DOE IV...\n
set *(0x10000000) = 0xCAFEBABA
set *(0x10000004) = 0xDEADBEEF
set *(0x10000008) = 0xD0ED0E00
print/x *0x10000000@3

