#!/bin/bash
set -ex

# Invoke GDB
riscv64-unknown-elf-gdb -n --batch -x mem_access.gdb >gdb.log
# Parse the log
cat gdb.log | grep -E '^\$[0-9]+' >out.txt

# Compare the dumps
diff -E -y mem_access_golden.txt out.txt

