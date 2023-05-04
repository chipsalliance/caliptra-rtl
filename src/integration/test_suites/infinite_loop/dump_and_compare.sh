#!/bin/bash
set -ex

# Invoke GDB and dump core registers
riscv64-unknown-elf-gdb -n --batch -x dump_registers.gdb >gdb.log
# Parse the log, extract register values. Skip those which change as the 
# program executes since we don't know at which point we tap in.
cat gdb.log | grep -E '^ra |^sp |^gp |^tp |^t[01256] |^s[0-9]+ |^a[0-9]+ ' >regdump.txt

# Compare the dumps
diff -E -y regdump_golden.txt regdump.txt

