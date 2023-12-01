# SPDX-License-Identifier: Apache-2.0
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
# http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#
init

set script_dir [file dirname [info script]]
source [file join $script_dir common.tcl]

array set data {
    0 0x12345678
    1 0xABBACDDC
    2 0xDEADBEEF
    3 0xFEEDBABE
    4 0xBEACCAEB
}
set dlen_words [array size data]
set dlen_bytes [expr {$dlen_words * 4}]

puts "Read Debug Module Status Register..."
set val [riscv dmi_read $dmstatus_addr]
puts "dmstatus: $val"
if {($val & 0x00000c00) == 0} {
    echo "The hart is halted!"
    shutdown error
}
puts ""

riscv set_mem_access sysbus
puts "Enable clock gating..."
write_memory $STDOUT 32 $mbox_clk_gate_en phys

puts "Set debug security state to locked..."
write_memory $STDOUT 32 $mbox_lock_debug phys
puts ""

puts "Retrieve mailbox lock..."
set golden {0x0}
set actual [read_memory $mbox_lock_mem_addr 32 1 phys]
if {[compare $actual $golden] != 0} {
    shutdown error
}
puts ""

puts "Write few bytes to mailbox..."
write_memory $mbox_cmd_mem_addr 32 0x12345678 phys
write_memory $mbox_dlen_mem_addr 32 $dlen_bytes phys
for {set i 0} {$i < $dlen_words} {incr i} {
    write_memory $mbox_datain_mem_addr 32 $data($i) phys
}
write_memory $mbox_execute_mem_addr 32 1 phys
puts ""

puts "Read mailbox status..."
set golden {0x500}
set actual [read_memory $mbox_status_mem_addr 32 1 phys]
if {[compare $actual $golden] != 0} {
    shutdown error
}
puts ""

puts "Halt CPU to access its registers..."
halt
puts "Initiate firmware halt (set register s1 to 0)..."
set_reg {s1 0}
puts "Resume CPU..."
resume
puts ""

puts "Read Debug Module Status Register..."
set val [riscv dmi_read $dmstatus_addr]
puts "dmstatus: $val"
if {($val & 0x00000c00) == 0} {
    echo "The hart is halted!"
    shutdown error
}
puts ""

puts "Read mailbox status and dlen..."
set golden $dlen_bytes
set actual [riscv dmi_read $mbox_dlen_dmi_addr]
if {[compare $actual $golden] != 0} {
    shutdown error
}
puts ""

puts "Read mailbox data..."
for {set i 0} {$i < $dlen_words} {incr i} {
    set golden $data($i)
    set actual [riscv dmi_read $mbox_dout_dmi_addr]
    if {[compare $actual $golden] != 0} {
        shutdown error
    }
}

# Success
shutdown
