# SPDX-License-Identifier: Apache-2.0
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
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

array set exp_data {
    7 0x77777777
    6 0x66666666
    5 0x55555555
    4 0x44444444
    3 0x33333333
    2 0x22222222
    1 0x11111111
    0 0x00000000
}

array set data {
    0 0x77777777
    1 0x66666666
    2 0x55555555
    3 0x44444444
    4 0x33333333
    5 0x22222222
    6 0x11111111
    7 0x00000000
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

puts "Poll mailbox status..."
set status [riscv dmi_read $mbox_status_dmi_addr]
#check if in execute tap state
while {($status & 0x000001C0) != 0x00000140} {
    after 100    ;# Wait 1000ms between polls to avoid busy looping.
    set status [riscv dmi_read $mbox_status_dmi_addr]
}
puts ""

puts "Read mailbox cmd..."
set golden 0xaface0ff
set actual [riscv dmi_read $mbox_cmd_dmi_addr]
if {[compare $actual $golden] != 0} {
    shutdown error
}
puts ""

puts "Read mailbox dlen..."
set golden $dlen_bytes
set actual [riscv dmi_read $mbox_dlen_dmi_addr]
if {[compare $actual $golden] != 0} {
    shutdown error
}
puts ""

puts "Read mailbox data..."
for {set i 0} {$i < $dlen_words} {incr i} {
    set golden $exp_data($i)
    # Check that write is ignored
    if { $i == [expr $dlen_words-1]} {
        riscv dmi_write $mbox_dout_dmi_addr 0xdeadbeef
    }
    set actual [riscv dmi_read $mbox_dout_dmi_addr]
    if {[compare $actual $golden] != 0} {
        shutdown error
    }
}

puts "Write resp to mailbox..."
riscv dmi_write $mbox_cmd_dmi_addr 0x4e110df7
riscv dmi_write $mbox_dlen_dmi_addr $dlen_bytes
for {set i 0} {$i < $dlen_words} {incr i} {
    riscv dmi_write $mbox_din_dmi_addr $data($i)
}
riscv dmi_write $mbox_status_dmi_addr 0x00000001
puts ""

puts "JTAG Mailbox flow 0 completed successfully."

puts "Acquire mailbox lock..."
set lock [riscv dmi_read $mbox_lock_dmi_addr]
#check if in execute tap state
while {($lock & 0x00000001) != 0x00000000} {
    after 100    ;# Wait 1000ms between polls to avoid busy looping.
    set lock [riscv dmi_read $mbox_lock_dmi_addr]
}
puts ""

puts "Write req to mailbox..."
riscv dmi_write $mbox_cmd_dmi_addr 0xaface0ff
riscv dmi_write $mbox_dlen_dmi_addr $dlen_bytes
for {set i 0} {$i < $dlen_words} {incr i} {
    # Check that write is ignored
    if { $i == [expr $dlen_words-1] && [compare [riscv dmi_read $mbox_din_dmi_addr] 0] != 0} {
        shutdown error
    }
    riscv dmi_write $mbox_din_dmi_addr $exp_data($i)
}
puts ""

puts "Set execute..."
riscv dmi_write $mbox_execute_dmi_addr 0x1

puts "Poll mailbox status..."
set status [riscv dmi_read $mbox_status_dmi_addr]
#check if in execute tap state
while {($status & 0x0000000F) != 0x00000001} {
    after 100    ;# Wait 1000ms between polls to avoid busy looping.
    set status [riscv dmi_read $mbox_status_dmi_addr]
}
puts ""

puts "Read mailbox cmd..."
set golden 0x4e110df7
set actual [riscv dmi_read $mbox_cmd_dmi_addr]
if {[compare $actual $golden] != 0} {
    shutdown error
}
puts ""

puts "Read mailbox dlen..."
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

puts "Clear execute..."
riscv dmi_write $mbox_execute_dmi_addr 0x0

puts "JTAG Mailbox flow 1 completed successfully."


puts "Acquire mailbox lock..."
set lock [riscv dmi_read $mbox_lock_dmi_addr]
#check if in execute tap state
while {($lock & 0x00000001) != 0x00000000} {
    after 100    ;# Wait 1000ms between polls to avoid busy looping.
    set lock [riscv dmi_read $mbox_lock_dmi_addr]
}
puts ""

puts "Write req to mailbox..."
riscv dmi_write $mbox_cmd_dmi_addr 0x4e110df7
riscv dmi_write $mbox_dlen_dmi_addr $dlen_bytes
for {set i 0} {$i < $dlen_words} {incr i} {
    riscv dmi_write $mbox_din_dmi_addr $data($i)
}
puts ""

puts "Set execute..."
riscv dmi_write $mbox_execute_dmi_addr 0x1

puts "Poll mailbox status..."
set status [riscv dmi_read $mbox_status_dmi_addr]
#check if in execute tap state
while {($status & 0x0000000F) != 0x00000001} {
    after 100    ;# Wait 1000ms between polls to avoid busy looping.
    set status [riscv dmi_read $mbox_status_dmi_addr]
}
puts ""

puts "Read mailbox cmd..."
set golden 0xaface0ff
set actual [riscv dmi_read $mbox_cmd_dmi_addr]
if {[compare $actual $golden] != 0} {
    shutdown error
}
puts ""

puts "Read mailbox dlen..."
set golden $dlen_bytes
set actual [riscv dmi_read $mbox_dlen_dmi_addr]
if {[compare $actual $golden] != 0} {
    shutdown error
}
puts ""

puts "Read mailbox data..."
for {set i 0} {$i < $dlen_words} {incr i} {
    set golden $exp_data($i)
    set actual [riscv dmi_read $mbox_dout_dmi_addr]
    if {[compare $actual $golden] != 0} {
        shutdown error
    }
}

puts "Clear execute..."
riscv dmi_write $mbox_execute_dmi_addr 0x0

puts "JTAG Mailbox flow 2 completed successfully."

puts "ROM to TAP Mailbox error w/ force unlock test"

puts "Poll mailbox status..."
set status [riscv dmi_read $mbox_status_dmi_addr]
#check if in execute tap state
while {($status & 0x000001C0) != 0x00000140} {
    after 100    ;# Wait 1000ms between polls to avoid busy looping.
    set status [riscv dmi_read $mbox_status_dmi_addr]
}
puts ""

puts "Read mailbox cmd..."
set golden 0xaface0ff
set actual [riscv dmi_read $mbox_cmd_dmi_addr]
if {[compare $actual $golden] != 0} {
    shutdown error
}
puts ""

puts "Read mailbox dlen..."
set golden $dlen_bytes
set actual [riscv dmi_read $mbox_dlen_dmi_addr]
if {[compare $actual $golden] != 0} {
    shutdown error
}
puts ""

puts "Read mailbox data..."
for {set i 0} {$i < $dlen_words} {incr i} {
    set golden $exp_data($i)
    set actual [riscv dmi_read $mbox_dout_dmi_addr]
    if {[compare $actual $golden] != 0} {
        shutdown error
    }
}

puts "Intentionally not setting state done"
puts "Wait for force unlock..."

while {($status & 0x0000000F) != 0x00000000} {
    set status [riscv dmi_read $mbox_status_dmi_addr]
}

after 5000
shutdown
