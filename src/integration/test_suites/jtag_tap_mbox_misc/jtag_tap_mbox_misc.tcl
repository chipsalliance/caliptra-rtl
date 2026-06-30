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

# Test 1
puts "Acquire mailbox lock..."
set lock [riscv dmi_read $mbox_lock_dmi_addr]
# Check if in execute tap state
while {($lock & 0x00000001) != 0x00000000} {
    after 100; # Wait 100ms between polls to avoid busy looping.
    set lock [riscv dmi_read $mbox_lock_dmi_addr]
}
puts ""

puts "SoC mailbox access req while TAP locks it completed successfully"

# Test 2
puts "Acquire mailbox lock..."
set lock [riscv dmi_read $mbox_lock_dmi_addr]
#check if in execute tap state
while {($lock & 0x00000001) != 0x00000000} {
    after 100; # Wait 100ms between polls to avoid busy looping.
    set lock [riscv dmi_read $mbox_lock_dmi_addr]
}
puts ""

puts "Write req to mailbox..."
riscv dmi_write $mbox_cmd_dmi_addr 0xaface0ff
riscv dmi_write $mbox_dlen_dmi_addr $dlen_bytes
for {set i 0} {$i < $dlen_words} {incr i} {
    riscv dmi_write $mbox_din_dmi_addr $exp_data($i)
}
puts ""

puts "Set execute..."
riscv dmi_write $mbox_execute_dmi_addr 0x1

puts "Poll mailbox status..."
set status [riscv dmi_read $mbox_status_dmi_addr]
#check if in execute tap state
while {($status & 0x0000000F) != 0x00000001} {
    after 100; # Wait 100ms between polls to avoid busy looping.
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

# Test 3
puts "Poll mailbox status..."
set status [riscv dmi_read $mbox_status_dmi_addr]
#check if in ready for data state
while {($status & 0x000001C0) != 0x00000080} {
    after 100; # Wait 100ms between polls to avoid busy looping.
    set status [riscv dmi_read $mbox_status_dmi_addr]
}
puts ""

puts "Writing to mbox without TAP lock"
riscv dmi_write $mbox_din_dmi_addr 0x0

puts "Poll mailbox status..."
set status [riscv dmi_read $mbox_status_dmi_addr]
#check if in execute tap state
while {($status & 0x000001C0) != 0x00000140} {
    after 100; # Wait 100ms between polls to avoid busy looping.
    set status [riscv dmi_read $mbox_status_dmi_addr]
}
puts ""

puts "Poll mailbox TAP mode..."
set tap_mode [read_memory $mbox_tap_mode_mem_addr 32 1 phys]
set tap_mode [expr {[lindex $tap_mode 0] & 0x1}]
set cmp_tap_mode {0x0}
# Wait for uC to disable TAP mode
while {[compare $tap_mode $cmp_tap_mode] != 0} {
    puts "CMP FAILED"
    after 100; # Wait 100ms between polls to avoid busy looping.
    set tap_mode [read_memory $mbox_tap_mode_mem_addr 32 1 phys]
    set tap_mode [expr {[lindex $tap_mode 0] & 0x1}]
}
puts ""

puts "Write resp to mailbox..."
riscv dmi_write $mbox_cmd_dmi_addr 0x4e110df7
riscv dmi_write $mbox_dlen_dmi_addr $dlen_bytes
for {set i 0} {$i < $dlen_words} {incr i} {
    riscv dmi_write $mbox_din_dmi_addr $data($i)
}
puts ""

puts "Set status to data ready"
riscv dmi_write $mbox_status_dmi_addr 0x1

puts "Poll mailbox TAP mode..."
set tap_mode [read_memory $mbox_tap_mode_mem_addr 32 1 phys]
set tap_mode [expr {[lindex $tap_mode 0] & 0x1}]
set cmp_tap_mode {0x1}
# Wait for uC to enable TAP mode
while {[compare $tap_mode $cmp_tap_mode] != 0} {
    after 100; # Wait 100ms between polls to avoid busy looping.
    set tap_mode [read_memory $mbox_tap_mode_mem_addr 32 1 phys]
    set tap_mode [expr {[lindex $tap_mode 0] & 0x1}]
}
puts ""

# Test 4
puts "Wait for mailbox to enter IDLE state..."
set status [riscv dmi_read $mbox_status_dmi_addr]
# Wait until mbox enters IDLE state
while {($status & 0x000001C0) != 0x00000000} {
    after 100; # Wait 100ms between polls to avoid busy looping.
    set status [riscv dmi_read $mbox_status_dmi_addr]
}
puts ""

puts "Wait for mailbox to leave IDLE state (FW locks)..."
set status [riscv dmi_read $mbox_status_dmi_addr]
# Wait until mbox enters IDLE state
while {($status & 0x000001C0) == 0x00000000} {
    after 100; # Wait 100ms between polls to avoid busy looping.
    set status [riscv dmi_read $mbox_status_dmi_addr]
}
puts ""

puts "Wait for mailbox to enter IDLE state (FW forces unlock)..."
set status [riscv dmi_read $mbox_status_dmi_addr]
# Wait until mbox enters IDLE state
while {($status & 0x000001C0) != 0x00000000} {
    after 100; # Wait 100ms between polls to avoid busy looping.
    set status [riscv dmi_read $mbox_status_dmi_addr]
}
puts ""

puts "Test 5: uC to SoC Mailbox with TAP dataout steal test"

# wait for EXECUTE_UC state
set status [riscv dmi_read $mbox_status_dmi_addr]
while {($status & 0x000001C0) != (0x6 << 6)} {
    after 100
    set status [riscv dmi_read $mbox_status_dmi_addr]
}

# steal and verify single value from dataout (SoC -> uC)
if {[compare [riscv dmi_read $mbox_dout_dmi_addr] 0x0] != 0} {
    shutdown error
}

# wait for EXECUTE_SOC state
set status [riscv dmi_read $mbox_status_dmi_addr]
while {($status & 0x000001C0) != (0x4 << 6)} {
    after 100
    set status [riscv dmi_read $mbox_status_dmi_addr]
}

# steal and verify single value from dataout (uC -> SoC)
if {[compare [riscv dmi_read $mbox_dout_dmi_addr] 0x77777777] != 0} {
    shutdown error
}

puts "uC to SoC Mailbox with TAP dataout steal completed successfully"

# Test 6 <- This test must be last since FW disables JTAG to execute it and
#           there is no way to synchronize between JTAG and FW again
#           This test expects mailbox to be initially in IDLE state

# Try to write from TAP
puts "Write to mbox"
riscv dmi_write $mbox_cmd_dmi_addr 0x0
riscv dmi_write $mbox_dlen_dmi_addr 0x0
riscv dmi_write $mbox_status_dmi_addr 0x0
riscv dmi_write $mbox_execute_dmi_addr 0x0
puts ""

puts "Acquire mailbox lock..."
set lock [riscv dmi_read $mbox_lock_dmi_addr]
while {($lock & 0x00000001) != 0x00000000} {
    after 100; # Wait 100ms between polls to avoid busy looping.
    set lock [riscv dmi_read $mbox_lock_dmi_addr]
}
puts ""

# Wait for uC to make mbox TAP unavailable
puts "Poll mbox avail..."
set mbox_avail [read_memory $soc_ifc_dbg_manuf_service_mem_addr 32 1 phys]
set mbox_avail [expr {[lindex $mbox_avail 0] & 0x1}]
set cmp_mbox_avail {0x0}
while {[compare $mbox_avail $cmp_mbox_avail] != 0} {
    after 100; # Wait 100ms between polls to avoid busy looping.
    set mbox_avail [read_memory $soc_ifc_dbg_manuf_service_mem_addr 32 1 phys]
    set mbox_avail [expr {[lindex $mbox_avail 0] & 0x1}]
}
puts ""

# Try to write from TAP
puts "Write to mbox"
riscv dmi_write $mbox_cmd_dmi_addr 0x0
riscv dmi_write $mbox_dlen_dmi_addr 0x0
riscv dmi_write $mbox_status_dmi_addr 0x0
riscv dmi_write $mbox_execute_dmi_addr 0x0
puts ""

shutdown
