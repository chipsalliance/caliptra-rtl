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


# init

# # Determine the script directory and source common functions
# set script_dir [file dirname [info script]]
# source [file join $script_dir common.tcl]

# # Define register addresses
# set SS_UDS_SEED_PROGRAMMING_BASE_ADDR_L 0x30030520
# set SS_UDS_SEED_PROGRAMMING_BASE_ADDR_H 0x30030524
# set SS_DBG_MANUF_SERVICE_REG_REQ          0x300305c0
# set SS_DBG_MANUF_SERVICE_REG_RSP          0x300305c4

# # Define the values to write into the seed programming registers.
# # Replace these example values with the appropriate ones.
# set seed_addr_low  0xDEADBEEF
# set seed_addr_high 0xCAFEBABE

# puts "Writing UDS seed programming base addresses..."
# # write_memory $SS_UDS_SEED_PROGRAMMING_BASE_ADDR_L 32 $seed_addr_low phys
# # write_memory $SS_UDS_SEED_PROGRAMMING_BASE_ADDR_H 32 $seed_addr_high phys

# # Write to the debug service register to trigger UDS programming.
# puts "Triggering UDS programming..."
# write_memory $SS_DBG_MANUF_SERVICE_REG_REQ 32 0x4 phys

# # First, confirm that the in-progress flag (bit 9, mask 0x100) is set.
# puts "Polling UDS programming status: waiting for in-progress flag..."
# set status [read_memory $SS_DBG_MANUF_SERVICE_REG_RSP 32 1 phys]
# if {($status & 0x100) == 0} {
#     puts "Expected in-progress flag (bit 9) not set initially. Waiting."
#     while {($status & 0x100) == 0} {
#         after 1000    ;# Wait 1000ms between polls to avoid busy looping.
#         set status [read_memory $SS_DBG_MANUF_SERVICE_REG_RSP 32 1 phys]
#     }
#     puts "Expected in-progress flag (bit 9)"
# }
# else{
#     puts "Expected in-progress flag (bit 9)"
# }

# # Now, continuously poll until the in-progress flag clears.
# while {($status & 0x100) != 0} {
#     after 1000    ;# Wait 1000ms between polls to avoid busy looping.
#     set status [read_memory $SS_DBG_MANUF_SERVICE_REG_RSP 32 1 phys]
# }

# puts "UDS programming in-progress flag cleared. Evaluating result..."

# # After the in-progress flag is cleared, read the response register.
# set rsp_val [read_memory $SS_DBG_MANUF_SERVICE_REG_RSP 32 1 phys]
# # Check for failure (bit 8, mask 0x80) and success (bit 7, mask 0x40).
# set failure [expr {($rsp_val & 0x80) != 0}]
# set success [expr {($rsp_val & 0x40) != 0}]

# if {$failure} {
#     puts "UDS programming failed (failure bit set)."
#     shutdown error
# } elseif {$success} {
#     puts "UDS programming succeeded (success bit set)."
# } else {
#     puts "UDS programming returned an unexpected status: $rsp_val"
#     shutdown error
# }

# puts "UDS programming completed successfully."
# shutdown



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


# Define register addresses
set SS_UDS_SEED_PROGRAMMING_BASE_ADDR_L 0x56
set SS_UDS_SEED_PROGRAMMING_BASE_ADDR_H 0x57
set SS_DBG_MANUF_SERVICE_REG_REQ        0x70
set SS_DBG_MANUF_SERVICE_REG_RSP        0x71

# Define the values to write into the seed programming registers.
# Replace these example values with the appropriate ones.
set seed_addr_low  0xDEADBEEF
set seed_addr_high 0xCAFEBABE

puts "Writing UDS seed programming base addresses..."
riscv dmi_write $SS_UDS_SEED_PROGRAMMING_BASE_ADDR_L $seed_addr_low
riscv dmi_write $SS_UDS_SEED_PROGRAMMING_BASE_ADDR_H $seed_addr_high

# Write to the debug service register to trigger UDS programming.
puts "Triggering UDS programming..."
riscv dmi_write $SS_DBG_MANUF_SERVICE_REG_REQ 0x4
set actual [riscv dmi_read $SS_DBG_MANUF_SERVICE_REG_REQ]
puts "SS_DBG_MANUF_SERVICE_REG_REQ: $actual"

# Polling UDS programming status
puts "Polling UDS programming status: waiting for in-progress flag..."
set status [riscv dmi_read $SS_DBG_MANUF_SERVICE_REG_RSP]
puts "Expected in-progress flag (bit 9) not set initially. Waiting."
while {([expr {$status & 0x100}] == 0)} {    
    after 100
    set status [riscv dmi_read $SS_DBG_MANUF_SERVICE_REG_RSP]
}

puts "In-progress flag set. Programming complete."

# Now, continuously poll until the in-progress flag clears.
while {($status & 0x100) != 0} {
    after 100    ;# Wait 1000ms between polls to avoid busy looping.
    set status [riscv dmi_read $SS_DBG_MANUF_SERVICE_REG_RSP]
}

puts "UDS programming in-progress flag cleared. Evaluating result..."

# After the in-progress flag is cleared, read the response register.
set rsp_val [riscv dmi_read $SS_DBG_MANUF_SERVICE_REG_RSP]
# Check for failure (bit 8, mask 0x80) and success (bit 7, mask 0x40).
set failure [expr {($rsp_val & 0x80) != 0}]
set success [expr {($rsp_val & 0x40) != 0}]

if {$failure} {
    puts "UDS programming failed (failure bit set)."
    shutdown error
} elseif {$success} {
    puts "UDS programming succeeded (success bit set)."
} else {
    puts "UDS programming returned an unexpected status: $rsp_val"
    shutdown error
}

puts "UDS programming completed successfully."
shutdown