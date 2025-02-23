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

set retry_count 100

set bootfsm_go_addr 0x61
set dmstatus_addr 0x11

set mbox_dlen_addr 0x50
set mbox_dout_addr 0x51
set mbox_status_addr 0x52

set dmstatus_rst_mask 0x000c0000
set dmstatus_run_mask 0x00000c00

puts "Disable Boot FSM GO"
riscv dmi_write $bootfsm_go_addr 0x0

puts "Wait for CPU to enter reset state..."
for {set x 0} {$x < $retry_count} {incr x} {
    set status_val [riscv dmi_read $dmstatus_addr]
    if {($status_val & $dmstatus_rst_mask) == $dmstatus_rst_mask} {
        puts "CPU in reset, enable Boot FSM GO"
        riscv dmi_write $bootfsm_go_addr 0x1
        break
    }
    if {$x == ($retry_count - 1)} {
        puts "Timeout"
        shutdown error
    }
}

for {set x 0} {$x < $retry_count} {incr x} {
    set status_val [riscv dmi_read $dmstatus_addr]
    if {($status_val & $dmstatus_run_mask) == $dmstatus_run_mask} {
        puts "CPU running, wait for test suite finish..."
        break
    }
    if {$x == ($retry_count - 1)} {
        puts "Timeout"
        shutdown error
    }
}

for {set x 0} {$x<$retry_count} {incr x} {
    set mbox_dlen_val [riscv dmi_read $mbox_dlen_addr]
    set mbox_status_val [riscv dmi_read $mbox_status_addr]
    if {($mbox_status_val == 0x500) && ($mbox_dlen_val == 1)} {
        set mbox_dout_val [riscv dmi_read $mbox_dout_addr]
        if {($mbox_dout_val == 1)} {
            puts "Test suite finished, success"
            shutdown
        }
    }
}

puts "CPU reset failed"
shutdown error
