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
proc compare {x y} {
    puts "'$x' vs. '$y'"

    if {[llength $y] != [llength $y]} {
        puts "length mismatch!"
        return -1
    }

    for {set i 0} {$i < [llength $x]} {incr i} {
        if {[lindex $x $i] != [lindex $y $i]} {
            puts "item $i mismatch!"
            return -1
        }
    }

    return 0
}

set STDOUT 0x300300cc

set mbox_clk_gate_en 0xf2
set mbox_lock_debug 0xf9
set mbox_unlock_debug 0xfa

set mbox_lock_mem_addr 0x30020000
set mbox_user_mem_addr 0x30020004
set mbox_cmd_mem_addr 0x30020008
set mbox_dlen_mem_addr 0x3002000C
set mbox_datain_mem_addr 0x30020010
set mbox_dataout_mem_addr 0x30020014
set mbox_execute_mem_addr 0x30020018
set mbox_status_mem_addr 0x3002001C
set mbox_unlock_mem_addr 0x30020020

set mbox_dlen_dmi_addr 0x50
set mbox_dout_dmi_addr 0x51
set mbox_status_dmi_addr 0x52

set dmstatus_addr 0x11

