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

#dmi_reg_bootfsm_go  only 1 bit
#dmi_reg_ss_debug_intent  only 1 bit
#dmi_reg_ss_dbg_manuf_service_reg_req  special access
#dmi_reg_ss_dbg_manuf_service_reg_rsp  read only

#can't be written by FW to test
# dmi_reg_ss_uds_seed_base_addr_l
# dmi_reg_ss_uds_seed_base_addr_h
# dmi_reg_hw_fatal_error
# dmi_reg_hw_non_fatal_error

array set rw_regs {
    0 dmi_reg_cptra_dbg_manuf_service_reg
    1 dmi_reg_ss_caliptra_base_addr_l
    2 dmi_reg_ss_caliptra_base_addr_h
    3 dmi_reg_ss_mci_base_addr_l
    4 dmi_reg_ss_mci_base_addr_h
    5 dmi_reg_ss_recovery_ifc_base_addr_l
    6 dmi_reg_ss_recovery_ifc_base_addr_h
    7 dmi_reg_ss_otp_fc_base_addr_l
    7 dmi_reg_ss_otp_fc_base_addr_h
    8 dmi_reg_ss_strap_generic_0
    9 dmi_reg_ss_strap_generic_1
    10 dmi_reg_ss_strap_generic_2
    11 dmi_reg_ss_strap_generic_3
    12 dmi_reg_ss_dbg_unlock_level0
    13 dmi_reg_ss_dbg_unlock_level1
    14 dmi_reg_ss_strap_caliptra_dma_axi_user
    15 dmi_reg_ss_external_staging_area_base_addr_l
    16 dmi_reg_ss_external_staging_area_base_addr_h
}

array set ro_regs {
    0 dmi_reg_boot_status
    1 dmi_reg_cptra_hw_errror_enc
    2 dmi_reg_cptra_fw_error_enc
    3 dmi_reg_fw_fatal_error
    4 dmi_reg_fw_non_fatal_error
}

array set ro_regs_mem {
    0 mem_reg_boot_status
    1 mem_reg_cptra_hw_errror_enc
    2 mem_reg_cptra_fw_error_enc
    3 mem_reg_fw_fatal_error
    4 mem_reg_fw_non_fatal_error
}

set num_rw_regs [array size rw_regs]
set num_ro_regs [array size ro_regs]
set num_ro_regs_mem [array size ro_regs_mem]

puts "Read Debug Module Status Register..."
set val [riscv dmi_read $dmstatus_addr]
puts "dmstatus: $val"
if {($val & 0x00000c00) == 0} {
    echo "The hart is halted!"
    shutdown error
}
puts ""

riscv set_mem_access sysbus

set golden5a {0x5a5a5a5a}
set goldena5 {0xa5a5a5a5}

puts "Checking the writable registers..."
for {set i 0} {$i < $num_rw_regs} {incr i} {
    #write golden5a
    riscv dmi_write [set $rw_regs($i)] $golden5a
    set actual [riscv dmi_read [set $rw_regs($i)]]
    if {[compare $actual $golden5a] != 0} {
        shutdown error
    }
    #write goldena5
    riscv dmi_write [set $rw_regs($i)] $goldena5
    set actual [riscv dmi_read [set $rw_regs($i)]]
    if {[compare $actual $goldena5] != 0} {
        shutdown error
    }
    #write variable
    riscv dmi_write [set $rw_regs($i)] $i$i$i
    set actual [riscv dmi_read [set $rw_regs($i)]]
    if {[compare $actual $i$i$i] != 0} {
        shutdown error
    }
}

puts "Reading the writable registers again..."
for {set i 0} {$i < $num_rw_regs} {incr i} {
    set golden $i$i$i
    set actual [riscv dmi_read [set $rw_regs($i)]]
    if {[compare $actual $golden] != 0} {
        shutdown error
    }
}

#Check read only registers
puts "Checking the read only registers..."
for {set i 0} {$i < $num_ro_regs} {incr i} {
    #write golden5a
    riscv dmi_write [set $ro_regs($i)] $golden5a
    set actual [riscv dmi_read [set $ro_regs($i)]]
    if {[compare $actual 0] != 0} {
        shutdown error
    }
    #write goldena5
    riscv dmi_write [set $ro_regs($i)] $goldena5
    set actual [riscv dmi_read [set $ro_regs($i)]]
    if {[compare $actual 0] != 0} {
        shutdown error
    }
}

#Write RO from uc and read back on dmi
puts "Checking the read only registers..."
for {set i 0} {$i < $num_ro_regs_mem} {incr i} {
    #write golden5a
    write_memory [set $ro_regs_mem($i)] 32 $golden5a phys
    set actual [riscv dmi_read [set $ro_regs($i)]]
    if {[compare $actual $golden5a] != 0} {
        #shutdown error
    }
    #write goldena5
    write_memory [set $ro_regs_mem($i)] 32 $goldena5 phys
    set actual [riscv dmi_read [set $ro_regs($i)]]
    if {[compare $actual $goldena5] != 0} {
        #shutdown error
    }
}

# Success
shutdown
