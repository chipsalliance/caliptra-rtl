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

set dmstatus_addr 0x11

#dmi register addresses
set mbox_dlen_dmi_addr 0x50
set mbox_dout_dmi_addr 0x51
set mbox_status_dmi_addr 0x52

#Uncore DMI Register encodings
#Mailbox registers
set dmi_reg_mbox_dout 0x51;
set dmi_reg_mbox_dlen 0x50;
set dmi_reg_mbox_din 0x62;
set dmi_reg_mbox_status 0x52;
set dmi_reg_mbox_lock 0x75;
set dmi_reg_mbox_cmd 0x76;
set dmi_reg_mbox_execute 0x77;

#Read only registers
set dmi_reg_boot_status 0x53;
set dmi_reg_cptra_hw_errror_enc 0x54;
set dmi_reg_cptra_fw_error_enc 0x55;
set dmi_reg_ss_uds_seed_base_addr_l 0x56;
set dmi_reg_ss_uds_seed_base_addr_h 0x57;
set dmi_reg_hw_fatal_error 0x58;
set dmi_reg_fw_fatal_error 0x59;
set dmi_reg_hw_non_fatal_error 0x5a;
set dmi_reg_fw_non_fatal_error 0x5b;

set mem_reg_boot_status 0x30030038;
set mem_reg_cptra_hw_errror_enc 0x30030010;
set mem_reg_cptra_fw_error_enc 0x30030014;
set mem_reg_ss_uds_seed_base_addr_l 0x30030520;
set mem_reg_ss_uds_seed_base_addr_h 0x30030524;
set mem_reg_hw_fatal_error 0x30030000;
set mem_reg_fw_fatal_error 0x30030008;
set mem_reg_hw_non_fatal_error 0x30030004;
set mem_reg_fw_non_fatal_error 0x3003000c;

#RW registers
set dmi_reg_cptra_dbg_manuf_service_reg 0x60;
set dmi_reg_bootfsm_go 0x61;
set dmi_reg_ss_debug_intent 0x63;
set dmi_reg_ss_caliptra_base_addr_l 0x64;
set dmi_reg_ss_caliptra_base_addr_h 0x65;
set dmi_reg_ss_mci_base_addr_l 0x66;
set dmi_reg_ss_mci_base_addr_h 0x67;
set dmi_reg_ss_recovery_ifc_base_addr_l 0x68;
set dmi_reg_ss_recovery_ifc_base_addr_h 0x69;
set dmi_reg_ss_otp_fc_base_addr_l 0x6a;
set dmi_reg_ss_otp_fc_base_addr_h 0x6b;
set dmi_reg_ss_strap_generic_0 0x6c;
set dmi_reg_ss_strap_generic_1 0x6d;
set dmi_reg_ss_strap_generic_2 0x6e;
set dmi_reg_ss_strap_generic_3 0x6f;
set dmi_reg_ss_dbg_manuf_service_reg_req 0x70;
set dmi_reg_ss_dbg_manuf_service_reg_rsp 0x71;
set dmi_reg_ss_dbg_unlock_level0 0x72;
set dmi_reg_ss_dbg_unlock_level1 0x73;
set dmi_reg_ss_strap_caliptra_dma_axi_user 0x74;


