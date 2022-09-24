# SPDX-License-Identifier: Apache-2.0
# Copyright 2022 Microsoft Corporation or its affiliates.
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
#Synopsys DC setup
#Design: Caliptra

#----------------------------
#Set libraries
#TODO: Add the correct libs
#----------------------------
set target_library [list /home/shared/hardware/common/technology/lib_data/tsmc/tsmc005ff/stdcell/H210/tcbn05_bwph210l6p51cnod_base_svt/110a/TSMCHOME/digital/Front_End/timing_power_noise/CCS/tcbn05_bwph210l6p51cnod_base_svt_110a/tcbn05_bwph210l6p51cnod_base_svttt_0p75v_85c_typical_ccs.db]
set mw_reference_library [list /home/shared/hardware/common/technology/lib_data/tsmc/tsmc005ff/stdcell/H210/tcbn05_bwph210l6p51cnod_base_svt/110a/TSMCHOME/digital/Back_End/milkyway/tcbn05_bwph210l6p51cnod_base_svt_110a]
set max_library [list ]
set min_library [list ]
set synthetic_library [list dw_foundation.sldb]
set link_library [list $target_library $synthetic_library]

#----------------------------
#Set design name and units of measurement
#----------------------------
set DESIGN_NAME $design
set_units -time ns -resistance kOhm -capacitance pF -voltage V -current mA

#----------------------------
#Analyze RTL files 
#----------------------------
analyze -format sverilog -vcs "-f $design.vf"

#----------------------------
#Elaborate, link and uniquify
#----------------------------
set command_status [elaborate $DESIGN_NAME -architecture verilog -library WORK -update]
if ($command_status==0) {quit}
set command_status [link]
if ($command_status==0) {quit}
set command_status [uniquify]
if ($command_status==0) {quit}

#----------------------------
#Set operating conditions
#----------------------------
#set command_status [set_operating_conditions -min_library $target_library -min nom_pvt -max_library $target_library -max nom_pvt]
#if ($command_status==0) {quit}

#----------------------------
#Specify clock attributes
#----------------------------
set command_status [create_clock -name "clk" -period 2 -waveform {0 1} {clk}]
if ($command_status==0) {quit}
set command_status [set_clock_uncertainty 0.4 [get_clocks clk]]
set command_status [set_clock_latency 0.2 [get_clocks clk]]
set command_status [set_input_transition -max 0.01 [all_inputs]]

#----------------------------
#Specify wire load model and max fanout
#----------------------------
set command_status [set_wire_load_mode top]
#set command_status [set_wire_load_model -name 90x90]
#if ($command_status==0) {quit}
set command_status [set_max_fanout 5000 [get_designs $DESIGN_NAME]]
#this isn't working
#set_app_var compile_enable_report_transformed_registers true

#----------------------------
#Compile design
#----------------------------
set command_status [compile -exact_map -map_effort medium -area_effort medium -power_effort medium -boundary_optimization]
if ($command_status==0) {quit}

#----------------------------
#Export files
#----------------------------
exec mkdir reports
cd reports

write -format verilog -hierarchy -output ${DESIGN_NAME}.netlist.v
write_sdc "dcon.sdc"
write_sdf "delay.sdf"
report_area -physical > ${DESIGN_NAME}.area.rpt
report_area -physical -hierarchy > ${DESIGN_NAME}.area.hier.rpt
report_qor -nosplit > ${DESIGN_NAME}.qor.rpt
report_timing -variation -derate -transition_time -nets -cap -inp -attributes -start_end_pair -sig 3 -max_paths 100 -sort_by slack > ${DESIGN_NAME}.timing.rpt

#Report Latches               
if {[sizeof_collection [all_registers -level_sensitive]] != 0} {
    report_cell [all_registers -level_sensitive ] -nosplit > ${DESIGN_NAME}.mapped.latches.rpt
} else {
    echo "Total 0 cells" > ${DESIGN_NAME}.mapped.latches.rpt
} 

#Reports Const Registers
#DC isn't supporting this command, find another way
#report_transformed_registers -constant -unloaded > ${DESIGN_NAME}.optimized.registers.rpt

cd ../
set mr_files [glob *.mr]
set syn_files [glob *.syn]
set pvl_files [glob *.pvl]
set pvk_files [glob *.pvk]
foreach f $mr_files {
	exec rm $f
}
foreach f $syn_files {
	exec rm $f
}
foreach f $pvl_files {
	exec rm $f
}
foreach f $pvk_files {
	exec rm $f
}
exec rm default.svf

exit
