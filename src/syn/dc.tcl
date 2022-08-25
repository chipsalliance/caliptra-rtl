#Synopsys DC setup
#Design: Caliptra
#Authors: Steven Lian and Kiran Upadhyayula

#----------------------------
#Set libraries
#TODO: Add the correct libs
#----------------------------
set target_library [list lsi_10k.db]
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
analyze -format sverilog { \
../hmac/rtl/hmac_ctrl.sv \
../hmac/rtl/hmac_core.v \
../hmac/rtl/hmac_param.sv \
../hmac/rtl/hmac.v \
../sha512/rtl/sha512.v \
../sha512/rtl/sha512_core.v \
../sha512/rtl/sha512_param.sv \
../sha512/rtl/sha512_w_mem.v \
../sha512/rtl/sha512_k_constants.v \
../sha512/rtl/sha512_h_constants.v \
../sha512/rtl/sha512_ctrl.sv \
../libs/rtl/ahb_slv_sif.sv \
../aes/rtl/aes_ctrl.sv \
../aes/rtl/aes.v \
../aes/rtl/aes_param.sv \
../aes/rtl/aes_core.v \
../aes/rtl/aes_decipher_block.v \
../aes/rtl/aes_encipher_block.v \
../aes/rtl/aes_inv_sbox.v \
../aes/rtl/aes_key_mem.v \
../aes/rtl/aes_sbox.v \
../aes/rtl/aes_cbc.v \
../aes/rtl/aes_core_cbc.v \
../ahb_lite_bus/rtl/ahb_bus.sv \
../ahb_lite_bus/rtl/ahb_node.sv \
../ahb_lite_bus/rtl/ahb_node_wrap.sv \
../ecc/rtl/ecc_arith_unit.sv \
../ecc/rtl/ecc_ctrl.sv \
../ecc/rtl/ecc_uop.sv \
../ecc/rtl/ecc_sequencer.sv \
../ecc/rtl/fau.sv \
../ecc/rtl/MontgomeryMultiplier.sv \
../ecc/rtl/PE_first.sv \
../ecc/rtl/PE.sv \
../ecc/rtl/PE_final.sv \
../ecc/rtl/mult_dsp.sv \
../ecc/rtl/add_sub_mod_alter.sv \
../ecc/rtl/add_sub_mod.sv \
../ecc/rtl/add_sub_gen.sv \
../ecc/rtl/adder.sv \
../ecc/rtl/expand.sv \
../ecc/rtl/compact.sv \
../ecc/rtl/ram_tdp_file.sv \
../hmac_drbg/rtl/hmac_drbg.v \
../hmac_drbg/rtl/hmac_drbg_param.sv \
../libs/rtl/caliptra_sram.sv \
../libs/rtl/caliptra_ahb_srom.sv \
../libs/rtl/apb_slv_sif.sv \
../mbox/rtl/mbox_csr_pkg.sv \
../mbox/rtl/mbox_reg_pkg.sv \
../mbox/rtl/mbox_top.sv \
../mbox/rtl/mbox.sv \
../mbox/rtl/mbox_boot_fsm.sv \
../mbox/rtl/mbox_arb.sv \
../mbox/rtl/mbox_csr.sv \
../mbox/rtl/mbox_reg.sv \
../sha256/rtl/sha256_ctrl.sv \
../sha256/rtl/sha256.v \
../sha256/rtl/sha256_param.sv \
../sha256/rtl/sha256_core.v \
../sha256/rtl/sha256_k_constants.v \
../sha256/rtl/sha256_w_mem.v
}

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
set command_status [set_operating_conditions -min_library lsi_10k -min nom_pvt -max_library lsi_10k -max nom_pvt]
if ($command_status==0) {quit}

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

#----------------------------
#Compile design
#----------------------------
set command_status [compile -exact_map -map_effort medium -area_effort medium -power_effort medium -boundary_optimization]
if ($command_status==0) {quit}

#----------------------------
#Export files
#----------------------------
exec mkdir -p -- outputs/$DESIGN_NAME
cd outputs/$DESIGN_NAME
#set command_status [write -format verilog -hierarchy -output "./outputs/hmac_ctrl_postsyn.v"]
#set command_status [write_sdc "/home/kupadhyayula/caliptra/ws1/Caliptra/src/hmac/syn/outputs/hmac_ctrl_postsyn.sdc"]
#set command_status [write_sdf -version 1.0 "/home/kupadhyayula/caliptra/ws1/Caliptra/src/hmac/syn/outputs/hmac_ctrl_postsyn.sdf"]
#set command_status [report_area > /home/kupadhyayula/caliptra/ws1/Caliptra/src/hmac/syn/outputs/area.rpt]
#set command_status [report_timing -max_paths 100 > /home/kupadhyayula/caliptra/ws1/Caliptra/src/hmac/syn/outputs/timing.rpt]
set command_status [write -format verilog -hierarchy -output "netlist.v"]
set command_status [write_sdc "dcon.sdc"]
set command_status [write_sdf "delay.sdf"]
set command_status [report_area > "area.rpt"]
set command_status [report_timing > "timing.rpt"]
cd ../..
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
