

##################################################################
## ENVIRONMENT VARIABLES
##################################################################
quietly set ::env(UVMF_VIP_LIBRARY_HOME) ../../../verification_ip
quietly set ::env(UVMF_PROJECT_DIR) ..

## Using VRM means that the build is occuring several more directories deeper underneath
## the sim directory, need to prepend some more '..'
if {[info exists ::env(VRM_BUILD)]} {
  quietly set ::env(UVMF_VIP_LIBRARY_HOME) "../../../../../$::env(UVMF_VIP_LIBRARY_HOME)"
  quietly set ::env(UVMF_PROJECT_DIR) "../../../../../$::env(UVMF_PROJECT_DIR)"
}
quietly set ::env(UVMF_VIP_LIBRARY_HOME) [file normalize $::env(UVMF_VIP_LIBRARY_HOME)]
quietly set ::env(UVMF_PROJECT_DIR) [file normalize $::env(UVMF_PROJECT_DIR)]
quietly echo "UVMF_VIP_LIBRARY_HOME = $::env(UVMF_VIP_LIBRARY_HOME)"
quietly echo "UVMF_PROJECT_DIR = $::env(UVMF_PROJECT_DIR)"


###################################################################
## HOUSEKEEPING : DELETE FILES THAT WILL BE REGENERATED
###################################################################
file delete -force *~ *.ucdb vsim.dbg *.vstf *.log work *.mem *.transcript.txt certe_dump.xml *.wlf covhtmlreport VRMDATA
file delete -force design.bin qwave.db dpiheader.h visualizer*.ses
file delete -force veloce.med veloce.wave veloce.map tbxbindings.h edsenv velrunopts.ini
file delete -force sv_connect.*

###################################################################
## COMPILE DUT SOURCE CODE
###################################################################
vlib work 
# pragma uvmf custom dut_compile_dofile_target begin
# UVMF_CHANGE_ME : Add commands to compile your dut here, replacing the default examples
#vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/rtl/verilog/verilog_dut.v
#vcom $env(UVMF_PROJECT_DIR)/rtl/vhdl/vhdl_dut.vhd

vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../libs/rtl/caliptra_sva.svh
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../keyvault/rtl/kv_defines.svh
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../hmac_drbg/rtl/hmac_drbg_param.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../hmac_drbg/rtl/hmac_drbg.v
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../hmac/rtl/hmac_core.v
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../hmac/rtl/hmac_ctrl.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../hmac/rtl/hmac_param.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../hmac/rtl/hmac.v
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../rtl/ecc_defines.svh
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../rtl/ecc_params.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../rtl/ecc_reg_pkg.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../rtl/ecc_top.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../rtl/ecc_reg.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../rtl/ecc_dsa_ctrl.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../rtl/ecc_dsa_sequencer.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../rtl/ecc_dsa_uop.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../rtl/ecc_fixed_msb.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../rtl/ecc_arith_unit.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../rtl/ecc_pm_ctrl.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../rtl/ecc_pm_uop.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../rtl/ecc_pm_sequencer.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../rtl/ecc_ram_tdp_file.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../rtl/ecc_fau.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../rtl/ecc_montgomerymultiplier.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../rtl/ecc_pe_first.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../rtl/ecc_pe.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../rtl/ecc_pe_final.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../rtl/ecc_mult_dsp.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../rtl/ecc_add_sub_mod_alter.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../rtl/ecc_adder.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../libs/rtl/ahb_slv_sif.sv

# pragma uvmf custom dut_compile_dofile_target end

###################################################################
## COMPILE UVMF BASE/COMMON SOURCE CODE
###################################################################
vlog -sv -timescale 1ps/1ps -suppress 2223 -suppress 2286 +incdir+$env(UVMF_HOME)/uvmf_base_pkg -F $env(UVMF_HOME)/uvmf_base_pkg/uvmf_base_pkg_filelist_hdl.f
vlog -sv -timescale 1ps/1ps -suppress 2223 -suppress 2286 +incdir+$env(UVMF_HOME)/uvmf_base_pkg -F $env(UVMF_HOME)/uvmf_base_pkg/uvmf_base_pkg_filelist_hvl.f


###################################################################
## UVMF INTERFACE COMPILATION
###################################################################
do $env(UVMF_VIP_LIBRARY_HOME)/interface_packages/ECC_in_pkg/compile.do
do $env(UVMF_VIP_LIBRARY_HOME)/interface_packages/ECC_out_pkg/compile.do

###################################################################
## UVMF ENVIRONMENT COMPILATION
###################################################################
do $env(UVMF_VIP_LIBRARY_HOME)/environment_packages/ECC_env_pkg/compile.do

###################################################################
## UVMF BENCHES COMPILATION
###################################################################
vlog -sv -timescale 1ps/1ps -suppress 2223 -suppress 2286 +incdir+$env(UVMF_PROJECT_DIR)/tb/parameters $env(UVMF_PROJECT_DIR)/tb/parameters/ECC_parameters_pkg.sv
vlog -sv -timescale 1ps/1ps -suppress 2223 -suppress 2286 +incdir+$env(UVMF_PROJECT_DIR)/tb/sequences $env(UVMF_PROJECT_DIR)/tb/sequences/ECC_sequences_pkg.sv
vlog -sv -timescale 1ps/1ps -suppress 2223 -suppress 2286 +incdir+$env(UVMF_PROJECT_DIR)/tb/tests $env(UVMF_PROJECT_DIR)/tb/tests/ECC_tests_pkg.sv

vlog -sv -timescale 1ps/1ps -suppress 2223 -suppress 2286 +incdir+$env(UVMF_PROJECT_DIR)/tb/testbench -F $env(UVMF_PROJECT_DIR)/tb/testbench/top_filelist_hdl.f
vlog -sv -timescale 1ps/1ps -suppress 2223 -suppress 2286  +incdir+$env(UVMF_PROJECT_DIR)/tb/testbench -F $env(UVMF_PROJECT_DIR)/tb/testbench/top_filelist_hvl.f

###################################################################
## OPTIMIZATION
###################################################################
vopt          hvl_top hdl_top   -o optimized_batch_top_tb
vopt  +acc    hvl_top hdl_top   -o optimized_debug_top_tb
