
#
#----------------------------------------------------------------------
#                                          
# DESCRIPTION: This makefile includes the shared makefile and contains
#   bench level make targets.
#
#----------------------------------------------------------------------


# pragma uvmf custom additional begin
# pragma uvmf custom additional end

# *********************************************************************************************
# UVMF library directory:
# This variable points to the UVMF release where uvmf_base_pkg directory resides.
# This variable points to release code that is not user modified.
# This variable allows for UVMF release directories to reside independent of project related verification IP and project bench directories.
# This code below looks "upward" for directory starting with UVMF_* and returns first match for use with the release examples.
UVMF_HOME ?= ___PLEASE_SET_AN_ENVIRONMENT_VARIABLE_NAMED_UVMF_HOME_TO_POINT_TO_THE_UVMF_INSTALLATION___

# pragma uvmf custom exports begin
#
# Project(s) specific verification IP library:
# Directory where reusable verification packages for interfaces, environments, utilities, etc. reside.
# This variable allows for your verification IP to reside independent of project bench and UVMF release directories.
# For examples deployed with UVMF this will be $(UVMF_HOME)/<example_group>/verification_ip
export UVMF_VIP_LIBRARY_HOME ?= $(PWD)/../../../verification_ip
#
# Project specific bench:
# Directory where bench specific code is located.
# This variable allows for project_benches to reside independent of verification IP and UVMF release directories.
# For examples deployed with UVMF this will be $(UVMF_HOME)/<example_group>/project_benches/<example_bench>
export UVMF_PROJECT_DIR ?= $(PWD)/..
#
#
# pragma uvmf custom exports end
# *********************************************************************************************

## Check PATH for required vinfo scripts
PVAL := $(shell command -v make_filelist.py 2> /dev/null)
ifndef PVAL
  MFLIST = $(UVMF_HOME)/scripts/make_filelist.py
else
  MFLIST = make_filelist.py
endif


# Set test case specific Variables
TEST_NAME            ?= test_top

TEST_SEED            ?= random
UVM_CLI_ARGS         = 

# Usage of Veloce, etc. to be input by the user (subject to defaults)
USE_VELOCE          ?= 0

# Usage of vinfo flow for generating file list
USE_VINFO           ?= 0

# Usage of Veloce and Questa profilers
USE_VELOCE_PROFILER ?= 0
USE_QUESTA_PROFILER ?= 0


# Set project Variables
TEST_PLAN_NAME       = ECC_TestPlan
REPORTING_DO_FILE    = ECC_reports_script


# Include makefile that includes targets for UVM_VIP_Library packages
include $(UVMF_HOME)/scripts/Makefile




# Include all requisite interface package targets for this bench
include $(UVMF_VIP_LIBRARY_HOME)/interface_packages/ECC_in_pkg/Makefile
include $(UVMF_VIP_LIBRARY_HOME)/interface_packages/ECC_out_pkg/Makefile

# Include all requisite environment package targets for this bench
include $(UVMF_VIP_LIBRARY_HOME)/environment_packages/ECC_env_pkg/Makefile



# Add to default compile/load/run arguments
VCOM_ARGS             += 

# Note: vsim-3009 error can be eliminated by adding -timescale 1ps/1ps to VLOG_ARGS

VLOG_ARGS             += $(UVM_DISABLE_FILE_LINE_CMD)

VELANALYZE_ARGS       +=
VELANALYZE_HVL_ARGS   +=

BATCH_VOPT_ARGS       +=
DEBUG_VOPT_ARGS       +=
EXTRA_VOPT_TOPS       += 
COMMON_VSIM_ARGS      +=  
COMMON_VSIM_ARGS      +=  


BATCH_VSIM_ARGS       += #-uvmcontrol=none
DEBUG_VSIM_ARGS       += 
EXTRA_VSIM_TOPS       += 

# pragma uvmf custom additional_args begin
# pragma uvmf custom additional_args end


# Project bench package source
ECC_PARAMETERS_PKG ?=\
$(UVMF_PROJECT_DIR)/tb/parameters/ECC_parameters_pkg.sv


ECC_SEQUENCES_PKG ?=\
$(UVMF_PROJECT_DIR)/tb/sequences/ECC_sequences_pkg.sv


ECC_TEST_PKG ?=\
$(UVMF_PROJECT_DIR)/tb/tests/ECC_tests_pkg.sv

# pragma uvmf custom dut_files begin
# UVMF_CHANGE_ME : Reference Verilog DUT source.
ECC_VERILOG_DUT ?=\
$(UVMF_PROJECT_DIR)/../../../../../hmac_drbg/rtl/hmac_drbg_param.sv\
$(UVMF_PROJECT_DIR)/../../../../../hmac_drbg/rtl/hmac_drbg.v\
$(UVMF_PROJECT_DIR)/../../../../../hmac/rtl/hmac_core.v\
$(UVMF_PROJECT_DIR)/../../../../../keyvault/rtl/kv_defines.svh\
$(UVMF_PROJECT_DIR)/../../../../../hmac/rtl/hmac_ctrl.sv\
$(UVMF_PROJECT_DIR)/../../../../../hmac/rtl/hmac_param.sv\
$(UVMF_PROJECT_DIR)/../../../../../hmac/rtl/hmac.v\
$(UVMF_PROJECT_DIR)/../../../../../sha512/rtl/sha512_ctrl.sv\
$(UVMF_PROJECT_DIR)/../../../../../sha512/rtl/sha512_core.v\
$(UVMF_PROJECT_DIR)/../../../../../sha512/rtl/sha512_h_constants.v\
$(UVMF_PROJECT_DIR)/../../../../../sha512/rtl/sha512_k_constants.v\
$(UVMF_PROJECT_DIR)/../../../../../sha512/rtl/sha512_param.sv\
$(UVMF_PROJECT_DIR)/../../../../../sha512/rtl/sha512.v\
$(UVMF_PROJECT_DIR)/../../../../../sha512/rtl/sha512_w_mem.v\
$(UVMF_PROJECT_DIR)/../../../../rtl/ecc_defines.svh\
$(UVMF_PROJECT_DIR)/../../../../rtl/ecc_params.sv\
$(UVMF_PROJECT_DIR)/../../../../rtl/ecc_reg_pkg.sv\
$(UVMF_PROJECT_DIR)/../../../../rtl/ecc_top.sv\
$(UVMF_PROJECT_DIR)/../../../../rtl/ecc_reg.sv\
$(UVMF_PROJECT_DIR)/../../../../rtl/ecc_dsa_ctrl.sv\
$(UVMF_PROJECT_DIR)/../../../../rtl/ecc_dsa_sequencer.sv\
$(UVMF_PROJECT_DIR)/../../../../rtl/ecc_dsa_uop.sv\
$(UVMF_PROJECT_DIR)/../../../../rtl/ecc_fixed_msb.sv\
$(UVMF_PROJECT_DIR)/../../../../rtl/ecc_arith_unit.sv\
$(UVMF_PROJECT_DIR)/../../../../rtl/ecc_pm_ctrl.sv\
$(UVMF_PROJECT_DIR)/../../../../rtl/ecc_pm_uop.sv\
$(UVMF_PROJECT_DIR)/../../../../rtl/ecc_pm_sequencer.sv\
$(UVMF_PROJECT_DIR)/../../../../rtl/ecc_ram_tdp_file.sv\
$(UVMF_PROJECT_DIR)/../../../../rtl/ecc_fau.sv\
$(UVMF_PROJECT_DIR)/../../../../rtl/ecc_montgomerymultiplier.sv\
$(UVMF_PROJECT_DIR)/../../../../rtl/ecc_pe_first.sv\
$(UVMF_PROJECT_DIR)/../../../../rtl/ecc_pe.sv\
$(UVMF_PROJECT_DIR)/../../../../rtl/ecc_pe_final.sv\
$(UVMF_PROJECT_DIR)/../../../../rtl/ecc_mult_dsp.sv\
$(UVMF_PROJECT_DIR)/../../../../rtl/ecc_add_sub_mod_alter.sv\
$(UVMF_PROJECT_DIR)/../../../../rtl/ecc_adder.sv\
$(UVMF_PROJECT_DIR)/../../../../../libs/rtl/caliptra_sva.svh\
$(UVMF_PROJECT_DIR)/../../../../../libs/rtl/ahb_slv_sif.sv


# UVMF_CHANGE_ME : Reference VHDL DUT source.
ECC_VHDL_DUT ?=\
$(UVMF_PROJECT_DIR)/rtl/vhdl/vhdl_dut.vhd
# pragma uvmf custom dut_files end


# Project bench package targets
COMP_ECC_PARAMETERS_PKG_TGT_0 = q_comp_ECC_parameters_pkg
COMP_ECC_PARAMETERS_PKG_TGT_1 = v_comp_ECC_parameters_pkg
COMP_ECC_PARAMETERS_PKG_TGT = $(COMP_ECC_PARAMETERS_PKG_TGT_$(USE_VELOCE))

comp_ECC_parameters_pkg: $(COMP_ECC_PARAMETERS_PKG_TGT)

q_comp_ECC_parameters_pkg:
	        $(HVL_COMP_CMD) +incdir+$(UVMF_PROJECT_DIR)/tb/parameters $(ECC_PARAMETERS_PKG)

v_comp_ECC_parameters_pkg: q_comp_ECC_parameters_pkg
	$(HDL_COMP_CMD) +incdir+$(UVMF_PROJECT_DIR)/tb/parameters $(ECC_PARAMETERS_PKG)
 

comp_ECC_sequence_pkg:
	$(HVL_COMP_CMD) +incdir+$(UVMF_PROJECT_DIR)/tb/sequences $(ECC_SEQUENCES_PKG)

comp_ECC_tests_pkg:
	$(HVL_COMP_CMD) +incdir+$(UVMF_PROJECT_DIR)/tb/tests $(ECC_TEST_PKG)

# pragma uvmf custom dut_compile_make_target begin
# UVMF_CHANGE_ME : Add make target to compile your verilog dut here
comp_ECC_verilog_dut: 
	echo "Compile your verilog DUT here"
	$(HDL_COMP_CMD) +incdir+$(UVMF_PROJECT_DIR)/../../../../../libs/rtl +incdir+$(UVMF_PROJECT_DIR)/../../../../../keyvault/rtl $(ECC_VERILOG_DUT)

# UVMF_CHANGE_ME : Add make target to compile your vhdl dut here
comp_ECC_vhdl_dut: 
	echo "Compile your vhdl DUT here"
	$(HDL_COMP_CMD_VHDL) $(ECC_VHDL_DUT)

# UVMF_CHANGE_ME : Add make target to compile your dut here
comp_ECC_dut: comp_ECC_verilog_dut 
# pragma uvmf custom dut_compile_make_target end


BUILD_TGT_0 = make_build
BUILD_TGT_1 = vinfo_build
BUILD_TGT = $(BUILD_TGT_$(USE_VINFO))


comp_hvl : comp_hvl_core


comp_hvl_core :   \
	 comp_ECC_in_pkg  comp_ECC_out_pkg  \
	comp_ECC_env_pkg \
	comp_ECC_parameters_pkg comp_ECC_sequence_pkg comp_ECC_tests_pkg 

comp_uvmf_core : comp_uvm_pkg comp_uvmf_base_pkg 

make_build: comp_ECC_dut comp_uvmf_core comp_hvl comp_test_bench  

hvl_build:  q_comp_ECC_in_pkg  q_comp_ECC_out_pkg  comp_ECC_env_pkg comp_ECC_sequence_pkg comp_ECC_tests_pkg hvl_comp_testbench link optimize


vinfo_build: comp_ECC_vhdl_dut  build_hdl_vinfo build_hvl_vinfo $(VINFO_TGT)

	$(HDL_COMP_CMD) -F hdl.vf
	$(VEL_COMP)

build: $(BUILD_TGT)

# pragma uvmf custom additional_targets begin
# pragma uvmf custom additional_targets end

