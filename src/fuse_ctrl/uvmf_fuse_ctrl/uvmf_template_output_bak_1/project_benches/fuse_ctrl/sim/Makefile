
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
TEST_PLAN_NAME       = fuse_ctrl_TestPlan
REPORTING_DO_FILE    = fuse_ctrl_reports_script


# Include makefile that includes targets for UVM_VIP_Library packages
include $(UVMF_HOME)/scripts/Makefile




# Include all requisite interface package targets for this bench
include $(UVMF_VIP_LIBRARY_HOME)/interface_packages/fuse_ctrl_rst_pkg/Makefile
include $(UVMF_VIP_LIBRARY_HOME)/interface_packages/fuse_ctrl_core_axi_write_if_pkg/Makefile
include $(UVMF_VIP_LIBRARY_HOME)/interface_packages/fuse_ctrl_prim_axi_write_if_pkg/Makefile
include $(UVMF_VIP_LIBRARY_HOME)/interface_packages/fuse_ctrl_core_axi_read_if_pkg/Makefile
include $(UVMF_VIP_LIBRARY_HOME)/interface_packages/fuse_ctrl_prim_axi_read_if_pkg/Makefile
include $(UVMF_VIP_LIBRARY_HOME)/interface_packages/fuse_ctrl_secreg_axi_read_if_pkg/Makefile
include $(UVMF_VIP_LIBRARY_HOME)/interface_packages/fuse_ctrl_lc_otp_if_pkg/Makefile
include $(UVMF_VIP_LIBRARY_HOME)/interface_packages/fuse_ctrl_in_if_pkg/Makefile

# Include all requisite environment package targets for this bench
include $(UVMF_VIP_LIBRARY_HOME)/environment_packages/fuse_ctrl_env_pkg/Makefile



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
fuse_ctrl_PARAMETERS_PKG ?=\
$(UVMF_PROJECT_DIR)/tb/parameters/fuse_ctrl_parameters_pkg.sv


fuse_ctrl_SEQUENCES_PKG ?=\
$(UVMF_PROJECT_DIR)/tb/sequences/fuse_ctrl_sequences_pkg.sv


fuse_ctrl_TEST_PKG ?=\
$(UVMF_PROJECT_DIR)/tb/tests/fuse_ctrl_tests_pkg.sv

# pragma uvmf custom dut_files begin
# UVMF_CHANGE_ME : Reference Verilog DUT source.
fuse_ctrl_VERILOG_DUT ?=\
$(UVMF_PROJECT_DIR)/../../../../../integration/rtl/config_defines.svh
$(UVMF_PROJECT_DIR)/../../../../../integration/rtl/caliptra_reg_defines.svh
$(UVMF_PROJECT_DIR)/../../../../../libs/rtl/caliptra_sva.svh
$(UVMF_PROJECT_DIR)/../../../../../libs/rtl/caliptra_macros.svh
$(UVMF_PROJECT_DIR)/../../../../../libs/rtl/caliptra_sram.sv
$(UVMF_PROJECT_DIR)/../../../../../libs/rtl/ahb_defines_pkg.sv
$(UVMF_PROJECT_DIR)/../../../../../libs/rtl/caliptra_ahb_srom.sv
$(UVMF_PROJECT_DIR)/../../../../../libs/rtl/apb_slv_sif.sv
$(UVMF_PROJECT_DIR)/../../../../../libs/rtl/ahb_slv_sif.sv
$(UVMF_PROJECT_DIR)/../../../../../libs/rtl/caliptra_icg.sv
$(UVMF_PROJECT_DIR)/../../../../../libs/rtl/clk_gate.sv
$(UVMF_PROJECT_DIR)/../../../../../libs/rtl/caliptra_2ff_sync.sv
$(UVMF_PROJECT_DIR)/../../../../../libs/rtl/ahb_to_reg_adapter.sv
$(UVMF_PROJECT_DIR)/../../../../../libs/rtl/skidbuffer.v
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_util_pkg.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_alert_pkg.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_subreg_pkg.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_mubi_pkg.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_cipher_pkg.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_pkg.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_sparse_fsm_pkg.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_pkg.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_otp_pkg.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_ram_1p_pkg.sv
$(UVMF_PROJECT_DIR)/../../../../../lc_ctrl/rtl/lc_ctrl_reg_pkg.sv
$(UVMF_PROJECT_DIR)/../../../../../lc_ctrl/rtl/lc_ctrl_state_pkg.sv
$(UVMF_PROJECT_DIR)/../../../../../lc_ctrl/rtl/lc_ctrl_pkg.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim_generic/rtl/caliptra_prim_generic_flop_en.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim_generic/rtl/caliptra_prim_generic_flop.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim_generic/rtl/caliptra_prim_generic_buf.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim_generic/rtl/caliptra_prim_generic_otp.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim_generic/rtl/caliptra_prim_generic_ram_1p.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim_generic/rtl/caliptra_prim_generic_and2.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_flop_en.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_cdc_rand_delay.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_flop_2sync.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_lfsr.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_double_lfsr.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_arbiter_fixed.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_arbiter_tree.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_edn_req.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_present.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_lc_sender.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_sync_reqack.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_sync_reqack_data.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_mubi4_sync.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_diff_decode.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_sec_anchor_buf.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_slicer.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_count.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_sparse_fsm_flop.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_dom_and_2share.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_sec_anchor_flop.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_reg_we_check.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_packer_fifo.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_max_tree.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_subreg_arb.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_subreg.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_intr_hw.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_onehot_check.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_mubi8_sync.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_mubi8_sender.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_fifo_sync_cnt.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_buf.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_lc_sync.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_alert_receiver.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_flop.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_alert_sender.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_fifo_sync.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_arbiter_ppc.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_sum_tree.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_subreg_ext.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_edge_detector.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_blanker.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_ram_1p_adv.sv
$(UVMF_PROJECT_DIR)/../../../../../tlul/rtl/tlul_pkg.sv
$(UVMF_PROJECT_DIR)/../../../../../tlul/rtl/tlul_assert_multiple.sv
$(UVMF_PROJECT_DIR)/../../../../../tlul/rtl/tlul_assert.sv
$(UVMF_PROJECT_DIR)/../../../../../tlul/rtl/sram2tlul.sv
$(UVMF_PROJECT_DIR)/../../../../../tlul/rtl/tlul_adapter_host.sv
$(UVMF_PROJECT_DIR)/../../../../../tlul/rtl/tlul_adapter_reg.sv
$(UVMF_PROJECT_DIR)/../../../../../tlul/rtl/tlul_adapter_sram.sv
$(UVMF_PROJECT_DIR)/../../../../../tlul/rtl/tlul_cmd_intg_chk.sv
$(UVMF_PROJECT_DIR)/../../../../../tlul/rtl/tlul_cmd_intg_gen.sv
$(UVMF_PROJECT_DIR)/../../../../../tlul/rtl/tlul_data_integ_dec.sv
$(UVMF_PROJECT_DIR)/../../../../../tlul/rtl/tlul_data_integ_enc.sv
$(UVMF_PROJECT_DIR)/../../../../../tlul/rtl/tlul_err_resp.sv
$(UVMF_PROJECT_DIR)/../../../../../tlul/rtl/tlul_err.sv
$(UVMF_PROJECT_DIR)/../../../../../tlul/rtl/tlul_fifo_async.sv
$(UVMF_PROJECT_DIR)/../../../../../tlul/rtl/tlul_fifo_sync.sv
$(UVMF_PROJECT_DIR)/../../../../../tlul/rtl/tlul_lc_gate.sv
$(UVMF_PROJECT_DIR)/../../../../../tlul/rtl/tlul_rsp_intg_chk.sv
$(UVMF_PROJECT_DIR)/../../../../../tlul/rtl/tlul_rsp_intg_gen.sv
$(UVMF_PROJECT_DIR)/../../../../../tlul/rtl/tlul_socket_1n.sv
$(UVMF_PROJECT_DIR)/../../../../../tlul/rtl/tlul_socket_m1.sv
$(UVMF_PROJECT_DIR)/../../../../../tlul/rtl/tlul_sram_byte.sv
$(UVMF_PROJECT_DIR)/../../../../../axi/rtl/axi_pkg.sv
$(UVMF_PROJECT_DIR)/../../../../../axi/rtl/axi_if.sv
$(UVMF_PROJECT_DIR)/../../../../../axi/rtl/axi_addr.v
$(UVMF_PROJECT_DIR)/../../../../../axi/rtl/axi_sub_rd.sv
$(UVMF_PROJECT_DIR)/../../../../../axi/rtl/axi_sub_wr.sv
$(UVMF_PROJECT_DIR)/../../../../../axi/rtl/axi_sub_arb.sv
$(UVMF_PROJECT_DIR)/../../../../../axi/rtl/axi_sub.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_22_16_dec.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_22_16_enc.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_28_22_dec.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_28_22_enc.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_39_32_dec.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_39_32_enc.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_64_57_dec.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_64_57_enc.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_72_64_dec.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_72_64_enc.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_hamming_22_16_dec.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_hamming_22_16_enc.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_hamming_39_32_dec.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_hamming_39_32_enc.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_hamming_72_64_dec.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_hamming_72_64_enc.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_hamming_76_68_dec.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_hamming_76_68_enc.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_inv_22_16_dec.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_inv_22_16_enc.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_inv_28_22_dec.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_inv_28_22_enc.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_inv_39_32_dec.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_inv_39_32_enc.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_inv_64_57_dec.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_inv_64_57_enc.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_inv_72_64_dec.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_inv_72_64_enc.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_inv_hamming_22_16_dec.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_inv_hamming_22_16_enc.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_inv_hamming_39_32_dec.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_inv_hamming_39_32_enc.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_inv_hamming_72_64_dec.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_inv_hamming_72_64_enc.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_inv_hamming_76_68_dec.sv
$(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_inv_hamming_76_68_enc.sv
$(UVMF_PROJECT_DIR)/../../../../../axi2tlul/rtl/axi2tlul_cmd_intg_gen.sv
$(UVMF_PROJECT_DIR)/../../../../../axi2tlul/rtl/sub2tlul.sv
$(UVMF_PROJECT_DIR)/../../../../../axi2tlul/rtl/axi2tlul.sv
$(UVMF_PROJECT_DIR)/../../../../../entropy_src/rtl/entropy_src_main_sm_pkg.sv
$(UVMF_PROJECT_DIR)/../../../../../entropy_src/rtl/entropy_src_ack_sm_pkg.sv
$(UVMF_PROJECT_DIR)/../../../../../entropy_src/rtl/entropy_src_reg_pkg.sv
$(UVMF_PROJECT_DIR)/../../../../../entropy_src/rtl/entropy_src_pkg.sv
$(UVMF_PROJECT_DIR)/../../../../../edn/rtl/edn_pkg.sv
$(UVMF_PROJECT_DIR)/../../../../../ast/rtl/ast_pkg.sv
$(UVMF_PROJECT_DIR)/../../../../../pwrmgr/rtl/pwrmgr_reg_pkg.sv
$(UVMF_PROJECT_DIR)/../../../../../pwrmgr/rtl/pwrmgr_pkg.sv
$(UVMF_PROJECT_DIR)/../../../../rtl/caliptra_otp_ctrl_reg_pkg.sv
$(UVMF_PROJECT_DIR)/../../../../rtl/caliptra_otp_ctrl_pkg.sv
$(UVMF_PROJECT_DIR)/../../../../rtl/caliptra_otp_ctrl_part_pkg.sv
$(UVMF_PROJECT_DIR)/../../../../rtl/caliptra_otp_ctrl_core_reg_top.sv
$(UVMF_PROJECT_DIR)/../../../../rtl/caliptra_otp_ctrl_prim_reg_top.sv
$(UVMF_PROJECT_DIR)/../../../../rtl/otp_ctrl_dai.sv
$(UVMF_PROJECT_DIR)/../../../../rtl/otp_ctrl_ecc_reg.sv
$(UVMF_PROJECT_DIR)/../../../../rtl/otp_ctrl_lci.sv
$(UVMF_PROJECT_DIR)/../../../../rtl/otp_ctrl_lfsr_timer.sv
$(UVMF_PROJECT_DIR)/../../../../rtl/otp_ctrl_part_buf.sv
$(UVMF_PROJECT_DIR)/../../../../rtl/otp_ctrl_part_unbuf.sv
$(UVMF_PROJECT_DIR)/../../../../rtl/otp_ctrl_scrmbl.sv
$(UVMF_PROJECT_DIR)/../../../../rtl/otp_ctrl.sv
$(UVMF_PROJECT_DIR)/../../../../rtl/otp_ctrl_top.sv


# UVMF_CHANGE_ME : Reference VHDL DUT source.
fuse_ctrl_VHDL_DUT ?=\
$(UVMF_PROJECT_DIR)/rtl/vhdl/vhdl_dut.vhd
# pragma uvmf custom dut_files end


# Project bench package targets
COMP_fuse_ctrl_PARAMETERS_PKG_TGT_0 = q_comp_fuse_ctrl_parameters_pkg
COMP_fuse_ctrl_PARAMETERS_PKG_TGT_1 = v_comp_fuse_ctrl_parameters_pkg
COMP_fuse_ctrl_PARAMETERS_PKG_TGT = $(COMP_fuse_ctrl_PARAMETERS_PKG_TGT_$(USE_VELOCE))

comp_fuse_ctrl_parameters_pkg: $(COMP_fuse_ctrl_PARAMETERS_PKG_TGT)

q_comp_fuse_ctrl_parameters_pkg:
	        $(HVL_COMP_CMD) +incdir+$(UVMF_PROJECT_DIR)/tb/parameters $(fuse_ctrl_PARAMETERS_PKG)

v_comp_fuse_ctrl_parameters_pkg: q_comp_fuse_ctrl_parameters_pkg
	$(HDL_COMP_CMD) +incdir+$(UVMF_PROJECT_DIR)/tb/parameters $(fuse_ctrl_PARAMETERS_PKG)
 

comp_fuse_ctrl_sequence_pkg:
	$(HVL_COMP_CMD) +incdir+$(UVMF_PROJECT_DIR)/tb/sequences $(fuse_ctrl_SEQUENCES_PKG)

comp_fuse_ctrl_tests_pkg:
	$(HVL_COMP_CMD) +incdir+$(UVMF_PROJECT_DIR)/tb/tests $(fuse_ctrl_TEST_PKG)

# pragma uvmf custom dut_compile_make_target begin
# UVMF_CHANGE_ME : Add make target to compile your verilog dut here
comp_fuse_ctrl_verilog_dut: 
	echo "Compile your verilog DUT here"
	$(HDL_COMP_CMD) +incdir+$(UVMF_PROJECT_DIR)/../../../../../libs/rtl $(fuse_ctrl_VERILOG_DUT)

# UVMF_CHANGE_ME : Add make target to compile your vhdl dut here
comp_fuse_ctrl_vhdl_dut: 
	echo "Compile your vhdl DUT here"
	$(HDL_COMP_CMD_VHDL) $(fuse_ctrl_VHDL_DUT)

# UVMF_CHANGE_ME : Add make target to compile your dut here
comp_fuse_ctrl_dut: comp_fuse_ctrl_vhdl_dut comp_fuse_ctrl_verilog_dut 
# pragma uvmf custom dut_compile_make_target end


BUILD_TGT_0 = make_build
BUILD_TGT_1 = vinfo_build
BUILD_TGT = $(BUILD_TGT_$(USE_VINFO))


comp_hvl : comp_hvl_core


comp_hvl_core :   \
	 comp_fuse_ctrl_rst_pkg  comp_fuse_ctrl_core_axi_write_if_pkg  comp_fuse_ctrl_prim_axi_write_if_pkg  comp_fuse_ctrl_core_axi_read_if_pkg  comp_fuse_ctrl_prim_axi_read_if_pkg  comp_fuse_ctrl_secreg_axi_read_if_pkg  comp_fuse_ctrl_lc_otp_if_pkg  comp_fuse_ctrl_in_if_pkg  \
	comp_fuse_ctrl_env_pkg \
	comp_fuse_ctrl_parameters_pkg comp_fuse_ctrl_sequence_pkg comp_fuse_ctrl_tests_pkg 

comp_uvmf_core : comp_uvm_pkg comp_uvmf_base_pkg 

make_build: comp_fuse_ctrl_dut comp_uvmf_core comp_hvl comp_test_bench  

hvl_build:  q_comp_fuse_ctrl_rst_pkg  q_comp_fuse_ctrl_core_axi_write_if_pkg  q_comp_fuse_ctrl_prim_axi_write_if_pkg  q_comp_fuse_ctrl_core_axi_read_if_pkg  q_comp_fuse_ctrl_prim_axi_read_if_pkg  q_comp_fuse_ctrl_secreg_axi_read_if_pkg  q_comp_fuse_ctrl_lc_otp_if_pkg  q_comp_fuse_ctrl_in_if_pkg  comp_fuse_ctrl_env_pkg comp_fuse_ctrl_sequence_pkg comp_fuse_ctrl_tests_pkg hvl_comp_testbench link optimize


vinfo_build: comp_fuse_ctrl_vhdl_dut  build_hdl_vinfo build_hvl_vinfo $(VINFO_TGT)

	$(HDL_COMP_CMD) -F hdl.vf
	$(VEL_COMP)

build: $(BUILD_TGT)

# pragma uvmf custom additional_targets begin
# pragma uvmf custom additional_targets end

