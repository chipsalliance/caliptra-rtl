

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
# pragma uvmf custom dut_compile_dofile_target end

vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../integration/rtl/config_defines.svh
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../integration/rtl/caliptra_reg_defines.svh
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../libs/rtl/caliptra_sva.svh
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../libs/rtl/caliptra_macros.svh
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../libs/rtl/caliptra_sram.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../libs/rtl/ahb_defines_pkg.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../libs/rtl/caliptra_ahb_srom.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../libs/rtl/apb_slv_sif.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../libs/rtl/ahb_slv_sif.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../libs/rtl/caliptra_icg.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../libs/rtl/clk_gate.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../libs/rtl/caliptra_2ff_sync.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../libs/rtl/ahb_to_reg_adapter.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../libs/rtl/skidbuffer.v
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_util_pkg.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_alert_pkg.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_subreg_pkg.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_mubi_pkg.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_cipher_pkg.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_pkg.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_sparse_fsm_pkg.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_pkg.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_otp_pkg.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_ram_1p_pkg.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../lc_ctrl/rtl/lc_ctrl_reg_pkg.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../lc_ctrl/rtl/lc_ctrl_state_pkg.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../lc_ctrl/rtl/lc_ctrl_pkg.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim_generic/rtl/caliptra_prim_generic_flop_en.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim_generic/rtl/caliptra_prim_generic_flop.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim_generic/rtl/caliptra_prim_generic_buf.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim_generic/rtl/caliptra_prim_generic_otp.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim_generic/rtl/caliptra_prim_generic_ram_1p.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim_generic/rtl/caliptra_prim_generic_and2.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_flop_en.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_cdc_rand_delay.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_flop_2sync.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_lfsr.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_double_lfsr.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_arbiter_fixed.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_arbiter_tree.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_edn_req.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_present.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_lc_sender.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_sync_reqack.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_sync_reqack_data.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_mubi4_sync.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_diff_decode.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_sec_anchor_buf.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_slicer.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_count.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_sparse_fsm_flop.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_dom_and_2share.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_sec_anchor_flop.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_reg_we_check.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_packer_fifo.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_max_tree.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_subreg_arb.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_subreg.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_intr_hw.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_onehot_check.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_mubi8_sync.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_mubi8_sender.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_fifo_sync_cnt.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_buf.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_lc_sync.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_alert_receiver.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_flop.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_alert_sender.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_fifo_sync.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_arbiter_ppc.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_sum_tree.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_subreg_ext.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_edge_detector.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_blanker.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_ram_1p_adv.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../tlul/rtl/tlul_pkg.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../tlul/rtl/tlul_assert_multiple.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../tlul/rtl/tlul_assert.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../tlul/rtl/sram2tlul.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../tlul/rtl/tlul_adapter_host.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../tlul/rtl/tlul_adapter_reg.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../tlul/rtl/tlul_adapter_sram.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../tlul/rtl/tlul_cmd_intg_chk.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../tlul/rtl/tlul_cmd_intg_gen.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../tlul/rtl/tlul_data_integ_dec.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../tlul/rtl/tlul_data_integ_enc.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../tlul/rtl/tlul_err_resp.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../tlul/rtl/tlul_err.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../tlul/rtl/tlul_fifo_async.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../tlul/rtl/tlul_fifo_sync.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../tlul/rtl/tlul_lc_gate.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../tlul/rtl/tlul_rsp_intg_chk.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../tlul/rtl/tlul_rsp_intg_gen.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../tlul/rtl/tlul_socket_1n.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../tlul/rtl/tlul_socket_m1.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../tlul/rtl/tlul_sram_byte.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../axi/rtl/axi_pkg.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../axi/rtl/axi_if.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../axi/rtl/axi_addr.v
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../axi/rtl/axi_sub_rd.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../axi/rtl/axi_sub_wr.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../axi/rtl/axi_sub_arb.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../axi/rtl/axi_sub.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_22_16_dec.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_22_16_enc.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_28_22_dec.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_28_22_enc.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_39_32_dec.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_39_32_enc.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_64_57_dec.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_64_57_enc.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_72_64_dec.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_72_64_enc.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_hamming_22_16_dec.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_hamming_22_16_enc.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_hamming_39_32_dec.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_hamming_39_32_enc.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_hamming_72_64_dec.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_hamming_72_64_enc.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_hamming_76_68_dec.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_hamming_76_68_enc.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_inv_22_16_dec.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_inv_22_16_enc.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_inv_28_22_dec.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_inv_28_22_enc.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_inv_39_32_dec.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_inv_39_32_enc.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_inv_64_57_dec.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_inv_64_57_enc.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_inv_72_64_dec.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_inv_72_64_enc.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_inv_hamming_22_16_dec.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_inv_hamming_22_16_enc.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_inv_hamming_39_32_dec.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_inv_hamming_39_32_enc.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_inv_hamming_72_64_dec.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_inv_hamming_72_64_enc.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_inv_hamming_76_68_dec.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../caliptra_prim/rtl/caliptra_prim_secded_inv_hamming_76_68_enc.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../axi2tlul/rtl/axi2tlul_cmd_intg_gen.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../axi2tlul/rtl/sub2tlul.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../axi2tlul/rtl/axi2tlul.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../entropy_src/rtl/entropy_src_main_sm_pkg.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../entropy_src/rtl/entropy_src_ack_sm_pkg.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../entropy_src/rtl/entropy_src_reg_pkg.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../entropy_src/rtl/entropy_src_pkg.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../edn/rtl/edn_pkg.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../ast/rtl/ast_pkg.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../pwrmgr/rtl/pwrmgr_reg_pkg.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../../pwrmgr/rtl/pwrmgr_pkg.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../rtl/caliptra_otp_ctrl_reg_pkg.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../rtl/caliptra_otp_ctrl_pkg.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../rtl/caliptra_otp_ctrl_part_pkg.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../rtl/caliptra_otp_ctrl_core_reg_top.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../rtl/caliptra_otp_ctrl_prim_reg_top.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../rtl/otp_ctrl_dai.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../rtl/otp_ctrl_ecc_reg.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../rtl/otp_ctrl_lci.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../rtl/otp_ctrl_lfsr_timer.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../rtl/otp_ctrl_part_buf.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../rtl/otp_ctrl_part_unbuf.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../rtl/otp_ctrl_scrmbl.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../rtl/otp_ctrl.sv
vlog -sv -timescale 1ps/1ps -suppress 2223,2286 $env(UVMF_PROJECT_DIR)/../../../../rtl/otp_ctrl_top.sv



###################################################################
## COMPILE UVMF BASE/COMMON SOURCE CODE
###################################################################
vlog -sv -timescale 1ps/1ps -suppress 2223 -suppress 2286 +incdir+$env(UVMF_HOME)/uvmf_base_pkg -F $env(UVMF_HOME)/uvmf_base_pkg/uvmf_base_pkg_filelist_hdl.f
vlog -sv -timescale 1ps/1ps -suppress 2223 -suppress 2286 +incdir+$env(UVMF_HOME)/uvmf_base_pkg -F $env(UVMF_HOME)/uvmf_base_pkg/uvmf_base_pkg_filelist_hvl.f


###################################################################
## UVMF INTERFACE COMPILATION
###################################################################
do $env(UVMF_VIP_LIBRARY_HOME)/interface_packages/fuse_ctrl_rst_pkg/compile.do
do $env(UVMF_VIP_LIBRARY_HOME)/interface_packages/fuse_ctrl_core_axi_write_if_pkg/compile.do
do $env(UVMF_VIP_LIBRARY_HOME)/interface_packages/fuse_ctrl_prim_axi_write_if_pkg/compile.do
do $env(UVMF_VIP_LIBRARY_HOME)/interface_packages/fuse_ctrl_core_axi_read_if_pkg/compile.do
do $env(UVMF_VIP_LIBRARY_HOME)/interface_packages/fuse_ctrl_prim_axi_read_if_pkg/compile.do
do $env(UVMF_VIP_LIBRARY_HOME)/interface_packages/fuse_ctrl_secreg_axi_read_if_pkg/compile.do
do $env(UVMF_VIP_LIBRARY_HOME)/interface_packages/fuse_ctrl_lc_otp_if_pkg/compile.do

###################################################################
## UVMF ENVIRONMENT COMPILATION
###################################################################
do $env(UVMF_VIP_LIBRARY_HOME)/environment_packages/fuse_ctrl_env_pkg/compile.do

###################################################################
## UVMF BENCHES COMPILATION
###################################################################
vlog -sv -timescale 1ps/1ps -suppress 2223 -suppress 2286 +incdir+$env(UVMF_PROJECT_DIR)/tb/parameters $env(UVMF_PROJECT_DIR)/tb/parameters/fuse_ctrl_parameters_pkg.sv
vlog -sv -timescale 1ps/1ps -suppress 2223 -suppress 2286 +incdir+$env(UVMF_PROJECT_DIR)/tb/sequences $env(UVMF_PROJECT_DIR)/tb/sequences/fuse_ctrl_sequences_pkg.sv
vlog -sv -timescale 1ps/1ps -suppress 2223 -suppress 2286 +incdir+$env(UVMF_PROJECT_DIR)/tb/tests $env(UVMF_PROJECT_DIR)/tb/tests/fuse_ctrl_tests_pkg.sv

vlog -sv -timescale 1ps/1ps -suppress 2223 -suppress 2286 +incdir+$env(UVMF_PROJECT_DIR)/tb/testbench -F $env(UVMF_PROJECT_DIR)/tb/testbench/top_filelist_hdl.f
vlog -sv -timescale 1ps/1ps -suppress 2223 -suppress 2286  +incdir+$env(UVMF_PROJECT_DIR)/tb/testbench -F $env(UVMF_PROJECT_DIR)/tb/testbench/top_filelist_hvl.f

###################################################################
## OPTIMIZATION
###################################################################
vopt          hvl_top hdl_top   -o optimized_batch_top_tb
vopt  +acc    hvl_top hdl_top   -o optimized_debug_top_tb
