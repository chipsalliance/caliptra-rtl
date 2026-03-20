# File list for unit-level simulation of aes.sv
# DUT:       src/aes/rtl/aes.sv
# Testbench: src/aes/tb/aes_tb.sv
#
# Derived from aes.vf; CLP wrapper files excluded (not needed for aes.sv unit test).
#
set CALIPTRA_ROOT ../../../
set CALIPTRA_PRIM_ROOT ../../../src/caliptra_prim_generic
set CALIPTRA_PRIM_MODULE_PREFIX caliptra_prim_generic
#
# Include directories - add these to your compile options separately:
# +incdir+${CALIPTRA_ROOT}/src/entropy_src/rtl
# +incdir+${CALIPTRA_ROOT}/src/csrng/rtl
# +incdir+${CALIPTRA_ROOT}/src/edn/rtl
# +incdir+${CALIPTRA_ROOT}/src/integration/rtl
# +incdir+${CALIPTRA_ROOT}/src/libs/rtl
# +incdir+${CALIPTRA_ROOT}/src/caliptra_prim/rtl
# +incdir+${CALIPTRA_ROOT}/src/lc_ctrl/rtl
# +incdir+${CALIPTRA_ROOT}/src/caliptra_prim_generic/rtl
# +incdir+${CALIPTRA_ROOT}/src/aes/rtl
# +incdir+${CALIPTRA_ROOT}/src/keyvault/rtl
# +incdir+${CALIPTRA_ROOT}/src/caliptra_tlul/rtl
# +incdir+${CALIPTRA_ROOT}/src/aes/tb

# Entropy / CSRNG / EDN packages
project addfile ${CALIPTRA_ROOT}/src/entropy_src/rtl/entropy_src_main_sm_pkg.sv
project addfile ${CALIPTRA_ROOT}/src/entropy_src/rtl/entropy_src_ack_sm_pkg.sv
project addfile ${CALIPTRA_ROOT}/src/entropy_src/rtl/entropy_src_reg_pkg.sv
project addfile ${CALIPTRA_ROOT}/src/entropy_src/rtl/entropy_src_pkg.sv
project addfile ${CALIPTRA_ROOT}/src/csrng/rtl/csrng_reg_pkg.sv
project addfile ${CALIPTRA_ROOT}/src/csrng/rtl/csrng_pkg.sv
project addfile ${CALIPTRA_ROOT}/src/edn/rtl/edn_pkg.sv

# Integration / lib headers
project addfile ${CALIPTRA_ROOT}/src/integration/rtl/config_defines.svh
project addfile ${CALIPTRA_ROOT}/src/libs/rtl/caliptra_sva.svh
project addfile ${CALIPTRA_ROOT}/src/libs/rtl/caliptra_macros.svh

# Caliptra primitive packages
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_util_pkg.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_alert_pkg.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_subreg_pkg.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_mubi_pkg.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_cipher_pkg.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_pkg.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_sparse_fsm_pkg.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_trivium_pkg.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_secded_pkg.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_otp_pkg.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_ram_1p_pkg.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_esc_pkg.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_count_pkg.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/keymgr_pkg.sv

# Life cycle
project addfile ${CALIPTRA_ROOT}/src/lc_ctrl/rtl/lc_ctrl_reg_pkg.sv
project addfile ${CALIPTRA_ROOT}/src/lc_ctrl/rtl/lc_ctrl_state_pkg.sv
project addfile ${CALIPTRA_ROOT}/src/lc_ctrl/rtl/lc_ctrl_pkg.sv

# Technology-mapped primitives (prim_generic)
project addfile ${CALIPTRA_PRIM_ROOT}/rtl/${CALIPTRA_PRIM_MODULE_PREFIX}_flop_en.sv
project addfile ${CALIPTRA_PRIM_ROOT}/rtl/${CALIPTRA_PRIM_MODULE_PREFIX}_flop.sv
project addfile ${CALIPTRA_PRIM_ROOT}/rtl/${CALIPTRA_PRIM_MODULE_PREFIX}_buf.sv
project addfile ${CALIPTRA_PRIM_ROOT}/rtl/${CALIPTRA_PRIM_MODULE_PREFIX}_ram_1p.sv
project addfile ${CALIPTRA_PRIM_ROOT}/rtl/${CALIPTRA_PRIM_MODULE_PREFIX}_and2.sv
project addfile ${CALIPTRA_PRIM_ROOT}/rtl/${CALIPTRA_PRIM_MODULE_PREFIX}_clock_mux2.sv
project addfile ${CALIPTRA_PRIM_ROOT}/rtl/${CALIPTRA_PRIM_MODULE_PREFIX}_clock_inv.sv
project addfile ${CALIPTRA_PRIM_ROOT}/rtl/${CALIPTRA_PRIM_MODULE_PREFIX}_xor2.sv
project addfile ${CALIPTRA_PRIM_ROOT}/rtl/${CALIPTRA_PRIM_MODULE_PREFIX}_xnor2.sv

# Caliptra primitive RTL
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_flop_en.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_cdc_rand_delay.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_flop_2sync.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_lfsr.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_double_lfsr.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_arbiter_fixed.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_arbiter_tree.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_edn_req.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_present.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_lc_sender.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_sync_reqack.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_sync_reqack_data.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_mubi4_sync.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_diff_decode.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_sec_anchor_buf.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_slicer.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_count.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_sparse_fsm_flop.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_dom_and_2share.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_sec_anchor_flop.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_reg_we_check.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_packer_fifo.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_max_tree.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_subreg_arb.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_subreg.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_intr_hw.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_onehot_check.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_onehot_enc.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_onehot_mux.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_mubi8_sync.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_mubi8_sender.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_fifo_sync_cnt.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_buf.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_lc_sync.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_alert_receiver.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_flop.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_alert_sender.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_fifo_sync.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_arbiter_ppc.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_sum_tree.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_subreg_ext.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_edge_detector.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_trivium.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_blanker.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_ram_1p_adv.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_mubi4_sender.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_packer.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_subreg_shadow.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_esc_receiver.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_mubi4_dec.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_clock_mux2.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_fifo_async.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_fifo_async_simple.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_gf_mult.sv

# AES packages and register model
project addfile ${CALIPTRA_ROOT}/src/aes/rtl/aes_reg_pkg.sv
project addfile ${CALIPTRA_ROOT}/src/aes/rtl/aes_pkg.sv
project addfile ${CALIPTRA_ROOT}/src/aes/rtl/aes_sbox_canright_pkg.sv

# SECDED ECC (needed by aes_reg_top via tlul_data_integ)
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_secded_22_16_dec.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_secded_22_16_enc.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_secded_28_22_dec.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_secded_28_22_enc.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_secded_39_32_dec.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_secded_39_32_enc.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_secded_64_57_dec.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_secded_64_57_enc.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_secded_72_64_dec.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_secded_72_64_enc.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_secded_hamming_22_16_dec.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_secded_hamming_22_16_enc.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_secded_hamming_39_32_dec.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_secded_hamming_39_32_enc.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_secded_hamming_72_64_dec.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_secded_hamming_72_64_enc.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_secded_hamming_76_68_dec.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_secded_hamming_76_68_enc.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_secded_inv_22_16_dec.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_secded_inv_22_16_enc.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_secded_inv_28_22_dec.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_secded_inv_28_22_enc.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_secded_inv_39_32_dec.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_secded_inv_39_32_enc.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_secded_inv_64_57_dec.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_secded_inv_64_57_enc.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_secded_inv_72_64_dec.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_secded_inv_72_64_enc.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_secded_inv_hamming_22_16_dec.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_secded_inv_hamming_22_16_enc.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_secded_inv_hamming_39_32_dec.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_secded_inv_hamming_39_32_enc.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_secded_inv_hamming_72_64_dec.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_secded_inv_hamming_72_64_enc.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_secded_inv_hamming_76_68_dec.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_prim/rtl/caliptra_prim_secded_inv_hamming_76_68_enc.sv

# TLUL package and supporting modules (needed by aes_reg_top)
project addfile ${CALIPTRA_ROOT}/src/caliptra_tlul/rtl/caliptra_tlul_pkg.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_tlul/rtl/caliptra_tlul_adapter_reg.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_tlul/rtl/caliptra_tlul_cmd_intg_gen.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_tlul/rtl/caliptra_tlul_cmd_intg_chk.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_tlul/rtl/caliptra_tlul_rsp_intg_gen.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_tlul/rtl/caliptra_tlul_rsp_intg_chk.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_tlul/rtl/caliptra_tlul_data_integ_dec.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_tlul/rtl/caliptra_tlul_data_integ_enc.sv
project addfile ${CALIPTRA_ROOT}/src/caliptra_tlul/rtl/caliptra_tlul_err.sv

# AES RTL (DUT and sub-modules)
project addfile ${CALIPTRA_ROOT}/src/aes/rtl/aes_sbox_canright.sv
project addfile ${CALIPTRA_ROOT}/src/aes/rtl/aes_sbox_canright_masked.sv
project addfile ${CALIPTRA_ROOT}/src/aes/rtl/aes_cipher_core.sv
project addfile ${CALIPTRA_ROOT}/src/aes/rtl/aes_sbox.sv
project addfile ${CALIPTRA_ROOT}/src/aes/rtl/aes_cipher_control_fsm_n.sv
project addfile ${CALIPTRA_ROOT}/src/aes/rtl/aes_cipher_control_fsm_p.sv
project addfile ${CALIPTRA_ROOT}/src/aes/rtl/aes_sbox_lut.sv
project addfile ${CALIPTRA_ROOT}/src/aes/rtl/aes_mix_columns.sv
project addfile ${CALIPTRA_ROOT}/src/aes/rtl/aes_sbox_dom.sv
project addfile ${CALIPTRA_ROOT}/src/aes/rtl/aes_sub_bytes.sv
project addfile ${CALIPTRA_ROOT}/src/aes/rtl/aes_sbox_canright_masked_noreuse.sv
project addfile ${CALIPTRA_ROOT}/src/aes/rtl/aes_sel_buf_chk.sv
project addfile ${CALIPTRA_ROOT}/src/aes/rtl/aes_cipher_control_fsm.sv
project addfile ${CALIPTRA_ROOT}/src/aes/rtl/aes_shift_rows.sv
project addfile ${CALIPTRA_ROOT}/src/aes/rtl/aes_mix_single_column.sv
project addfile ${CALIPTRA_ROOT}/src/aes/rtl/aes_cipher_control.sv
project addfile ${CALIPTRA_ROOT}/src/aes/rtl/aes_prng_masking.sv
project addfile ${CALIPTRA_ROOT}/src/aes/rtl/aes_key_expand.sv
project addfile ${CALIPTRA_ROOT}/src/aes/rtl/aes_control.sv
project addfile ${CALIPTRA_ROOT}/src/aes/rtl/aes_control_fsm.sv
project addfile ${CALIPTRA_ROOT}/src/aes/rtl/aes_control_fsm_n.sv
project addfile ${CALIPTRA_ROOT}/src/aes/rtl/aes_control_fsm_p.sv
project addfile ${CALIPTRA_ROOT}/src/aes/rtl/aes_core.sv
project addfile ${CALIPTRA_ROOT}/src/aes/rtl/aes_ctr.sv
project addfile ${CALIPTRA_ROOT}/src/aes/rtl/aes_ctr_fsm.sv
project addfile ${CALIPTRA_ROOT}/src/aes/rtl/aes_ctr_fsm_n.sv
project addfile ${CALIPTRA_ROOT}/src/aes/rtl/aes_ctr_fsm_p.sv
project addfile ${CALIPTRA_ROOT}/src/aes/rtl/aes_ctrl_gcm_reg_shadowed.sv
project addfile ${CALIPTRA_ROOT}/src/aes/rtl/aes_ctrl_reg_shadowed.sv
project addfile ${CALIPTRA_ROOT}/src/aes/rtl/aes_ghash.sv
project addfile ${CALIPTRA_ROOT}/src/aes/rtl/aes_prng_clearing.sv
project addfile ${CALIPTRA_ROOT}/src/aes/rtl/aes_reduced_round.sv
project addfile ${CALIPTRA_ROOT}/src/aes/rtl/aes_reg_status.sv
project addfile ${CALIPTRA_ROOT}/src/aes/rtl/aes_reg_top.sv
project addfile ${CALIPTRA_ROOT}/src/aes/rtl/aes.sv

# Testbench
project addfile ${CALIPTRA_ROOT}/src/aes/tb/aes_tb.sv
