 

onerror {resume}
quietly WaveActivateNextPane {} 0

add wave -noupdate -divider ECC_in_agent 
add wave -noupdate /uvm_root/uvm_test_top/environment/ECC_in_agent/ECC_in_agent_monitor/txn_stream
add wave -noupdate -group ECC_in_agent_bus /hdl_top/ECC_in_agent_bus/*
add wave -noupdate -divider ECC_out_agent 
add wave -noupdate /uvm_root/uvm_test_top/environment/ECC_out_agent/ECC_out_agent_monitor/txn_stream
add wave -noupdate -group ECC_out_agent_bus /hdl_top/ECC_out_agent_bus/*
add wave -noupdate -divider Internal_Signals
add wave -noupdate /hdl_top/dut/ecc_dsa_ctrl_i/dsa_busy
add wave -noupdate /hdl_top/dut/ecc_dsa_ctrl_i/pm_busy_o
add wave -noupdate /hdl_top/dut/ecc_dsa_ctrl_i/cmd_reg
add wave -noupdate /hdl_top/dut/ecc_reg_hwif_in
add wave -noupdate /hdl_top/dut/ecc_reg_hwif_out
add wave -noupdate /hdl_top/dut/hrdata_o
add wave -noupdate /hdl_top/hrdata_top
add wave -noupdate -divider ECC_out_monitor_bfm
add wave -noupdate /hdl_top/ECC_out_agent_mon_bfm/transaction_flag_out_monitor_i
add wave -noupdate /hdl_top/ECC_out_agent_mon_bfm/transaction_flag
add wave -noupdate /hdl_top/ECC_out_agent_mon_bfm/privkey
add wave -noupdate /hdl_top/ECC_out_agent_mon_bfm/pubkey_x
add wave -noupdate /hdl_top/ECC_out_agent_mon_bfm/pubkey_y
add wave -noupdate /hdl_top/ECC_out_agent_mon_bfm/R
add wave -noupdate /hdl_top/ECC_out_agent_mon_bfm/S
add wave -noupdate /hdl_top/ECC_out_agent_mon_bfm/verify
add wave -noupdate /hdl_top/ECC_out_agent_mon_bfm/op

TreeUpdate [SetDefaultTree]
quietly wave cursor active 0
configure wave -namecolwidth 472
configure wave -valuecolwidth 100
configure wave -justifyvalue left
configure wave -signalnamewidth 0
configure wave -snapdistance 10
configure wave -datasetprefix 0
configure wave -rowmargin 4
configure wave -childrowmargin 2
configure wave -gridoffset 0
configure wave -gridperiod 1
configure wave -griddelta 40
configure wave -timeline 0
configure wave -timelineunits ns
update
WaveRestoreZoom {27 ns} {168 ns}

