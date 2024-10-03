 

onerror {resume}
quietly WaveActivateNextPane {} 0

add wave -noupdate -divider fuse_ctrl_rst_in_agent 
add wave -noupdate /uvm_root/uvm_test_top/environment/fuse_ctrl_rst_in_agent/fuse_ctrl_rst_in_agent_monitor/txn_stream
add wave -noupdate -group fuse_ctrl_rst_in_agent_bus /hdl_top/fuse_ctrl_rst_in_agent_bus/*
add wave -noupdate -divider fuse_ctrl_rst_out_agent 
add wave -noupdate /uvm_root/uvm_test_top/environment/fuse_ctrl_rst_out_agent/fuse_ctrl_rst_out_agent_monitor/txn_stream
add wave -noupdate -group fuse_ctrl_rst_out_agent_bus /hdl_top/fuse_ctrl_rst_out_agent_bus/*
add wave -noupdate -divider fuse_ctrl_core_axi_write_in_if_agent 
add wave -noupdate /uvm_root/uvm_test_top/environment/fuse_ctrl_core_axi_write_in_if_agent/fuse_ctrl_core_axi_write_in_if_agent_monitor/txn_stream
add wave -noupdate -group fuse_ctrl_core_axi_write_in_if_agent_bus /hdl_top/fuse_ctrl_core_axi_write_in_if_agent_bus/*
add wave -noupdate -divider fuse_ctrl_core_axi_write_out_if_agent 
add wave -noupdate /uvm_root/uvm_test_top/environment/fuse_ctrl_core_axi_write_out_if_agent/fuse_ctrl_core_axi_write_out_if_agent_monitor/txn_stream
add wave -noupdate -group fuse_ctrl_core_axi_write_out_if_agent_bus /hdl_top/fuse_ctrl_core_axi_write_out_if_agent_bus/*
add wave -noupdate -divider fuse_ctrl_prim_axi_write_in_if_agent 
add wave -noupdate /uvm_root/uvm_test_top/environment/fuse_ctrl_prim_axi_write_in_if_agent/fuse_ctrl_prim_axi_write_in_if_agent_monitor/txn_stream
add wave -noupdate -group fuse_ctrl_prim_axi_write_in_if_agent_bus /hdl_top/fuse_ctrl_prim_axi_write_in_if_agent_bus/*
add wave -noupdate -divider fuse_ctrl_prim_axi_write_out_if_agent 
add wave -noupdate /uvm_root/uvm_test_top/environment/fuse_ctrl_prim_axi_write_out_if_agent/fuse_ctrl_prim_axi_write_out_if_agent_monitor/txn_stream
add wave -noupdate -group fuse_ctrl_prim_axi_write_out_if_agent_bus /hdl_top/fuse_ctrl_prim_axi_write_out_if_agent_bus/*
add wave -noupdate -divider fuse_ctrl_core_axi_read_in_if_agent 
add wave -noupdate /uvm_root/uvm_test_top/environment/fuse_ctrl_core_axi_read_in_if_agent/fuse_ctrl_core_axi_read_in_if_agent_monitor/txn_stream
add wave -noupdate -group fuse_ctrl_core_axi_read_in_if_agent_bus /hdl_top/fuse_ctrl_core_axi_read_in_if_agent_bus/*
add wave -noupdate -divider fuse_ctrl_core_axi_read_out_if_agent 
add wave -noupdate /uvm_root/uvm_test_top/environment/fuse_ctrl_core_axi_read_out_if_agent/fuse_ctrl_core_axi_read_out_if_agent_monitor/txn_stream
add wave -noupdate -group fuse_ctrl_core_axi_read_out_if_agent_bus /hdl_top/fuse_ctrl_core_axi_read_out_if_agent_bus/*
add wave -noupdate -divider fuse_ctrl_prim_axi_read_in_if_agent 
add wave -noupdate /uvm_root/uvm_test_top/environment/fuse_ctrl_prim_axi_read_in_if_agent/fuse_ctrl_prim_axi_read_in_if_agent_monitor/txn_stream
add wave -noupdate -group fuse_ctrl_prim_axi_read_in_if_agent_bus /hdl_top/fuse_ctrl_prim_axi_read_in_if_agent_bus/*
add wave -noupdate -divider fuse_ctrl_prim_axi_read_out_if_agent 
add wave -noupdate /uvm_root/uvm_test_top/environment/fuse_ctrl_prim_axi_read_out_if_agent/fuse_ctrl_prim_axi_read_out_if_agent_monitor/txn_stream
add wave -noupdate -group fuse_ctrl_prim_axi_read_out_if_agent_bus /hdl_top/fuse_ctrl_prim_axi_read_out_if_agent_bus/*
add wave -noupdate -divider fuse_ctrl_secreg_axi_read_in_if_agent 
add wave -noupdate /uvm_root/uvm_test_top/environment/fuse_ctrl_secreg_axi_read_in_if_agent/fuse_ctrl_secreg_axi_read_in_if_agent_monitor/txn_stream
add wave -noupdate -group fuse_ctrl_secreg_axi_read_in_if_agent_bus /hdl_top/fuse_ctrl_secreg_axi_read_in_if_agent_bus/*
add wave -noupdate -divider fuse_ctrl_secreg_axi_read_out_if_agent 
add wave -noupdate /uvm_root/uvm_test_top/environment/fuse_ctrl_secreg_axi_read_out_if_agent/fuse_ctrl_secreg_axi_read_out_if_agent_monitor/txn_stream
add wave -noupdate -group fuse_ctrl_secreg_axi_read_out_if_agent_bus /hdl_top/fuse_ctrl_secreg_axi_read_out_if_agent_bus/*
add wave -noupdate -divider fuse_ctrl_lc_otp_in_if_agent 
add wave -noupdate /uvm_root/uvm_test_top/environment/fuse_ctrl_lc_otp_in_if_agent/fuse_ctrl_lc_otp_in_if_agent_monitor/txn_stream
add wave -noupdate -group fuse_ctrl_lc_otp_in_if_agent_bus /hdl_top/fuse_ctrl_lc_otp_in_if_agent_bus/*
add wave -noupdate -divider fuse_ctrl_lc_otp_out_if_agent 
add wave -noupdate /uvm_root/uvm_test_top/environment/fuse_ctrl_lc_otp_out_if_agent/fuse_ctrl_lc_otp_out_if_agent_monitor/txn_stream
add wave -noupdate -group fuse_ctrl_lc_otp_out_if_agent_bus /hdl_top/fuse_ctrl_lc_otp_out_if_agent_bus/*
add wave -noupdate -divider fuse_ctrl_in_if_agent 
add wave -noupdate /uvm_root/uvm_test_top/environment/fuse_ctrl_in_if_agent/fuse_ctrl_in_if_agent_monitor/txn_stream
add wave -noupdate -group fuse_ctrl_in_if_agent_bus /hdl_top/fuse_ctrl_in_if_agent_bus/*
add wave -noupdate -divider fuse_ctrl_out_if_agent 
add wave -noupdate /uvm_root/uvm_test_top/environment/fuse_ctrl_out_if_agent/fuse_ctrl_out_if_agent_monitor/txn_stream
add wave -noupdate -group fuse_ctrl_out_if_agent_bus /hdl_top/fuse_ctrl_out_if_agent_bus/*

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

