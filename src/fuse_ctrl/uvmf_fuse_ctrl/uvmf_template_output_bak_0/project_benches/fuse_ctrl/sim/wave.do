 

onerror {resume}
quietly WaveActivateNextPane {} 0

add wave -noupdate -divider fuse_ctrl_rst_agent 
add wave -noupdate /uvm_root/uvm_test_top/environment/fuse_ctrl_rst_agent/fuse_ctrl_rst_agent_monitor/txn_stream
add wave -noupdate -group fuse_ctrl_rst_agent_bus /hdl_top/fuse_ctrl_rst_agent_bus/*
add wave -noupdate -divider fuse_ctrl_core_axi_write_agent 
add wave -noupdate /uvm_root/uvm_test_top/environment/fuse_ctrl_core_axi_write_agent/fuse_ctrl_core_axi_write_agent_monitor/txn_stream
add wave -noupdate -group fuse_ctrl_core_axi_write_agent_bus /hdl_top/fuse_ctrl_core_axi_write_agent_bus/*
add wave -noupdate -divider fuse_ctrl_prim_axi_write_agent 
add wave -noupdate /uvm_root/uvm_test_top/environment/fuse_ctrl_prim_axi_write_agent/fuse_ctrl_prim_axi_write_agent_monitor/txn_stream
add wave -noupdate -group fuse_ctrl_prim_axi_write_agent_bus /hdl_top/fuse_ctrl_prim_axi_write_agent_bus/*
add wave -noupdate -divider fuse_ctrl_core_axi_read_agent 
add wave -noupdate /uvm_root/uvm_test_top/environment/fuse_ctrl_core_axi_read_agent/fuse_ctrl_core_axi_read_agent_monitor/txn_stream
add wave -noupdate -group fuse_ctrl_core_axi_read_agent_bus /hdl_top/fuse_ctrl_core_axi_read_agent_bus/*
add wave -noupdate -divider fuse_ctrl_prim_axi_read_agent 
add wave -noupdate /uvm_root/uvm_test_top/environment/fuse_ctrl_prim_axi_read_agent/fuse_ctrl_prim_axi_read_agent_monitor/txn_stream
add wave -noupdate -group fuse_ctrl_prim_axi_read_agent_bus /hdl_top/fuse_ctrl_prim_axi_read_agent_bus/*
add wave -noupdate -divider fuse_ctrl_secreg_axi_read_agent 
add wave -noupdate /uvm_root/uvm_test_top/environment/fuse_ctrl_secreg_axi_read_agent/fuse_ctrl_secreg_axi_read_agent_monitor/txn_stream
add wave -noupdate -group fuse_ctrl_secreg_axi_read_agent_bus /hdl_top/fuse_ctrl_secreg_axi_read_agent_bus/*
add wave -noupdate -divider fuse_ctrl_lc_otp_if_agent 
add wave -noupdate /uvm_root/uvm_test_top/environment/fuse_ctrl_lc_otp_if_agent/fuse_ctrl_lc_otp_if_agent_monitor/txn_stream
add wave -noupdate -group fuse_ctrl_lc_otp_if_agent_bus /hdl_top/fuse_ctrl_lc_otp_if_agent_bus/*

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

