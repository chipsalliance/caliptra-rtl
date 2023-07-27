 

onerror {resume}
quietly WaveActivateNextPane {} 0

add wave -noupdate -divider soc_ifc_ctrl_agent 
add wave -noupdate /uvm_root/uvm_test_top/environment/soc_ifc_ctrl_agent/soc_ifc_ctrl_agent_monitor/txn_stream
add wave -noupdate -group soc_ifc_ctrl_agent_bus /hdl_top/soc_ifc_ctrl_agent_bus/*
add wave -noupdate -divider cptra_ctrl_agent 
add wave -noupdate /uvm_root/uvm_test_top/environment/cptra_ctrl_agent/cptra_ctrl_agent_monitor/txn_stream
add wave -noupdate -group cptra_ctrl_agent_bus /hdl_top/cptra_ctrl_agent_bus/*
add wave -noupdate -divider soc_ifc_status_agent 
add wave -noupdate /uvm_root/uvm_test_top/environment/soc_ifc_status_agent/soc_ifc_status_agent_monitor/txn_stream
add wave -noupdate -group soc_ifc_status_agent_bus /hdl_top/soc_ifc_status_agent_bus/*
add wave -noupdate -divider cptra_status_agent 
add wave -noupdate /uvm_root/uvm_test_top/environment/cptra_status_agent/cptra_status_agent_monitor/txn_stream
add wave -noupdate -group cptra_status_agent_bus /hdl_top/cptra_status_agent_bus/*
add wave -noupdate -divider mbox_sram_agent 
add wave -noupdate /uvm_root/uvm_test_top/environment/mbox_sram_agent/mbox_sram_agent_monitor/txn_stream
add wave -noupdate -group mbox_sram_agent_bus /hdl_top/mbox_sram_agent_bus/*

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

