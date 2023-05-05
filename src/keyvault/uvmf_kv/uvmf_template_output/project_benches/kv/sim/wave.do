 

onerror {resume}
quietly WaveActivateNextPane {} 0

add wave -noupdate -divider kv_rst_agent 
add wave -noupdate /uvm_root/uvm_test_top/environment/kv_rst_agent/kv_rst_agent_monitor/txn_stream
add wave -noupdate -group kv_rst_agent_bus /hdl_top/kv_rst_agent_bus/*
add wave -noupdate -divider kv_hmac_write_agent 
add wave -noupdate /uvm_root/uvm_test_top/environment/kv_hmac_write_agent/kv_hmac_write_agent_monitor/txn_stream
add wave -noupdate -group kv_hmac_write_agent_bus /hdl_top/kv_hmac_write_agent_bus/*
add wave -noupdate -divider kv_sha512_write_agent 
add wave -noupdate /uvm_root/uvm_test_top/environment/kv_sha512_write_agent/kv_sha512_write_agent_monitor/txn_stream
add wave -noupdate -group kv_sha512_write_agent_bus /hdl_top/kv_sha512_write_agent_bus/*
add wave -noupdate -divider kv_ecc_write_agent 
add wave -noupdate /uvm_root/uvm_test_top/environment/kv_ecc_write_agent/kv_ecc_write_agent_monitor/txn_stream
add wave -noupdate -group kv_ecc_write_agent_bus /hdl_top/kv_ecc_write_agent_bus/*
add wave -noupdate -divider kv_doe_write_agent 
add wave -noupdate /uvm_root/uvm_test_top/environment/kv_doe_write_agent/kv_doe_write_agent_monitor/txn_stream
add wave -noupdate -group kv_doe_write_agent_bus /hdl_top/kv_doe_write_agent_bus/*
add wave -noupdate -divider kv_hmac_key_read_agent 
add wave -noupdate /uvm_root/uvm_test_top/environment/kv_hmac_key_read_agent/kv_hmac_key_read_agent_monitor/txn_stream
add wave -noupdate -group kv_hmac_key_read_agent_bus /hdl_top/kv_hmac_key_read_agent_bus/*
add wave -noupdate -divider kv_hmac_block_read_agent 
add wave -noupdate /uvm_root/uvm_test_top/environment/kv_hmac_block_read_agent/kv_hmac_block_read_agent_monitor/txn_stream
add wave -noupdate -group kv_hmac_block_read_agent_bus /hdl_top/kv_hmac_block_read_agent_bus/*
add wave -noupdate -divider kv_sha512_block_read_agent 
add wave -noupdate /uvm_root/uvm_test_top/environment/kv_sha512_block_read_agent/kv_sha512_block_read_agent_monitor/txn_stream
add wave -noupdate -group kv_sha512_block_read_agent_bus /hdl_top/kv_sha512_block_read_agent_bus/*
add wave -noupdate -divider kv_ecc_privkey_read_agent 
add wave -noupdate /uvm_root/uvm_test_top/environment/kv_ecc_privkey_read_agent/kv_ecc_privkey_read_agent_monitor/txn_stream
add wave -noupdate -group kv_ecc_privkey_read_agent_bus /hdl_top/kv_ecc_privkey_read_agent_bus/*
add wave -noupdate -divider kv_ecc_seed_read_agent 
add wave -noupdate /uvm_root/uvm_test_top/environment/kv_ecc_seed_read_agent/kv_ecc_seed_read_agent_monitor/txn_stream
add wave -noupdate -group kv_ecc_seed_read_agent_bus /hdl_top/kv_ecc_seed_read_agent_bus/*
add wave -noupdate -divider kv_ecc_msg_read_agent 
add wave -noupdate /uvm_root/uvm_test_top/environment/kv_ecc_msg_read_agent/kv_ecc_msg_read_agent_monitor/txn_stream
add wave -noupdate -group kv_ecc_msg_read_agent_bus /hdl_top/kv_ecc_msg_read_agent_bus/*

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

