 

onerror resume
wave tags F0
wave update off

wave spacer -backgroundcolor Salmon { kv_rst_agent }
wave add uvm_test_top.environment.kv_rst_agent.kv_rst_agent_monitor.txn_stream -radix string -tag F0
wave group kv_rst_agent_bus
wave add -group kv_rst_agent_bus hdl_top.kv_rst_agent_bus.* -radix hexadecimal -tag F0
wave group kv_rst_agent_bus -collapse
wave insertion [expr [wave index insertpoint] +1]
wave spacer -backgroundcolor Salmon { kv_hmac_write_agent }
wave add uvm_test_top.environment.kv_hmac_write_agent.kv_hmac_write_agent_monitor.txn_stream -radix string -tag F0
wave group kv_hmac_write_agent_bus
wave add -group kv_hmac_write_agent_bus hdl_top.kv_hmac_write_agent_bus.* -radix hexadecimal -tag F0
wave group kv_hmac_write_agent_bus -collapse
wave insertion [expr [wave index insertpoint] +1]
wave spacer -backgroundcolor Salmon { kv_sha512_write_agent }
wave add uvm_test_top.environment.kv_sha512_write_agent.kv_sha512_write_agent_monitor.txn_stream -radix string -tag F0
wave group kv_sha512_write_agent_bus
wave add -group kv_sha512_write_agent_bus hdl_top.kv_sha512_write_agent_bus.* -radix hexadecimal -tag F0
wave group kv_sha512_write_agent_bus -collapse
wave insertion [expr [wave index insertpoint] +1]
wave spacer -backgroundcolor Salmon { kv_ecc_write_agent }
wave add uvm_test_top.environment.kv_ecc_write_agent.kv_ecc_write_agent_monitor.txn_stream -radix string -tag F0
wave group kv_ecc_write_agent_bus
wave add -group kv_ecc_write_agent_bus hdl_top.kv_ecc_write_agent_bus.* -radix hexadecimal -tag F0
wave group kv_ecc_write_agent_bus -collapse
wave insertion [expr [wave index insertpoint] +1]
wave spacer -backgroundcolor Salmon { kv_doe_write_agent }
wave add uvm_test_top.environment.kv_doe_write_agent.kv_doe_write_agent_monitor.txn_stream -radix string -tag F0
wave group kv_doe_write_agent_bus
wave add -group kv_doe_write_agent_bus hdl_top.kv_doe_write_agent_bus.* -radix hexadecimal -tag F0
wave group kv_doe_write_agent_bus -collapse
wave insertion [expr [wave index insertpoint] +1]
wave spacer -backgroundcolor Salmon { kv_hmac_key_read_agent }
wave add uvm_test_top.environment.kv_hmac_key_read_agent.kv_hmac_key_read_agent_monitor.txn_stream -radix string -tag F0
wave group kv_hmac_key_read_agent_bus
wave add -group kv_hmac_key_read_agent_bus hdl_top.kv_hmac_key_read_agent_bus.* -radix hexadecimal -tag F0
wave group kv_hmac_key_read_agent_bus -collapse
wave insertion [expr [wave index insertpoint] +1]
wave spacer -backgroundcolor Salmon { kv_hmac_block_read_agent }
wave add uvm_test_top.environment.kv_hmac_block_read_agent.kv_hmac_block_read_agent_monitor.txn_stream -radix string -tag F0
wave group kv_hmac_block_read_agent_bus
wave add -group kv_hmac_block_read_agent_bus hdl_top.kv_hmac_block_read_agent_bus.* -radix hexadecimal -tag F0
wave group kv_hmac_block_read_agent_bus -collapse
wave insertion [expr [wave index insertpoint] +1]
wave spacer -backgroundcolor Salmon { kv_mldsa_key_read_agent }
wave add uvm_test_top.environment.kv_mldsa_key_read_agent.kv_mldsa_key_read_agent_monitor.txn_stream -radix string -tag F0
wave group kv_mldsa_key_read_agent_bus
wave add -group kv_mldsa_key_read_agent_bus hdl_top.kv_mldsa_key_read_agent_bus.* -radix hexadecimal -tag F0
wave group kv_mldsa_key_read_agent_bus -collapse
wave insertion [expr [wave index insertpoint] +1]
wave spacer -backgroundcolor Salmon { kv_ecc_privkey_read_agent }
wave add uvm_test_top.environment.kv_ecc_privkey_read_agent.kv_ecc_privkey_read_agent_monitor.txn_stream -radix string -tag F0
wave group kv_ecc_privkey_read_agent_bus
wave add -group kv_ecc_privkey_read_agent_bus hdl_top.kv_ecc_privkey_read_agent_bus.* -radix hexadecimal -tag F0
wave group kv_ecc_privkey_read_agent_bus -collapse
wave insertion [expr [wave index insertpoint] +1]
wave spacer -backgroundcolor Salmon { kv_ecc_seed_read_agent }
wave add uvm_test_top.environment.kv_ecc_seed_read_agent.kv_ecc_seed_read_agent_monitor.txn_stream -radix string -tag F0
wave group kv_ecc_seed_read_agent_bus
wave add -group kv_ecc_seed_read_agent_bus hdl_top.kv_ecc_seed_read_agent_bus.* -radix hexadecimal -tag F0
wave group kv_ecc_seed_read_agent_bus -collapse
wave insertion [expr [wave index insertpoint] +1]
wave spacer -backgroundcolor Salmon { kv_ecc_msg_read_agent }
wave add uvm_test_top.environment.kv_ecc_msg_read_agent.kv_ecc_msg_read_agent_monitor.txn_stream -radix string -tag F0
wave group kv_ecc_msg_read_agent_bus
wave add -group kv_ecc_msg_read_agent_bus hdl_top.kv_ecc_msg_read_agent_bus.* -radix hexadecimal -tag F0
wave group kv_ecc_msg_read_agent_bus -collapse
wave insertion [expr [wave index insertpoint] +1]

wave update on
WaveSetStreamView

