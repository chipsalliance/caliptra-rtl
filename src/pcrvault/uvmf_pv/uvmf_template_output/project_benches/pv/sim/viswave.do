 

onerror resume
wave tags F0
wave update off

wave spacer -backgroundcolor Salmon { pv_rst_agent }
wave add uvm_test_top.environment.pv_rst_agent.pv_rst_agent_monitor.txn_stream -radix string -tag F0
wave group pv_rst_agent_bus
wave add -group pv_rst_agent_bus hdl_top.pv_rst_agent_bus.* -radix hexadecimal -tag F0
wave group pv_rst_agent_bus -collapse
wave insertion [expr [wave index insertpoint] +1]
wave spacer -backgroundcolor Salmon { pv_sha512_write_agent }
wave add uvm_test_top.environment.pv_sha512_write_agent.pv_sha512_write_agent_monitor.txn_stream -radix string -tag F0
wave group pv_sha512_write_agent_bus
wave add -group pv_sha512_write_agent_bus hdl_top.pv_sha512_write_agent_bus.* -radix hexadecimal -tag F0
wave group pv_sha512_write_agent_bus -collapse
wave insertion [expr [wave index insertpoint] +1]
wave spacer -backgroundcolor Salmon { pv_sha512_block_read_agent }
wave add uvm_test_top.environment.pv_sha512_block_read_agent.pv_sha512_block_read_agent_monitor.txn_stream -radix string -tag F0
wave group pv_sha512_block_read_agent_bus
wave add -group pv_sha512_block_read_agent_bus hdl_top.pv_sha512_block_read_agent_bus.* -radix hexadecimal -tag F0
wave group pv_sha512_block_read_agent_bus -collapse
wave insertion [expr [wave index insertpoint] +1]

wave update on
WaveSetStreamView

