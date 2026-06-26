 

onerror resume
wave tags F0
wave update off

wave spacer -backgroundcolor Salmon { HMAC_rst_agent }
wave add uvm_test_top.environment.HMAC_rst_agent.hmac_rst_agent_monitor.txn_stream -radix string -tag F0
wave group hmac_rst_agent_bus
wave add -group hmac_rst_agent_bus hdl_top.hmac_rst_agent_bus.* -radix hexadecimal -tag F0
wave group hmac_rst_agent_bus -collapse
wave insertion [expr [wave index insertpoint] +1]

wave update on
WaveSetStreamView

