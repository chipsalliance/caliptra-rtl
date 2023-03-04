 

onerror resume
wave tags F0
wave update off

wave spacer -backgroundcolor Salmon { HMAC_in_agent }
wave add uvm_test_top.environment.HMAC_in_agent.HMAC_in_agent_monitor.txn_stream -radix string -tag F0
wave group HMAC_in_agent_bus
wave add -group HMAC_in_agent_bus hdl_top.HMAC_in_agent_bus.* -radix hexadecimal -tag F0
wave group HMAC_in_agent_bus -collapse
wave insertion [expr [wave index insertpoint] +1]
wave spacer -backgroundcolor Salmon { HMAC_out_agent }
wave add uvm_test_top.environment.HMAC_out_agent.HMAC_out_agent_monitor.txn_stream -radix string -tag F0
wave group HMAC_out_agent_bus
wave add -group HMAC_out_agent_bus hdl_top.HMAC_out_agent_bus.* -radix hexadecimal -tag F0
wave group HMAC_out_agent_bus -collapse
wave insertion [expr [wave index insertpoint] +1]

wave update on
WaveSetStreamView

