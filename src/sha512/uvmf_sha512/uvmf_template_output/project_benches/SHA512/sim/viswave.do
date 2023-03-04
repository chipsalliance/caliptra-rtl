 

onerror resume
wave tags F0
wave update off

wave spacer -backgroundcolor Salmon { SHA512_in_agent }
wave add uvm_test_top.environment.SHA512_in_agent.SHA512_in_agent_monitor.txn_stream -radix string -tag F0
wave group SHA512_in_agent_bus
wave add -group SHA512_in_agent_bus hdl_top.SHA512_in_agent_bus.* -radix hexadecimal -tag F0
wave group SHA512_in_agent_bus -collapse
wave insertion [expr [wave index insertpoint] +1]
wave spacer -backgroundcolor Salmon { SHA512_out_agent }
wave add uvm_test_top.environment.SHA512_out_agent.SHA512_out_agent_monitor.txn_stream -radix string -tag F0
wave group SHA512_out_agent_bus
wave add -group SHA512_out_agent_bus hdl_top.SHA512_out_agent_bus.* -radix hexadecimal -tag F0
wave group SHA512_out_agent_bus -collapse
wave insertion [expr [wave index insertpoint] +1]

wave update on
WaveSetStreamView

