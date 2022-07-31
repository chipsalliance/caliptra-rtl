 

onerror resume
wave tags F0
wave update off

wave spacer -backgroundcolor Salmon { AES_in_agent }
wave add uvm_test_top.environment.AES_in_agent.AES_in_agent_monitor.txn_stream -radix string -tag F0
wave group AES_in_agent_bus
wave add -group AES_in_agent_bus hdl_top.AES_in_agent_bus.* -radix hexadecimal -tag F0
wave group AES_in_agent_bus -collapse
wave insertion [expr [wave index insertpoint] +1]
wave spacer -backgroundcolor Salmon { AES_out_agent }
wave add uvm_test_top.environment.AES_out_agent.AES_out_agent_monitor.txn_stream -radix string -tag F0
wave group AES_out_agent_bus
wave add -group AES_out_agent_bus hdl_top.AES_out_agent_bus.* -radix hexadecimal -tag F0
wave group AES_out_agent_bus -collapse
wave insertion [expr [wave index insertpoint] +1]

wave update on
WaveSetStreamView

