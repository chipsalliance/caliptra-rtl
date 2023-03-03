 

onerror resume
wave tags F0
wave update off

wave spacer -backgroundcolor Salmon { ECC_in_agent }
wave add uvm_test_top.environment.ECC_in_agent.ECC_in_agent_monitor.txn_stream -radix string -tag F0
wave group ECC_in_agent_bus
wave add -group ECC_in_agent_bus hdl_top.ECC_in_agent_bus.* -radix hexadecimal -tag F0
wave group ECC_in_agent_bus -collapse
wave insertion [expr [wave index insertpoint] +1]
wave spacer -backgroundcolor Salmon { ECC_out_agent }
wave add uvm_test_top.environment.ECC_out_agent.ECC_out_agent_monitor.txn_stream -radix string -tag F0
wave group ECC_out_agent_bus
wave add -group ECC_out_agent_bus hdl_top.ECC_out_agent_bus.* -radix hexadecimal -tag F0
wave group ECC_out_agent_bus -collapse
wave insertion [expr [wave index insertpoint] +1]
wave group Internal_Signals
wave add -group Internal_Signals hdl_top.dut.ecc_dsa_ctrl_i.dsa_busy
wave add -group Internal_Signals hdl_top.dut.ecc_dsa_ctrl_i.pm_busy_o
wave add -group Internal_Signals hdl_top.dut.ecc_dsa_ctrl_i.cmd_reg
wave group ECC_out_monitor_bfm
wave add -group ECC_out_monitor_bfm hdl_top.ECC_out_agent_mon_bfm.* -radix hexadecimal -tag F0
wave insertion [expr [wave index insertpoint] +1]

wave update on
WaveSetStreamView

