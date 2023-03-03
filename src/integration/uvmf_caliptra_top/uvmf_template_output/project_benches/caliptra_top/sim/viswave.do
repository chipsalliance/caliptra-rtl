 

onerror resume
wave tags F0
wave update off

wave spacer -backgroundcolor Salmon { soc_ifc_subenv_soc_ifc_ctrl_agent }
wave add uvm_test_top.environment.soc_ifc_subenv.soc_ifc_ctrl_agent.soc_ifc_ctrl_agent_monitor.txn_stream -radix string -tag F0
wave group soc_ifc_subenv_soc_ifc_ctrl_agent_bus
wave add -group soc_ifc_subenv_soc_ifc_ctrl_agent_bus hdl_top.soc_ifc_subenv_soc_ifc_ctrl_agent_bus.* -radix hexadecimal -tag F0
wave group soc_ifc_subenv_soc_ifc_ctrl_agent_bus -collapse
wave insertion [expr [wave index insertpoint] +1]
wave spacer -backgroundcolor Salmon { soc_ifc_subenv_cptra_ctrl_agent }
wave add uvm_test_top.environment.soc_ifc_subenv.cptra_ctrl_agent.cptra_ctrl_agent_monitor.txn_stream -radix string -tag F0
wave group soc_ifc_subenv_cptra_ctrl_agent_bus
wave add -group soc_ifc_subenv_cptra_ctrl_agent_bus hdl_top.soc_ifc_subenv_cptra_ctrl_agent_bus.* -radix hexadecimal -tag F0
wave group soc_ifc_subenv_cptra_ctrl_agent_bus -collapse
wave insertion [expr [wave index insertpoint] +1]
wave spacer -backgroundcolor Salmon { soc_ifc_subenv_soc_ifc_status_agent }
wave add uvm_test_top.environment.soc_ifc_subenv.soc_ifc_status_agent.soc_ifc_status_agent_monitor.txn_stream -radix string -tag F0
wave group soc_ifc_subenv_soc_ifc_status_agent_bus
wave add -group soc_ifc_subenv_soc_ifc_status_agent_bus hdl_top.soc_ifc_subenv_soc_ifc_status_agent_bus.* -radix hexadecimal -tag F0
wave group soc_ifc_subenv_soc_ifc_status_agent_bus -collapse
wave insertion [expr [wave index insertpoint] +1]
wave spacer -backgroundcolor Salmon { soc_ifc_subenv_cptra_status_agent }
wave add uvm_test_top.environment.soc_ifc_subenv.cptra_status_agent.cptra_status_agent_monitor.txn_stream -radix string -tag F0
wave group soc_ifc_subenv_cptra_status_agent_bus
wave add -group soc_ifc_subenv_cptra_status_agent_bus hdl_top.soc_ifc_subenv_cptra_status_agent_bus.* -radix hexadecimal -tag F0
wave group soc_ifc_subenv_cptra_status_agent_bus -collapse
wave insertion [expr [wave index insertpoint] +1]

wave update on
WaveSetStreamView

