 

onerror resume
wave tags F0
wave update off

wave spacer -backgroundcolor Salmon { fuse_ctrl_rst_in_agent }
wave add uvm_test_top.environment.fuse_ctrl_rst_in_agent.fuse_ctrl_rst_in_agent_monitor.txn_stream -radix string -tag F0
wave group fuse_ctrl_rst_in_agent_bus
wave add -group fuse_ctrl_rst_in_agent_bus hdl_top.fuse_ctrl_rst_in_agent_bus.* -radix hexadecimal -tag F0
wave group fuse_ctrl_rst_in_agent_bus -collapse
wave insertion [expr [wave index insertpoint] +1]
wave spacer -backgroundcolor Salmon { fuse_ctrl_rst_out_agent }
wave add uvm_test_top.environment.fuse_ctrl_rst_out_agent.fuse_ctrl_rst_out_agent_monitor.txn_stream -radix string -tag F0
wave group fuse_ctrl_rst_out_agent_bus
wave add -group fuse_ctrl_rst_out_agent_bus hdl_top.fuse_ctrl_rst_out_agent_bus.* -radix hexadecimal -tag F0
wave group fuse_ctrl_rst_out_agent_bus -collapse
wave insertion [expr [wave index insertpoint] +1]
wave spacer -backgroundcolor Salmon { fuse_ctrl_core_axi_write_in_if_agent }
wave add uvm_test_top.environment.fuse_ctrl_core_axi_write_in_if_agent.fuse_ctrl_core_axi_write_in_if_agent_monitor.txn_stream -radix string -tag F0
wave group fuse_ctrl_core_axi_write_in_if_agent_bus
wave add -group fuse_ctrl_core_axi_write_in_if_agent_bus hdl_top.fuse_ctrl_core_axi_write_in_if_agent_bus.* -radix hexadecimal -tag F0
wave group fuse_ctrl_core_axi_write_in_if_agent_bus -collapse
wave insertion [expr [wave index insertpoint] +1]
wave spacer -backgroundcolor Salmon { fuse_ctrl_core_axi_write_out_if_agent }
wave add uvm_test_top.environment.fuse_ctrl_core_axi_write_out_if_agent.fuse_ctrl_core_axi_write_out_if_agent_monitor.txn_stream -radix string -tag F0
wave group fuse_ctrl_core_axi_write_out_if_agent_bus
wave add -group fuse_ctrl_core_axi_write_out_if_agent_bus hdl_top.fuse_ctrl_core_axi_write_out_if_agent_bus.* -radix hexadecimal -tag F0
wave group fuse_ctrl_core_axi_write_out_if_agent_bus -collapse
wave insertion [expr [wave index insertpoint] +1]
wave spacer -backgroundcolor Salmon { fuse_ctrl_prim_axi_write_in_if_agent }
wave add uvm_test_top.environment.fuse_ctrl_prim_axi_write_in_if_agent.fuse_ctrl_prim_axi_write_in_if_agent_monitor.txn_stream -radix string -tag F0
wave group fuse_ctrl_prim_axi_write_in_if_agent_bus
wave add -group fuse_ctrl_prim_axi_write_in_if_agent_bus hdl_top.fuse_ctrl_prim_axi_write_in_if_agent_bus.* -radix hexadecimal -tag F0
wave group fuse_ctrl_prim_axi_write_in_if_agent_bus -collapse
wave insertion [expr [wave index insertpoint] +1]
wave spacer -backgroundcolor Salmon { fuse_ctrl_prim_axi_write_out_if_agent }
wave add uvm_test_top.environment.fuse_ctrl_prim_axi_write_out_if_agent.fuse_ctrl_prim_axi_write_out_if_agent_monitor.txn_stream -radix string -tag F0
wave group fuse_ctrl_prim_axi_write_out_if_agent_bus
wave add -group fuse_ctrl_prim_axi_write_out_if_agent_bus hdl_top.fuse_ctrl_prim_axi_write_out_if_agent_bus.* -radix hexadecimal -tag F0
wave group fuse_ctrl_prim_axi_write_out_if_agent_bus -collapse
wave insertion [expr [wave index insertpoint] +1]
wave spacer -backgroundcolor Salmon { fuse_ctrl_core_axi_read_in_if_agent }
wave add uvm_test_top.environment.fuse_ctrl_core_axi_read_in_if_agent.fuse_ctrl_core_axi_read_in_if_agent_monitor.txn_stream -radix string -tag F0
wave group fuse_ctrl_core_axi_read_in_if_agent_bus
wave add -group fuse_ctrl_core_axi_read_in_if_agent_bus hdl_top.fuse_ctrl_core_axi_read_in_if_agent_bus.* -radix hexadecimal -tag F0
wave group fuse_ctrl_core_axi_read_in_if_agent_bus -collapse
wave insertion [expr [wave index insertpoint] +1]
wave spacer -backgroundcolor Salmon { fuse_ctrl_core_axi_read_out_if_agent }
wave add uvm_test_top.environment.fuse_ctrl_core_axi_read_out_if_agent.fuse_ctrl_core_axi_read_out_if_agent_monitor.txn_stream -radix string -tag F0
wave group fuse_ctrl_core_axi_read_out_if_agent_bus
wave add -group fuse_ctrl_core_axi_read_out_if_agent_bus hdl_top.fuse_ctrl_core_axi_read_out_if_agent_bus.* -radix hexadecimal -tag F0
wave group fuse_ctrl_core_axi_read_out_if_agent_bus -collapse
wave insertion [expr [wave index insertpoint] +1]
wave spacer -backgroundcolor Salmon { fuse_ctrl_prim_axi_read_in_if_agent }
wave add uvm_test_top.environment.fuse_ctrl_prim_axi_read_in_if_agent.fuse_ctrl_prim_axi_read_in_if_agent_monitor.txn_stream -radix string -tag F0
wave group fuse_ctrl_prim_axi_read_in_if_agent_bus
wave add -group fuse_ctrl_prim_axi_read_in_if_agent_bus hdl_top.fuse_ctrl_prim_axi_read_in_if_agent_bus.* -radix hexadecimal -tag F0
wave group fuse_ctrl_prim_axi_read_in_if_agent_bus -collapse
wave insertion [expr [wave index insertpoint] +1]
wave spacer -backgroundcolor Salmon { fuse_ctrl_prim_axi_read_out_if_agent }
wave add uvm_test_top.environment.fuse_ctrl_prim_axi_read_out_if_agent.fuse_ctrl_prim_axi_read_out_if_agent_monitor.txn_stream -radix string -tag F0
wave group fuse_ctrl_prim_axi_read_out_if_agent_bus
wave add -group fuse_ctrl_prim_axi_read_out_if_agent_bus hdl_top.fuse_ctrl_prim_axi_read_out_if_agent_bus.* -radix hexadecimal -tag F0
wave group fuse_ctrl_prim_axi_read_out_if_agent_bus -collapse
wave insertion [expr [wave index insertpoint] +1]
wave spacer -backgroundcolor Salmon { fuse_ctrl_secreg_axi_read_in_if_agent }
wave add uvm_test_top.environment.fuse_ctrl_secreg_axi_read_in_if_agent.fuse_ctrl_secreg_axi_read_in_if_agent_monitor.txn_stream -radix string -tag F0
wave group fuse_ctrl_secreg_axi_read_in_if_agent_bus
wave add -group fuse_ctrl_secreg_axi_read_in_if_agent_bus hdl_top.fuse_ctrl_secreg_axi_read_in_if_agent_bus.* -radix hexadecimal -tag F0
wave group fuse_ctrl_secreg_axi_read_in_if_agent_bus -collapse
wave insertion [expr [wave index insertpoint] +1]
wave spacer -backgroundcolor Salmon { fuse_ctrl_secreg_axi_read_out_if_agent }
wave add uvm_test_top.environment.fuse_ctrl_secreg_axi_read_out_if_agent.fuse_ctrl_secreg_axi_read_out_if_agent_monitor.txn_stream -radix string -tag F0
wave group fuse_ctrl_secreg_axi_read_out_if_agent_bus
wave add -group fuse_ctrl_secreg_axi_read_out_if_agent_bus hdl_top.fuse_ctrl_secreg_axi_read_out_if_agent_bus.* -radix hexadecimal -tag F0
wave group fuse_ctrl_secreg_axi_read_out_if_agent_bus -collapse
wave insertion [expr [wave index insertpoint] +1]
wave spacer -backgroundcolor Salmon { fuse_ctrl_lc_otp_in_if_agent }
wave add uvm_test_top.environment.fuse_ctrl_lc_otp_in_if_agent.fuse_ctrl_lc_otp_in_if_agent_monitor.txn_stream -radix string -tag F0
wave group fuse_ctrl_lc_otp_in_if_agent_bus
wave add -group fuse_ctrl_lc_otp_in_if_agent_bus hdl_top.fuse_ctrl_lc_otp_in_if_agent_bus.* -radix hexadecimal -tag F0
wave group fuse_ctrl_lc_otp_in_if_agent_bus -collapse
wave insertion [expr [wave index insertpoint] +1]
wave spacer -backgroundcolor Salmon { fuse_ctrl_lc_otp_out_if_agent }
wave add uvm_test_top.environment.fuse_ctrl_lc_otp_out_if_agent.fuse_ctrl_lc_otp_out_if_agent_monitor.txn_stream -radix string -tag F0
wave group fuse_ctrl_lc_otp_out_if_agent_bus
wave add -group fuse_ctrl_lc_otp_out_if_agent_bus hdl_top.fuse_ctrl_lc_otp_out_if_agent_bus.* -radix hexadecimal -tag F0
wave group fuse_ctrl_lc_otp_out_if_agent_bus -collapse
wave insertion [expr [wave index insertpoint] +1]
wave spacer -backgroundcolor Salmon { fuse_ctrl_in_if_agent }
wave add uvm_test_top.environment.fuse_ctrl_in_if_agent.fuse_ctrl_in_if_agent_monitor.txn_stream -radix string -tag F0
wave group fuse_ctrl_in_if_agent_bus
wave add -group fuse_ctrl_in_if_agent_bus hdl_top.fuse_ctrl_in_if_agent_bus.* -radix hexadecimal -tag F0
wave group fuse_ctrl_in_if_agent_bus -collapse
wave insertion [expr [wave index insertpoint] +1]
wave spacer -backgroundcolor Salmon { fuse_ctrl_out_if_agent }
wave add uvm_test_top.environment.fuse_ctrl_out_if_agent.fuse_ctrl_out_if_agent_monitor.txn_stream -radix string -tag F0
wave group fuse_ctrl_out_if_agent_bus
wave add -group fuse_ctrl_out_if_agent_bus hdl_top.fuse_ctrl_out_if_agent_bus.* -radix hexadecimal -tag F0
wave group fuse_ctrl_out_if_agent_bus -collapse
wave insertion [expr [wave index insertpoint] +1]

wave update on
WaveSetStreamView

