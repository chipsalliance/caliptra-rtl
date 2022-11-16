onerror resume
wave update off
wave tags  F0
wave spacer -group Transaction -backgroundcolor Salmon {AHB_LITE_SLAVE_0 Txns}
wave group Transaction -backgroundcolor #004466
wave add -group Transaction hdl_qvip_ahb_lite_slave.ahb_lite_slave_0.ahb_lite_slave_0_bfm.burst_transfer -tag F0 -radix string
wave add -group Transaction hdl_qvip_ahb_lite_slave.ahb_lite_slave_0.ahb_lite_slave_0_bfm.single_transfer -tag F0 -radix string
wave add -group Transaction hdl_qvip_ahb_lite_slave.ahb_lite_slave_0.ahb_lite_slave_0_bfm.master_request_phase -tag F0 -radix string
wave add -group Transaction hdl_qvip_ahb_lite_slave.ahb_lite_slave_0.ahb_lite_slave_0_bfm.master_control_phase -tag F0 -radix string
wave add -group Transaction hdl_qvip_ahb_lite_slave.ahb_lite_slave_0.ahb_lite_slave_0_bfm.master_wr_data_phase -tag F0 -radix string
wave add -group Transaction hdl_qvip_ahb_lite_slave.ahb_lite_slave_0.ahb_lite_slave_0_bfm.user_data_phase -tag F0 -radix string
wave add -group Transaction hdl_qvip_ahb_lite_slave.ahb_lite_slave_0.ahb_lite_slave_0_bfm.user_address_phase -tag F0 -radix string
wave add -group Transaction hdl_qvip_ahb_lite_slave.ahb_lite_slave_0.ahb_lite_slave_0_bfm.master_rd_data_phase -tag F0 -radix string
wave add -group Transaction hdl_qvip_ahb_lite_slave.ahb_lite_slave_0.ahb_lite_slave_0_bfm.master_response_phase -tag F0 -radix string
wave add -group Transaction hdl_qvip_ahb_lite_slave.ahb_lite_slave_0.ahb_lite_slave_0_bfm.master_control_cycle -tag F0 -radix string
wave add -group Transaction hdl_qvip_ahb_lite_slave.ahb_lite_slave_0.ahb_lite_slave_0_bfm.master_wr_data_cycle -tag F0 -radix string
wave add -group Transaction hdl_qvip_ahb_lite_slave.ahb_lite_slave_0.ahb_lite_slave_0_bfm.user_data_cycle -tag F0 -radix string
wave add -group Transaction hdl_qvip_ahb_lite_slave.ahb_lite_slave_0.ahb_lite_slave_0_bfm.user_address_cycle -tag F0 -radix string
wave add -group Transaction hdl_qvip_ahb_lite_slave.ahb_lite_slave_0.ahb_lite_slave_0_bfm.master_rd_data_cycle -tag F0 -radix string
wave add -group Transaction hdl_qvip_ahb_lite_slave.ahb_lite_slave_0.ahb_lite_slave_0_bfm.slave_single_transfer -tag F0 -radix string
wave add -group Transaction hdl_qvip_ahb_lite_slave.ahb_lite_slave_0.ahb_lite_slave_0_bfm.slave_control_phase -tag F0 -radix string
wave add -group Transaction hdl_qvip_ahb_lite_slave.ahb_lite_slave_0.ahb_lite_slave_0_bfm.slave_wr_data_phase -tag F0 -radix string
wave add -group Transaction hdl_qvip_ahb_lite_slave.ahb_lite_slave_0.ahb_lite_slave_0_bfm.slave_user_data_phase -tag F0 -radix string
wave add -group Transaction hdl_qvip_ahb_lite_slave.ahb_lite_slave_0.ahb_lite_slave_0_bfm.slave_user_address_phase -tag F0 -radix string
wave add -group Transaction hdl_qvip_ahb_lite_slave.ahb_lite_slave_0.ahb_lite_slave_0_bfm.slave_rd_data_phase -tag F0 -radix string
wave add -group Transaction hdl_qvip_ahb_lite_slave.ahb_lite_slave_0.ahb_lite_slave_0_bfm.slave_response_phase -tag F0 -radix string
wave add -group Transaction hdl_qvip_ahb_lite_slave.ahb_lite_slave_0.ahb_lite_slave_0_bfm.slave_response_cycle -tag F0 -radix string
wave add -group Transaction hdl_qvip_ahb_lite_slave.ahb_lite_slave_0.ahb_lite_slave_0_bfm.slave_hsplit_cycle -tag F0 -radix string
wave add -group Transaction hdl_qvip_ahb_lite_slave.ahb_lite_slave_0.ahb_lite_slave_0_bfm.arbitration -tag F0 -radix string
wave add -group Transaction hdl_qvip_ahb_lite_slave.ahb_lite_slave_0.ahb_lite_slave_0_bfm.arbiter_request_phase -tag F0 -radix string
wave add -group Transaction hdl_qvip_ahb_lite_slave.ahb_lite_slave_0.ahb_lite_slave_0_bfm.arbiter_grant_phase -tag F0 -radix string
wave add -group Transaction hdl_qvip_ahb_lite_slave.ahb_lite_slave_0.ahb_lite_slave_0_bfm.arbiter_control_phase -tag F0 -radix string
wave add -group Transaction hdl_qvip_ahb_lite_slave.ahb_lite_slave_0.ahb_lite_slave_0_bfm.core_control_phase -tag F0 -radix string
wave add -group Transaction hdl_qvip_ahb_lite_slave.ahb_lite_slave_0.ahb_lite_slave_0_bfm.core_response_phase -tag F0 -radix string
wave add -group Transaction hdl_qvip_ahb_lite_slave.ahb_lite_slave_0.ahb_lite_slave_0_bfm.core_control_cycle -tag F0 -radix string
wave add -group Transaction hdl_qvip_ahb_lite_slave.ahb_lite_slave_0.ahb_lite_slave_0_bfm.arbiter_request_cycle -tag F0 -radix string
wave add -group Transaction hdl_qvip_ahb_lite_slave.ahb_lite_slave_0.ahb_lite_slave_0_bfm.arbiter_grant_cycle -tag F0 -radix string
wave add -group Transaction hdl_qvip_ahb_lite_slave.ahb_lite_slave_0.ahb_lite_slave_0_bfm.arbiter_control_cycle -tag F0 -radix string
wave add -group Transaction hdl_qvip_ahb_lite_slave.ahb_lite_slave_0.ahb_lite_slave_0_bfm.core_response_cycle -tag F0 -radix string
wave insertion [expr [wave index insertpoint] + 1]
wave update on
WaveSetStreamView
