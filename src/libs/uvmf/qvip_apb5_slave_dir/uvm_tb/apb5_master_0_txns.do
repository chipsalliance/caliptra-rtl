onerror resume
wave update off
wave tags  F0
wave spacer -group Transaction -backgroundcolor Salmon {APB5_MASTER_0 Txns}
wave group Transaction -backgroundcolor #004466
wave add -group Transaction hdl_qvip_apb5_slave.apb5_master_0.apb_if.apb3_transaction -tag F0 -radix string
wave add -group Transaction hdl_qvip_apb5_slave.apb5_master_0.apb_if.write -tag F0 -radix string
wave add -group Transaction hdl_qvip_apb5_slave.apb5_master_0.apb_if.read -tag F0 -radix string
wave add -group Transaction hdl_qvip_apb5_slave.apb5_master_0.apb_if.write_data_phase -tag F0 -radix string
wave add -group Transaction hdl_qvip_apb5_slave.apb5_master_0.apb_if.response_phase -tag F0 -radix string
wave add -group Transaction hdl_qvip_apb5_slave.apb5_master_0.apb_if.setup_phase -tag F0 -radix string
wave add -group Transaction hdl_qvip_apb5_slave.apb5_master_0.apb_if.access_phase -tag F0 -radix string
wave add -group Transaction hdl_qvip_apb5_slave.apb5_master_0.apb_if.wakeup_cycle -tag F0 -radix string
wave insertion [expr [wave index insertpoint] + 1]
wave update on
WaveSetStreamView
