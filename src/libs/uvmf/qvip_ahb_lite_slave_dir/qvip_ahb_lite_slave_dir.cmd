// Version '20220406'
// Library '2022.2:04/20/2022:16:06'
"Configurator" create VIP_instance 2022.2:MGC/amba/ahb
"Configurator" change type ahb_lite_slave rename
"Configurator" change instance /top/ahb_lite_slave_0 agent ahb_lite_slave_0
"Configurator" change variable agent.agent_type AHB_MASTER
"Configurator" sequence add ahb_lite_slave_0 ahb_single_rd_deparam_seq
"Configurator" sequence add ahb_lite_slave_0 ahb_single_wr_deparam_seq 0
"Configurator" change instance /top/ahb_lite_slave_0 bfm
"Configurator" change instance /top/ahb_lite_slave_0 agent ahb_lite_slave_0
"Configurator" change instance /top/ahb_lite_slave_0 rtl ahb_lite_slave_0
"Configurator" change instance /top/ahb_lite_slave_0 agent ahb_lite_slave_0
"Configurator" address_map create MEM
"Configurator" address_map create CSR
"Configurator" address_map create REG
"Configurator" change variable vip_config.addr_map MEM
"Configurator" address_map delete REG
"Configurator" address_map delete CSR
"Configurator" address_map delete MEM
"Configurator" address_map create MBOX
"Configurator" address_map MBOX add MAP_NORMAL,"MEM",0,MAP_NS,4'h0,64'h30000000,64'h20000,MEM_NORMAL,MAP_NORM_SEC_DATA
"Configurator" address_map MBOX add MAP_NORMAL,"CSR",1,MAP_NS,4'h0,64'h30030000,64'h10000,MEM_NORMAL,MAP_NORM_SEC_DATA
"Configurator" address_map MBOX add MAP_NORMAL,"CSR_",1,MAP_NS,4'h0,64'h30030000,64'h10000,MEM_NORMAL,MAP_NORM_SEC_DATA
"Configurator" address_map MBOX update MAP_NORMAL,"CSR",1,MAP_NS,4'h0,64'h30020000,64'h10000,MEM_NORMAL,MAP_NORM_SEC_DATA
"Configurator" address_map MBOX update MAP_NORMAL,"REG",2,MAP_NS,4'h0,64'h30030000,64'h10000,MEM_NORMAL,MAP_NORM_SEC_DATA
"Configurator" change variable vip_config.addr_map MBOX
"Configurator" change instance /top/default_clk_gen
"Configurator" change instance /top/default_reset_gen
"Configurator" change instance /top/ahb_lite_slave_0
"Configurator" change instance /top/ahb_lite_slave_0 bfm
"Configurator" change instance /top/ahb_lite_slave_0 agent ahb_lite_slave_0
"Configurator" change instance /top/ahb_lite_slave_0 rtl ahb_lite_slave_0
"Configurator" change hash_param WDATA_WIDTH 64
"Configurator" change hash_param RDATA_WIDTH 64
// "Configurator" generate options
// Thu Nov 3 2022 21:32:42
