//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
//----------------------------------------------------------------------
// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------                     
//               
// Description: This top level module instantiates all synthesizable
//    static content.  This and tb_top.sv are the two top level modules
//    of the simulation.  
//
//    This module instantiates the following:
//        DUT: The Design Under Test
//        Interfaces:  Signal bundles that contain signals connected to DUT
//        Driver BFM's: BFM's that actively drive interface signals
//        Monitor BFM's: BFM's that passively monitor interface signals
//
//----------------------------------------------------------------------

//----------------------------------------------------------------------
//

module hdl_top;

import kv_parameters_pkg::*;
import qvip_ahb_lite_slave_params_pkg::*;
import uvmf_base_pkg_hdl::*;

  // pragma attribute hdl_top partition_module_xrtl                                            
  hdl_qvip_ahb_lite_slave 
      #(
        .AHB_LITE_SLAVE_0_ACTIVE(1),
        .UNIQUE_ID("uvm_test_top.environment.qvip_ahb_lite_slave_subenv."),
        .EXT_CLK_RESET(1)
       ) uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl();

// pragma uvmf custom clock_generator begin
  bit clk;
  // Instantiate a clk driver 
  // tbx clkgen
  initial begin
    clk = 0;
    #0ns;
    forever begin
      clk = ~clk;
      #5ns;
    end
  end
// pragma uvmf custom clock_generator end

// pragma uvmf custom reset_generator begin
  bit rst;
  // Instantiate a rst driver
  // tbx clkgen
  initial begin
    rst = 0; 
    #200ns;
    rst =  1; 
  end
// pragma uvmf custom reset_generator end

  // pragma uvmf custom module_item_additional begin
  // pragma uvmf custom module_item_additional end

  // Instantiate the signal bundle, monitor bfm and driver bfm for each interface.
  // The signal bundle, _if, contains signals to be connected to the DUT.
  // The monitor, monitor_bfm, observes the bus, _if, and captures transactions.
  // The driver, driver_bfm, drives transactions onto the bus, _if.
  kv_rst_if  kv_rst_agent_bus(
     // pragma uvmf custom kv_rst_agent_bus_connections begin
     .clk(clk), .dummy(1'b1)
     // pragma uvmf custom kv_rst_agent_bus_connections end
     );
  kv_write_if  kv_hmac_write_agent_bus(
     // pragma uvmf custom kv_hmac_write_agent_bus_connections begin
     .clk(clk), .dummy(1'b1)
     // pragma uvmf custom kv_hmac_write_agent_bus_connections end
     );
  kv_write_if  kv_sha512_write_agent_bus(
     // pragma uvmf custom kv_sha512_write_agent_bus_connections begin
     .clk(clk), .dummy(1'b1)
     // pragma uvmf custom kv_sha512_write_agent_bus_connections end
     );
  kv_write_if  kv_ecc_write_agent_bus(
     // pragma uvmf custom kv_ecc_write_agent_bus_connections begin
     .clk(clk), .dummy(1'b1)
     // pragma uvmf custom kv_ecc_write_agent_bus_connections end
     );
  kv_write_if  kv_doe_write_agent_bus(
     // pragma uvmf custom kv_doe_write_agent_bus_connections begin
     .clk(clk), .dummy(1'b1)
     // pragma uvmf custom kv_doe_write_agent_bus_connections end
     );
  kv_read_if  kv_hmac_key_read_agent_bus(
     // pragma uvmf custom kv_hmac_key_read_agent_bus_connections begin
     .clk(clk), .dummy(1'b1)
     // pragma uvmf custom kv_hmac_key_read_agent_bus_connections end
     );
  kv_read_if  kv_hmac_block_read_agent_bus(
     // pragma uvmf custom kv_hmac_block_read_agent_bus_connections begin
     .clk(clk), .dummy(1'b1)
     // pragma uvmf custom kv_hmac_block_read_agent_bus_connections end
     );
  kv_read_if  kv_sha512_block_read_agent_bus(
     // pragma uvmf custom kv_sha512_block_read_agent_bus_connections begin
     .clk(clk), .dummy(1'b1)
     // pragma uvmf custom kv_sha512_block_read_agent_bus_connections end
     );
  kv_read_if  kv_ecc_privkey_read_agent_bus(
     // pragma uvmf custom kv_ecc_privkey_read_agent_bus_connections begin
     .clk(clk), .dummy(1'b1)
     // pragma uvmf custom kv_ecc_privkey_read_agent_bus_connections end
     );
  kv_read_if  kv_ecc_seed_read_agent_bus(
     // pragma uvmf custom kv_ecc_seed_read_agent_bus_connections begin
     .clk(clk), .dummy(1'b1)
     // pragma uvmf custom kv_ecc_seed_read_agent_bus_connections end
     );

  kv_rst_monitor_bfm  kv_rst_agent_mon_bfm(kv_rst_agent_bus.monitor_port);
  kv_write_monitor_bfm  kv_hmac_write_agent_mon_bfm(kv_hmac_write_agent_bus.monitor_port);
  kv_write_monitor_bfm  kv_sha512_write_agent_mon_bfm(kv_sha512_write_agent_bus.monitor_port);
  kv_write_monitor_bfm  kv_ecc_write_agent_mon_bfm(kv_ecc_write_agent_bus.monitor_port);
  kv_write_monitor_bfm  kv_doe_write_agent_mon_bfm(kv_doe_write_agent_bus.monitor_port);
  kv_read_monitor_bfm  kv_hmac_key_read_agent_mon_bfm(kv_hmac_key_read_agent_bus.monitor_port);
  kv_read_monitor_bfm  kv_hmac_block_read_agent_mon_bfm(kv_hmac_block_read_agent_bus.monitor_port);
  kv_read_monitor_bfm  kv_sha512_block_read_agent_mon_bfm(kv_sha512_block_read_agent_bus.monitor_port);
  kv_read_monitor_bfm  kv_ecc_privkey_read_agent_mon_bfm(kv_ecc_privkey_read_agent_bus.monitor_port);
  kv_read_monitor_bfm  kv_ecc_seed_read_agent_mon_bfm(kv_ecc_seed_read_agent_bus.monitor_port);
  kv_rst_driver_bfm  kv_rst_agent_drv_bfm(kv_rst_agent_bus.initiator_port);
  kv_write_driver_bfm  kv_hmac_write_agent_drv_bfm(kv_hmac_write_agent_bus.initiator_port);
  kv_write_driver_bfm  kv_sha512_write_agent_drv_bfm(kv_sha512_write_agent_bus.initiator_port);
  kv_write_driver_bfm  kv_ecc_write_agent_drv_bfm(kv_ecc_write_agent_bus.initiator_port);
  kv_write_driver_bfm  kv_doe_write_agent_drv_bfm(kv_doe_write_agent_bus.initiator_port);
  kv_read_driver_bfm  kv_hmac_key_read_agent_drv_bfm(kv_hmac_key_read_agent_bus.initiator_port);
  kv_read_driver_bfm  kv_hmac_block_read_agent_drv_bfm(kv_hmac_block_read_agent_bus.initiator_port);
  kv_read_driver_bfm  kv_sha512_block_read_agent_drv_bfm(kv_sha512_block_read_agent_bus.initiator_port);
  kv_read_driver_bfm  kv_ecc_privkey_read_agent_drv_bfm(kv_ecc_privkey_read_agent_bus.initiator_port);
  kv_read_driver_bfm  kv_ecc_seed_read_agent_drv_bfm(kv_ecc_seed_read_agent_bus.initiator_port);

  // pragma uvmf custom dut_instantiation begin
  // AHB Clock/reset
  assign uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.default_clk_gen_CLK     = clk;
  assign uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.default_reset_gen_RESET = kv_rst_agent_bus.rst_b;

  import kv_defines_pkg::*;
  kv_defines_pkg::kv_read_t  [kv_defines_pkg::KV_NUM_READ-1:0]  kv_read ;
  kv_defines_pkg::kv_rd_resp_t  [kv_defines_pkg::KV_NUM_READ-1:0]  kv_rd_resp ;
  kv_defines_pkg::kv_write_t [kv_defines_pkg::KV_NUM_WRITE-1:0]  kv_write;
  kv_defines_pkg::kv_wr_resp_t [kv_defines_pkg::KV_NUM_WRITE-1:0]  kv_wr_resp;
  localparam HMAC_WRITE_IDX   = 0;
  localparam SHA512_WRITE_IDX = 1;
  localparam ECC_WRITE_IDX    = 2;
  localparam DOE_WRITE_IDX    = 3;
  localparam HMAC_KEY_READ_IDX     = 0;
  localparam HMAC_BLOCK_READ_IDX   = 1;
  localparam SHA512_BLOCK_READ_IDX = 2;
  localparam ECC_PRIVKEY_READ_IDX  = 3;
  localparam ECC_SEED_READ_IDX     = 4;

  always_comb begin
    kv_write[HMAC_WRITE_IDX  ] = kv_hmac_write_agent_bus.kv_write;
    kv_write[SHA512_WRITE_IDX] = kv_sha512_write_agent_bus.kv_write;
    kv_write[ECC_WRITE_IDX   ] = kv_ecc_write_agent_bus.kv_write;
    kv_write[DOE_WRITE_IDX   ] = kv_doe_write_agent_bus.kv_write;
    kv_read[HMAC_KEY_READ_IDX    ] = kv_hmac_key_read_agent_bus.kv_read;
    kv_read[HMAC_BLOCK_READ_IDX  ] = kv_hmac_block_read_agent_bus.kv_read;
    kv_read[SHA512_BLOCK_READ_IDX] = kv_sha512_block_read_agent_bus.kv_read;
    kv_read[ECC_PRIVKEY_READ_IDX ] = kv_ecc_privkey_read_agent_bus.kv_read;
    kv_read[ECC_SEED_READ_IDX    ] = kv_ecc_seed_read_agent_bus.kv_read;
  end
  assign kv_hmac_key_read_agent_bus.kv_rd_resp     = kv_rd_resp[HMAC_KEY_READ_IDX    ];
  assign kv_hmac_block_read_agent_bus.kv_rd_resp   = kv_rd_resp[HMAC_BLOCK_READ_IDX  ];
  assign kv_sha512_block_read_agent_bus.kv_rd_resp = kv_rd_resp[SHA512_BLOCK_READ_IDX];
  assign kv_ecc_privkey_read_agent_bus.kv_rd_resp  = kv_rd_resp[ECC_PRIVKEY_READ_IDX ];
  assign kv_ecc_seed_read_agent_bus.kv_rd_resp     = kv_rd_resp[ECC_SEED_READ_IDX    ];

  assign kv_hmac_write_agent_bus.kv_wr_resp        = kv_wr_resp[HMAC_WRITE_IDX       ];
  assign kv_sha512_write_agent_bus.kv_wr_resp      = kv_wr_resp[SHA512_WRITE_IDX     ];
  assign kv_ecc_write_agent_bus.kv_wr_resp         = kv_wr_resp[ECC_WRITE_IDX        ];
  assign kv_doe_write_agent_bus.kv_wr_resp         = kv_wr_resp[DOE_WRITE_IDX        ];

  kv #(
      .AHB_ADDR_WIDTH(15       ),
      .AHB_DATA_WIDTH(64       )
  ) dut (
      .clk              (clk          ),
      .rst_b            (kv_rst_agent_bus.rst_b        ),
      .core_only_rst_b  (kv_rst_agent_bus.core_only_rst_b),
      .cptra_pwrgood    (kv_rst_agent_bus.cptra_pwrgood),

      .debugUnlock_or_scan_mode_switch (kv_rst_agent_bus.debug_locked),

      //uC AHB Lite Interface
      //from SLAVES PORT
      .haddr_i    (uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HADDR[14:0]),
      .hwdata_i   (uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HWDATA     ),
      .hsel_i     (1'b1                                                                                     ),
      .hwrite_i   (uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HWRITE     ),
      .hready_i   (uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HREADYOUT  ),
      .htrans_i   (uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HTRANS     ),
      .hsize_i    (uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HSIZE      ),

      .hresp_o    (uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HRESP      ),
      .hreadyout_o(uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HREADY     ),
      .hrdata_o   (uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HRDATA     ),

      .kv_read (kv_read ),
      .kv_write(kv_write),
      .kv_rd_resp(kv_rd_resp),
      .kv_wr_resp(kv_wr_resp)
  );
    assign uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HBURST    = 3'b0;
    assign uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HPROT     = 7'b0;
    assign uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HMASTLOCK = 1'b0;
    assign uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HSEL      = 1'b0;
    assign uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HNONSEC   = 1'b0;
    assign uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HAUSER    = 64'b0;
    assign uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HWUSER    = 64'b0;
    assign uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HRUSER    = 64'b0;
    assign uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_mult_HSEL = 16'b0;
    assign uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HEXCL     = 1'b0;
    assign uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HMASTER   = 16'b0;
    assign uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HEXOKAY   = 1'b0;
  // pragma uvmf custom dut_instantiation end

  initial begin      // tbx vif_binding_block 
    import uvm_pkg::uvm_config_db;
    // The monitor_bfm and driver_bfm for each interface is placed into the uvm_config_db.
    // They are placed into the uvm_config_db using the string names defined in the parameters package.
    // The string names are passed to the agent configurations by test_top through the top level configuration.
    // They are retrieved by the agents configuration class for use by the agent.
    uvm_config_db #( virtual kv_rst_monitor_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , kv_rst_agent_BFM , kv_rst_agent_mon_bfm ); 
    uvm_config_db #( virtual kv_write_monitor_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , kv_hmac_write_agent_BFM , kv_hmac_write_agent_mon_bfm ); 
    uvm_config_db #( virtual kv_write_monitor_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , kv_sha512_write_agent_BFM , kv_sha512_write_agent_mon_bfm ); 
    uvm_config_db #( virtual kv_write_monitor_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , kv_ecc_write_agent_BFM , kv_ecc_write_agent_mon_bfm ); 
    uvm_config_db #( virtual kv_write_monitor_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , kv_doe_write_agent_BFM , kv_doe_write_agent_mon_bfm ); 
    uvm_config_db #( virtual kv_read_monitor_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , kv_hmac_key_read_agent_BFM , kv_hmac_key_read_agent_mon_bfm ); 
    uvm_config_db #( virtual kv_read_monitor_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , kv_hmac_block_read_agent_BFM , kv_hmac_block_read_agent_mon_bfm ); 
    uvm_config_db #( virtual kv_read_monitor_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , kv_sha512_block_read_agent_BFM , kv_sha512_block_read_agent_mon_bfm ); 
    uvm_config_db #( virtual kv_read_monitor_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , kv_ecc_privkey_read_agent_BFM , kv_ecc_privkey_read_agent_mon_bfm ); 
    uvm_config_db #( virtual kv_read_monitor_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , kv_ecc_seed_read_agent_BFM , kv_ecc_seed_read_agent_mon_bfm ); 
    uvm_config_db #( virtual kv_rst_driver_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , kv_rst_agent_BFM , kv_rst_agent_drv_bfm  );
    uvm_config_db #( virtual kv_write_driver_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , kv_hmac_write_agent_BFM , kv_hmac_write_agent_drv_bfm  );
    uvm_config_db #( virtual kv_write_driver_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , kv_sha512_write_agent_BFM , kv_sha512_write_agent_drv_bfm  );
    uvm_config_db #( virtual kv_write_driver_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , kv_ecc_write_agent_BFM , kv_ecc_write_agent_drv_bfm  );
    uvm_config_db #( virtual kv_write_driver_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , kv_doe_write_agent_BFM , kv_doe_write_agent_drv_bfm  );
    uvm_config_db #( virtual kv_read_driver_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , kv_hmac_key_read_agent_BFM , kv_hmac_key_read_agent_drv_bfm  );
    uvm_config_db #( virtual kv_read_driver_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , kv_hmac_block_read_agent_BFM , kv_hmac_block_read_agent_drv_bfm  );
    uvm_config_db #( virtual kv_read_driver_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , kv_sha512_block_read_agent_BFM , kv_sha512_block_read_agent_drv_bfm  );
    uvm_config_db #( virtual kv_read_driver_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , kv_ecc_privkey_read_agent_BFM , kv_ecc_privkey_read_agent_drv_bfm  );
    uvm_config_db #( virtual kv_read_driver_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , kv_ecc_seed_read_agent_BFM , kv_ecc_seed_read_agent_drv_bfm  );
  end

endmodule

// pragma uvmf custom external begin
// pragma uvmf custom external end

