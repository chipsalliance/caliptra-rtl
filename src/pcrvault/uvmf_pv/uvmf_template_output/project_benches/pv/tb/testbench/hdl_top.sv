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

import pv_parameters_pkg::*;
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
  pv_rst_if  pv_rst_agent_bus(
     // pragma uvmf custom pv_rst_agent_bus_connections begin
     .clk(clk), .dummy(1'b1)
     // pragma uvmf custom pv_rst_agent_bus_connections end
     );
  pv_write_if  pv_sha512_write_agent_bus(
     // pragma uvmf custom pv_sha512_write_agent_bus_connections begin
     .clk(clk), .dummy(1'b1)
     // pragma uvmf custom pv_sha512_write_agent_bus_connections end
     );
  pv_read_if  pv_sha512_block_read_agent_bus(
     // pragma uvmf custom pv_sha512_block_read_agent_bus_connections begin
     .clk(clk), .dummy(1'b1)
     // pragma uvmf custom pv_sha512_block_read_agent_bus_connections end
     );
  pv_rst_monitor_bfm  pv_rst_agent_mon_bfm(pv_rst_agent_bus.monitor_port);
  pv_write_monitor_bfm  pv_sha512_write_agent_mon_bfm(pv_sha512_write_agent_bus.monitor_port);
  pv_read_monitor_bfm  pv_sha512_block_read_agent_mon_bfm(pv_sha512_block_read_agent_bus.monitor_port);
  pv_rst_driver_bfm  pv_rst_agent_drv_bfm(pv_rst_agent_bus.initiator_port);
  pv_write_driver_bfm  pv_sha512_write_agent_drv_bfm(pv_sha512_write_agent_bus.initiator_port);
  pv_read_driver_bfm  pv_sha512_block_read_agent_drv_bfm(pv_sha512_block_read_agent_bus.initiator_port);

  // pragma uvmf custom dut_instantiation begin
  assign uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.default_clk_gen_CLK     = clk;
  assign uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.default_reset_gen_RESET = pv_rst_agent_bus.rst_b;

  import pv_defines_pkg::*;
  pv_defines_pkg::pv_read_t     [pv_defines_pkg::PV_NUM_READ-1:0]  pv_read;
  pv_defines_pkg::pv_rd_resp_t  [pv_defines_pkg::PV_NUM_READ-1:0]  pv_rd_resp;
  pv_defines_pkg::pv_write_t    [pv_defines_pkg::PV_NUM_WRITE-1:0] pv_write;
  pv_defines_pkg::pv_wr_resp_t  [pv_defines_pkg::PV_NUM_WRITE-1:0] pv_wr_resp;

  localparam SHA512_WRITE_IDX = 0;
  localparam SHA512_BLOCK_READ_IDX = 0;

  always_comb begin
    pv_write[SHA512_WRITE_IDX]      = pv_sha512_write_agent_bus.pv_write;
    pv_read [SHA512_BLOCK_READ_IDX] = pv_sha512_block_read_agent_bus.pv_read;
  end

  assign pv_sha512_block_read_agent_bus.pv_rd_resp  = pv_rd_resp[SHA512_BLOCK_READ_IDX];
  assign pv_sha512_write_agent_bus.pv_wr_resp       = pv_wr_resp[SHA512_WRITE_IDX];

  pv #(
    .AHB_ADDR_WIDTH(15), //(`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_PV)),
    .AHB_DATA_WIDTH(64) //(`CALIPTRA_AHB_HDATA_SIZE)
  )
  dut
  (
      .clk           (clk),
      .rst_b         (pv_rst_agent_bus.rst_b),
      .cptra_pwrgood (pv_rst_agent_bus.cptra_pwrgood),
      .core_only_rst_b(pv_rst_agent_bus.core_only_rst_b),
      .fw_update_rst_window(pv_rst_agent_bus.fw_update_rst_window),
      .haddr_i       (uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HADDR[14:0]),
      .hwdata_i      (uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HWDATA     ),
      .hsel_i        (1'b1),
      .hwrite_i      (uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HWRITE     ),
      .hready_i      (uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HREADYOUT  ),
      .htrans_i      (uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HTRANS     ),
      .hsize_i       (uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HSIZE      ),
      .hresp_o       (uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HRESP      ),
      .hreadyout_o   (uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HREADY     ),
      .hrdata_o      (uvm_test_top_environment_qvip_ahb_lite_slave_subenv_qvip_hdl.ahb_lite_slave_0_HRDATA     ),

      .pv_read       (pv_read),
      .pv_write      (pv_write),
      .pv_rd_resp    (pv_rd_resp),
      .pv_wr_resp    (pv_wr_resp)
  );

  pcrvault_cov_bind i_pcrvault_cov_bind();

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
    uvm_config_db #( virtual pv_rst_monitor_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , pv_rst_agent_BFM , pv_rst_agent_mon_bfm ); 
    uvm_config_db #( virtual pv_write_monitor_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , pv_sha512_write_agent_BFM , pv_sha512_write_agent_mon_bfm ); 
    uvm_config_db #( virtual pv_read_monitor_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , pv_sha512_block_read_agent_BFM , pv_sha512_block_read_agent_mon_bfm ); 
    uvm_config_db #( virtual pv_rst_driver_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , pv_rst_agent_BFM , pv_rst_agent_drv_bfm  );
    uvm_config_db #( virtual pv_write_driver_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , pv_sha512_write_agent_BFM , pv_sha512_write_agent_drv_bfm  );
    uvm_config_db #( virtual pv_read_driver_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , pv_sha512_block_read_agent_BFM , pv_sha512_block_read_agent_drv_bfm  );
  end

endmodule

// pragma uvmf custom external begin
// pragma uvmf custom external end

