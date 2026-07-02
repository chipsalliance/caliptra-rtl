// Copyright lowRISC contributors
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// An interface to track an AHB bus

interface ahb_if (input clk_i, input rst_ni);
  import uvm_pkg::*;
  `include "uvm_macros.svh"
  import dv_utils_pkg::if_mode_e, dv_utils_pkg::Host, dv_utils_pkg::Device, dv_utils_pkg::Monitor;

  // The interface mode.
  //
  //  - Host:    An agent is driving the interface signals through host_cb acting as a Manager.
  //  - Device:  An agent is driving the interface signals through device_cb, as a Subordinate.
  //  - Monitor: No agent is driving interface signals and the interface is purely passive.
  if_mode_e if_mode = Monitor;

  // The ADDR_WIDTH property. Set this by calling set_addr_width().
  //
  // Note: This size is not constrained in the AHB specification (issue C), but the specification
  //       recommends to set it in the range 10..64. The default value of 32 matches a historical
  //       convention (used in issues A and B of the specification). The max-footprint approach in
  //       this interface only supports widths up to 64.
  int unsigned addr_width = 32;

  // The HBURST_WIDTH property. Set this by calling set_hburst_width().
  int unsigned hburst_width = 3;

  // The HPROT_WIDTH property. Set this by calling set_hprot_width().
  int unsigned hprot_width = 7;

  // The DATA_WIDTH property. Set this by calling set_data_width().
  int unsigned data_width = 256;

  // The Write_Strobes property. Enable or disable this by calling set_has_write_strobes().
  bit          has_write_strobes = 1;

  // The number of subordinates attached to the bus. Each will have its own HSELx line, driven by a
  // decoder. Set this by calling set_num_subordinates().
  //
  // Note: There must be at least one subordinate (the default value, because this is likely to
  //       match many block-level testbenches). The max-footprint approach in this interface only
  //       supports num_subordinates <= 8.
  int unsigned num_subordinates = 1;

  // The defined manager signals
  //
  // This interface uses a max footprint approach. Signals of configurable width (like haddr) might
  // only use the lower bits.
  wire [63:0]   haddr;
  wire [2:0]    hburst;
  wire          hmastlock;
  wire [6:0]    hprot;
  wire [2:0]    hsize;
  wire [1:0]    htrans;
  wire [1023:0] hwdata;
  wire [127:0]  hwstrb;
  wire          hwrite;

  // The defined decoder signal
  //
  // This interface uses a max footprint approach. The hsel signal has configurable width so might
  // only use the lower bits.
  //
  // Note that when if_mode == Host the interface drives hsel through host_cb, grouping the decoder
  // with the manager as part of the "host side".
  wire [7:0]    hsel;

  // The defined subordinate signals
  //
  // This interface uses a max footprint approach, supporting up to 8 subordinates and a data width
  // of 1024 bits.
  wire [7:0][1023:0] hrdata;
  wire [7:0]         hreadyout;
  wire [7:0]         hresp;

  // The defined multiplexor signals
  //
  // This interface uses a max footprint approach, supporting a data width of 1024 bits. The
  // hrdata_muxed and hresp_muxed signals are the selected subordinate's hrdata and hresp signals,
  // respectively.
  //
  // When if_mode == Device, these are driven by a multiplexor built in to the interface.
  wire [1023:0] hrdata_muxed;
  wire          hready;
  wire          hresp_muxed;

  // Copies of the signals driven by host_cb (only used if if_mode == Host). The "*_driven" signals
  // are directly driven by the clocking block. The "*_internal" signals track these, but take masks
  // into account for signals with configurable length and are also cleared on reset.
  logic [63:0]   haddr_driven, haddr_internal;
  logic [2:0]    hburst_driven, hburst_internal;
  logic          hmastlock_driven, hmastlock_internal;
  logic [6:0]    hprot_driven, hprot_internal;
  logic [2:0]    hsize_driven, hsize_internal;
  logic [1:0]    htrans_driven, htrans_internal;
  logic [1023:0] hwdata_driven, hwdata_internal;
  logic [127:0]  hwstrb_driven, hwstrb_internal;
  logic          hwrite_driven, hwrite_internal;
  logic [7:0]    hsel_driven, hsel_internal;

  // Copies of the signals driven by device_cb (only used if if_mode == Device). The "*_driven"
  // signals are directly driven by the clocking block. The "*_internal" signals track these, but
  // take masks into account for signals with configurable length and are also cleared on reset.
  logic [7:0][1023:0] hrdata_driven, hrdata_internal;
  logic [7:0]         hreadyout_driven, hreadyout_internal;
  logic [7:0]         hresp_driven, hresp_internal;

  // A multiplexor is defined in the interface, for use when if_mode == Device or if_mode ==
  // Manager. This drives *_internal signals (zeroing everything combinatorially on a reset)
  //
  // The multiplexing is done with a combinatorial block, using OR to pick the value from the
  // selected subordinate. The hready signal is special and is defined to be 1 when no subordinate
  // is selected: that signal is intended for a subordinate to exert back pressure in the middle of
  // the data phase, so it doesn't make sense for it to be false when no subordinate is acting.
  logic [1023:0] hrdata_muxed_internal;
  logic          hready_internal;
  logic          hresp_muxed_internal;

  always_comb begin
    hrdata_muxed_internal = '0;
    hready_internal = 1'b1;
    hresp_muxed_internal = 1'b0;

    if (rst_ni) begin
      for (int unsigned i = 0; i < num_subordinates && i < 8; i++) begin
        if (hsel[i]) begin
          hrdata_muxed_internal  |= hrdata[i];
          hready_internal        &= hreadyout[i];
          hresp_muxed_internal   |= hresp[i];
        end
      end
    end
  end

  // Masks used when converting some *_driven signals to *_internal
  logic [63:0]        haddr_mask;
  logic [2:0]         hburst_mask;
  logic [6:0]         hprot_mask;
  logic [1023:0]      data_mask;
  logic [127:0]       strb_mask;
  logic [7:0]         hsel_mask;
  logic [7:0][1023:0] sub_data_mask;

  assign haddr_mask   = (64'b1 << addr_width) - 1;
  assign hburst_mask  = (3'b1 << hburst_width) - 1;
  assign hprot_mask   = (7'b1 << hprot_width) - 1;
  assign data_mask    = (1024'b1 << data_width) - 1;
  assign strb_mask    = has_write_strobes ? ((128'b1 << ((data_width + 7) / 8)) - 1) : '0;
  assign hsel_mask    = (8'b1 << num_subordinates) - 1;

  always_comb begin
    for (int unsigned i = 0; i < 8; i++) begin
      sub_data_mask[i] = (i < num_subordinates) ? data_mask : '0;
    end
  end

  clocking mon_cb @(posedge clk_i);
    input haddr;
    input hburst;
    input hmastlock;
    input hprot;
    input hsize;
    input htrans;
    input hwdata;
    input hwstrb;
    input hwrite;
    input hsel;
    input hrdata;
    input hreadyout;
    input hresp;
    input hrdata_muxed;
    input hready;
    input hresp_muxed;
  endclocking

  clocking host_cb @(posedge clk_i);
    output haddr     = haddr_driven;
    output hburst    = hburst_driven;
    output hmastlock = hmastlock_driven;
    output hprot     = hprot_driven;
    output hsize     = hsize_driven;
    output htrans    = htrans_driven;
    output hwdata    = hwdata_driven;
    output hwstrb    = hwstrb_driven;
    output hwrite    = hwrite_driven;
    output hsel      = hsel_driven;
    input  hrdata;
    input  hreadyout;
    input  hresp;
    input  hrdata_muxed;
    input  hready;
    input  hresp_muxed;
  endclocking

  clocking device_cb @(posedge clk_i);
    input  haddr;
    input  hburst;
    input  hmastlock;
    input  hprot;
    input  hsize;
    input  htrans;
    input  hwdata;
    input  hwstrb;
    input  hwrite;
    input  hsel;
    output hrdata    = hrdata_driven;
    output hreadyout = hreadyout_driven;
    output hresp     = hresp_driven;
  endclocking

  always_comb begin
    if (!rst_ni) begin
      haddr_internal     = '0;
      hburst_internal    = '0;
      hmastlock_internal = '0;
      hprot_internal     = '0;
      hsize_internal     = '0;
      htrans_internal    = '0;
      hwdata_internal    = '0;
      hwstrb_internal    = '0;
      hwrite_internal    = '0;
      hsel_internal      = '0;
      hrdata_internal    = '0;
      hreadyout_internal = '0;
      hresp_internal     = '0;
    end else begin
      haddr_internal     = haddr_driven & haddr_mask;
      hburst_internal    = hburst_driven & hburst_mask;
      hmastlock_internal = hmastlock_driven;
      hprot_internal     = hprot_driven & hprot_mask;
      hsize_internal     = hsize_driven;
      htrans_internal    = htrans_driven;
      hwdata_internal    = hwdata_driven & data_mask;
      hwstrb_internal    = hwstrb_driven & strb_mask;
      hwrite_internal    = hwrite_driven;
      hsel_internal      = hsel_driven & hsel_mask;
      hrdata_internal    = hrdata_driven & sub_data_mask;
      hreadyout_internal = hreadyout_driven;
      hresp_internal     = hresp_driven;
    end
  end

  assign haddr         = (if_mode == Host)   ? haddr_internal         : 'z;
  assign hburst        = (if_mode == Host)   ? hburst_internal        : 'z;
  assign hmastlock     = (if_mode == Host)   ? hmastlock_internal     : 'z;
  assign hprot         = (if_mode == Host)   ? hprot_internal         : 'z;
  assign hsize         = (if_mode == Host)   ? hsize_internal         : 'z;
  assign htrans        = (if_mode == Host)   ? htrans_internal        : 'z;
  assign hwdata        = (if_mode == Host)   ? hwdata_internal        : 'z;
  assign hwstrb        = (if_mode == Host)   ? hwstrb_internal        : 'z;
  assign hwrite        = (if_mode == Host)   ? hwrite_internal        : 'z;
  assign hsel          = (if_mode == Host)   ? hsel_internal          : 'z;
  assign hrdata        = (if_mode == Device) ? hrdata_internal        : 'z;
  assign hreadyout     = (if_mode == Device) ? hreadyout_internal     : 'z;
  assign hresp         = (if_mode == Device) ? hresp_internal         : 'z;

  // Note that the hrdata_muxed, hready and hresp_muxed signals come from a "*_internal" signal for
  // either active mode (Host or Device): in both cases, the interface is supplying the multiplexor,
  // which drives this signal to both the manager and the subordinate.
  assign hrdata_muxed  = (if_mode inside {Host, Device}) ? hrdata_muxed_internal : 'z;
  assign hready        = (if_mode inside {Host, Device}) ? hready_internal       : 'z;
  assign hresp_muxed   = (if_mode inside {Host, Device}) ? hresp_muxed_internal  : 'z;

  // If if_mode is not Device, the hrdata signals from subordinates are being driven by RTL. That
  // RTL might not be using the full widths of the interface. Unfortunately, the muxing would
  // convert the resulting 'z bits to 'x. Add a weak pull-down here.
  //
  // Because if_mode is not static, this pull-down is also applied when if-mode == Device. The whole
  // signal will be driven by the device_cb anyway, so this won't have any effect.
  assign (weak0, weak1) hrdata = '0;

  // Set the ADDR_WIDTH property. The AHB specification (issue C) does not constrain the value, but
  // we disallow widths over 64 (in order that a max-footprint approach is possible in this
  // interface).
  function void set_addr_width(int unsigned width);
    if (width > 64) begin
      `uvm_error($sformatf("%m"),
                 $sformatf("Cannot set ADDR_WIDTH to %0d: max supported width is 64.",
                           width))
      width = 64;
    end
    addr_width = width;
  endfunction

  // Set the HBURST_WIDTH property. The AHB specification (issue C) only allows widths of 0 and 3.
  function void set_hburst_width(int unsigned width);
    if (width != 0 && width != 3) begin
      `uvm_error($sformatf("%m"),
                 $sformatf("Cannot set HBURST_WIDTH to %0d: allowed values are 0, 3.",
                           width))
      width = 0;
    end
    hburst_width = width;
  endfunction

  // Set the HPROT_WIDTH property. The AHB specification (issue C) only allows widths of 0, 4 and 7.
  function void set_hprot_width(int unsigned width);
    if (width != 0 && width != 4 && width != 7) begin
      `uvm_error($sformatf("%m"),
                 $sformatf("Cannot set HPROT_WIDTH to %0d: allowed values are 0, 4 and 7.",
                           width))
      width = 0;
    end
    hprot_width = width;
  endfunction

  // Set the DATA_WIDTH property. The AHB specification (issue C) only allows widths of 8, 16, 32,
  // 64, 128, 256, 512 and 1024.
  function void set_data_width(int unsigned width);
    if (! (width inside {8, 16, 32, 64, 128, 256, 512, 1024})) begin
      `uvm_error($sformatf("%m"),
                 $sformatf("Cannot set DATA_WIDTH to %0d: must be power of 2 between 8 and 1024.",
                           width))
      width = 32;
    end
    data_width = width;
  endfunction

  // Configure the Write_Strobes property (if false, there is no HWSTRB signal).
  function void set_has_write_strobes(bit enabled);
    has_write_strobes = enabled;
  endfunction

  // Set the number of subordinates (and thus the width of the HSEL signal). This must be in the
  // range 1..8.
  function void set_num_subordinates(int unsigned num);
    if (num == 0 || num > 8) begin
      `uvm_error($sformatf("%m"),
                 $sformatf("Cannot set num_subordinates to %0d: number must be in the range 1..8.",
                           num))
      num = 8;
    end
    num_subordinates = num;
  endfunction
endinterface
