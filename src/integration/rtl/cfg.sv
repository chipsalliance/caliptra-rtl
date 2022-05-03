`ifndef CFG_SV
`define CFG_SV
  `define AHB_SLAVES_NUM      4'd3 // Number of slaves AHB
  `define AHB_MASTERS_NUM     4'd1 // Number of masters AHB
  `define AHB_HADDR_SIZE      32 // bit-width AHB address haddr
  `define AHB_HDATA_SIZE      64 // bit-width AHB data
  `define SLAVE_BASE_ADDR     {32'h4000_0000, 32'hEE00_0000, 32'h8000_0000} // Array with slave base address
  `define SLAVE_MASK_ADDR     {32'h4000_FFFF, 32'hEE00_FFFF, 32'hD100_0000}  // Array with slave offset address
  `define RUST_TOP            rust_top_tb
  `define RUST_RV_TOP         `RUST_TOP.rust_top_dut
  `define RV_TOP              `RUST_RV_TOP.rvtop
`endif
