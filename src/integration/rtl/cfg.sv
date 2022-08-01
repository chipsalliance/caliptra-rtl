`ifndef CFG_SV
`define CFG_SV
  `define AHB_SLAVES_NUM      4'd6 // Number of slaves AHB
  `define AHB_MASTERS_NUM     4'd1 // Number of masters AHB
  `define AHB_HADDR_SIZE      32 // bit-width AHB address haddr
  `define AHB_HDATA_SIZE      64 // bit-width AHB data
  `define APB_ADDR_WIDTH      32 // bit-width APB address
  `define APB_DATA_WIDTH      32 // bit-width APB data
  `define APB_USER_WIDTH      32 // bit-width APB PAUSER field
  `define QSPI_CS_WIDTH       2
  `define QSPI_IO_WIDTH       4
  `define SOC_SEC_STATE_WIDTH 3
  `define SLAVE_BASE_ADDR     {32'h10010000, 32'h3000_0000, 32'h6000_0000, 32'h4000_0000, 32'hEE00_0000, 32'h8000_0000} // Array with slave base address
  `define SLAVE_MASK_ADDR     {32'h10010FFF, 32'h3003_FFFF, 32'h6000_FFFF, 32'h4000_FFFF, 32'hEE00_FFFF, 32'hD100_0000}  // Array with slave offset address
  `define CALIPTRA_TOP        caliptra_top_tb
  `define CALIPTRA_RV_TOP     `CALIPTRA_TOP.caliptra_top_dut
  `define RV_TOP              `CALIPTRA_RV_TOP.rvtop
`endif
