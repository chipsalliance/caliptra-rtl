`ifndef CFG_SV
`define CFG_SV
  `define AHB_SLAVES_NUM      4'd2 // Number of slaves AHB
  `define AHB_MASTERS_NUM     4'd1 // Number of masters AHB
  `define AHB_HADDR_SIZE      32 // bit-width AHB address haddr
  `define AHB_HDATA_SIZE      32 // bit-width AHB data
  `define SLAVE_BASE_ADDR     {32'h2000_0100,32'h2000_0000} // Array with slave base address
  `define SLAVE_MASK_ADDR     {32'h2000_01FF,32'h2000_00FF}  // Array with slave offset address
`endif
