// Copyright (C) Microsoft Corporation. All rights reserved.

module integration_top(output wire dummy_pin);

  wire [7:0] nand2_ZN;
  wire [7:0] nand2_A;
  wire [7:0] nand2_B;

  assign dummy_pin = ^nand2_ZN[7:0];

  //------------------------------------------
  // NAND2
  //------------------------------------------
  assign nand2_A[7:0]  = 8'b00000000;
  assign nand2_B[7:0]  = 8'b00000000; 

  MPS_DP_NAND2 #(.WIDTH(8))  nand2(
  .ZN   (nand2_ZN[7:0]),
  .A    (nand2_A[7:0]),
  .B    (nand2_B[7:0]));

endmodule : integration_top
