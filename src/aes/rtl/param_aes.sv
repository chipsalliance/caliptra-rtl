  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  localparam BASE_ADDR        = 32'h60000000;

  localparam ADDR_NAME        = BASE_ADDR + 32'h00000000;
  localparam ADDR_VERSION     = BASE_ADDR + 32'h00000004;

  localparam ADDR_CTRL        = BASE_ADDR + 32'h00000008;
  localparam CTRL_INIT_BIT    = 0;
  localparam CTRL_NEXT_BIT    = 1;

  localparam ADDR_STATUS      = BASE_ADDR + 32'h0000000c;
  localparam STATUS_READY_BIT = 0;
  localparam STATUS_VALID_BIT = 1;

  localparam ADDR_CONFIG      = BASE_ADDR + 32'h00000010;
  localparam CTRL_ENCDEC_BIT  = 0;
  localparam CTRL_KEYLEN_BIT  = 1;

  localparam ADDR_KEY0        = BASE_ADDR + 32'h00000020;
  localparam ADDR_KEY3        = BASE_ADDR + 32'h0000002c;

  localparam ADDR_BLOCK0      = BASE_ADDR + 32'h00000030;
  localparam ADDR_BLOCK1      = BASE_ADDR + 32'h00000034;

  localparam ADDR_RESULT0     = BASE_ADDR + 32'h00000040;
  localparam ADDR_RESULT1     = BASE_ADDR + 32'h00000044;

  localparam CORE_NAME        = 64'h20202020_73206165; // "aes "
  localparam CORE_VERSION     = 64'h00000000_3630302e; // "0.60"