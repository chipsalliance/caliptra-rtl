  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  localparam BASE_ADDR        = 32'h60000000;

  localparam ADDR_NAME0        = BASE_ADDR + 32'h00000000;
  localparam ADDR_NAME1        = BASE_ADDR + 32'h00000004;
  localparam ADDR_VERSION0     = BASE_ADDR + 32'h00000008;
  localparam ADDR_VERSION1     = BASE_ADDR + 32'h0000000c;

  localparam ADDR_CTRL        = BASE_ADDR + 32'h00000010;
  localparam CTRL_INIT_BIT    = 0;
  localparam CTRL_NEXT_BIT    = 1;

  localparam ADDR_STATUS      = BASE_ADDR + 32'h00000018;
  localparam STATUS_READY_BIT = 0;
  localparam STATUS_VALID_BIT = 1;

  localparam ADDR_CONFIG      = BASE_ADDR + 32'h00000020;
  localparam CTRL_ENCDEC_BIT  = 0;
  localparam CTRL_KEYLEN_BIT  = 1;

  localparam ADDR_KEY_START   = BASE_ADDR + 32'h00000040;
  localparam ADDR_KEY_END     = BASE_ADDR + 32'h0000005c;

  localparam ADDR_BLOCK_START = BASE_ADDR + 32'h00000080;
  localparam ADDR_BLOCK_END   = BASE_ADDR + 32'h0000008c;

  localparam ADDR_RESULT_START= BASE_ADDR + 32'h00000100;
  localparam ADDR_RESULT_END  = BASE_ADDR + 32'h0000010c;

  localparam CORE_NAME        = 64'h20202020_73206165; // "aes "
  localparam CORE_VERSION     = 64'h00000000_3630302e; // "0.60"

  // `define DATA_BUS_64