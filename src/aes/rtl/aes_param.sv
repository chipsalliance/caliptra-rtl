  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  localparam AES_BASE_ADDR        = 32'h60000000;

  localparam AES_ADDR_NAME0        = AES_BASE_ADDR + 32'h00000000;
  localparam AES_ADDR_NAME1        = AES_BASE_ADDR + 32'h00000004;
  localparam AES_ADDR_VERSION0     = AES_BASE_ADDR + 32'h00000008;
  localparam AES_ADDR_VERSION1     = AES_BASE_ADDR + 32'h0000000c;

  localparam AES_ADDR_CTRL        = AES_BASE_ADDR + 32'h00000010;
  localparam AES_CTRL_INIT_BIT    = 0;
  localparam AES_CTRL_NEXT_BIT    = 1;

  localparam AES_ADDR_STATUS      = AES_BASE_ADDR + 32'h00000018;
  localparam AES_STATUS_READY_BIT = 0;
  localparam AES_STATUS_VALID_BIT = 1;

  localparam AES_ADDR_CONFIG      = AES_BASE_ADDR + 32'h00000020;
  localparam AES_CTRL_ENCDEC_BIT  = 0;
  localparam AES_CTRL_KEYLEN_BIT  = 1;

  localparam AES_ADDR_KEY_START   = AES_BASE_ADDR + 32'h00000040;
  localparam AES_ADDR_KEY_END     = AES_BASE_ADDR + 32'h0000005c;

  localparam AES_ADDR_BLOCK_START = AES_BASE_ADDR + 32'h00000080;
  localparam AES_ADDR_BLOCK_END   = AES_BASE_ADDR + 32'h0000008c;

  localparam AES_ADDR_RESULT_START= AES_BASE_ADDR + 32'h00000100;
  localparam AES_ADDR_RESULT_END  = AES_BASE_ADDR + 32'h0000010c;

  localparam AES_ADDR_IV_START = AES_BASE_ADDR + 32'h00000110;
  localparam AES_ADDR_IV_END   = AES_BASE_ADDR + 32'h0000011c;

  localparam AES_CORE_NAME        = 64'h20202020_73206165; // "aes "
  localparam AES_CORE_VERSION     = 64'h00000000_3630302e; // "0.60"

  // `define AES_DATA_BUS_64

  `define AES_CBC_MODE
