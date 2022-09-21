  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  localparam AES_ADDR_NAME0        = 32'h00000000;
  localparam AES_ADDR_NAME1        = 32'h00000004;
  localparam AES_ADDR_VERSION0     = 32'h00000008;
  localparam AES_ADDR_VERSION1     = 32'h0000000c;

  localparam AES_ADDR_CTRL        = 32'h00000010;
  localparam AES_CTRL_INIT_BIT    = 0;
  localparam AES_CTRL_NEXT_BIT    = 1;

  localparam AES_ADDR_STATUS      = 32'h00000018;
  localparam AES_STATUS_READY_BIT = 0;
  localparam AES_STATUS_VALID_BIT = 1;

  localparam AES_ADDR_CONFIG      = 32'h00000020;
  localparam AES_CTRL_ENCDEC_BIT  = 0;
  localparam AES_CTRL_KEYLEN_BIT  = 1;

  localparam AES_ADDR_KEY_START   = 32'h00000040;
  localparam AES_ADDR_KEY_END     = 32'h0000005c;

  localparam AES_ADDR_BLOCK_START = 32'h00000080;
  localparam AES_ADDR_BLOCK_END   = 32'h0000008c;

  localparam AES_ADDR_RESULT_START= 32'h00000100;
  localparam AES_ADDR_RESULT_END  = 32'h0000010c;

  localparam AES_ADDR_IV_START = 32'h00000110;
  localparam AES_ADDR_IV_END   = 32'h0000011c;

  localparam AES_ADDR_KV_CTRL  = 32'h00000200;

  localparam AES_CORE_NAME        = 64'h20202020_73206165; // "aes "
  localparam AES_CORE_VERSION     = 64'h00000000_3630302e; // "0.60"

  //`define AES_DATA_BUS_64

  `define AES_CBC_MODE
