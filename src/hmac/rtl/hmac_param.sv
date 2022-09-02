  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  localparam HMAC_BASE_ADDR        = 32'h10010000;
  
  localparam HMAC_ADDR_NAME0       = HMAC_BASE_ADDR + 32'h00000000;
  localparam HMAC_ADDR_NAME1       = HMAC_BASE_ADDR + 32'h00000004;
  localparam HMAC_ADDR_VERSION0    = HMAC_BASE_ADDR + 32'h00000008;
  localparam HMAC_ADDR_VERSION1    = HMAC_BASE_ADDR + 32'h0000000C;

  localparam HMAC_ADDR_CTRL        = HMAC_BASE_ADDR + 32'h00000010;
  localparam HMAC_CTRL_INIT_BIT    = 0;
  localparam HMAC_CTRL_NEXT_BIT    = 1;

  localparam HMAC_ADDR_STATUS      = HMAC_BASE_ADDR + 32'h00000018;
  localparam HMAC_STATUS_READY_BIT = 0;
  localparam HMAC_STATUS_VALID_BIT = 1;

  localparam HMAC_ADDR_KEY0        = HMAC_BASE_ADDR + 32'h00000040;
  localparam HMAC_ADDR_KEY11       = HMAC_BASE_ADDR + 32'h0000006C;

  localparam HMAC_ADDR_BLOCK0      = HMAC_BASE_ADDR + 32'h00000080;
  localparam HMAC_ADDR_BLOCK31     = HMAC_BASE_ADDR + 32'h000000fC;

  localparam HMAC_ADDR_TAG0        = HMAC_BASE_ADDR + 32'h00000100;
  localparam HMAC_ADDR_TAG11       = HMAC_BASE_ADDR + 32'h0000012C;

  localparam HMAC_KV_CTRL          = HMAC_BASE_ADDR + 32'h00000200;

  localparam HMAC_CORE_NAME        = 64'h61327368_6163686d; // "hmacsha2"
  localparam HMAC_CORE_VERSION     = 64'h00000000_3030312e; // "1.00"