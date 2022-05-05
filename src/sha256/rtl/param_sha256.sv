  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  localparam BASE_ADDR        = 32'h50000000;

  localparam ADDR_NAME        = BASE_ADDR + 32'h00000000;
  localparam ADDR_VERSION     = BASE_ADDR + 32'h00000004;

  localparam ADDR_CTRL        = BASE_ADDR + 32'h00000008;
  localparam CTRL_INIT_BIT    = 0;
  localparam CTRL_NEXT_BIT    = 1;
  localparam CTRL_MODE_BIT    = 2;

  localparam ADDR_STATUS      = BASE_ADDR + 32'h0000000c;
  localparam STATUS_READY_BIT = 0;
  localparam STATUS_VALID_BIT = 1;

  localparam ADDR_BLOCK0      = BASE_ADDR + 32'h00000020;
  localparam ADDR_BLOCK7      = BASE_ADDR + 32'h0000003c;

  localparam ADDR_DIGEST0     = BASE_ADDR + 32'h00000040;
  localparam ADDR_DIGEST3     = BASE_ADDR + 32'h0000004c;

  localparam CORE_NAME        = 64'h35362d32_61327368; // "sha2-256"
  localparam CORE_VERSION     = 64'h00000000_3830312e; // "1.80"

  localparam MODE_SHA_224     = 1'h0;
  localparam MODE_SHA_256     = 1'h1;