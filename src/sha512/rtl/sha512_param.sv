  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  localparam BASE_ADDR            = 32'h40000000;

  localparam ADDR_NAME            = BASE_ADDR + 32'h00000000;
  localparam ADDR_VERSION         = BASE_ADDR + 32'h00000008;

  localparam ADDR_CTRL            = BASE_ADDR + 32'h00000010;
  localparam CTRL_INIT_BIT        = 0;
  localparam CTRL_NEXT_BIT        = 1;
  localparam CTRL_MODE_LOW_BIT    = 2;
  localparam CTRL_MODE_HIGH_BIT   = 3;
  localparam CTRL_WORK_FACTOR_BIT = 7;

  localparam ADDR_STATUS          = BASE_ADDR + 32'h00000018;
  localparam STATUS_READY_BIT     = 0;
  localparam STATUS_VALID_BIT     = 1;

  localparam ADDR_WORK_FACTOR_NUM = BASE_ADDR + 32'h00000020;

  localparam ADDR_BLOCK0          = BASE_ADDR + 32'h00000080;
  localparam ADDR_BLOCK15         = BASE_ADDR + 32'h000000f8;

  localparam ADDR_DIGEST0         = BASE_ADDR + 32'h00000100;
  localparam ADDR_DIGEST7         = BASE_ADDR + 32'h00000138;

  localparam CORE_NAME            = 64'h31322d35_61327368; // "sha2-512"
  localparam CORE_VERSION         = 64'h00000000_3830302e; // "0.80"

  localparam MODE_SHA_512_224     = 2'h0;
  localparam MODE_SHA_512_256     = 2'h1;
  localparam MODE_SHA_384         = 2'h2;
  localparam MODE_SHA_512         = 2'h3;

  localparam DEFAULT_WORK_FACTOR_NUM = 32'h000f0000;