  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  localparam ADDR_NAME0           = 32'h00000000;
  localparam ADDR_NAME1           = 32'h00000004;
  localparam ADDR_VERSION0        = 32'h00000008;
  localparam ADDR_VERSION1        = 32'h0000000c;

  localparam ADDR_CTRL            = 32'h00000010;
  localparam CTRL_INIT_BIT        = 0;
  localparam CTRL_NEXT_BIT        = 1;
  localparam CTRL_MODE_LOW_BIT    = 2;
  localparam CTRL_MODE_HIGH_BIT   = 3;
  localparam CTRL_WORK_FACTOR_BIT = 7;

  localparam ADDR_STATUS          = 32'h00000018;
  localparam STATUS_READY_BIT     = 0;
  localparam STATUS_VALID_BIT     = 1;

  localparam ADDR_WORK_FACTOR_NUM = 32'h00000020;

  localparam ADDR_BLOCK_START     = 32'h00000080;
  localparam ADDR_BLOCK_END       = 32'h000000ff;

  localparam ADDR_DIGEST_START    = 32'h00000100;
  localparam ADDR_DIGEST_END      = 32'h0000013f;

  localparam CORE_NAME0           = 32'h61327368; // "sha2"
  localparam CORE_NAME1           = 32'h31322d35; // "-512"
  localparam CORE_VERSION0        = 32'h3830302e; // "0.80"
  localparam CORE_VERSION1        = 32'h00000000; // "0"

  localparam MODE_SHA_512_224     = 2'h0;
  localparam MODE_SHA_512_256     = 2'h1;
  localparam MODE_SHA_384         = 2'h2;
  localparam MODE_SHA_512         = 2'h3;

  localparam DEFAULT_WORK_FACTOR_NUM = 32'h000f0000;

  // `define DATA_BUS_64
  
//======================================================================
// EOF sha512_param.sv
//======================================================================
