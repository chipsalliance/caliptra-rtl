  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  localparam HMAC_DRBG_SEED_LENGTH        = 32'd384;
  localparam HMAC_DRBG_GARBAGE_LENGTH     = 32'd1024 -32'd384- HMAC_DRBG_SEED_LENGTH - 32'd8 - 32'd1 - 32'd12; // 1 for header and 12 bit for message length

  localparam HMAC_DRBG_KEYGEN             = 0;
  localparam HMAC_DRBG_SIGNING            = 1;

  localparam HMAC_DRBG_PRIME              = 384'h7712d4b4bedaa2188cf251d4b34028ba0cc9919793d7d625035391eb0f1f0969bd6408cb7346d5f76d5c176da4b424b5;
  