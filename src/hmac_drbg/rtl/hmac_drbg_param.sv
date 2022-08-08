  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  localparam HMAC_DRBG_SEED_LENGTH        = 32'd384;
  localparam HMAC_DRBG_GARBAGE_LENGTH     = 32'd1024 -32'd384- HMAC_DRBG_SEED_LENGTH - 32'd8 - 32'd1 - 32'd12; // 1 for header and 12 bit for message length

  localparam HMAC_DRBG_KEYGEN             = 0;
  localparam HMAC_DRBG_SIGNING            = 1;

  localparam HMAC_DRBG_PRIME              = 384'hFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFC7634D81F4372DDF581A0DB248B0A77AECEC196ACCC52973;
  