// SPDX-License-Identifier: Apache-2.0
//
// Package definitions for the SHA3-384 entropy combiner.

package entropy_combiner_pkg;

  // Main datapath sequencer states for the CSRNG-facing entropy_src_hw_if bridge.
  // The combine path requests both entropy sources, waits until both 384b seeds
  // are captured, feeds ES0||ES1 as a single SHA3-384 block, then returns one
  // 384b digest with one CSRNG ack. KAT states reuse the same SHA3 datapath for
  // one fixed POST vector of 0..768 bits, bounded to one SHA3-384 block.
  //
  // Sparse Hamming-distance-3 encoding (codes reused from entropy_src_main_sm_pkg)
  // so a single-bit glitch yields an undefined code trapped to combiner_st_error.
  localparam int unsigned CombinerStateWidth = 9;
  typedef enum logic [CombinerStateWidth-1:0] {
    combiner_st_idle         = 9'b011110101,
    combiner_st_req_entropy  = 9'b111010010,
    combiner_st_sha_start    = 9'b000101100,
    combiner_st_sha_feed     = 9'b001011001,
    combiner_st_sha_process  = 9'b011111000,
    combiner_st_sha_wait     = 9'b010111111,
    combiner_st_comb_ack     = 9'b110011000,
    combiner_st_wait_req_low = 9'b010001110,
    combiner_st_kat_done     = 9'b100001111,
    combiner_st_error        = 9'b001110011
  } entropy_combiner_state_e;

  // Reset default is fips_policy_and_both. The configurable value mode is for
  // integration/debug policy experiments and is not selected unless ROM/FW sets it.
  typedef enum logic [1:0] {
    fips_policy_and_both = 2'b00,
    fips_policy_es0_only = 2'b01,
    fips_policy_cfg      = 2'b10
  } entropy_combiner_fips_policy_e;

  // Combiner core identity. These are reported through the combiner-owned
  // COMBINER_NAME/COMBINER_VERSION registers so ROM can identify this block
  // independently from the ot_sha3 gates used inside it.
  localparam bit [63:0] ENTROPY_COMBINER_CORE_NAME    = 64'h6d62636f_61337368; // "sha3comb"
  localparam bit [63:0] ENTROPY_COMBINER_CORE_VERSION = 64'h00000000_3032322e; // "2.20" (v2.2)

endpackage
