// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
//======================================================================
//
// entropy_combiner_es_csrng_tb.sv
// -------------------------------
// Full entropy datapath integration: two real entropy_src IPs feeding the
// entropy combiner, whose combined seed feeds a real CSRNG (CTR_DRBG).
//
//   physical_rng(IS0) --itrng--> entropy_src ES0 --\
//                                                    >-- combiner --es_hw_if--> CSRNG --> genbits
//   physical_rng(IS1) --itrng--> entropy_src ES1 --/
//
// The CSRNG (not the TB) is the consumer of the combiner's entropy: on an
// INSTANTIATE-from-entropy command it drives es_req to the combiner, the
// combiner fans out to ES0/ES1, hashes ES0||ES1 with SHA3-384 and returns the
// 384-bit seed, and CSRNG runs its AES-256 CTR_DRBG. The TB drives CSRNG's SW
// application interface over AHB (enable / instantiate / generate) and checks
// the generated bits against the reference model in tb/csrng_drbg_model.py:
//
//   seed    = SHA3-384(IS0 || IS1)            (combiner)
//   genbits = CTR_DRBG(seed) generate 128b    (CSRNG)
//
// Both entropy_src instances run in RAW/BYPASS mode (es_bits == InitialSeed),
// so the whole chain is deterministic. The mubi/lc enum straps of entropy_src
// and csrng are tied inside RTL wrappers (entropy_src_raw_wrap / csrng_raw_wrap)
// to avoid TB/RTL enum-type mismatches under partition compile.
//
//======================================================================

module entropy_combiner_es_csrng_tb
  import entropy_src_pkg::*;
  ();

  //----------------------------------------------------------------
  // Parameters
  //----------------------------------------------------------------
  localparam int CLK_HALF_PERIOD = 2;
  localparam int SEED_W          = entropy_src_pkg::CSRNG_BUS_WIDTH; // 384
  localparam int AHB_ADDR_W      = 32;
  localparam int AHB_DATA_W      = 32;
  localparam int RNG_DUTY_CYCLE  = 4;

  // itrng InitialSeeds (raw es_bits in bypass mode).
  localparam logic [SEED_W-1:0] IS0 =
    384'h33f63b65f57ad68765693560e743cc5010518e4bf4ecbeba71dc56aaa08b394311731d9df763fc5d27e4ed3e4b7de947;
  localparam logic [SEED_W-1:0] IS1 =
    384'h9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e9587f9e1a34b2d0c7658493a1fbe6d2c0a;
  // Combiner seed delivered to CSRNG = SHA3-384(IS0 || IS1).
  // Combiner-mode seed/genbits (both entropy_src used): SHA3-384(IS0 || IS1).
  // From tb/csrng_drbg_model.py chain_genbits_words(IS0, IS1, 128).
  localparam logic [SEED_W-1:0] EXP_SEED_COMBINE =
    384'hd5137041d197084214e3d6e04ed17ca7264825e7f707961a45184d1b0be62b48bdfce4d0ae18be5c42c8e0169c387d16;
  localparam logic [31:0] EXP_GENBITS_COMBINE [4] = '{
    32'hae5f5d34, 32'h43f0422c, 32'h0057f623, 32'h08c811aa
  };
  // Bypass-mode seed/genbits (ES1 disabled): seed = ES0 raw seed = IS0.
  // From tb/csrng_drbg_model.py csrng_genbits_words(IS0, 128).
  localparam logic [SEED_W-1:0] EXP_SEED_BYPASS = IS0;
  localparam logic [31:0] EXP_GENBITS_BYPASS [4] = '{
    32'h15eb2a44, 32'h310851dd, 32'hba1365ab, 32'h4c7322f4
  };

  // entropy_src registers / values (raw/bypass, as in entropy_src_tb.sv).
  localparam logic [31:0] ES_ADDR_MODULE_ENABLE = 32'h20;
  localparam logic [31:0] ES_ADDR_CONF          = 32'h24;
  localparam logic [31:0] ES_CONF_RAW_BYPASS    = 32'h2649999;
  localparam logic [31:0] ES_MODULE_ENABLE_ON   = 32'h6;

  // csrng registers / commands (as in csrng_tb.sv).
  localparam logic [31:0] CS_ADDR_CTRL        = 32'h14;
  localparam logic [31:0] CS_ADDR_CMD_REQ     = 32'h18;
  localparam logic [31:0] CS_ADDR_SW_CMD_STS  = 32'h2c;
  localparam logic [31:0] CS_ADDR_GENBITS_VLD = 32'h30;
  localparam logic [31:0] CS_ADDR_GENBITS     = 32'h34;
  localparam logic [31:0] CS_CTRL_ENABLE      = 32'h666;   // enable + sw_app_enable
  localparam logic [31:0] CS_CMD_INSTANTIATE  = 32'h901;   // instantiate from entropy source
  localparam logic [31:0] CS_CMD_GENERATE_128 = 32'h1003;  // generate 128b
  localparam logic [31:0] CS_SW_CMD_RDY       = 32'h6;
  localparam logic [31:0] CS_GENBITS_VALID    = 32'h1;

  localparam logic [1:0] AHB_HTRANS_IDLE   = 2'h0;
  localparam logic [1:0] AHB_HTRANS_NONSEQ = 2'h2;

  //----------------------------------------------------------------
  // Clock / reset
  //----------------------------------------------------------------
  logic clk_tb;
  logic reset_n_tb;
  logic cptra_pwrgood_tb;

  //----------------------------------------------------------------
  // entropy_src shared config AHB bus (both ES configured identically)
  //----------------------------------------------------------------
  logic [AHB_ADDR_W-1:0] es_haddr;
  logic [AHB_DATA_W-1:0] es_hwdata;
  logic                  es_hsel, es_hwrite, es_hready;
  logic [1:0]            es_htrans;
  logic [2:0]            es_hsize;
  logic                  es0_hresp, es0_hreadyout;
  logic [AHB_DATA_W-1:0] es0_hrdata;
  logic                  es1_hresp, es1_hreadyout;
  logic [AHB_DATA_W-1:0] es1_hrdata;

  //----------------------------------------------------------------
  // csrng command AHB bus
  //----------------------------------------------------------------
  logic [AHB_ADDR_W-1:0] cs_haddr;
  logic [AHB_DATA_W-1:0] cs_hwdata;
  logic                  cs_hsel, cs_hwrite, cs_hready;
  logic [1:0]            cs_htrans;
  logic [2:0]            cs_hsize;
  logic                  cs_hresp, cs_hreadyout;
  logic [AHB_DATA_W-1:0] cs_hrdata;

  //----------------------------------------------------------------
  // entropy_src_hw_if wiring
  //----------------------------------------------------------------
  entropy_src_hw_if_req_t es0_hw_req, es1_hw_req;   // combiner -> ES
  entropy_src_hw_if_rsp_t es0_hw_rsp, es1_hw_rsp;   // ES -> combiner
  entropy_src_hw_if_req_t comb_csrng_req;           // CSRNG -> combiner (es_req)
  entropy_src_hw_if_rsp_t comb_csrng_rsp;           // combiner -> CSRNG (es_ack/es_bits)

  //----------------------------------------------------------------
  // itrng wiring
  //----------------------------------------------------------------
  entropy_src_rng_req_t es0_rng_req, es1_rng_req;
  entropy_src_rng_rsp_t es0_rng_rsp, es1_rng_rsp;

  logic combine_en_tb;

  // TB-controlled itrng start gates (hold a source idle to skew ES0/ES1
  // arrival, or to keep the secondary source disabled).
  logic rng0_go, rng1_go;

  // combiner AHB (KAT) unused + open outputs.
  logic          comb_hresp, comb_hreadyout;
  logic [31:0]   comb_hrdata;
  logic          comb_error_intr, comb_notif_intr, comb_ahb_lock;

  //----------------------------------------------------------------
  // Bookkeeping / snoop
  //----------------------------------------------------------------
  integer            error_ctr, tc_ctr;
  logic [31:0]       read_data;
  logic [SEED_W-1:0] csrng_seed_seen;
  logic              csrng_seed_valid;

  //----------------------------------------------------------------
  // DUT: entropy combiner (combine mode)
  //----------------------------------------------------------------
  entropy_combiner #(
    .AHB_DATA_WIDTH(32),
    .AHB_ADDR_WIDTH(32)
  ) u_combiner (
    .clk              (clk_tb),
    .reset_n          (reset_n_tb),
    .cptra_pwrgood_i  (cptra_pwrgood_tb),

    .csrng_hw_if_req_i(comb_csrng_req),
    .csrng_hw_if_rsp_o(comb_csrng_rsp),

    .es0_hw_if_req_o  (es0_hw_req),
    .es0_hw_if_rsp_i  (es0_hw_rsp),
    .es1_hw_if_req_o  (es1_hw_req),
    .es1_hw_if_rsp_i  (es1_hw_rsp),

    .combine_en_i     (combine_en_tb),

    .haddr_i          (32'h0),
    .hwdata_i         (32'h0),
    .hsel_i           (1'b0),
    .hwrite_i         (1'b0),
    .hready_i         (1'b1),
    .htrans_i         (2'b00),
    .hsize_i          (3'b000),
    .hresp_o          (comb_hresp),
    .hreadyout_o      (comb_hreadyout),
    .hrdata_o         (comb_hrdata),

    .error_intr_o     (comb_error_intr),
    .notif_intr_o     (comb_notif_intr),
    .ahb_lock_o       (comb_ahb_lock)
  );

  //----------------------------------------------------------------
  // Two real entropy_src IPs (via RTL wrapper) + itrng sources
  //----------------------------------------------------------------
  entropy_src_raw_wrap #(
    .AHBDataWidth(AHB_DATA_W),
    .AHBAddrWidth(AHB_ADDR_W)
  ) u_es0 (
    .clk_i               (clk_tb),
    .rst_ni              (reset_n_tb),
    .haddr_i             (es_haddr),
    .hwdata_i            (es_hwdata),
    .hsel_i              (es_hsel),
    .hwrite_i            (es_hwrite),
    .hready_i            (es_hready),
    .htrans_i            (es_htrans),
    .hsize_i             (es_hsize),
    .hresp_o             (es0_hresp),
    .hreadyout_o         (es0_hreadyout),
    .hrdata_o            (es0_hrdata),
    .entropy_src_hw_if_i (es0_hw_req),
    .entropy_src_hw_if_o (es0_hw_rsp),
    .entropy_src_rng_o   (es0_rng_req),
    .entropy_src_rng_i   (es0_rng_rsp)
  );

  entropy_src_raw_wrap #(
    .AHBDataWidth(AHB_DATA_W),
    .AHBAddrWidth(AHB_ADDR_W)
  ) u_es1 (
    .clk_i               (clk_tb),
    .rst_ni              (reset_n_tb),
    .haddr_i             (es_haddr),
    .hwdata_i            (es_hwdata),
    .hsel_i              (es_hsel),
    .hwrite_i            (es_hwrite),
    .hready_i            (es_hready),
    .htrans_i            (es_htrans),
    .hsize_i             (es_hsize),
    .hresp_o             (es1_hresp),
    .hreadyout_o         (es1_hreadyout),
    .hrdata_o            (es1_hrdata),
    .entropy_src_hw_if_i (es1_hw_req),
    .entropy_src_hw_if_o (es1_hw_rsp),
    .entropy_src_rng_o   (es1_rng_req),
    .entropy_src_rng_i   (es1_rng_rsp)
  );

  physical_rng #(
    .UseInitialSeed(1'b1),
    .InitialSeed   (IS0),
    .DutyCycle     (RNG_DUTY_CYCLE)
  ) u_rng0 (
    .clk    (clk_tb),
    .enable (es0_rng_req.rng_enable & rng0_go),
    .data   (es0_rng_rsp.rng_b),
    .valid  (es0_rng_rsp.rng_valid)
  );

  physical_rng #(
    .UseInitialSeed(1'b1),
    .InitialSeed   (IS1),
    .DutyCycle     (RNG_DUTY_CYCLE)
  ) u_rng1 (
    .clk    (clk_tb),
    .enable (es1_rng_req.rng_enable & rng1_go),
    .data   (es1_rng_rsp.rng_b),
    .valid  (es1_rng_rsp.rng_valid)
  );

  //----------------------------------------------------------------
  // Real CSRNG (via RTL wrapper), consuming the combiner's entropy.
  //----------------------------------------------------------------
  csrng_raw_wrap #(
    .AHBDataWidth(AHB_DATA_W),
    .AHBAddrWidth(AHB_ADDR_W)
  ) u_csrng (
    .clk_i               (clk_tb),
    .rst_ni              (reset_n_tb),
    .haddr_i             (cs_haddr),
    .hwdata_i            (cs_hwdata),
    .hsel_i              (cs_hsel),
    .hwrite_i            (cs_hwrite),
    .hready_i            (cs_hready),
    .htrans_i            (cs_htrans),
    .hsize_i             (cs_hsize),
    .hresp_o             (cs_hresp),
    .hreadyout_o         (cs_hreadyout),
    .hrdata_o            (cs_hrdata),
    .entropy_src_hw_if_o (comb_csrng_req),
    .entropy_src_hw_if_i (comb_csrng_rsp)
  );

  //----------------------------------------------------------------
  // Clock
  //----------------------------------------------------------------
  always #CLK_HALF_PERIOD clk_tb = ~clk_tb;

  //----------------------------------------------------------------
  // Snoop the 384-bit seed the combiner delivers to CSRNG (negedge sample:
  // comb ack is a one-cycle combinational pulse).
  //----------------------------------------------------------------
  always @(negedge clk_tb or negedge reset_n_tb) begin
    if (!reset_n_tb) begin
      csrng_seed_seen  <= '0;
      csrng_seed_valid <= 1'b0;
    end else if (comb_csrng_rsp.es_ack && !csrng_seed_valid) begin
      csrng_seed_seen  <= comb_csrng_rsp.es_bits;
      csrng_seed_valid <= 1'b1;
    end
  end

  //----------------------------------------------------------------
  // init_sim()
  //----------------------------------------------------------------
  task init_sim;
    begin
      clk_tb           = 1'b0;
      reset_n_tb       = 1'b0;
      cptra_pwrgood_tb = 1'b0;

      es_haddr  = '0; es_hwdata = '0; es_hsel = 1'b0; es_hwrite = 1'b0;
      es_hready = 1'b1; es_htrans = AHB_HTRANS_IDLE; es_hsize = 3'b010;

      cs_haddr  = '0; cs_hwdata = '0; cs_hsel = 1'b0; cs_hwrite = 1'b0;
      cs_hready = 1'b1; cs_htrans = AHB_HTRANS_IDLE; cs_hsize = 3'b010;

      combine_en_tb = 1'b0;
      rng0_go       = 1'b0;
      rng1_go       = 1'b0;
      read_data     = '0;
      error_ctr     = 0;
      tc_ctr        = 0;
    end
  endtask

  //----------------------------------------------------------------
  // reset_dut()
  //----------------------------------------------------------------
  task reset_dut;
    begin
      $display("*** Toggle reset.");
      reset_n_tb       = 1'b0;
      cptra_pwrgood_tb = 1'b0;
      repeat (5) @(posedge clk_tb);
      reset_n_tb       = 1'b1;
      cptra_pwrgood_tb = 1'b1;
      repeat (2) @(posedge clk_tb);
    end
  endtask

  //----------------------------------------------------------------
  // AHB write to both entropy_src (shared bus)
  //----------------------------------------------------------------
  task write_es(input logic [31:0] address, input logic [31:0] word);
    begin
      $display("[%0t] write_es(addr=0x%08x, data=0x%08x)", $time, address, word);
      es_hsel = 1'b1; es_haddr = address; es_hwdata = word;
      es_hwrite = 1'b1; es_hready = 1'b1;
      es_htrans = AHB_HTRANS_NONSEQ; es_hsize = 3'b010;
      @(posedge clk_tb);
      es_haddr = 'z; es_hwrite = 1'b0; es_htrans = AHB_HTRANS_IDLE;
      wait (es0_hreadyout == 1'b1 && es1_hreadyout == 1'b1);
      @(posedge clk_tb);
      es_hsel = 1'b0;
    end
  endtask

  //----------------------------------------------------------------
  // AHB write / read / poll to csrng
  //----------------------------------------------------------------
  task write_cs(input logic [31:0] address, input logic [31:0] word);
    begin
      $display("[%0t] write_cs(addr=0x%08x, data=0x%08x)", $time, address, word);
      cs_hsel = 1'b1; cs_haddr = address; cs_hwdata = word;
      cs_hwrite = 1'b1; cs_hready = 1'b1;
      cs_htrans = AHB_HTRANS_NONSEQ; cs_hsize = 3'b010;
      @(posedge clk_tb);
      cs_haddr = 'z; cs_hwrite = 1'b0; cs_htrans = AHB_HTRANS_IDLE;
      wait (cs_hreadyout == 1'b1);
      @(posedge clk_tb);
      cs_hsel = 1'b0;
    end
  endtask

  task read_cs(input logic [31:0] address);
    begin
      cs_hsel = 1'b1; cs_haddr = address; cs_hwrite = 1'b0; cs_hready = 1'b1;
      cs_htrans = AHB_HTRANS_NONSEQ; cs_hsize = 3'b010;
      @(posedge clk_tb);
      cs_hwdata = '0; cs_haddr = 'z; cs_htrans = AHB_HTRANS_IDLE;
      read_data = cs_hrdata;
      wait (cs_hreadyout == 1'b1);
      @(posedge clk_tb);
      cs_hsel = 1'b0;
    end
  endtask

  // Poll a csrng register until it equals `value`, with a timeout.
  task poll_cs(input logic [31:0] address, input logic [31:0] value, input string tag);
    integer polls;
    begin
      polls = 0;
      do begin
        read_cs(address);
        repeat (10) @(posedge clk_tb);
        polls = polls + 1;
        if (polls > 20000) begin
          error_ctr = error_ctr + 1;
          $display("*** ERROR: poll timeout on %s (addr 0x%08x) last=0x%08x",
                   tag, address, read_data);
          disable poll_cs;
        end
      end while (read_data != value);
    end
  endtask

  //----------------------------------------------------------------
  // configure_es() - raw/bypass mode + enable, for both entropy_src.
  //----------------------------------------------------------------
  task configure_es;
    begin
      write_es(ES_ADDR_CONF, ES_CONF_RAW_BYPASS);
      write_es(ES_ADDR_MODULE_ENABLE, ES_MODULE_ENABLE_ON);
    end
  endtask

  //----------------------------------------------------------------
  // display_test_result()
  //----------------------------------------------------------------
  task display_test_result;
    begin
      if (error_ctr == 0) begin
        $display("*** All %0d checks completed successfully.", tc_ctr);
        $display("* TESTCASE PASSED");
      end else begin
        $display("*** %0d checks completed, %0d errors.", tc_ctr, error_ctr);
        $display("* TESTCASE FAILED");
      end
    end
  endtask

  //----------------------------------------------------------------
  // run_case() - one full chain run: bring up ES + CSRNG, instantiate CSRNG
  // from the entropy interface (seed via the combiner), generate 128b, and
  // check the seed + genbits. es{0,1}_delay skew the ES0/ES1 itrng release
  // (arrival order); secondary_en=0 keeps ES1 disabled (bypass topology).
  //----------------------------------------------------------------
  task run_case(input logic   combine_en,
                input integer es0_delay,
                input integer es1_delay,
                input logic   secondary_en,
                input string  tag);
    integer err_at_entry;
    integer j;
    logic [SEED_W-1:0] exp_seed;
    logic [31:0]       exp_gb;
    begin
      err_at_entry = error_ctr;

      // Hold both itrng sources, strap combine_en, reset, bring up ES + CSRNG.
      rng0_go = 1'b0;
      rng1_go = 1'b0;
      combine_en_tb = combine_en;
      reset_dut();
      repeat (50) @(posedge clk_tb);
      configure_es();
      repeat (20) @(posedge clk_tb);
      write_cs(CS_ADDR_CTRL, CS_CTRL_ENABLE);
      repeat (20) @(posedge clk_tb);

      // Instantiate from the entropy source: CSRNG drives es_req through the
      // combiner, which requests ES0/ES1.
      $display("*** [%s] INSTANTIATE combine_en=%0b es0_delay=%0d es1_delay=%0d secondary_en=%0b",
               tag, combine_en, es0_delay, es1_delay, secondary_en);
      write_cs(CS_ADDR_CMD_REQ, CS_CMD_INSTANTIATE);

      // Release the itrng sources with the requested arrival skew (one delay is
      // always 0). ES1 is only released when it participates (secondary_en).
      if (es0_delay <= es1_delay) begin
        rng0_go = 1'b1;
        repeat (es1_delay - es0_delay) @(posedge clk_tb);
        if (secondary_en) rng1_go = 1'b1;
      end else begin
        if (secondary_en) rng1_go = 1'b1;
        repeat (es0_delay - es1_delay) @(posedge clk_tb);
        rng0_go = 1'b1;
      end

      poll_cs(CS_ADDR_SW_CMD_STS, CS_SW_CMD_RDY, "instantiate SW_CMD_STS");

      // Seed delivered to CSRNG: combine mode = SHA3-384(IS0||IS1); bypass = IS0.
      exp_seed = combine_en ? EXP_SEED_COMBINE : EXP_SEED_BYPASS;
      if (!csrng_seed_valid || (csrng_seed_seen !== exp_seed)) begin
        error_ctr = error_ctr + 1;
        $display("*** [%s] combiner->CSRNG seed MISMATCH valid=%0b", tag, csrng_seed_valid);
        $display("      exp = %096h", exp_seed);
        $display("      got = %096h", csrng_seed_seen);
      end

      // Generate 128b and check against the CTR_DRBG reference model.
      write_cs(CS_ADDR_CMD_REQ, CS_CMD_GENERATE_128);
      poll_cs(CS_ADDR_GENBITS_VLD, CS_GENBITS_VALID, "generate GENBITS_VLD");
      for (j = 0; j < 4; j = j + 1) begin
        read_cs(CS_ADDR_GENBITS);
        exp_gb = combine_en ? EXP_GENBITS_COMBINE[j] : EXP_GENBITS_BYPASS[j];
        if (read_data !== exp_gb) begin
          error_ctr = error_ctr + 1;
          $display("*** [%s] GENBITS[%0d] MISMATCH exp=0x%08x got=0x%08x",
                   tag, j, exp_gb, read_data);
        end
      end

      if (error_ctr == err_at_entry)
        $display("    [%s] PASS  seed=%096h", tag, csrng_seed_seen);
      tc_ctr = tc_ctr + 1;
      repeat (30) @(posedge clk_tb);
    end
  endtask

  //----------------------------------------------------------------
  // Main - same inputs (IS0/IS1), four ES timing/config cases.
  //----------------------------------------------------------------
  initial begin
    init_sim();
    $display("*** entropy_combiner + dual entropy_src + CSRNG chain: 4 cases");

    // 1) ES1 (primary/ES0) arrives faster than ES2 (secondary/ES1).
    run_case(1'b1, 0,   257, 1'b1, "case1-ES1-faster-than-ES2");
    // 2) ES1 (primary/ES0) arrives slower than ES2 (secondary/ES1).
    run_case(1'b1, 139, 0,   1'b1, "case2-ES1-slower-than-ES2");
    // 3) Both entropy_src outputs arrive at the same time.
    run_case(1'b1, 0,   0,   1'b1, "case3-both-same-time");
    // 4) ES2 (secondary/ES1) disabled -> combiner bypass, seed = ES1(ES0) only.
    run_case(1'b0, 0,   0,   1'b0, "case4-ES2-disabled");

    display_test_result();
    $finish;
  end

  //----------------------------------------------------------------
  // Global watchdog
  //----------------------------------------------------------------
  initial begin
    #80_000_000;
    $display("*** ERROR: global simulation timeout.");
    $display("* TESTCASE FAILED");
    $finish;
  end

endmodule
