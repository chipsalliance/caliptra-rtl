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
// sha3_ctrl_tb.v
// --------
// SHA3 testbench for the SHA3 AHB-lite interface controller.
//
//======================================================================

module sha3_ctrl_tb ();

  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  parameter DEBUG = 0;

  // Algorithm selector: 0=SHA3, 1=SHAKE, 2=cSHAKE
  parameter int    ALGO_TYPE  = 1;

  // SHA3 variant selector: set to 224, 256, 384, or 512
  parameter int    SHA3_MODE = 512;

  // Security strength for SHAKE/cSHAKE: 128 or 256
  parameter int    SHAKE_BITS = 256;

  parameter string IN_FILE   = "../stimulus/acvp/SHAKE-256.txt";
  parameter string OUT_FILE  = "../stimulus/acvp/SHAKE-256_digest.txt";


  parameter CLK_HALF_PERIOD = 1;
  parameter CLK_PERIOD      = 2 * CLK_HALF_PERIOD;

  parameter AHB_HTRANS_IDLE   = 0;
  parameter AHB_HTRANS_BUSY   = 1;
  parameter AHB_HTRANS_NONSEQ = 2;
  parameter AHB_HTRANS_SEQ    = 3;

  parameter AHB_ADDR_WIDTH = 32;
  parameter AHB_DATA_WIDTH = 32;

  //----------------------------------------------------------------
  // SHA3 register address map (hardcoded - no .svh for SHA3)
  //----------------------------------------------------------------
  parameter SHA3_NAME_0          = 32'h00001000;
  parameter SHA3_NAME_1          = 32'h00001004;
  parameter SHA3_VERSION_0       = 32'h00001008;
  parameter SHA3_VERSION_1       = 32'h0000100C;
  parameter SHA3_CFG             = 32'h00001024;  // CFG_SHADOWED
  parameter SHA3_CFG_KMAC        = 32'h00000014;  // CFG_SHADOWED
  parameter SHA3_CMD             = 32'h00001028;
  parameter SHA3_CMD_KMAC        = 32'h00000018;
  parameter SHA3_STATUS          = 32'h0000102C;
  parameter SHA3_STATUS_KMAC     = 32'h0000001C;
  parameter SHA3_STATE_BASE      = 32'h00001200;  // 0x40 words (1600 bits)
  parameter SHA3_STATE_BASE_KMAC = 32'h00000400;  // 0x40 words (1600 bits)
  parameter SHA3_MSG_FIFO_KMAC   = 32'h00000800;  // write-only message FIFO
  // PREFIX registers: 11 x 32-bit words at AHB 0x1020..0x1048
  // (= KMAC offsets 0x20..0x48 + VH_REGISTER_ADDRESS_OFFSET 0x1000)
  parameter SHA3_PREFIX_BASE     = 32'h00001020;  // PREFIX_0

  // CMD sparse encoding (6-bit field, written to CMD[5:0])
  parameter CMD_START   = 32'h0000001D;  // 6'b011101 = 29
  parameter CMD_PROCESS = 32'h0000002E;  // 6'b101110 = 46
  parameter CMD_RUN     = 32'h00000031;  // 6'b110001 = 49
  parameter CMD_DONE    = 32'h00000016;  // 6'b010110 = 22

  // STATUS bit positions
  parameter STATUS_SHA3_IDLE    = 0;
  parameter STATUS_SHA3_ABSORB  = 1;
  parameter STATUS_SHA3_SQUEEZE = 2;

  // CFG for SHA3-256: kstrength=L256(2) at bits[3:1], mode=SHA3(0) at bits[5:4]
  // cfg = (2 << 1) | (0 << 4) = 0x04
  parameter SHA3_256_CFG = 32'h00000004;

  // Additional SHA3 register addresses (from sha3_reg.rdl)
  parameter SHA3_ALERT_TEST  = 32'h0000001C;  // Alert test register
  parameter SHA3_CFG_REGWEN  = 32'h00000020;  // CFG write-enable (RO; 0=locked)
  parameter SHA3_ERR_CODE    = 32'h000000D0;  // Error code register (RO)

  // STATUS register additional field bit positions
  parameter STATUS_FIFO_DEPTH_LSB    = 8;   // fifo_depth[12:8]
  parameter STATUS_FIFO_EMPTY        = 14;  // fifo_empty[14]
  parameter STATUS_FIFO_FULL         = 15;  // fifo_full[15]
  parameter STATUS_ALERT_FATAL_FAULT = 16;  // ALERT_FATAL_FAULT[16]
  parameter STATUS_ALERT_RECOV_ERR   = 17;  // ALERT_RECOV_CTRL_UPDATE_ERR[17]

  // CMD register additional field bit position
  parameter CMD_ERR_PROCESSED_BIT    = 10;  // err_processed[10]

  // CFG_SHADOWED kstrength field values (bits [3:1])
  parameter CFG_KSTRENGTH_L128       = 3'h0;
  parameter CFG_KSTRENGTH_L224       = 3'h1;
  parameter CFG_KSTRENGTH_L256       = 3'h2;
  parameter CFG_KSTRENGTH_L384       = 3'h3;
  parameter CFG_KSTRENGTH_L512       = 3'h4;

  // CFG_SHADOWED mode field values (bits [5:4])
  parameter CFG_MODE_SHA3            = 2'h0;
  parameter CFG_MODE_SHAKE           = 2'h2;
  parameter CFG_MODE_CSHAKE          = 2'h3;

  // Derived from SHA3_MODE - controls RTL config, state read width, and output format
  localparam int DIGEST_BITS  = SHA3_MODE;          // 224 / 256 / 384 / 512
  localparam int DIGEST_WORDS = DIGEST_BITS / 32;   // 7  / 8   / 12  / 16
  localparam int DIGEST_HEX   = DIGEST_BITS / 4;    // 56 / 64  / 96  / 128

  localparam [2:0] KSTRENGTH =
      (ALGO_TYPE != 0)   ? ((SHAKE_BITS == 128) ? CFG_KSTRENGTH_L128 : CFG_KSTRENGTH_L256) :
      (SHA3_MODE == 224) ? CFG_KSTRENGTH_L224 :
      (SHA3_MODE == 384) ? CFG_KSTRENGTH_L384 :
      (SHA3_MODE == 512) ? CFG_KSTRENGTH_L512 :
                           CFG_KSTRENGTH_L256;   // default / 256

  // Mode selected at compile time
  localparam [1:0] CFG_MODE_SEL =
      (ALGO_TYPE == 2) ? CFG_MODE_CSHAKE :
      (ALGO_TYPE == 1) ? CFG_MODE_SHAKE  :
                         CFG_MODE_SHA3;

  // Words available per Keccak squeeze for XOF modes
  // SHAKE-128/cSHAKE-128 rate = 1344 bits = 42 words
  // SHAKE-256/cSHAKE-256 rate = 1088 bits = 34 words
  localparam int RATE_WORDS   = (SHAKE_BITS == 128) ? 42 : 34;

  // Maximum XOF output accumulator size (bits); covers observed max outLen ~61056 bits
  localparam int MAX_XOF_BITS = 65536;

  parameter VH_REGISTER_ADDRESS_OFFSET = 32'h0000_1000;

  //----------------------------------------------------------------
  // Register and Wire declarations.
  //----------------------------------------------------------------
  reg [31:0] cycle_ctr;
  reg [31:0] error_ctr;
  reg [31:0] tc_ctr;

  reg        clk_tb;
  reg        reset_n_tb;
  reg        cptra_pwrgood_tb;

  reg [AHB_ADDR_WIDTH-1:0] haddr_i_tb;
  reg [AHB_DATA_WIDTH-1:0] hwdata_i_tb;
  reg                      hsel_i_tb;
  reg                      hwrite_i_tb;
  reg                      hready_i_tb;
  reg [1:0]                htrans_i_tb;
  reg [2:0]                hsize_i_tb;

  wire                      hresp_o_tb;
  wire                      hreadyout_o_tb;
  wire [AHB_DATA_WIDTH-1:0] hrdata_o_tb;

  wire busy_o_tb;
  wire error_intr_tb;
  wire notif_intr_tb;

  reg [31:0]  read_data;
  reg [511:0] digest_data;  // widened to accommodate SHA3-512 (largest variant)
  reg [MAX_XOF_BITS-1:0] xof_data;  // SHAKE/cSHAKE variable-length output accumulator

  //----------------------------------------------------------------
  // Device Under Test.
  //----------------------------------------------------------------
  sha3_ctrl #(
    .AHB_DATA_WIDTH(32),
    .AHB_ADDR_WIDTH(32)
  ) dut (
    .clk                             (clk_tb),
    .reset_n                         (reset_n_tb),
    .cptra_pwrgood                   (cptra_pwrgood_tb),

    .haddr_i                         (haddr_i_tb),
    .hwdata_i                        (hwdata_i_tb),
    .hsel_i                          (hsel_i_tb),
    .hwrite_i                        (hwrite_i_tb),
    .hready_i                        (hready_i_tb),
    .htrans_i                        (htrans_i_tb),
    .hsize_i                         (hsize_i_tb),

    .hresp_o                         (hresp_o_tb),
    .hreadyout_o                     (hreadyout_o_tb),
    .hrdata_o                        (hrdata_o_tb),

    .busy_o                          (busy_o_tb),
    .error_intr                      (error_intr_tb),
    .notif_intr                      (notif_intr_tb),
    .debugUnlock_or_scan_mode_switch (1'b0)
  );

  //----------------------------------------------------------------
  // clk_gen
  //
  // Clock generator process.
  //----------------------------------------------------------------
  always
    begin : clk_gen
      #CLK_HALF_PERIOD clk_tb = !clk_tb;
    end // clk_gen

  //----------------------------------------------------------------
  // sys_monitor
  //
  // Generates a cycle counter and displays information about
  // the dut as needed.
  //----------------------------------------------------------------
  always
    begin : sys_monitor
      #(CLK_PERIOD);
      cycle_ctr = cycle_ctr + 1;
    end

  //----------------------------------------------------------------
  // init_sim()
  //
  // Initialize all counters and testbed functionality as well
  // as setting the DUT inputs to defined values.
  //----------------------------------------------------------------
  task init_sim;
    begin
      cycle_ctr = 32'h00000000;
      error_ctr = 32'h00000000;
      tc_ctr    = 32'h00000000;

      clk_tb           = 0;
      reset_n_tb       = 0;
      cptra_pwrgood_tb = 0;

      haddr_i_tb  = 0;
      hwdata_i_tb = 0;
      hsel_i_tb   = 0;
      hwrite_i_tb = 0;
      hready_i_tb = 0;
      htrans_i_tb = AHB_HTRANS_IDLE;
      hsize_i_tb  = 3'b010;  // 32-bit word access
    end
  endtask // init_sim

  //----------------------------------------------------------------
  // reset_dut()
  //
  // Toggles reset to force the DUT into a well defined state.
  //----------------------------------------------------------------
  task reset_dut;
    begin
      $display("*** Toggle reset.");
      reset_n_tb       = 0;
      cptra_pwrgood_tb = 0;

      #(4 * CLK_HALF_PERIOD);

      reset_n_tb       = 1;
      cptra_pwrgood_tb = 1;
    end
  endtask // reset_dut

  //----------------------------------------------------------------
  // display_test_result()
  //
  // Display the accumulated test results.
  //----------------------------------------------------------------
  task display_test_result;
    begin
      if (error_ctr == 0)
        begin
          $display("*** All %02d test cases completed successfully.", tc_ctr);
          $display("* TESTCASE PASSED");
        end
      else
        begin
          $display("*** %02d test cases completed.", tc_ctr);
          $display("*** %02d errors detected during testing.", error_ctr);
          $display("* TESTCASE FAILED");
        end
    end
  endtask // display_test_result

  //----------------------------------------------------------------
  // read_single_word()
  //
  // Read a data word from the given address in the DUT.
  // The word read will be available in the global variable read_data.
  //----------------------------------------------------------------
  task read_single_word(input [31:0] address);
    begin
      @(posedge clk_tb);
      hsel_i_tb   = 1;
      haddr_i_tb  = address;
      hwrite_i_tb = 0;
      hready_i_tb = 1;
      htrans_i_tb = AHB_HTRANS_NONSEQ;
      hsize_i_tb  = 3'b010;
      @(posedge clk_tb);
      wait(hreadyout_o_tb == 1'b1);
      @(negedge clk_tb);
      read_data = hrdata_o_tb;
      @(posedge clk_tb);
      hwdata_i_tb = '0;
      haddr_i_tb  = '0;
      htrans_i_tb = AHB_HTRANS_IDLE;
    end
  endtask // read_single_word

  task read_single_word_delay(input [31:0] address);
    begin
      @(posedge clk_tb);
      hsel_i_tb   = 1;
      haddr_i_tb  = address;
      hwrite_i_tb = 0;
      hready_i_tb = 1;
      htrans_i_tb = AHB_HTRANS_NONSEQ;
      hsize_i_tb  = 3'b010;
      //@(posedge clk_tb);
      //wait(hreadyout_o_tb == 1'b1);
      @(posedge hreadyout_o_tb);
      @(negedge clk_tb);
      read_data = hrdata_o_tb;
      hwdata_i_tb = '0;
      haddr_i_tb  = '0;
      htrans_i_tb = AHB_HTRANS_IDLE;
    end
  endtask // read_single_word_delay

  //task read_single_word(input [31:0] address);
  //  begin
  //    @(posedge clk_tb);
  //    hsel_i_tb   = 1;
  //    haddr_i_tb  = address;
  //    hwrite_i_tb = 0;
  //    hready_i_tb = 1;
  //    htrans_i_tb = AHB_HTRANS_NONSEQ;
  //    hsize_i_tb  = 3'b010;

  //    repeat (2) @(posedge clk_tb);
  //    wait(hreadyout_o_tb == 1'b1);

  //    // Capture data while hrdata is valid (before any clock edge changes it)
  //    read_data = hrdata_o_tb;

  //    // External (TLUL) access: hold dv_i high through one posedge so
  //    // resp_ack fires and pending_q clears before htrans drops.
  //    if (address < VH_REGISTER_ADDRESS_OFFSET)
  //      @(posedge clk_tb);

  //    hwdata_i_tb = 0;
  //    haddr_i_tb  = '0;
  //    htrans_i_tb = AHB_HTRANS_IDLE;
  //  end
  //endtask

  //----------------------------------------------------------------
  // write_single_word()
  //
  // Write the given word to the DUT using the DUT interface.
  //----------------------------------------------------------------
  task write_single_word(input [31:0] address,
                         input [31:0] word);
    begin
      @(posedge clk_tb);
      hsel_i_tb   = 1;
      haddr_i_tb  = address;
      hwrite_i_tb = 1;
      hready_i_tb = 1;
      htrans_i_tb = AHB_HTRANS_NONSEQ;
      hsize_i_tb  = 3'b010;
      @(posedge clk_tb);
      wait(hreadyout_o_tb == 1'b1);
      hwdata_i_tb = word;
      @(posedge clk_tb);
      haddr_i_tb  = '0;
      hwrite_i_tb = 0;
      htrans_i_tb = AHB_HTRANS_IDLE;
    end
  endtask // write_single_word
  
  //task write_single_word(input [31:0] address,
  //                       input [31:0] word);
  //  begin
  //    @(posedge clk_tb);
  //    hsel_i_tb   = 1;
  //    haddr_i_tb  = address;
  //    hwrite_i_tb = 1;
  //    hready_i_tb = 1;
  //    htrans_i_tb = AHB_HTRANS_NONSEQ;
  //    hsize_i_tb  = 3'b010;
  //    wait(hreadyout_o_tb == 1'b0);
  //    //repeat (2) @(posedge clk_tb);
  //    wait(hreadyout_o_tb == 1'b1);

  //    // External (TLUL) access: hold dv_i high through one posedge so
  //    // resp_ack can fire and pending_q clears before htrans drops.
  //    // Internal accesses (addr >= VH_REGISTER_ADDRESS_OFFSET) skip this.
  //    //if (address < VH_REGISTER_ADDRESS_OFFSET)
  //    //  @(posedge clk_tb);

  //    haddr_i_tb  = '0;
  //    hwdata_i_tb = word;
  //    hwrite_i_tb = 0;
  //    htrans_i_tb = AHB_HTRANS_IDLE;
  //  end
  //endtask

  //----------------------------------------------------------------
  // check_name_version()
  //
  // Read the name and version from the DUT.
  //----------------------------------------------------------------
  task check_name_version;
    reg [31:0] name0;
    reg [31:0] name1;
    reg [31:0] version0;
    reg [31:0] version1;
    begin
      read_single_word(SHA3_NAME_0);
      name0 = read_data;
      read_single_word(SHA3_NAME_1);
      name1 = read_data;
      read_single_word(SHA3_VERSION_0);
      version0 = read_data;
      read_single_word(SHA3_VERSION_1);
      version1 = read_data;

      $display("DUT name: %c%c%c%c%c%c%c%c",
               name0[15 :  8], name0[7  :  0],
               name0[31 : 24], name0[23 : 16], 
               name1[15 :  8], name1[7  :  0],
               name1[31 : 24], name1[23 : 16]);
      $display("DUT version: %c%c%c%c%c%c%c%c",
               version0[15 :  8], version0[7  :  0],
               version0[31 : 24], version0[23 : 16],
               version1[15 :  8], version1[7  :  0],
               version1[31 : 24], version1[23 : 16]);
    end
  endtask // check_name_version

  //----------------------------------------------------------------
  // wait_sha3_done()
  //
  // Poll SHA3_STATUS until sha3_squeeze (bit 2) is set, indicating
  // the Keccak permutation is complete and digest is ready to read.
  //----------------------------------------------------------------
  task wait_sha3_done;
    begin
      read_data = 0;
      #(CLK_PERIOD);

      while (!read_data[STATUS_SHA3_SQUEEZE])
        begin
          read_single_word(SHA3_STATUS_KMAC);
        end
    end
  endtask // wait_sha3_done

  //----------------------------------------------------------------
  // read_state_n()
  //
  // Read DIGEST_WORDS x 32-bit words from STATE registers into
  // digest_data. DIGEST_WORDS is derived from SHA3_MODE.
  //----------------------------------------------------------------
  task read_state_n;
    int w;
    begin
      digest_data = 0;
      for (w = 0; w < DIGEST_WORDS; w++)
        begin
          read_single_word_delay(SHA3_STATE_BASE_KMAC + (w * 4));
          // Store word 0 at the most-significant position so that $displayh/%h
          // prints the digest in the correct big-endian (NIST) byte order.
          digest_data[(DIGEST_WORDS-1-w)*32 +: 32] = read_data;
        end
    end
  endtask // read_state_n


  //----------------------------------------------------------------
  // read_xof_n()
  //
  // Read variable-length XOF output for SHAKE/cSHAKE.  Issues
  // sha3_run() (which internally polls STATUS.sha3_squeeze) between
  // squeeze blocks when the requested output exceeds one rate block.
  // Stores words with word-0 at the MSB of xof_data so that printing
  // in ascending word-index order yields the correct NIST byte order.
  // Calls sha3_done() after all output has been collected.
  //
  // outLen_bits must be a positive multiple of 32.
  //----------------------------------------------------------------
  task read_xof_n(input int unsigned outLen_bits);
    int unsigned total_words, words_read, n, w;
    begin
      assert (outLen_bits % 32 == 0)
        else $display("WARNING: read_xof_n: outLen_bits=%0d is not a multiple of 32",
                      outLen_bits);

      total_words = outLen_bits / 32;
      words_read  = 0;
      xof_data    = 0;

      while (words_read < total_words)
        begin
          // Number of words to consume from this squeeze block
          n = ((total_words - words_read) < RATE_WORDS) ?
               (total_words - words_read) : RATE_WORDS;

          for (w = 0; w < n; w++)
            begin
              read_single_word_delay(SHA3_STATE_BASE_KMAC + (w * 4));
              // Place word 0 of each squeeze at the highest bit position so
              // iterating ww = 0..total_words-1 with %08h prints in NIST order.
              xof_data[(total_words - 1 - words_read - w) * 32 +: 32] = read_data;
            end

          words_read += n;

          // Issue CMD_RUN to squeeze the next block (sha3_run also polls done).
          if (words_read < total_words)
            sha3_run();
        end

      sha3_done();
    end
  endtask // read_xof_n


  //----------------------------------------------------------------
  // wait_sha3_idle()
  //
  // Sample busy_o_tb on each posedge clk_tb until the DUT signals
  // idle (busy_o == 0).  busy_o is combinational from a registered
  // source (sha_idle), so its value is stable after each rising edge.
  // This avoids AHB register-poll overhead used by the old approach.
  //----------------------------------------------------------------
  task wait_sha3_idle;
    begin
      @(posedge clk_tb);
      while (busy_o_tb)
        @(posedge clk_tb);
    end
  endtask // wait_sha3_idle


  //----------------------------------------------------------------
  // configure_sha3()
  //
  // Wait for the engine to be idle, then program CFG_SHADOWED with
  // the given mode, kstrength, msg_endianness and state_endianness.
  // CFG_SHADOWED is a shadowed register and requires two consecutive
  // identical writes to commit the value.
  //----------------------------------------------------------------
  task configure_sha3(input [1:0] mode,
                      input [2:0] kstrength,
                      input       msg_endianness,
                      input       state_endianness);
    reg [31:0] cfg_val;
    begin
      wait_sha3_idle();

      cfg_val = (kstrength      << 1) |
                (mode           << 4) |
                (msg_endianness << 8) |
                (state_endianness << 9);

      write_single_word(SHA3_CFG, cfg_val);
      write_single_word(SHA3_CFG, cfg_val);
      // SHA3_CFG (0x1024) aliases PREFIX_1 via the VH adapter - do NOT write here.
      // CFG_SHADOWED requires two consecutive identical writes to commit (shadow protocol).
      write_single_word(SHA3_CFG_KMAC, cfg_val);
      write_single_word(SHA3_CFG_KMAC, cfg_val);
    end
  endtask // configure_sha3


  //----------------------------------------------------------------
  // sha3_start()
  //
  // Issue the START command to the SHA3 engine, signalling that it
  // should begin accepting incoming message data. Messages written
  // to MSG_FIFO before START is issued are silently discarded.
  // Polls STATUS.sha3_absorb after issuing the command to confirm
  // the engine has entered absorb state before returning - matching
  // the driver behaviour in sha3.rs digest_start().
  //----------------------------------------------------------------
  task sha3_start;
    begin
      write_single_word(SHA3_CMD, CMD_START);
      write_single_word(SHA3_CMD_KMAC, CMD_START);
      #(CLK_PERIOD);
      hsel_i_tb = 0;

      // Wait until engine enters absorb state (ready to accept MSG_FIFO data)
      read_data = 0;
      #(CLK_PERIOD);
      while (!read_data[STATUS_SHA3_ABSORB])
        begin
          read_single_word(SHA3_STATUS_KMAC);
        end
    end
  endtask // sha3_start


  //----------------------------------------------------------------
  // sha3_process()
  //
  // Issue the PROCESS command after all message words have been
  // written to MSG_FIFO. The engine completes the sponge absorbing
  // step and applies SHA3 padding per the SHA3 specification.
  //----------------------------------------------------------------
  task sha3_process;
    begin
      write_single_word(SHA3_CMD, CMD_PROCESS);
      write_single_word(SHA3_CMD_KMAC, CMD_PROCESS);
      #(CLK_PERIOD);
      hsel_i_tb = 0;
    end
  endtask // sha3_process


  //----------------------------------------------------------------
  // sha3_run()
  //
  // Issue the RUN command to trigger one additional full Keccak
  // round. Used when the desired digest length exceeds the Keccak
  // rate. No interrupt is generated on completion; this task polls
  // STATUS.sha3_squeeze to confirm readiness before returning.
  //----------------------------------------------------------------
  task sha3_run;
    begin
      write_single_word(SHA3_CMD, CMD_RUN);
      write_single_word(SHA3_CMD_KMAC, CMD_RUN);
      #(CLK_PERIOD);
      hsel_i_tb = 0;
      wait_sha3_done();
    end
  endtask // sha3_run


  //----------------------------------------------------------------
  // sha3_done()
  //
  // Issue the DONE command after all digest data has been read.
  // Clears the Keccak state, SHA3 FSM, and internal variables,
  // returning the engine to idle for the next operation.
  //----------------------------------------------------------------
  task sha3_done;
    begin
      write_single_word(SHA3_CMD_KMAC, CMD_DONE);
      #(CLK_PERIOD);
      hsel_i_tb = 0;
    end
  endtask // sha3_done


  //----------------------------------------------------------------
  // write_prefix()
  //
  // Write the cSHAKE PREFIX registers PREFIX_0..PREFIX_10 (11 words,
  // AHB 0x1020..0x1048) from a pre-encoded 88-character hex string.
  //
  // prefix_hex is produced by convert_cshake_req.py and contains
  //   encode_string(N) || encode_string(S)
  // zero-padded to 44 bytes per NIST SP 800-185.
  //
  // Must be called after configure_sha3() and before sha3_start().
  //----------------------------------------------------------------
  task write_prefix(input string prefix_hex);
    string       word_str;
    logic [31:0] word_val;
    int i;
    begin
      for (i = 0; i < 11; i++)
        begin
          word_str = prefix_hex.substr(i * 8, i * 8 + 7);
          word_val = word_str.atohex();
          write_single_word(SHA3_PREFIX_BASE + (i * 4), word_val);
        end
    end
  endtask // write_prefix


  //----------------------------------------------------------------
  // acvp_test()
  //
  // Process ACVP test vectors from ../stimulus/acvp/SHA3-256.txt
  // and write digests to ../stimulus/acvp/SHA3-256_digest.txt
  //
  // Input file format (cervf -of IR, one line per test case):
  //   AFT <tgId> <tcId> <len> <msg_hex>
  //   MCT <tgId> <tcId> <len> <seed_hex>
  //
  // Output file format (cervf -oj input, one line per result):
  //   AFT <tcId> <digest_hex>
  //   MCT <tcId> <digest_hex>   (100 lines per MCT test case)
  //
  // SHA3 AFT message flow:
  //   1. configure_sha3() - wait idle, write CFG_SHADOWED x2
  //   2. sha3_start()     - issue CMD_START
  //   3. Write message words to MSG_FIFO (32 bits at a time)
  //   4. sha3_process()   - issue CMD_PROCESS
  //   5. wait_sha3_done() - poll STATUS.sha3_squeeze
  //   6. read_state_256() - read 8 STATE words into digest_data
  //   7. sha3_done()      - issue CMD_DONE
  //
  // SHA3 MCT pseudo code:
  //   MD[0] = SEED
  //   For ol = 0 to 99:
  //     For il = 0 to 999:
  //       MD[il+1] = SHA3(MD[il])
  //     Output MD[1000]; SEED = MD[1000]
  //----------------------------------------------------------------
  task acvp_test;
    int fin, fout, scan_result;
    string pt, test_type;
    int tcid;
    int pt_len;
    int num_words;
    int i;
    string word_str;
    string md_str;
    string dummy_str;
    reg [31:0] word_val;
    // SHAKE / cSHAKE per-test variables
    int unsigned msg_len_bits;      // message length in bits (0 = empty message)
    int unsigned xof_outLen_bits;   // requested XOF output length in bits
    int unsigned words_to_write;    // = xof_outLen_bits / 32
    string prefix_hex;              // 88-char cSHAKE PREFIX (pre-encoded by Python)
    begin
      if (ALGO_TYPE == 0)
        $display("   -- SHA3-%0d ACVP testbench started --", SHA3_MODE);
      else if (ALGO_TYPE == 1)
        $display("   -- SHAKE-%0d ACVP testbench started --", SHAKE_BITS);
      else
        $display("   -- cSHAKE-%0d ACVP testbench started --", SHAKE_BITS);

      fin  = $fopen(IN_FILE,  "r");
      if (fin == 0)
        begin
          $display("ERROR: Input file %s not found", IN_FILE);
          $stop;
        end

      fout = $fopen(OUT_FILE, "w");
      if (fout == 0)
        begin
          $display("ERROR: Cannot open output file %s", OUT_FILE);
          $fclose(fin);
          $stop;
        end

      // ================================================================
      // SHA3 branch (ALGO_TYPE == 0): AFT + MCT, fixed-length output
      // ================================================================
      if (ALGO_TYPE == 0)
        begin
          while (1)
            begin
              // cervf IR format: <testType> <tgId> <tcId> <len> <msg_hex>
              scan_result = $fscanf(fin, "%s %*d %d %*d %s", test_type, tcid, pt);
              if (scan_result != 3)
                begin
                  $display("End of file reached after %0d test vectors", tc_ctr);
                  break;
                end

              if (test_type == "AFT")
                begin
                  $display("MSG: Running AFT vector %4d", tcid);

                  pt_len = pt.len();

                  //------------------------------------------------------
                  // Step 1: Configure SHA3 (SHA3 mode, kstrength,
                  //         big-endian message and state).
                  //         Waits for idle; writes CFG_SHADOWED twice.
                  //------------------------------------------------------
                  configure_sha3(CFG_MODE_SEL, KSTRENGTH, 1'b1, 1'b1);

                  //------------------------------------------------------
                  // Step 2: Issue START - engine begins absorbing.
                  //------------------------------------------------------
                  sha3_start();

                  //------------------------------------------------------
                  // Step 3: Stream message words into MSG_FIFO.
                  //         Parse hex string 8 chars (32 bits) at a time.
                  //         Last partial word padded with trailing zeros.
                  //------------------------------------------------------
                  num_words = (pt_len + 7) / 8;

                  for (i = 0; i < num_words; i++)
                    begin
                      if ((i * 8 + 8) <= pt_len)
                        begin
                          word_str = pt.substr(i * 8, i * 8 + 7);
                        end
                      else
                        begin
                          word_str = pt.substr(i * 8, pt_len - 1);
                          while (word_str.len() < 8)
                            word_str = {word_str, "0"};
                        end
                      word_val = word_str.atohex();
                      write_single_word(SHA3_MSG_FIFO_KMAC, word_val);
                    end

                  //------------------------------------------------------
                  // Step 4: Issue PROCESS - finishes absorbing,
                  //         triggers Keccak permutation.
                  //------------------------------------------------------
                  sha3_process();

                  //------------------------------------------------------
                  // Step 5: Poll STATUS until sha3_squeeze (bit 2) = 1.
                  //------------------------------------------------------
                  wait_sha3_done();

                  //------------------------------------------------------
                  // Step 6: Read DIGEST_WORDS STATE words.
                  //------------------------------------------------------
                  read_state_n();

                  case (SHA3_MODE)
                    224: $display("TC%0d digest: %056h", tcid, digest_data[223:0]);
                    384: $display("TC%0d digest: %096h", tcid, digest_data[383:0]);
                    512: $display("TC%0d digest: %0128h", tcid, digest_data[511:0]);
                    default: $display("TC%0d digest: %064h", tcid, digest_data[255:0]);
                  endcase
                  case (SHA3_MODE)
                    224: $fwrite(fout, "%s %0d %056h\n", test_type, tcid, digest_data[223:0]);
                    384: $fwrite(fout, "%s %0d %096h\n", test_type, tcid, digest_data[383:0]);
                    512: $fwrite(fout, "%s %0d %0128h\n", test_type, tcid, digest_data[511:0]);
                    default: $fwrite(fout, "%s %0d %064h\n", test_type, tcid, digest_data[255:0]);
                  endcase

                  //------------------------------------------------------
                  // Step 7: Issue DONE - engine returns to idle.
                  //------------------------------------------------------
                  sha3_done();

                  tc_ctr = tc_ctr + 1;
                end

              else if (test_type == "MCT")
                begin
                  //------------------------------------------------------
                  // SHA3 MCT: MD[0] = SEED; repeat 100 outer iterations.
                  // Each outer iteration hashes the running digest 1000
                  // times and outputs the final result.
                  //------------------------------------------------------
                  $display("MSG: Running MCT vector %4d", tcid);

                  md_str = pt;  // SEED from input file

                  for (int ol = 0; ol < 100; ol++)
                    begin
                      for (int il = 0; il < 1000; il++)
                        begin
                          if (il % 100 == 0)
                            $display("ol count: %3d il count: %3d", ol, il);

                          configure_sha3(CFG_MODE_SEL, KSTRENGTH,
                                         1'b1, 1'b1);
                          sha3_start();

                          //-- Write previous digest as next message ------
                          pt_len   = md_str.len();
                          num_words = (pt_len + 7) / 8;

                          for (i = 0; i < num_words; i++)
                            begin
                              if ((i * 8 + 8) <= pt_len)
                                begin
                                  word_str = md_str.substr(i * 8, i * 8 + 7);
                                end
                              else
                                begin
                                  word_str = md_str.substr(i * 8, pt_len - 1);
                                  while (word_str.len() < 8)
                                    word_str = {word_str, "0"};
                                end
                              word_val = word_str.atohex();
                              write_single_word(SHA3_MSG_FIFO_KMAC, word_val);
                            end

                          sha3_process();
                          wait_sha3_done();
                          read_state_n();
                          sha3_done();

                          case (SHA3_MODE)
                            224: md_str = $sformatf("%056h", digest_data[223:0]);
                            384: md_str = $sformatf("%096h", digest_data[383:0]);
                            512: md_str = $sformatf("%0128h", digest_data[511:0]);
                            default: md_str = $sformatf("%064h", digest_data[255:0]);
                          endcase
                        end // inner loop

                      case (SHA3_MODE)
                        224: $fwrite(fout, "%s %0d %056h\n", test_type, tcid, digest_data[223:0]);
                        384: $fwrite(fout, "%s %0d %096h\n", test_type, tcid, digest_data[383:0]);
                        512: $fwrite(fout, "%s %0d %0128h\n", test_type, tcid, digest_data[511:0]);
                        default: $fwrite(fout, "%s %0d %064h\n", test_type, tcid, digest_data[255:0]);
                      endcase
                    end // outer loop

                  tc_ctr = tc_ctr + 1;
                end

              else
                begin
                  $display("MSG: Skipping vector type '%s' tcId %0d",
                           test_type, tcid);
                end
            end // while(1) SHA3
        end // ALGO_TYPE == 0

      // ================================================================
      // SHAKE branch (ALGO_TYPE == 1): AFT only, variable-length output
      // Input format: AFT <tgId> <tcId> <len_bits> <outLen_bits> <msg_hex>
      //   len_bits == 0 means empty message; MSG_FIFO writes are skipped.
      //   msg_hex == "00" is the placeholder emitted by convert_shake_req.py
      //   for zero-length messages and is not written to MSG_FIFO.
      // ================================================================
      else if (ALGO_TYPE == 1)
        begin
          while (1)
            begin
              scan_result = $fscanf(fin, "%s %*d %d %d %d %s",
                                    test_type, tcid, msg_len_bits, xof_outLen_bits, pt);
              if (scan_result != 5)
                begin
                  $display("End of file reached after %0d test vectors", tc_ctr);
                  break;
                end

              $display("MSG: Running SHAKE-%0d AFT vector %4d (msgLen=%0d outLen=%0d bits)",
                       SHAKE_BITS, tcid, msg_len_bits, xof_outLen_bits);

              pt_len = pt.len();

              // Step 1: Configure SHAKE
              configure_sha3(CFG_MODE_SEL, KSTRENGTH, 1'b1, 1'b1);

              // Step 2: START
              sha3_start();

              // Step 3: Write message words - skip entirely for empty messages.
              if (msg_len_bits > 0)
                begin
                  num_words = (pt_len + 7) / 8;
                  for (i = 0; i < num_words; i++)
                    begin
                      if ((i * 8 + 8) <= pt_len)
                        begin
                          word_str = pt.substr(i * 8, i * 8 + 7);
                        end
                      else
                        begin
                          word_str = pt.substr(i * 8, pt_len - 1);
                          while (word_str.len() < 8)
                            word_str = {word_str, "0"};
                        end
                      word_val = word_str.atohex();
                      write_single_word(SHA3_MSG_FIFO_KMAC, word_val);
                    end
                end

              // Step 4: PROCESS
              sha3_process();

              // Step 5: Wait for squeeze
              wait_sha3_done();

              // Step 6: Read XOF output (issues CMD_RUN between squeezes,
              //         calls sha3_done() at the end)
              read_xof_n(xof_outLen_bits);

              // Step 7: Write output line
              words_to_write = xof_outLen_bits / 32;
              $fwrite(fout, "%s %0d ", test_type, tcid);
              for (int ww = 0; ww < words_to_write; ww++)
                $fwrite(fout, "%08h", xof_data[(words_to_write - 1 - ww) * 32 +: 32]);
              $fwrite(fout, "\n");

              tc_ctr = tc_ctr + 1;
            end // while(1) SHAKE
        end // ALGO_TYPE == 1

      // ================================================================
      // cSHAKE branch (ALGO_TYPE == 2): AFT only, variable-length output
      // Input format: AFT <tgId> <tcId> <len_bits> <outLen_bits> <prefix_88hex> <msg_hex>
      // Comment lines beginning with '#' (skipped overlength vectors) are ignored.
      // ================================================================
      else if (ALGO_TYPE == 2)
        begin
          while (1)
            begin
              scan_result = $fscanf(fin, "%s %*d %d %*d %d %s %s",
                                    test_type, tcid, xof_outLen_bits, prefix_hex, pt);
              if (scan_result < 1)
                begin
                  $display("End of file reached after %0d test vectors", tc_ctr);
                  break;
                end

              // Skip comment lines emitted for overlength-customization vectors
              if (test_type == "#")
                begin
                  void'($fgets(dummy_str, fin));
                  continue;
                end

              if (scan_result != 5)
                begin
                  $display("End of file reached after %0d test vectors", tc_ctr);
                  break;
                end

              $display("MSG: Running cSHAKE-%0d AFT vector %4d (outLen=%0d bits)",
                       SHAKE_BITS, tcid, xof_outLen_bits);

              pt_len = pt.len();

              // Step 1: Configure cSHAKE
              configure_sha3(CFG_MODE_SEL, KSTRENGTH, 1'b1, 1'b1);

              // Step 2: Write PREFIX registers (before START)
              write_prefix(prefix_hex);

              // Step 3: START
              sha3_start();

              // Step 4: Write message words
              num_words = (pt_len + 7) / 8;
              for (i = 0; i < num_words; i++)
                begin
                  if ((i * 8 + 8) <= pt_len)
                    begin
                      word_str = pt.substr(i * 8, i * 8 + 7);
                    end
                  else
                    begin
                      word_str = pt.substr(i * 8, pt_len - 1);
                      while (word_str.len() < 8)
                        word_str = {word_str, "0"};
                    end
                  word_val = word_str.atohex();
                  write_single_word(SHA3_MSG_FIFO_KMAC, word_val);
                end

              // Step 5: PROCESS
              sha3_process();

              // Step 6: Wait for squeeze
              wait_sha3_done();

              // Step 7: Read XOF output
              read_xof_n(xof_outLen_bits);

              // Step 8: Write output line
              words_to_write = xof_outLen_bits / 32;
              $fwrite(fout, "%s %0d ", test_type, tcid);
              for (int ww = 0; ww < words_to_write; ww++)
                $fwrite(fout, "%08h", xof_data[(words_to_write - 1 - ww) * 32 +: 32]);
              $fwrite(fout, "\n");

              tc_ctr = tc_ctr + 1;
            end // while(1) cSHAKE
        end // ALGO_TYPE == 2

      else
        begin
          $display("ERROR: Unknown ALGO_TYPE=%0d (must be 0=SHA3, 1=SHAKE, 2=cSHAKE)",
                   ALGO_TYPE);
        end

      $fclose(fin);
      $fclose(fout);

      if (ALGO_TYPE == 0)
        $display("   -- SHA3-%0d ACVP testbench completed: %0d vectors processed --",
                 SHA3_MODE, tc_ctr);
      else if (ALGO_TYPE == 1)
        $display("   -- SHAKE-%0d ACVP testbench completed: %0d vectors processed --",
                 SHAKE_BITS, tc_ctr);
      else
        $display("   -- cSHAKE-%0d ACVP testbench completed: %0d vectors processed --",
                 SHAKE_BITS, tc_ctr);
    end
  endtask // acvp_test

  //----------------------------------------------------------------
  // sha3_test
  // The main test functionality.
  //----------------------------------------------------------------
  initial
    begin : sha3_test
      $display("   -- Testbench for sha3_ctrl started --");

      init_sim();
      reset_dut();
      check_name_version();

      acvp_test();

      display_test_result();

      $display("   -- Testbench for sha3_ctrl done --");
      $finish;
    end // sha3_test

endmodule // sha3_ctrl_tb
