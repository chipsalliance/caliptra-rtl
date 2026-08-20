//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
//----------------------------------------------------------------------
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

// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
// Description: This file contains the top level and utility sequences
//     used by test_top. It can be extended to create derivative top
//     level sequences.
//
//----------------------------------------------------------------------
//
//----------------------------------------------------------------------
//


typedef HMAC_env_configuration  hmac_env_configuration_t;

class HMAC_bench_sequence_base extends uvmf_sequence_base #(uvm_sequence_item);

  `uvm_object_utils( HMAC_bench_sequence_base );

  // pragma uvmf custom sequences begin

typedef HMAC_env_sequence_base #(
        .CONFIG_T(hmac_env_configuration_t)
        )
        hmac_env_sequence_base_t;
rand hmac_env_sequence_base_t hmac_env_seq;



  // UVMF_CHANGE_ME : Instantiate, construct, and start sequences as needed to create stimulus scenarios.
  // Instantiate sequences here
  typedef HMAC_rst_random_sequence  hmac_rst_agent_random_seq_t;
  hmac_rst_agent_random_seq_t hmac_rst_agent_random_seq;
  // pragma uvmf custom sequences end

  // Sequencer handles for each active interface in the environment
  typedef HMAC_rst_transaction  hmac_rst_agent_transaction_t;
  uvm_sequencer #(hmac_rst_agent_transaction_t)  hmac_rst_agent_sequencer; 

  // Sequencer handles for each QVIP interface
  mvc_sequencer uvm_test_top_environment_qvip_ahb_lite_slave_subenv_ahb_lite_slave_0_sqr;

  // Top level environment configuration handle
  hmac_env_configuration_t top_configuration;

  // Configuration handles to access interface BFM's
  HMAC_rst_configuration  hmac_rst_agent_config;
  // Local handle to register model for convenience
  hmac_reg_model_top reg_model;
  uvm_status_e status;

  // pragma uvmf custom class_item_additional begin

  // Shared STATUS poll watchdog limit (used by wait_for_status).
  localparam int unsigned BENCH_POLL_LIMIT = 5000;
  // Number of dwords in one HMAC raw SHA block (32 * 32-bit = 1024 bits).
  localparam int unsigned BENCH_BLOCK_DWORDS = 32;

  // ----------------------------------------------------------------
  // Poll HMAC512_STATUS until any bit in mask_bit is set. Bounded by
  // BENCH_POLL_LIMIT so a hung DUT fails the test instead of the sim.
  //   READY = bit 0   -> use 32'h1
  //   VALID = bit 1   -> use 32'h2
  // ----------------------------------------------------------------
  task wait_for_status(input bit [31:0] mask_bit,
                       input string     bit_name,
                       output bit [31:0] data);
    int poll_count = 0;
    do begin
      reg_model.HMAC512_STATUS.read(status, data);
      poll_count++;
      if (poll_count > BENCH_POLL_LIMIT) begin
        `uvm_fatal("HMAC_BENCH",
          $sformatf("STATUS.%s never asserted after %0d polls -- DUT hung",
                    bit_name, BENCH_POLL_LIMIT))
      end
    end while ((data & mask_bit) == 0);
  endtask

  // ----------------------------------------------------------------
  // RAL helpers shared by every sequence. They wrap the foreach
  // loops over HMAC512_{KEY,BLOCK,TAG,LFSR_SEED} so sequence bodies
  // only state what data they want to move, not how to walk the regs.
  // ----------------------------------------------------------------
  task write_block_regs(input bit [31:0] blk []);
    foreach (reg_model.HMAC512_BLOCK[i])
      reg_model.HMAC512_BLOCK[i].write(status, blk[i]);
  endtask

  task write_key_regs(input bit [31:0] k [16]);
    foreach (reg_model.HMAC512_KEY[i])
      reg_model.HMAC512_KEY[i].write(status, k[i]);
  endtask

  task read_tag_regs(output bit [31:0] tag [16]);
    foreach (reg_model.HMAC512_TAG[i])
      reg_model.HMAC512_TAG[i].read(status, tag[i]);
  endtask

  task write_tag_regs(input bit [31:0] tag [16]);
    foreach (reg_model.HMAC512_TAG[i])
      reg_model.HMAC512_TAG[i].write(status, tag[i]);
  endtask

  task write_random_lfsr_seed();
    foreach (reg_model.HMAC512_LFSR_SEED[i])
      reg_model.HMAC512_LFSR_SEED[i].write(status, $urandom());
  endtask

  // ----------------------------------------------------------------
  // Write CTRL.ZEROIZE and wait for STATUS.READY. Required between
  // back-to-back operations because hmac.sv gates ready_reg on the
  // awaiting_zeroize flag after every final tag write.
  // ----------------------------------------------------------------
  task zeroize_and_wait();
    bit [31:0] read_data;
    reg_model.HMAC512_CTRL.INIT.set(1'b0);
    reg_model.HMAC512_CTRL.NEXT.set(1'b0);
    reg_model.HMAC512_CTRL.LAST.set(1'b0);
    reg_model.HMAC512_CTRL.RESTORE.set(1'b0);
    reg_model.HMAC512_CTRL.ZEROIZE.set(1'b1);
    reg_model.HMAC512_CTRL.update(status);
    fork hmac_rst_agent_config.wait_for_num_clocks(8); join
    wait_for_status(32'h1, "READY", read_data);
  endtask

  // ----------------------------------------------------------------
  // Synthesize the FIPS-180 padding tail block. Caller passes the
  // total block_length B (so the HMAC core hashes K_ipad + B-1 msg
  // blocks + 1 pad block); pad_len_bits = B * 1024.
  // ----------------------------------------------------------------
  function void build_pad_block(input int unsigned block_length,
                                output bit [31:0] blk [BENCH_BLOCK_DWORDS]);
    blk[0] = 32'h8000_0000;
    for (int i = 1; i < 31; i++) blk[i] = 32'h0;
    blk[31] = block_length * 1024;
  endfunction

  // ----------------------------------------------------------------
  // Drive blocks[start_idx..end_idx] for one HMAC op.
  //   restore_first: 1 -> first CTRL is RESTORE plus NEXT (multi-block
  //                       resume) or LAST (single remaining block).
  //                  0 -> first CTRL is INIT.
  //   mode_bit     : 0 -> HMAC-384, 1 -> HMAC-512.
  //   wait_last    : 1 -> wait STATUS.VALID, 0 -> wait STATUS.READY.
  // CTRL bits: [0]=INIT [1]=NEXT [3]=MODE [5]=LAST [7]=RESTORE.
  // ----------------------------------------------------------------
  task run_blocks(input bit [31:0] blocks [],
                  input int unsigned start_idx,
                  input int unsigned end_idx,
                  input int unsigned total_blocks,
                  input bit          restore_first,
                  input bit          mode_bit,
                  input bit          wait_last);
    bit [31:0] read_data;
    bit [31:0] ctrl_val;
    bit [31:0] blk [BENCH_BLOCK_DWORDS];

    for (int unsigned b = start_idx; b <= end_idx; b++) begin
      foreach (blk[i]) blk[i] = blocks[b * BENCH_BLOCK_DWORDS + i];
      write_block_regs(blk);

      ctrl_val = 32'h0;
      if (b == start_idx && restore_first) begin
        ctrl_val[7] = 1'b1;
        if (b != total_blocks - 1)
          ctrl_val[1] = 1'b1;
      end else if (b == 0) begin
        ctrl_val[0] = 1'b1;
      end else begin
        ctrl_val[1] = 1'b1;
      end
      if (mode_bit)              ctrl_val[3] = 1'b1;
      if (b == total_blocks - 1) ctrl_val[5] = 1'b1;

      reg_model.HMAC512_CTRL.write(status, ctrl_val);
      // Wait for CTRL singlepulse to clear READY before polling.
      fork hmac_rst_agent_config.wait_for_num_clocks(8); join

      if (b == end_idx && wait_last)
        wait_for_status(32'h2, "VALID", read_data);
      else
        wait_for_status(32'h1, "READY", read_data);
    end
  endtask
  // pragma uvmf custom class_item_additional end

  // ****************************************************************************
  function new( string name = "" );
    super.new( name );
    // Retrieve the configuration handles from the uvm_config_db

    // Retrieve top level configuration handle
    if ( !uvm_config_db#(hmac_env_configuration_t)::get(null,UVMF_CONFIGURATIONS, "TOP_ENV_CONFIG",top_configuration) ) begin
      `uvm_info("CFG", "*** FATAL *** uvm_config_db::get can not find TOP_ENV_CONFIG.  Are you using an older UVMF release than what was used to generate this bench?",UVM_NONE);
      `uvm_fatal("CFG", "uvm_config_db#(hmac_env_configuration_t)::get cannot find resource TOP_ENV_CONFIG");
    end

    // Retrieve config handles for all agents
    if( !uvm_config_db #( HMAC_rst_configuration )::get( null , UVMF_CONFIGURATIONS , hmac_rst_agent_BFM , hmac_rst_agent_config ) ) 
      `uvm_fatal("CFG" , "uvm_config_db #( HMAC_rst_configuration )::get cannot find resource hmac_rst_agent_BFM" )

    // Assign the sequencer handles from the handles within agent configurations
    hmac_rst_agent_sequencer = hmac_rst_agent_config.get_sequencer();

    // Retrieve QVIP sequencer handles from the uvm_config_db
    if( !uvm_config_db #(mvc_sequencer)::get( null,UVMF_SEQUENCERS,"uvm_test_top.environment.qvip_ahb_lite_slave_subenv.ahb_lite_slave_0", uvm_test_top_environment_qvip_ahb_lite_slave_subenv_ahb_lite_slave_0_sqr) ) 
      `uvm_warning("CFG" , "uvm_config_db #( mvc_sequencer )::get cannot find resource ahb_lite_slave_0" ) 
    reg_model = top_configuration.hmac_rm;


    // pragma uvmf custom new begin
    // pragma uvmf custom new end

  endfunction

  // ****************************************************************************
  virtual task body();
    // pragma uvmf custom body begin

    // Construct sequences here

    hmac_env_seq = hmac_env_sequence_base_t::type_id::create("hmac_env_seq");

    hmac_rst_agent_random_seq     = hmac_rst_agent_random_seq_t::type_id::create("hmac_rst_agent_random_seq");
    fork
      hmac_rst_agent_config.wait_for_reset();
    join
    reg_model.reset();
    // Start RESPONDER sequences here
    fork
    join_none
    // Start INITIATOR sequences here.
    //
    // abr/mldsa style: NO repeat() of rst_random_seq. The DUT's
    // reset_n + cptra_pwrgood come directly from hdl_top's `bit rst`
    // which goes high at 200ns. The rst agent driver_bfm does not
    // drive any DUT pin in this env -- it exists only so the rst
    // monitor's analysis port can feed the predictor's reset hook
    // (for future otf_reset tests that toggle ev_rst).
    fork
    join

hmac_env_seq.start(top_configuration.vsqr);

    // UVMF_CHANGE_ME : Extend the simulation XXX number of clocks after 
    // the last sequence to allow for the last sequence item to flow 
    // through the design.
    fork
      hmac_rst_agent_config.wait_for_num_clocks(400);
    join

    // pragma uvmf custom body end
  endtask

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

