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
// DESCRIPTION: This file contains environment level sequences that will
//    be reused from block to top level simulations.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class kv_env_sequence_base #( 
      type CONFIG_T
      ) extends uvmf_virtual_sequence_base #(.CONFIG_T(CONFIG_T));


  `uvm_object_param_utils( kv_env_sequence_base #(
                           CONFIG_T
                           ) );

   parameter int HMAC_WRITE = 0;
   parameter int MLKEM_WRITE = 1;
   parameter int ECC_WRITE = 2;
   parameter int DOE_WRITE = 3;
   parameter int AES_WRITE = 4;

  // Handle to the environments register model
// This handle needs to be set before use.
  kv_reg_model_top  reg_model;

  rand reg [KV_ENTRY_ADDR_W-1:0] hmac_write_entry, mlkem_write_entry, ecc_write_entry, doe_write_entry, aes_write_entry;   
  rand reg [KV_NUM_WRITE-1:0] wr_clients; 

// This kv_env_sequence_base contains a handle to a kv_env_configuration object 
// named configuration.  This configuration variable contains a handle to each 
// sequencer within each agent within this environment and any sub-environments.
// The configuration object handle is automatically assigned in the pre_body in the
// base class of this sequence.  The configuration handle is retrieved from the
// virtual sequencer that this sequence is started on.
// Available sequencer handles within the environment configuration:

  // Initiator agent sequencers in kv_environment:
    // configuration.kv_rst_agent_config.sequencer
    // configuration.kv_hmac_write_agent_config.sequencer
    // configuration.kv_mlkem_write_agent_config.sequencer
    // configuration.kv_ecc_write_agent_config.sequencer
    // configuration.kv_doe_write_agent_config.sequencer
    // configuration.kv_aes_write_agent_config.sequencer
    // configuration.kv_hmac_key_read_agent_config.sequencer
    // configuration.kv_hmac_block_read_agent_config.sequencer
    // configuration.kv_mldsa_key_read_agent_config.sequencer
    // configuration.kv_ecc_privkey_read_agent_config.sequencer
    // configuration.kv_ecc_seed_read_agent_config.sequencer
    // configuration.kv_aes_key_read_agent_config.sequencer
    // configuration.kv_mlkem_seed_read_agent_config.sequencer
    // configuration.kv_mlkem_msg_read_agent_config.sequencer
    // configuration.kv_dma_read_agent_config.sequencer

  // Responder agent sequencers in kv_environment:


    typedef kv_rst_random_sequence kv_rst_agent_random_sequence_t;
    kv_rst_agent_random_sequence_t kv_rst_agent_rand_seq;

    typedef kv_write_key_entry_sequence kv_write_agent_key_entry_sequence_t;
    kv_write_agent_key_entry_sequence_t hmac_write_seq;
    kv_write_agent_key_entry_sequence_t mlkem_write_seq;
    kv_write_agent_key_entry_sequence_t ecc_write_seq;
    kv_write_agent_key_entry_sequence_t doe_write_seq;
    kv_write_agent_key_entry_sequence_t aes_write_seq;

    typedef kv_read_random_sequence kv_hmac_key_read_agent_random_sequence_t;
    kv_hmac_key_read_agent_random_sequence_t kv_hmac_key_read_agent_rand_seq;

    typedef kv_read_random_sequence kv_hmac_block_read_agent_random_sequence_t;
    kv_hmac_block_read_agent_random_sequence_t kv_hmac_block_read_agent_rand_seq;

    typedef kv_read_random_sequence kv_mldsa_key_read_agent_random_sequence_t;
    kv_mldsa_key_read_agent_random_sequence_t kv_mldsa_key_read_agent_rand_seq;

    typedef kv_read_random_sequence kv_ecc_privkey_read_agent_random_sequence_t;
    kv_ecc_privkey_read_agent_random_sequence_t kv_ecc_privkey_read_agent_rand_seq;

    typedef kv_read_random_sequence kv_ecc_seed_read_agent_random_sequence_t;
    kv_ecc_seed_read_agent_random_sequence_t kv_ecc_seed_read_agent_rand_seq;

    typedef kv_read_random_sequence kv_aes_key_read_agent_random_sequence_t;
    kv_aes_key_read_agent_random_sequence_t kv_aes_key_read_agent_rand_seq;

    typedef kv_read_random_sequence kv_mlkem_seed_read_agent_random_sequence_t;
    kv_mlkem_seed_read_agent_random_sequence_t kv_mlkem_seed_read_agent_rand_seq;

    typedef kv_read_random_sequence kv_mlkem_msg_read_agent_random_sequence_t;
    kv_mlkem_msg_read_agent_random_sequence_t kv_mlkem_msg_read_agent_rand_seq;

    typedef kv_read_random_sequence kv_dma_read_agent_random_sequence_t;
    kv_dma_read_agent_random_sequence_t kv_dma_read_agent_rand_seq;




  // pragma uvmf custom class_item_additional begin
  // pragma uvmf custom class_item_additional end
  
  function new(string name = "" );
    super.new(name);
    kv_rst_agent_rand_seq = kv_rst_agent_random_sequence_t::type_id::create("kv_rst_agent_rand_seq");
    hmac_write_seq = kv_write_agent_key_entry_sequence_t::type_id::create("hmac_write_seq");
    if(!this.randomize()) `uvm_error("KV WR RD", "Failed to randomize KV WRITE seq");
    mlkem_write_seq = kv_write_agent_key_entry_sequence_t::type_id::create("mlkem_write_seq");
    if(!this.randomize()) `uvm_error("KV WR RD", "Failed to randomize KV WRITE seq");
    ecc_write_seq = kv_write_agent_key_entry_sequence_t::type_id::create("ecc_write_seq");
    if(!this.randomize()) `uvm_error("KV WR RD", "Failed to randomize KV WRITE seq");
    doe_write_seq = kv_write_agent_key_entry_sequence_t::type_id::create("doe_write_seq");
    if(!this.randomize()) `uvm_error("KV WR RD", "Failed to randomize KV WRITE seq");
    aes_write_seq = kv_write_agent_key_entry_sequence_t::type_id::create("aes_write_seq");
    if(!this.randomize()) `uvm_error("KV WR RD", "Failed to randomize KV WRITE seq");
    kv_hmac_key_read_agent_rand_seq = kv_hmac_key_read_agent_random_sequence_t::type_id::create("kv_hmac_key_read_agent_rand_seq");
    kv_hmac_block_read_agent_rand_seq = kv_hmac_block_read_agent_random_sequence_t::type_id::create("kv_hmac_block_read_agent_rand_seq");
    kv_mldsa_key_read_agent_rand_seq = kv_mldsa_key_read_agent_random_sequence_t::type_id::create("kv_mldsa_key_read_agent_rand_seq");
    kv_ecc_privkey_read_agent_rand_seq = kv_ecc_privkey_read_agent_random_sequence_t::type_id::create("kv_ecc_privkey_read_agent_rand_seq");
    kv_ecc_seed_read_agent_rand_seq = kv_ecc_seed_read_agent_random_sequence_t::type_id::create("kv_ecc_seed_read_agent_rand_seq");
    kv_aes_key_read_agent_rand_seq = kv_aes_key_read_agent_random_sequence_t::type_id::create("kv_aes_key_read_agent_rand_seq");
    kv_mlkem_seed_read_agent_rand_seq = kv_mlkem_seed_read_agent_random_sequence_t::type_id::create("kv_mlkem_seed_read_agent_rand_seq");
    kv_mlkem_msg_read_agent_rand_seq = kv_mlkem_msg_read_agent_random_sequence_t::type_id::create("kv_mlkem_msg_read_agent_rand_seq");
    kv_dma_read_agent_rand_seq = kv_dma_read_agent_random_sequence_t::type_id::create("kv_dma_read_agent_rand_seq");


  endfunction

virtual task gen_rand_entries();
   std::randomize(hmac_write_entry) with {
       hmac_write_entry < KV_NUM_KEYS;
       hmac_write_entry != mlkem_write_entry;
       hmac_write_entry != ecc_write_entry;
       hmac_write_entry != doe_write_entry;
       hmac_write_entry != aes_write_entry;
   };

   std::randomize(mlkem_write_entry) with {
       mlkem_write_entry < KV_NUM_KEYS;
       mlkem_write_entry != hmac_write_entry;
       mlkem_write_entry != ecc_write_entry;
       mlkem_write_entry != doe_write_entry;
       mlkem_write_entry != aes_write_entry;
   };

   std::randomize(ecc_write_entry) with {
       ecc_write_entry < KV_NUM_KEYS;
       ecc_write_entry != hmac_write_entry;
       ecc_write_entry != mlkem_write_entry;
       ecc_write_entry != doe_write_entry;
       ecc_write_entry != aes_write_entry;
   };

   std::randomize(doe_write_entry) with {
       doe_write_entry < KV_NUM_KEYS;
       doe_write_entry != hmac_write_entry;
       doe_write_entry != mlkem_write_entry;
       doe_write_entry != ecc_write_entry;
       doe_write_entry != aes_write_entry;
   };

   std::randomize(aes_write_entry) with {
       aes_write_entry < KV_NUM_KEYS;
       aes_write_entry != hmac_write_entry;
       aes_write_entry != mlkem_write_entry;
       aes_write_entry != ecc_write_entry;
       aes_write_entry != doe_write_entry;
   };

endtask

virtual task queue_writes();

        repeat(20) begin
         gen_rand_entries();
        std::randomize(wr_clients);

      //   fork
         begin
            if (wr_clients[HMAC_WRITE]) begin
                `uvm_info("QUEUE_HMAC_WRITE", $sformatf("hmac write with entry = %h", hmac_write_entry), UVM_HIGH)
                uvm_config_db#(reg [KV_ENTRY_ADDR_W-1:0])::set(null, "uvm_test_top.environment.kv_hmac_write_agent.sequencer.hmac_write_seq", "local_write_entry",hmac_write_entry);
                hmac_write_seq.start(configuration.kv_hmac_write_agent_config.sequencer);
            end
         end
         begin
            if (wr_clients[MLKEM_WRITE]) begin
                `uvm_info("QUEUE_MLKEM_WRITE", $sformatf("mldsa write with entry = %h", mlkem_write_entry), UVM_HIGH)
                uvm_config_db#(reg [KV_ENTRY_ADDR_W-1:0])::set(null, "uvm_test_top.environment.kv_mlkem_write_agent.sequencer.mlkem_write_seq", "local_write_entry",mlkem_write_entry);
                mlkem_write_seq.start(configuration.kv_mlkem_write_agent_config.sequencer);
            end
         end
         begin
            if (wr_clients[ECC_WRITE]) begin
                `uvm_info("QUEUE_ECC_WRITE", $sformatf("ecc write with entry = %h", ecc_write_entry), UVM_HIGH)
                uvm_config_db#(reg [KV_ENTRY_ADDR_W-1:0])::set(null, "uvm_test_top.environment.kv_ecc_write_agent.sequencer.ecc_write_seq", "local_write_entry",ecc_write_entry);
                ecc_write_seq.start(configuration.kv_ecc_write_agent_config.sequencer);
            end
         end
         begin
            if (wr_clients[DOE_WRITE]) begin
                `uvm_info("QUEUE_DOE_WRITE", $sformatf("doe write with entry = %h", doe_write_entry), UVM_HIGH)
                uvm_config_db#(reg [KV_ENTRY_ADDR_W-1:0])::set(null, "uvm_test_top.environment.kv_doe_write_agent.sequencer.doe_write_seq", "local_write_entry",doe_write_entry);
                doe_write_seq.start(configuration.kv_doe_write_agent_config.sequencer);
            end
         end
         begin
            if (wr_clients[AES_WRITE]) begin
                `uvm_info("QUEUE_AES_WRITE", $sformatf("aes write with entry = %h", aes_write_entry), UVM_HIGH)
                uvm_config_db#(reg [KV_ENTRY_ADDR_W-1:0])::set(null, "uvm_test_top.environment.kv_aes_write_agent.sequencer.aes_write_seq", "local_write_entry",aes_write_entry);
                aes_write_seq.start(configuration.kv_aes_write_agent_config.sequencer);
            end
         end
      //   join
         configuration.kv_hmac_write_agent_config.wait_for_num_clocks(100);
         configuration.kv_mlkem_write_agent_config.wait_for_num_clocks(100);
         configuration.kv_ecc_write_agent_config.wait_for_num_clocks(100);
         configuration.kv_doe_write_agent_config.wait_for_num_clocks(100);
         configuration.kv_aes_write_agent_config.wait_for_num_clocks(100);
        end
    endtask

  virtual task body();

    if ( configuration.kv_rst_agent_config.sequencer != null )
       repeat (25) kv_rst_agent_rand_seq.start(configuration.kv_rst_agent_config.sequencer);
    if ( configuration.kv_hmac_write_agent_config.sequencer != null )
       repeat (25) hmac_write_seq.start(configuration.kv_hmac_write_agent_config.sequencer);
    if ( configuration.kv_mlkem_write_agent_config.sequencer != null )
       repeat (25) mlkem_write_seq.start(configuration.kv_mlkem_write_agent_config.sequencer);
    if ( configuration.kv_ecc_write_agent_config.sequencer != null )
       repeat (25) ecc_write_seq.start(configuration.kv_ecc_write_agent_config.sequencer);
    if ( configuration.kv_doe_write_agent_config.sequencer != null )
       repeat (25) doe_write_seq.start(configuration.kv_doe_write_agent_config.sequencer);
    if ( configuration.kv_aes_write_agent_config.sequencer != null )
       repeat (25) aes_write_seq.start(configuration.kv_aes_write_agent_config.sequencer);

    if ( configuration.kv_hmac_key_read_agent_config.sequencer != null )
       repeat (25) kv_hmac_key_read_agent_rand_seq.start(configuration.kv_hmac_key_read_agent_config.sequencer);
    if ( configuration.kv_hmac_block_read_agent_config.sequencer != null )
       repeat (25) kv_hmac_block_read_agent_rand_seq.start(configuration.kv_hmac_block_read_agent_config.sequencer);
    if ( configuration.kv_mldsa_key_read_agent_config.sequencer != null )
       repeat (25) kv_mldsa_key_read_agent_rand_seq.start(configuration.kv_mldsa_key_read_agent_config.sequencer);
    if ( configuration.kv_ecc_privkey_read_agent_config.sequencer != null )
       repeat (25) kv_ecc_privkey_read_agent_rand_seq.start(configuration.kv_ecc_privkey_read_agent_config.sequencer);
    if ( configuration.kv_ecc_seed_read_agent_config.sequencer != null )
       repeat (25) kv_ecc_seed_read_agent_rand_seq.start(configuration.kv_ecc_seed_read_agent_config.sequencer);
    if ( configuration.kv_aes_key_read_agent_config.sequencer != null )
       repeat (25) kv_aes_key_read_agent_rand_seq.start(configuration.kv_aes_key_read_agent_config.sequencer);
    if ( configuration.kv_mlkem_seed_read_agent_config.sequencer != null )
       repeat (25) kv_mlkem_seed_read_agent_rand_seq.start(configuration.kv_mlkem_seed_read_agent_config.sequencer);
    if ( configuration.kv_mlkem_msg_read_agent_config.sequencer != null )
       repeat (25) kv_mlkem_msg_read_agent_rand_seq.start(configuration.kv_mlkem_msg_read_agent_config.sequencer);
    if ( configuration.kv_dma_read_agent_config.sequencer != null )
       repeat (25) kv_dma_read_agent_rand_seq.start(configuration.kv_dma_read_agent_config.sequencer);


  endtask

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

