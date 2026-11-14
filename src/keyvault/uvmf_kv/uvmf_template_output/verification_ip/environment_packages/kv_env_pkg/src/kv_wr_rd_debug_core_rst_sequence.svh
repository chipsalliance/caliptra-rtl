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
// DESCRIPTION: Performs KV writes while randomly issuing debug unlock
// via input pin or CLEAR_SECRETS reg. A core reset is issued after the
// writes and then all entries/dwords are read
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//

class kv_wr_rd_debug_core_rst_sequence #(
    type CONFIG_T
) extends kv_env_sequence_base #(.CONFIG_T(CONFIG_T));

    `uvm_object_param_utils(kv_wr_rd_debug_core_rst_sequence #(CONFIG_T));

    typedef kv_rst_poweron_sequence kv_rst_agent_poweron_sequence_t;
    kv_rst_agent_poweron_sequence_t kv_rst_agent_poweron_seq;
    kv_rst_agent_poweron_sequence_t kv_rst_agent_poweron_seq_2;

    typedef kv_rst_core_rst_sequence kv_rst_core_rst_sequence_t;
    kv_rst_core_rst_sequence_t kv_rst_agent_core_rst_seq;

    typedef kv_rst_debug_sequence kv_rst_agent_debug_sequence_t;
    kv_rst_agent_debug_sequence_t kv_rst_agent_debug_seq;

    typedef kv_write_key_entry_sequence kv_write_agent_key_entry_sequence_t;
    kv_write_agent_key_entry_sequence_t hmac_write_seq;
    kv_write_agent_key_entry_sequence_t mlkem_write_seq;
    kv_write_agent_key_entry_sequence_t ecc_write_seq;
    kv_write_agent_key_entry_sequence_t doe_write_seq;

    typedef kv_read_key_entry_sequence kv_read_agent_key_entry_sequence_t;
    kv_read_agent_key_entry_sequence_t hmac_key_read_seq;
    kv_read_agent_key_entry_sequence_t hmac_block_read_seq;
    kv_read_agent_key_entry_sequence_t mldsa_key_read_seq;
    kv_read_agent_key_entry_sequence_t ecc_privkey_read_seq;
    kv_read_agent_key_entry_sequence_t ecc_seed_read_seq;
    kv_read_agent_key_entry_sequence_t aes_key_read_seq;
    kv_read_agent_key_entry_sequence_t mlkem_seed_read_seq;
    kv_read_agent_key_entry_sequence_t mlkem_msg_read_seq;

    rand reg [KV_ENTRY_ADDR_W-1:0] hmac_write_entry, mlkem_write_entry, ecc_write_entry, doe_write_entry;    
    rand int unsigned wait_cycles_from_seq;
    rand bit debug_type;
    rand reg [1:0] clear_secrets_data;

    typedef enum {SECURITY_STATE, CLEAR_SECRETS} debug_inputs;

    function new(string name = "");
        super.new(name);
        kv_rst_agent_poweron_seq = kv_rst_agent_poweron_sequence_t::type_id::create("kv_rst_agent_poweron_seq");
        if(!this.randomize()) `uvm_error("KV WR RD", "Failed to randomize KV RST poweron seq");
        kv_rst_agent_poweron_seq_2 = kv_rst_agent_poweron_sequence_t::type_id::create("kv_rst_agent_poweron_seq_2");
        if(!this.randomize()) `uvm_error("KV WR RD", "Failed to randomize KV RST poweron seq");
        kv_rst_agent_core_rst_seq = kv_rst_core_rst_sequence_t::type_id::create("kv_rst_agent_core_rst_seq");
        if(!this.randomize()) `uvm_error("KV_WR_RD_LOCK", "Failed to randomize KV_CORE_RST seq");

        kv_rst_agent_debug_seq = kv_rst_agent_debug_sequence_t::type_id::create("kv_rst_agent_debug_seq");
        if(!this.randomize()) `uvm_error("KV WR RD", "Failed to randomize KV RST debug seq");
        
        hmac_write_seq = kv_write_agent_key_entry_sequence_t::type_id::create("hmac_write_seq");
        if(!this.randomize()) `uvm_error("KV WR RD", "Failed to randomize KV WRITE seq");
        mlkem_write_seq = kv_write_agent_key_entry_sequence_t::type_id::create("mlkem_write_seq");
        if(!this.randomize()) `uvm_error("KV WR RD", "Failed to randomize KV WRITE seq");
        ecc_write_seq = kv_write_agent_key_entry_sequence_t::type_id::create("ecc_write_seq");
        if(!this.randomize()) `uvm_error("KV WR RD", "Failed to randomize KV WRITE seq");
        doe_write_seq = kv_write_agent_key_entry_sequence_t::type_id::create("doe_write_seq");
        if(!this.randomize()) `uvm_error("KV WR RD", "Failed to randomize KV WRITE seq");
        
        hmac_key_read_seq = kv_read_agent_key_entry_sequence_t::type_id::create("hmac_key_read_seq");
        if(!this.randomize()) `uvm_error("KV WR RD", "Failed to randomize KV READ seq");
        hmac_block_read_seq = kv_read_agent_key_entry_sequence_t::type_id::create("hmac_block_read_seq");
        if(!this.randomize()) `uvm_error("KV WR RD", "Failed to randomize KV READ seq");
        mldsa_key_read_seq = kv_read_agent_key_entry_sequence_t::type_id::create("mldsa_key_read_seq");
        if(!this.randomize()) `uvm_error("KV WR RD", "Failed to randomize KV READ seq");
        ecc_privkey_read_seq = kv_read_agent_key_entry_sequence_t::type_id::create("ecc_privkey_read_seq");
        if(!this.randomize()) `uvm_error("KV WR RD", "Failed to randomize KV READ seq");
        ecc_seed_read_seq = kv_read_agent_key_entry_sequence_t::type_id::create("ecc_seed_read_seq");
        if(!this.randomize()) `uvm_error("KV WR RD", "Failed to randomize KV READ seq");
        aes_key_read_seq = kv_read_agent_key_entry_sequence_t::type_id::create("aes_key_read_seq");
        if(!this.randomize()) `uvm_error("KV WR RD", "Failed to randomize KV READ seq");  
        mlkem_seed_read_seq = kv_read_agent_key_entry_sequence_t::type_id::create("mlkem_seed_read_seq");
        if(!this.randomize()) `uvm_error("KV WR RD", "Failed to randomize KV READ seq");
        mlkem_msg_read_seq = kv_read_agent_key_entry_sequence_t::type_id::create("mlkem_msg_read_seq");
        if(!this.randomize()) `uvm_error("KV WR RD", "Failed to randomize KV READ seq");      
        //kv_rst_agent_poweron_seq_2 = kv_rst_agent_poweron_sequence_t::type_id::create("kv_rst_agent_poweron_seq_2");
        
    endfunction

    task check_reset_debug_overlap();
        uvm_status_e status;
        uvm_reg_data_t actual, metadata;
        localparam int ENTRY = KV_NUM_KEYS - 1;
        localparam int WORD = KV_NUM_DWORDS - 1;
        localparam logic [KV_DATA_W-1:0] SEED = 32'hc35aa53c;
        // Selector 0 pattern from src/libs/rtl/caliptra_macros.svh.
        localparam logic [KV_DATA_W-1:0] DEBUG_FILL = 32'haaaa_aaaa;

        `uvm_info("KV_CORE_DEBUG_OVERLAP", "Checking core-only retention versus debug/scan-transition flush", UVM_MEDIUM)
        kv_rst_agent_poweron_seq_2.start(configuration.kv_rst_agent_config.sequencer);
        configuration.kv_rst_agent_config.wait_for_num_clocks(5);
        reg_model.kv_reg_rm.KEY_ENTRY[ENTRY][WORD].write(
            status, SEED, UVM_FRONTDOOR, reg_model.kv_hmac_write_map, this);
        if (status != UVM_IS_OK)
            `uvm_fatal("KV_CORE_DEBUG_OVERLAP", "Seed write failed")
        checked_read(configuration.kv_hmac_key_read_agent_config, ENTRY, WORD, SEED, 0, WORD);
        metadata = (uvm_reg_data_t'((1 << KV_NUM_READ) - 1) <<
                    reg_model.kv_reg_rm.KEY_CTRL[ENTRY].dest_valid.get_lsb_pos()) |
                   (uvm_reg_data_t'(WORD) <<
                    reg_model.kv_reg_rm.KEY_CTRL[ENTRY].last_dword.get_lsb_pos());

        // First prove normal core-only reset retains nonzero key data. This
        // call uses the unchanged default behavior, with no transition input.
        kv_rst_agent_core_rst_seq.start(configuration.kv_rst_agent_config.sequencer);
        checked_read(configuration.kv_hmac_key_read_agent_config, ENTRY, WORD, SEED, 0, WORD);
        reg_model.kv_reg_rm.KEY_CTRL[ENTRY].write(
            status, 'h3, UVM_FRONTDOOR, reg_model.kv_AHB_map, this);
        if (status != UVM_IS_OK)
            `uvm_fatal("KV_CORE_DEBUG_OVERLAP", "Lock write failed")
        reg_model.kv_reg_rm.KEY_CTRL[ENTRY].read(
            status, actual, UVM_FRONTDOOR, reg_model.kv_AHB_map, this);
        if (status != UVM_IS_OK || actual !== (metadata | 'h3))
            `uvm_fatal("KV_CORE_DEBUG_OVERLAP", "Seed metadata/locks did not reach hardware")

        // debug_mode drives debugUnlock_or_scan_mode_switch. Holding it with
        // core reset must FLUSH data, not preserve it as core reset alone does.
        kv_rst_agent_core_rst_seq.overlap_debug_transition = 1'b1;
        kv_rst_agent_core_rst_seq.start(configuration.kv_rst_agent_config.sequencer);
        kv_rst_agent_core_rst_seq.overlap_debug_transition = 1'b0;
        configuration.kv_rst_agent_config.wait_for_num_clocks(5);
        @(negedge configuration.kv_rst_agent_config.monitor_bfm.clk_i);
        if (configuration.kv_rst_agent_config.monitor_bfm.cptra_pwrgood_i !== 1'b1 ||
            configuration.kv_rst_agent_config.monitor_bfm.rst_b_i !== 1'b1 ||
            configuration.kv_rst_agent_config.monitor_bfm.core_only_rst_b_i !== 1'b1 ||
            configuration.kv_rst_agent_config.monitor_bfm.fw_update_rst_window_i !== 1'b0 ||
            configuration.kv_rst_agent_config.monitor_bfm.debug_locked_i !== 1'b0 ||
            configuration.kv_rst_agent_config.monitor_bfm.cptra_in_debug_scan_mode_i !== 1'b0)
            `uvm_fatal("KV_CORE_DEBUG_OVERLAP", "Reset/debug pins did not return to normal")
        reg_model.kv_reg_rm.KEY_CTRL[ENTRY].read(
            status, actual, UVM_FRONTDOOR, reg_model.kv_AHB_map, this);
        if (status != UVM_IS_OK || actual !== metadata)
            `uvm_fatal("KV_CORE_DEBUG_OVERLAP", $sformatf(
                "Core reset must clear locks and retain metadata: actual=%h expected=%h", actual, metadata))
        reg_model.kv_reg_rm.CLEAR_SECRETS.read(
            status, actual, UVM_FRONTDOOR, reg_model.kv_AHB_map, this);
        if (status != UVM_IS_OK || actual !== '0)
            `uvm_fatal("KV_CORE_DEBUG_OVERLAP", "CLEAR_SECRETS changed from selector 0")
        for (int offset = 0; offset < KV_NUM_DWORDS; offset++)
            checked_read(configuration.kv_hmac_key_read_agent_config,
                         ENTRY, offset, DEBUG_FILL, 0, WORD);

        reg_model.kv_reg_rm.KEY_ENTRY[ENTRY][0].write(
            status, ~SEED, UVM_FRONTDOOR, reg_model.kv_hmac_write_map, this);
        if (status != UVM_IS_OK)
            `uvm_fatal("KV_CORE_DEBUG_OVERLAP", "Recovery write failed")
        checked_read(configuration.kv_hmac_key_read_agent_config, ENTRY, 0, ~SEED, 0, 0);
        checked_read(configuration.kv_hmac_key_read_agent_config,
                     ENTRY, WORD, DEBUG_FILL, 0, 0);
    endtask

    virtual task body();
        uvm_status_e sts;
        //uvm_reg_data_t rd_data;
        int write_entry = 0; 
        int write_offset = 0;
        int read_entry = 0; 
        int read_offset = 0;

        reg [31:0] wr_data, rd_data;
        reg_model = configuration.kv_rm;


        //Issue and wait for reset
        if(configuration.kv_rst_agent_config.sequencer != null)
            kv_rst_agent_poweron_seq.start(configuration.kv_rst_agent_config.sequencer);
        else
            `uvm_error("KV WR RD", "kv_rst_agent_config.sequencer is null!")
        
        
                //Unlock debug mode or clear secrets randomly
                
                    std::randomize(debug_type); //0 - security state, 1 - clear secrets
                    
                    std::randomize(wait_cycles_from_seq) with {
                        wait_cycles_from_seq >= 5;
                        wait_cycles_from_seq <= 50;
                    };

                    std::randomize(clear_secrets_data); //wren, debug_value0/1

                    //Wait for random delay before starting debug txn
                    configuration.kv_rst_agent_config.wait_for_num_clocks(wait_cycles_from_seq);

                    case(debug_type)
                        SECURITY_STATE: begin
                            //start debug seq on rst agent
                            kv_rst_agent_debug_seq.start(configuration.kv_rst_agent_config.sequencer);
                        end
                        CLEAR_SECRETS: begin
                            reg_model.kv_reg_rm.CLEAR_SECRETS.write(sts, clear_secrets_data, UVM_FRONTDOOR, reg_model.kv_AHB_map, this);
                            assert(sts == UVM_IS_OK) else `uvm_error("AHB_CLEAR_SECRETS_SET", "Failed when writing to CLEAR_SECRETS reg!")
                        end
                    endcase
                
                //Write to all entries
                for (write_entry = 0; write_entry < KV_NUM_KEYS; write_entry++) begin
                    for(write_offset = 0; write_offset < KV_NUM_DWORDS; write_offset++) begin
                        uvm_config_db#(reg [KV_ENTRY_ADDR_W-1:0])::set(null, "uvm_test_top.environment.kv_mlkem_write_agent.sequencer.mlkem_write_seq", "local_write_entry",write_entry);
                        uvm_config_db#(reg [KV_ENTRY_SIZE_W-1:0])::set(null, "uvm_test_top.environment.kv_mlkem_write_agent.sequencer.mlkem_write_seq", "local_write_offset",write_offset);
                        mlkem_write_seq.start(configuration.kv_mlkem_write_agent_config.sequencer);
                    end
                end
            
            //Issue core reset before reading
            kv_rst_agent_core_rst_seq.start(configuration.kv_rst_agent_config.sequencer);

            //Read all entries
            for (read_entry = 0; read_entry < KV_NUM_KEYS; read_entry++) begin
                for (read_offset = 0; read_offset < KV_NUM_DWORDS; read_offset++) begin
                    uvm_config_db#(reg [KV_ENTRY_ADDR_W-1:0])::set(null, "uvm_test_top.environment.kv_mldsa_key_read_agent.sequencer.mldsa_key_read_seq", "local_read_entry",read_entry);
                    uvm_config_db#(reg [KV_ENTRY_SIZE_W-1:0])::set(null, "uvm_test_top.environment.kv_mldsa_key_read_agent.sequencer.mldsa_key_read_seq", "local_read_offset",read_offset);
                    mldsa_key_read_seq.start(configuration.kv_mldsa_key_read_agent_config.sequencer);
                end
            end
            
        
        check_reset_debug_overlap();
    endtask
endclass