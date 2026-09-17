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

//----------------------------------------------------------------------
// DESCRIPTION: Exercises KV multi-write collision (kv_multi_write_err).
//
// Two or more crypto write agents drive write_en simultaneously.
// RTL detects this via kv_write_cnt > 1 and clears ALL entries.
// After the collision, we verify that reads return error and that
// a subsequent single-client write succeeds (recovery).
//----------------------------------------------------------------------

class kv_multi_write_collision_sequence #(
    type CONFIG_T
) extends kv_env_sequence_base #(.CONFIG_T(CONFIG_T));

    `uvm_object_param_utils(kv_multi_write_collision_sequence #(CONFIG_T));

    typedef kv_rst_poweron_sequence kv_rst_agent_poweron_sequence_t;
    kv_rst_agent_poweron_sequence_t kv_rst_agent_poweron_seq;

    typedef kv_write_key_entry_sequence kv_write_agent_key_entry_sequence_t;
    kv_write_agent_key_entry_sequence_t hmac_write_seq;
    kv_write_agent_key_entry_sequence_t ecc_write_seq;
    kv_write_agent_key_entry_sequence_t doe_write_seq;

    typedef kv_read_key_entry_sequence kv_read_agent_key_entry_sequence_t;
    kv_read_agent_key_entry_sequence_t hmac_key_read_seq;
    kv_read_agent_key_entry_sequence_t ecc_privkey_read_seq;

    rand reg [KV_ENTRY_ADDR_W-1:0] collision_entry;
    rand reg [KV_ENTRY_ADDR_W-1:0] pre_write_entry;
    rand reg [KV_ENTRY_ADDR_W-1:0] recovery_entry;
    rand reg [KV_ENTRY_SIZE_W-1:0] recovery_offset;

    //dest_valid bit 0 corresponds to the hmac_key_read client, which is the
    //client used to read back the recovery entry
    localparam reg [KV_NUM_READ-1:0] HMAC_KEY_READ_DEST_VALID = 'h1;

    constraint c_entries {
        collision_entry < KV_NUM_KEYS;
        pre_write_entry < KV_NUM_KEYS;
        recovery_entry  < KV_NUM_KEYS;
        recovery_offset < KV_NUM_DWORDS;
        pre_write_entry != collision_entry;
        recovery_entry  != collision_entry;
        recovery_entry  != pre_write_entry;
    }

    function new(string name = "");
        super.new(name);
        kv_rst_agent_poweron_seq = kv_rst_agent_poweron_sequence_t::type_id::create("kv_rst_agent_poweron_seq");
        hmac_write_seq = kv_write_agent_key_entry_sequence_t::type_id::create("hmac_write_seq");
        ecc_write_seq  = kv_write_agent_key_entry_sequence_t::type_id::create("ecc_write_seq");
        doe_write_seq  = kv_write_agent_key_entry_sequence_t::type_id::create("doe_write_seq");
        hmac_key_read_seq   = kv_read_agent_key_entry_sequence_t::type_id::create("hmac_key_read_seq");
        ecc_privkey_read_seq = kv_read_agent_key_entry_sequence_t::type_id::create("ecc_privkey_read_seq");
    endfunction

    virtual task body();
        int entry;
        int offset;

        if(!this.randomize()) `uvm_error("KV_MULTI_WR", "Failed to randomize collision sequence");

        `uvm_info("KV_MULTI_WR", $sformatf("collision_entry=%0d pre_write_entry=%0d recovery_entry=%0d recovery_offset=%0d",
                  collision_entry, pre_write_entry, recovery_entry, recovery_offset), UVM_LOW)

        // ── Phase 1: Power-on reset ──
        if (configuration.kv_rst_agent_config.sequencer != null)
            kv_rst_agent_poweron_seq.start(configuration.kv_rst_agent_config.sequencer);
        else
            `uvm_error("KV_MULTI_WR", "kv_rst_agent_config.sequencer is null!")

        // ── Phase 2: Pre-populate an entry with valid data (single writer) ──
        `uvm_info("KV_MULTI_WR", "Pre-populating entry with HMAC write (single client)", UVM_LOW)
        uvm_config_db#(reg [KV_ENTRY_ADDR_W-1:0])::set(null,
            "uvm_test_top.environment.kv_hmac_write_agent.sequencer.hmac_write_seq",
            "local_write_entry", pre_write_entry);
        hmac_write_seq.start(configuration.kv_hmac_write_agent_config.sequencer);

        // Small gap to let predictor settle
        configuration.kv_hmac_write_agent_config.wait_for_num_clocks(5);

        // ── Phase 3: Multi-write collision — fork 2 agents writing simultaneously ──
        `uvm_info("KV_MULTI_WR", "Driving simultaneous writes from HMAC + ECC (collision)", UVM_LOW)
        uvm_config_db#(reg [KV_ENTRY_ADDR_W-1:0])::set(null,
            "uvm_test_top.environment.kv_hmac_write_agent.sequencer.hmac_write_seq",
            "local_write_entry", collision_entry);
        uvm_config_db#(reg [KV_ENTRY_ADDR_W-1:0])::set(null,
            "uvm_test_top.environment.kv_ecc_write_agent.sequencer.ecc_write_seq",
            "local_write_entry", collision_entry);
        fork
            hmac_write_seq.start(configuration.kv_hmac_write_agent_config.sequencer);
            ecc_write_seq.start(configuration.kv_ecc_write_agent_config.sequencer);
        join

        // Wait for collision clear to propagate (registered — 1 cycle)
        configuration.kv_hmac_write_agent_config.wait_for_num_clocks(5);

        // ── Phase 4: Verify reads return error (all entries destroyed) ──
        `uvm_info("KV_MULTI_WR", "Reading pre-populated entry — should return resp_err after collision", UVM_LOW)
        uvm_config_db#(reg [KV_ENTRY_ADDR_W-1:0])::set(null,
            "uvm_test_top.environment.kv_hmac_key_read_agent.sequencer.hmac_key_read_seq",
            "local_read_entry", pre_write_entry);
        hmac_key_read_seq.start(configuration.kv_hmac_key_read_agent_config.sequencer);

        configuration.kv_hmac_write_agent_config.wait_for_num_clocks(5);

        // ── Phase 5: Recovery — write a new entry with single client, read back ──
        `uvm_info("KV_MULTI_WR", "Recovery: single HMAC write to verify KV accepts writes after collision", UVM_LOW)
        uvm_config_db#(reg [KV_ENTRY_ADDR_W-1:0])::set(null,
            "uvm_test_top.environment.kv_hmac_write_agent.sequencer.hmac_write_seq",
            "local_write_entry", recovery_entry);
        uvm_config_db#(reg [KV_ENTRY_SIZE_W-1:0])::set(null,
            "uvm_test_top.environment.kv_hmac_write_agent.sequencer.hmac_write_seq",
            "local_write_offset", recovery_offset);
        //Allow the hmac_key_read client to read the recovered entry
        uvm_config_db#(reg [KV_NUM_READ-1:0])::set(null,
            "uvm_test_top.environment.kv_hmac_write_agent.sequencer.hmac_write_seq",
            "local_write_dest_valid", HMAC_KEY_READ_DEST_VALID);
        hmac_write_seq.start(configuration.kv_hmac_write_agent_config.sequencer);

        configuration.kv_hmac_write_agent_config.wait_for_num_clocks(5);

        // Read back the recovered entry — scoreboard checks data and resp_err
        `uvm_info("KV_MULTI_WR", "Recovery: reading back recovered entry to confirm KV is usable again", UVM_LOW)
        uvm_config_db#(reg [KV_ENTRY_ADDR_W-1:0])::set(null,
            "uvm_test_top.environment.kv_hmac_key_read_agent.sequencer.hmac_key_read_seq",
            "local_read_entry", recovery_entry);
        uvm_config_db#(reg [KV_ENTRY_SIZE_W-1:0])::set(null,
            "uvm_test_top.environment.kv_hmac_key_read_agent.sequencer.hmac_key_read_seq",
            "local_read_offset", recovery_offset);
        hmac_key_read_seq.start(configuration.kv_hmac_key_read_agent_config.sequencer);

        configuration.kv_hmac_write_agent_config.wait_for_num_clocks(5);

        // Release the forced offset/dest_valid so the remaining writes randomize again
        uvm_config_db#(reg [KV_ENTRY_SIZE_W-1:0])::set(null,
            "uvm_test_top.environment.kv_hmac_write_agent.sequencer.hmac_write_seq",
            "local_write_offset", 'x);
        uvm_config_db#(reg [KV_NUM_READ-1:0])::set(null,
            "uvm_test_top.environment.kv_hmac_write_agent.sequencer.hmac_write_seq",
            "local_write_dest_valid", 'x);

        // ── Phase 6: Three-way collision ──
        `uvm_info("KV_MULTI_WR", "Driving 3-way collision: HMAC + ECC + DOE", UVM_LOW)
        uvm_config_db#(reg [KV_ENTRY_ADDR_W-1:0])::set(null,
            "uvm_test_top.environment.kv_hmac_write_agent.sequencer.hmac_write_seq",
            "local_write_entry", collision_entry);
        uvm_config_db#(reg [KV_ENTRY_ADDR_W-1:0])::set(null,
            "uvm_test_top.environment.kv_ecc_write_agent.sequencer.ecc_write_seq",
            "local_write_entry", collision_entry);
        uvm_config_db#(reg [KV_ENTRY_ADDR_W-1:0])::set(null,
            "uvm_test_top.environment.kv_doe_write_agent.sequencer.doe_write_seq",
            "local_write_entry", collision_entry);
        fork
            hmac_write_seq.start(configuration.kv_hmac_write_agent_config.sequencer);
            ecc_write_seq.start(configuration.kv_ecc_write_agent_config.sequencer);
            doe_write_seq.start(configuration.kv_doe_write_agent_config.sequencer);
        join

        configuration.kv_hmac_write_agent_config.wait_for_num_clocks(10);

        `uvm_info("KV_MULTI_WR", "Multi-write collision sequence complete", UVM_LOW)
    endtask

endclass
