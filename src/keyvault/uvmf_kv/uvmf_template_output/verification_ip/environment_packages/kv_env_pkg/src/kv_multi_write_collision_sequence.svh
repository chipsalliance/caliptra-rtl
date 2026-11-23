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
// An untouched witness entry (pre_write_entry) is populated and checked
// readable at the pins before each collision, then checked at the pins
// afterwards for the cleared response (error, zero data, last_dword 0).
// Because a denied read is masked to zero, a probe word is then written to
// restore read permission and word 0 is re-read to prove the data was erased.
// The three-writer phase also checks that all three write_en are high
// on the same clock edge.
// A subsequent single-client write must succeed (recovery).
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
    localparam logic [KV_DATA_W-1:0] WITNESS_DATA = 32'h39c6_5a87;
    localparam logic [KV_DATA_W-1:0] PROBE_DATA   = 32'hc639_a578;
    localparam int PROBE_WORD = 1;
    // Clocks to wait after a collision before the pin-level witness read, so
    // the check does not depend on the scoreboard's collision tolerance window.
    localparam int COLLISION_SETTLE_CLKS = 20;
    localparam int THREE_WAY_WATCH_CLKS = 32;

    // Single HMAC-client write of one word, readable by the hmac_key_read client.
    task write_word(int entry, int offset, logic [KV_DATA_W-1:0] data);
        kv_write_transaction tx;
        tx = kv_write_transaction#()::type_id::create("witness_write_tx");
        start_item(tx, -1, configuration.kv_hmac_write_agent_config.sequencer);
        tx.write_en = 1'b1;
        tx.write_entry = KV_ENTRY_ADDR_W'(entry);
        tx.write_offset = KV_ENTRY_SIZE_W'(offset);
        tx.write_data = data;
        tx.write_dest_valid = HMAC_KEY_READ_DEST_VALID;
        finish_item(tx);
        configuration.kv_hmac_write_agent_config.wait_for_num_clocks(5);
    endtask

    // Write WITNESS_DATA to word 0 of an entry and confirm it at the pins.
    task write_witness(int entry);
        write_word(entry, 0, WITNESS_DATA);
        checked_read(configuration.kv_hmac_key_read_agent_config, entry, 0, WITNESS_DATA, 0, 0);
    endtask

    // A collision clears dest_valid, last_dword and data of every entry.
    // The denied read only proves dest_valid was cleared (read data is masked
    // without permission), so restore permission through PROBE_WORD and
    // check that word 0 itself was erased.
    task check_witness_cleared(int entry);
        configuration.kv_hmac_write_agent_config.wait_for_num_clocks(COLLISION_SETTLE_CLKS);
        checked_read(configuration.kv_hmac_key_read_agent_config, entry, 0, '0, 1, 0);
        write_word(entry, PROBE_WORD, PROBE_DATA);
        checked_read(configuration.kv_hmac_key_read_agent_config, entry, 0, '0, 0, PROBE_WORD);
        checked_read(configuration.kv_hmac_key_read_agent_config, entry, PROBE_WORD,
                     PROBE_DATA, 0, PROBE_WORD);
    endtask

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
        bit three_way_seen;

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
        write_witness(pre_write_entry);

        // ── Phase 3: Multi-write collision — fork 2 agents writing simultaneously ──
        // Neither colliding write targets pre_write_entry, so that entry is an
        // untouched witness: it only reads back as cleared if the collision
        // wipes the whole vault rather than just the two written entries.
        `uvm_info("KV_MULTI_WR", "Driving simultaneous HMAC + ECC writes to different entries", UVM_LOW)
        uvm_config_db#(reg [KV_ENTRY_ADDR_W-1:0])::set(null,
            "uvm_test_top.environment.kv_hmac_write_agent.sequencer.hmac_write_seq",
            "local_write_entry", collision_entry);
        uvm_config_db#(reg [KV_ENTRY_ADDR_W-1:0])::set(null,
            "uvm_test_top.environment.kv_ecc_write_agent.sequencer.ecc_write_seq",
            "local_write_entry", recovery_entry);
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
        // The scoreboard skips read responses inside its collision tolerance
        // window, so also check the untouched witness directly at the pins.
        check_witness_cleared(pre_write_entry);

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
        // Re-populate the witness (cleared by Phase 3); no Phase 6 writer targets it.
        write_witness(pre_write_entry);
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
        three_way_seen = 0;
        fork
            hmac_write_seq.start(configuration.kv_hmac_write_agent_config.sequencer);
            ecc_write_seq.start(configuration.kv_ecc_write_agent_config.sequencer);
            doe_write_seq.start(configuration.kv_doe_write_agent_config.sequencer);
            begin
                // Bounded watcher: the three requests must share one clock edge,
                // otherwise this phase only proves a two-writer collision.
                kv_write_t hmac_req, ecc_req, doe_req;
                repeat (THREE_WAY_WATCH_CLKS) begin
                    @(posedge configuration.kv_hmac_write_agent_config.monitor_bfm.clk_i);
                    hmac_req = kv_write_t'(configuration.kv_hmac_write_agent_config.monitor_bfm.kv_write_i);
                    ecc_req = kv_write_t'(configuration.kv_ecc_write_agent_config.monitor_bfm.kv_write_i);
                    doe_req = kv_write_t'(configuration.kv_doe_write_agent_config.monitor_bfm.kv_write_i);
                    if (hmac_req.write_en === 1'b1 && ecc_req.write_en === 1'b1 &&
                        doe_req.write_en === 1'b1)
                        three_way_seen = 1;
                end
            end
        join
        if (!three_way_seen)
            `uvm_error("KV_MULTI_WR", $sformatf(
                "HMAC, ECC and DOE write_en were never high on the same edge within %0d clocks",
                THREE_WAY_WATCH_CLKS))

        check_witness_cleared(pre_write_entry);

        `uvm_info("KV_MULTI_WR", "Multi-write collision sequence complete", UVM_LOW)
    endtask

endclass
