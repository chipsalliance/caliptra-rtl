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
//----------------------------------------------------------------------
//
// DESCRIPTION: Debug-mode transition flush with mixed lock states.
// Seeds every entry with deterministic data readable by the HMAC key
// reader, creates four lock groups, then triggers a debug-mode
// transition. The transition flush writes the debug value into every
// entry regardless of lock state and leaves dest_valid unchanged.
// Entries without lock_use are pin-checked for the debug value;
// lock_use entries are pin-checked for a masked error with zero data.
// A core-only reset then clears the locks while retaining storage, and
// all 24 entries are pin-checked for the debug value, so a flush that
// skipped locked entries leaves visible seed data.
//
// Lock groups:
//   Entries  0-5 : lock_wr only
//   Entries  6-11: lock_use only
//   Entries 12-17: lock_wr + lock_use
//   Entries 18-23: unlocked
//----------------------------------------------------------------------

class kv_debug_flush_mixed_locks_sequence #(
    type CONFIG_T
) extends kv_env_sequence_base #(.CONFIG_T(CONFIG_T));

    `uvm_object_param_utils(kv_debug_flush_mixed_locks_sequence #(CONFIG_T));

    typedef kv_rst_poweron_sequence kv_rst_agent_poweron_sequence_t;
    kv_rst_agent_poweron_sequence_t kv_rst_agent_poweron_seq;

    typedef kv_rst_debug_sequence kv_rst_agent_debug_sequence_t;
    kv_rst_agent_debug_sequence_t kv_rst_agent_debug_seq;

    typedef kv_rst_scan_on_sequence kv_rst_agent_scan_on_sequence_t;
    kv_rst_agent_scan_on_sequence_t kv_rst_agent_scan_on_seq;

    typedef kv_rst_core_rst_sequence kv_rst_agent_core_rst_sequence_t;
    kv_rst_agent_core_rst_sequence_t kv_rst_agent_core_rst_seq;

    localparam int LAST_WORD = KV_NUM_DWORDS - 1;
    // Selector-0 debug pattern (CLP_DEBUG_MODE_KV_0, caliptra_macros.svh).
    localparam logic [KV_DATA_W-1:0] DEBUG_FILL = 32'haaaa_aaaa;

    function new(string name = "");
        super.new(name);
        kv_rst_agent_poweron_seq = kv_rst_agent_poweron_sequence_t::type_id::create("kv_rst_agent_poweron_seq");
        kv_rst_agent_debug_seq = kv_rst_agent_debug_sequence_t::type_id::create("kv_rst_agent_debug_seq");
        kv_rst_agent_scan_on_seq = kv_rst_agent_scan_on_sequence_t::type_id::create("kv_rst_agent_scan_on_seq");
        kv_rst_agent_core_rst_seq = kv_rst_agent_core_rst_sequence_t::type_id::create("kv_rst_agent_core_rst_seq");
    endfunction

    function logic [KV_DATA_W-1:0] seed_data(int entry, int offset);
        return 32'h3c69_0000 | (entry << 8) | offset;
    endfunction

    function bit lock_use_group(int entry);
        return entry >= 6 && entry < 18;
    endfunction

    virtual task body();
        uvm_status_e sts;
        int write_entry, write_offset, read_entry, read_offset;
        reg [2:0] lock_data;
        reg_model = configuration.kv_rm;

        `uvm_info("DEBUG_FLUSH_MIXED", "=== Phase 1: Power-on reset ===", UVM_MEDIUM)
        if(configuration.kv_rst_agent_config.sequencer != null)
            kv_rst_agent_poweron_seq.start(configuration.kv_rst_agent_config.sequencer);
        else
            `uvm_error("DEBUG_FLUSH_MIXED", "kv_rst_agent_config.sequencer is null!")

        `uvm_info("DEBUG_FLUSH_MIXED", "=== Phase 2: Populate all 24 entries via DOE write agent ===", UVM_MEDIUM)
        // Deterministic data; dest_valid is random but always includes the
        // HMAC key reader so every entry can be observed at its pins.
        for (write_entry = 0; write_entry < KV_NUM_KEYS; write_entry++) begin
            logic [KV_NUM_READ-1:0] dest_valid;
            dest_valid = KV_NUM_READ'($urandom) | (KV_NUM_READ'(1) << KV_DEST_IDX_HMAC_KEY);
            for (write_offset = 0; write_offset < KV_NUM_DWORDS; write_offset++) begin
                kv_write_transaction seed_write;
                seed_write = kv_write_transaction#()::type_id::create("mixed_seed_write");
                start_item(seed_write, -1, configuration.kv_doe_write_agent_config.sequencer);
                seed_write.write_en = 1'b1;
                seed_write.write_entry = KV_ENTRY_ADDR_W'(write_entry);
                seed_write.write_offset = KV_ENTRY_SIZE_W'(write_offset);
                seed_write.write_data = seed_data(write_entry, write_offset);
                seed_write.write_dest_valid = dest_valid;
                finish_item(seed_write);
            end
            // Positive control: the seed is stored and readable before locks.
            checked_read(configuration.kv_hmac_key_read_agent_config,
                         write_entry, 0, seed_data(write_entry, 0), 0, LAST_WORD);
        end

        `uvm_info("DEBUG_FLUSH_MIXED", "=== Phase 3: Set deliberate mixed lock states ===", UVM_MEDIUM)
        for (write_entry = 0; write_entry < KV_NUM_KEYS; write_entry++) begin
            if (write_entry < 6)
                lock_data = 3'b001; // lock_wr only
            else if (write_entry < 12)
                lock_data = 3'b010; // lock_use only
            else if (write_entry < 18)
                lock_data = 3'b011; // lock_wr + lock_use
            else
                lock_data = 3'b000; // unlocked

            if (lock_data != 0) begin
                reg_model.kv_reg_rm.KEY_CTRL[write_entry].write(sts, lock_data, UVM_FRONTDOOR, reg_model.kv_AHB_map, this);
                assert(sts == UVM_IS_OK) else `uvm_error("DEBUG_FLUSH_MIXED", $sformatf("Failed writing KEY_CTRL[%0d]", write_entry))
            end
        end

        `uvm_info("DEBUG_FLUSH_MIXED", "=== Phase 4: Trigger debug mode transition (flush all entries) ===", UVM_MEDIUM)
        kv_rst_agent_debug_seq.start(configuration.kv_rst_agent_config.sequencer);

        `uvm_info("DEBUG_FLUSH_MIXED", "=== Phase 5: Pin-check flushed debug value; lock_use entries read masked ===", UVM_MEDIUM)
        // The flush does not touch last_dword, which Phase 2 left at LAST_WORD.
        for (read_entry = 0; read_entry < KV_NUM_KEYS; read_entry++) begin
            for (read_offset = 0; read_offset < KV_NUM_DWORDS; read_offset++) begin
                if (lock_use_group(read_entry))
                    checked_read(configuration.kv_hmac_key_read_agent_config,
                                 read_entry, read_offset, '0, 1, LAST_WORD);
                else
                    checked_read(configuration.kv_hmac_key_read_agent_config,
                                 read_entry, read_offset, DEBUG_FILL, 0, LAST_WORD);
            end
        end

        `uvm_info("DEBUG_FLUSH_MIXED", "=== Phase 5b: Core-only reset lifts locks; every entry must hold the debug value ===", UVM_MEDIUM)
        // Core-only reset clears lock_wr/lock_use but retains data, dest_valid
        // and last_dword, exposing storage of the former lock_use entries.
        kv_rst_agent_core_rst_seq.start(configuration.kv_rst_agent_config.sequencer);
        for (read_entry = 0; read_entry < KV_NUM_KEYS; read_entry++) begin
            for (read_offset = 0; read_offset < KV_NUM_DWORDS; read_offset++) begin
                checked_read(configuration.kv_hmac_key_read_agent_config,
                             read_entry, read_offset, DEBUG_FILL, 0, LAST_WORD);
            end
        end

        `uvm_info("DEBUG_FLUSH_MIXED", "=== Phase 6: Explicit fills in steady debug/scan mode ===", UVM_MEDIUM)
        // Clear locks, then use the existing scan sequence's transition pulse
        // followed by a steady mode level, so CLEAR_SECRETS is the flush source.
        kv_rst_agent_poweron_seq.start(configuration.kv_rst_agent_config.sequencer);
        for (write_entry = 0; write_entry < KV_NUM_KEYS; write_entry++) begin
            kv_write_transaction seed_write;
            seed_write = kv_write_transaction#()::type_id::create("scan_seed_write");
            start_item(seed_write, -1, configuration.kv_doe_write_agent_config.sequencer);
            seed_write.write_en = 1'b1;
            seed_write.write_entry = KV_ENTRY_ADDR_W'(write_entry);
            seed_write.write_offset = KV_ENTRY_SIZE_W'(KV_NUM_DWORDS - 1);
            seed_write.write_data = 32'h1357_9bdf;
            seed_write.write_dest_valid = KV_NUM_READ'(1) << KV_DEST_IDX_HMAC_KEY;
            finish_item(seed_write);
            checked_read(configuration.kv_hmac_key_read_agent_config,
                         write_entry, KV_NUM_DWORDS - 1, 32'h1357_9bdf,
                         0, KV_NUM_DWORDS - 1);
        end
        kv_rst_agent_scan_on_seq.start(configuration.kv_rst_agent_config.sequencer);
        configuration.kv_rst_agent_config.wait_for_num_clocks(5);
        // Entry starts with pattern 0; both requests should change that pattern.
        for (int selection = 1; selection >= 0; selection--) begin
            reg_model.kv_reg_rm.CLEAR_SECRETS.write(
                sts, (selection << 1) | 1, UVM_FRONTDOOR, reg_model.kv_AHB_map, this);
            if (sts != UVM_IS_OK)
                `uvm_fatal("DEBUG_FLUSH_MIXED", "CLEAR_SECRETS fill request failed")
            configuration.kv_rst_agent_config.wait_for_num_clocks(5);
            for (read_entry = 0; read_entry < KV_NUM_KEYS; read_entry++) begin
                for (read_offset = 0; read_offset < KV_NUM_DWORDS; read_offset++) begin
                    checked_read(configuration.kv_hmac_key_read_agent_config,
                                 read_entry, read_offset,
                                 selection ? 32'h5555_5555 : 32'haaaa_aaaa,
                                 0, KV_NUM_DWORDS - 1);
                end
            end
        end
        kv_rst_agent_poweron_seq.start(configuration.kv_rst_agent_config.sequencer);
        `uvm_info("DEBUG_FLUSH_MIXED", "=== Debug flush with mixed locks sequence complete ===", UVM_MEDIUM)
    endtask

endclass
