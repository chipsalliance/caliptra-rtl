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
// DESCRIPTION: Security property validation — debug mode flush must
// destroy ALL key entries regardless of lock state. Deliberately creates
// four lock groups, triggers debug mode, then reads back to confirm
// every entry returns error (data zeroed, val_ctrl set).
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

    typedef kv_write_key_entry_sequence kv_write_agent_key_entry_sequence_t;
    kv_write_agent_key_entry_sequence_t doe_write_seq;

    typedef kv_read_key_entry_sequence kv_read_agent_key_entry_sequence_t;
    kv_read_agent_key_entry_sequence_t hmac_key_read_seq;

    function new(string name = "");
        super.new(name);
        kv_rst_agent_poweron_seq = kv_rst_agent_poweron_sequence_t::type_id::create("kv_rst_agent_poweron_seq");
        kv_rst_agent_debug_seq = kv_rst_agent_debug_sequence_t::type_id::create("kv_rst_agent_debug_seq");
        doe_write_seq = kv_write_agent_key_entry_sequence_t::type_id::create("doe_write_seq");
        hmac_key_read_seq = kv_read_agent_key_entry_sequence_t::type_id::create("hmac_key_read_seq");
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
        for (write_entry = 0; write_entry < KV_NUM_KEYS; write_entry++) begin
            for (write_offset = 0; write_offset < KV_NUM_DWORDS; write_offset++) begin
                uvm_config_db#(reg [KV_ENTRY_ADDR_W-1:0])::set(null, "uvm_test_top.environment.kv_doe_write_agent.sequencer.doe_write_seq", "local_write_entry", write_entry);
                uvm_config_db#(reg [KV_ENTRY_SIZE_W-1:0])::set(null, "uvm_test_top.environment.kv_doe_write_agent.sequencer.doe_write_seq", "local_write_offset", write_offset);
                doe_write_seq.start(configuration.kv_doe_write_agent_config.sequencer);
            end
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

        `uvm_info("DEBUG_FLUSH_MIXED", "=== Phase 5: Read all entries — expect resp_err on every read (data flushed) ===", UVM_MEDIUM)
        for (read_entry = 0; read_entry < KV_NUM_KEYS; read_entry++) begin
            for (read_offset = 0; read_offset < KV_NUM_DWORDS; read_offset++) begin
                uvm_config_db#(reg [KV_ENTRY_ADDR_W-1:0])::set(null, "uvm_test_top.environment.kv_hmac_key_read_agent.sequencer.hmac_key_read_seq", "local_read_entry", read_entry);
                uvm_config_db#(reg [KV_ENTRY_SIZE_W-1:0])::set(null, "uvm_test_top.environment.kv_hmac_key_read_agent.sequencer.hmac_key_read_seq", "local_read_offset", read_offset);
                hmac_key_read_seq.start(configuration.kv_hmac_key_read_agent_config.sequencer);
            end
        end

        `uvm_info("DEBUG_FLUSH_MIXED", "=== Debug flush with mixed locks sequence complete ===", UVM_MEDIUM)
    endtask

endclass
