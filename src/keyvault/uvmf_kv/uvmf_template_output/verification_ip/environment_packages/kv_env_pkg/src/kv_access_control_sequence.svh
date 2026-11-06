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

class kv_access_control_sequence #(
    type CONFIG_T
) extends kv_env_sequence_base #(.CONFIG_T(CONFIG_T));

    `uvm_object_param_utils(kv_access_control_sequence #(CONFIG_T));

    localparam int TARGET = 10;
    localparam int DENIED = 11;
    localparam int OTHER = 12;
    localparam int PARK = 13;
    localparam int WORD = 1;
    localparam int CLEAR_STREAM_BEATS = 64;
    localparam int LOCK_STREAM_BEATS = 64;
    localparam int CPU_STREAM_BEATS = 64;
    localparam logic [KV_DATA_W-1:0] KEY_DATA = 32'h1357_9bdf;
    localparam logic [KV_DATA_W-1:0] DENIED_DATA = 32'h2468_ace1;
    localparam logic [KV_NUM_READ-1:0] ALL_DEST = '1;

    function new(string name = "");
        super.new(name);
    endfunction

    function kv_write_configuration writer_config(int client);
        case (client)
            KV_WRITE_IDX_HMAC:  return configuration.kv_hmac_write_agent_config;
            KV_WRITE_IDX_MLKEM: return configuration.kv_mlkem_write_agent_config;
            KV_WRITE_IDX_ECC:   return configuration.kv_ecc_write_agent_config;
            KV_WRITE_IDX_DOE:   return configuration.kv_doe_write_agent_config;
            KV_WRITE_IDX_AES:   return configuration.kv_aes_write_agent_config;
            default: begin
                `uvm_fatal("KV_POLICY", $sformatf("Invalid writer %0d", client))
                return null;
            end
        endcase
    endfunction

    function kv_read_configuration reader_config(int client);
        case (client)
            KV_DEST_IDX_HMAC_KEY:   return configuration.kv_hmac_key_read_agent_config;
            KV_DEST_IDX_HMAC_BLOCK: return configuration.kv_hmac_block_read_agent_config;
            KV_DEST_IDX_MLDSA_SEED: return configuration.kv_mldsa_key_read_agent_config;
            KV_DEST_IDX_ECC_PKEY:   return configuration.kv_ecc_privkey_read_agent_config;
            KV_DEST_IDX_ECC_SEED:   return configuration.kv_ecc_seed_read_agent_config;
            KV_DEST_IDX_AES_KEY:    return configuration.kv_aes_key_read_agent_config;
            KV_DEST_IDX_MLKEM_SEED: return configuration.kv_mlkem_seed_read_agent_config;
            KV_DEST_IDX_MLKEM_MSG:  return configuration.kv_mlkem_msg_read_agent_config;
            KV_DEST_IDX_DMA_DATA:   return configuration.kv_dma_read_agent_config;
            default: begin
                `uvm_fatal("KV_POLICY", $sformatf("Invalid reader %0d", client))
                return null;
            end
        endcase
    endfunction

    task settle();
        configuration.kv_rst_agent_config.wait_for_num_clocks(4);
        @(negedge configuration.kv_rst_agent_config.monitor_bfm.clk_i);
    endtask

    task reset_state(bit powergood, bit main_reset, bit core_reset, bit fw_window,
                     bit scan_mode = 0);
        kv_rst_transaction tx;
        tx = kv_rst_transaction::type_id::create("policy_reset");
        start_item(tx, -1, configuration.kv_rst_agent_config.sequencer);
        tx.set_pwrgood = powergood;
        tx.assert_rst = main_reset;
        tx.assert_core_rst = core_reset;
        tx.assert_fw_upd_rst = fw_window;
        tx.wait_cycles = 8;
        tx.debug_mode = 0;
        tx.scan_mode = scan_mode;
        finish_item(tx);
        settle();
        if (configuration.kv_rst_agent_config.monitor_bfm.cptra_pwrgood_i !== powergood ||
            configuration.kv_rst_agent_config.monitor_bfm.rst_b_i !== !main_reset ||
            configuration.kv_rst_agent_config.monitor_bfm.core_only_rst_b_i !== !core_reset ||
            configuration.kv_rst_agent_config.monitor_bfm.fw_update_rst_window_i !== fw_window ||
            configuration.kv_rst_agent_config.monitor_bfm.cptra_in_debug_scan_mode_i !== scan_mode)
            `uvm_fatal("KV_POLICY", "Reset/window pins did not reach the requested state")
    endtask

    task core_reset(bit scan_mode = 0);
        reset_state(1, 0, 1, 0, scan_mode);
        reset_state(1, 0, 0, 0, scan_mode);
    endtask

    task write_word(int client, int entry, logic [KV_DATA_W-1:0] data,
                    logic [KV_NUM_READ-1:0] destinations, int offset = WORD);
        kv_write_transaction tx;
        kv_write_configuration cfg;
        cfg = writer_config(client);
        tx = kv_write_transaction#()::type_id::create("policy_write");
        start_item(tx, -1, cfg.sequencer);
        tx.write_en = 1;
        tx.write_entry = KV_ENTRY_ADDR_W'(entry);
        tx.write_offset = KV_ENTRY_SIZE_W'(offset);
        tx.write_data = data;
        tx.write_dest_valid = destinations;
        finish_item(tx);
        // The driver does not return error. The existing monitor/scoreboard does.
    endtask

    task read_word(int client, int entry, logic [KV_DATA_W-1:0] data,
                   bit error, int last_word = WORD);
        checked_read(reader_config(client), entry, WORD, data, error, last_word);
    endtask

    task read_all(int entry, logic [KV_DATA_W-1:0] data,
                  bit error, int last_word = WORD);
        for (int client = 0; client < KV_NUM_READ; client++)
            read_word(client, entry, data, error, last_word);
    endtask

    task park_reads(int entry = PARK);
        read_all(entry, '0, 1, 0);
    endtask

    task control(int entry, bit lock_write, bit lock_use, bit clear_entry);
        uvm_status_e status;
        uvm_reg_data_t data;
        data = '0;
        data[reg_model.kv_reg_rm.KEY_CTRL[entry].lock_wr.get_lsb_pos()] = lock_write;
        data[reg_model.kv_reg_rm.KEY_CTRL[entry].lock_use.get_lsb_pos()] = lock_use;
        data[reg_model.kv_reg_rm.KEY_CTRL[entry].clear.get_lsb_pos()] = clear_entry;
        reg_model.kv_reg_rm.KEY_CTRL[entry].write(
            status, data, UVM_FRONTDOOR, reg_model.kv_AHB_map, this);
        if (status != UVM_IS_OK)
            `uvm_fatal("KV_POLICY", $sformatf("KEY_CTRL[%0d] write failed", entry))
    endtask

    task check_control(int entry, bit lock_write, bit lock_use,
                       logic [KV_NUM_READ-1:0] destinations, int last_word = WORD);
        uvm_status_e status;
        uvm_reg_data_t actual, expected;
        expected = '0;
        expected[reg_model.kv_reg_rm.KEY_CTRL[entry].lock_wr.get_lsb_pos()] = lock_write;
        expected[reg_model.kv_reg_rm.KEY_CTRL[entry].lock_use.get_lsb_pos()] = lock_use;
        expected |= uvm_reg_data_t'(destinations) <<
                    reg_model.kv_reg_rm.KEY_CTRL[entry].dest_valid.get_lsb_pos();
        expected |= uvm_reg_data_t'(last_word) <<
                    reg_model.kv_reg_rm.KEY_CTRL[entry].last_dword.get_lsb_pos();
        reg_model.kv_reg_rm.KEY_CTRL[entry].read(
            status, actual, UVM_FRONTDOOR, reg_model.kv_AHB_map, this);
        if (status != UVM_IS_OK || actual !== expected)
            `uvm_error("KV_POLICY", $sformatf(
                "KEY_CTRL[%0d]: status=%s actual=%h expected=%h",
                entry, status.name(), actual, expected))
    endtask

    task denied_writes(bit lock_write, bit lock_use);
        check_control(TARGET, lock_write, lock_use, ALL_DEST);
        for (int client = 0; client < KV_NUM_WRITE; client++) begin
            write_word(client, TARGET, ~KEY_DATA ^ KV_DATA_W'(client), '0);
            settle();
        end
        check_control(TARGET, lock_write, lock_use, ALL_DEST);
    endtask

    task clear_overlap(int client, int entry = TARGET);
        kv_write_configuration cfg;
        kv_write_t request;
        bit clear_done, blocked_seen, held_clear_seen;
        int clear_age, held_beats;
        int park_entry, witness_entry;
        cfg = writer_config(client);
        clear_done = 0;
        blocked_seen = 0;
        held_clear_seen = 0;
        clear_age = 0;
        held_beats = 0;
        park_entry = (entry == PARK) ? (PARK + 1) % KV_NUM_KEYS : PARK;
        witness_entry = (PARK + 2) % KV_NUM_KEYS;
        if (witness_entry == entry)
            witness_entry = (witness_entry + 1) % KV_NUM_KEYS;
        `uvm_info("KV_POLICY", $sformatf(
            "Checking held clear and recovery: writer %0d entry %0d", client, entry), UVM_LOW)
        write_word(client, entry, KEY_DATA, ALL_DEST);
        settle();
        check_control(entry, 0, 0, ALL_DEST);
        read_word(KV_DEST_IDX_HMAC_KEY, entry, KEY_DATA, 0);
        write_word(client, witness_entry, DENIED_DATA, ALL_DEST);
        settle();
        check_control(witness_entry, 0, 0, ALL_DEST);
        read_word(KV_DEST_IDX_HMAC_KEY, witness_entry, DENIED_DATA, 0);
        park_reads(park_entry);
        // A continuous single-producer stream spans the AHB clear. RTL retains
        // key_entry_clear until that stream ends; no other writer is active.
        fork
            begin
                configuration.kv_rst_agent_config.wait_for_num_clocks(4);
                control(entry, 0, 0, 1);
                clear_done = 1;
            end
            begin
                for (int beat = 0; beat < CLEAR_STREAM_BEATS; beat++) begin
                    if (beat == CLEAR_STREAM_BEATS - 8 && !clear_done)
                        `uvm_fatal("KV_POLICY", $sformatf(
                            "AHB clear for entry %0d did not complete within the bounded write stream", entry))
                    write_word(client, entry, KEY_DATA ^ KV_DATA_W'(beat), ALL_DEST);
                end
            end
            begin
                repeat (CLEAR_STREAM_BEATS + 4) begin
                    @(posedge cfg.monitor_bfm.clk_i);
                    request = kv_write_t'(cfg.monitor_bfm.kv_write_i);
                    if (clear_done)
                        clear_age++;
                    if (request.write_en === 1'b1 && request.write_entry == entry &&
                        request.write_offset == WORD && cfg.monitor_bfm.kv_wr_resp_i === 1'b1) begin
                        blocked_seen = 1;
                        // The CSR singlepulse is gone; consecutive denials witness held clear.
                        if (clear_age >= 4) begin
                            held_beats++;
                            if (held_beats >= 2)
                                held_clear_seen = 1;
                        end
                    end
                    else
                        held_beats = 0;
                end
            end
        join
        settle();
        if (!clear_done || !blocked_seen || !held_clear_seen)
            `uvm_fatal("KV_POLICY", $sformatf(
                "Writer %0d entry %0d: clear completed=%0b denial=%0b held=%0b",
                client, entry, clear_done, blocked_seen, held_clear_seen))
        check_control(entry, 0, 0, '0, 0);
        read_all(entry, '0, 1, 0);
        check_control(witness_entry, 0, 0, ALL_DEST);
        read_all(witness_entry, DENIED_DATA, 0);
        park_reads(park_entry);

        write_word(client, entry, ~KEY_DATA, ALL_DEST);
        settle();
        check_control(entry, 0, 0, ALL_DEST);
        read_all(entry, ~KEY_DATA, 0);
        park_reads(park_entry);
        control(entry, 0, 0, 1);
        settle();
        check_control(entry, 0, 0, '0, 0);
        read_all(entry, '0, 1, 0);
        check_control(witness_entry, 0, 0, ALL_DEST);
        read_all(witness_entry, DENIED_DATA, 0);
        control(witness_entry, 0, 0, 1);
        settle();
        check_control(witness_entry, 0, 0, '0, 0);
        read_all(witness_entry, '0, 1, 0);
        park_reads(park_entry);
    endtask

    task lock_overlap(int client);
        kv_write_configuration cfg;
        kv_write_t request;
        logic [KV_DATA_W-1:0] previous_data, retained_data;
        bit lock_done, boundary_seen, previous_accepted, targets_word;
        cfg = writer_config(client);
        lock_done = 0;
        boundary_seen = 0;
        previous_accepted = 0;
        previous_data = '0;
        retained_data = '0;
        write_word(client, TARGET, KEY_DATA, ALL_DEST);
        settle();
        check_control(TARGET, 0, 0, ALL_DEST);
        park_reads();
        fork
            begin
                configuration.kv_rst_agent_config.wait_for_num_clocks(4);
                control(TARGET, 1, 0, 0);
                lock_done = 1;
            end
            begin
                for (int beat = 0; beat < LOCK_STREAM_BEATS; beat++) begin
                    if (beat == LOCK_STREAM_BEATS - 8 && !lock_done)
                        `uvm_fatal("KV_POLICY", "AHB lock did not complete within the bounded write stream")
                    // Changing data keeps the change-sensitive write monitor active.
                    write_word(client, TARGET, KEY_DATA ^ KV_DATA_W'(beat), ALL_DEST);
                end
            end
            begin
                repeat (LOCK_STREAM_BEATS + 4) begin
                    @(posedge cfg.monitor_bfm.clk_i);
                    request = kv_write_t'(cfg.monitor_bfm.kv_write_i);
                    targets_word = !$isunknown(request) && request.write_en &&
                                   request.write_entry == TARGET && request.write_offset == WORD;
                    if (!boundary_seen && previous_accepted && targets_word &&
                        cfg.monitor_bfm.kv_wr_resp_i === 1'b1) begin
                        boundary_seen = 1;
                        // The preceding accepted input is the retained-data oracle.
                        retained_data = previous_data;
                    end
                    previous_accepted = targets_word &&
                                        cfg.monitor_bfm.kv_wr_resp_i === 1'b0;
                    previous_data = request.write_data;
                end
            end
        join
        settle();
        if (!lock_done || !boundary_seen)
            `uvm_fatal("KV_POLICY", $sformatf(
                "Writer %0d did not observe adjacent accepted/lock-denied writes", client))
        check_control(TARGET, 1, 0, ALL_DEST);
        write_word(client, TARGET, ~retained_data, '0);
        settle();
        check_control(TARGET, 1, 0, ALL_DEST);
        read_all(TARGET, retained_data, 0);
        park_reads();
    endtask

    task cpu_read_overlap(int client, bit selection);
        kv_write_configuration cfg;
        uvm_status_e status;
        bit cpu_done;
        cfg = writer_config(client);
        cpu_done = 0;
        if (configuration.kv_rst_agent_config.monitor_bfm.cptra_in_debug_scan_mode_i !== 1'b0)
            `uvm_fatal("KV_POLICY", "Non-debug CPU overlap requires debug/scan mode to be inactive")
        `uvm_info("KV_POLICY", $sformatf(
            "Producer %0d with non-debug CLEAR_SECRETS selector %0d", client, selection), UVM_LOW)
        fork
            begin
                for (int beat = 0; beat < CPU_STREAM_BEATS; beat++) begin
                    if (beat == CPU_STREAM_BEATS - 8 && !cpu_done)
                        `uvm_fatal("KV_POLICY", "CPU access did not complete within the bounded write stream")
                    write_word(client, TARGET, KEY_DATA ^ KV_DATA_W'(beat), ALL_DEST);
                end
            end
            begin
                configuration.kv_rst_agent_config.wait_for_num_clocks(4);
                // Outside debug/scan, neither selector may replace stored data.
                reg_model.kv_reg_rm.CLEAR_SECRETS.write(
                    status, (int'(selection) << 1) | 1,
                    UVM_FRONTDOOR, reg_model.kv_AHB_map, this);
                if (status != UVM_IS_OK)
                    `uvm_fatal("KV_POLICY", "Non-debug CLEAR_SECRETS write failed")
                check_control(TARGET, 0, 0, ALL_DEST);
                cpu_done = 1;
            end
        join
        settle();
        if (!cpu_done)
            `uvm_fatal("KV_POLICY", "CPU/write overlap did not complete")
        read_all(TARGET, KEY_DATA ^ KV_DATA_W'(CPU_STREAM_BEATS - 1), 0);
        checked_read(reader_config(KV_DEST_IDX_HMAC_KEY), TARGET, 0, '0, 0, WORD);
        read_all(DENIED, DENIED_DATA, 0);
        park_reads();
    endtask

    task lock_population_sweep();
        int counts[5] = '{0, 1, 2, 6, KV_NUM_KEYS};
        kv_rst_scan_on_sequence scan;
        uvm_status_e status;
        uvm_reg_data_t actual;
        bit lock_write, lock_use, protected_entry;
        int rank;
        for (int scan_mode = 0; scan_mode < 2; scan_mode++) begin
            if (scan_mode) begin
                scan = kv_rst_scan_on_sequence::type_id::create("population_scan");
                scan.start(configuration.kv_rst_agent_config.sequencer);
                settle();
            end
            foreach (counts[write_index]) begin
                foreach (counts[use_index]) begin
                    core_reset(scan_mode);
                    park_reads();
                    write_word(KV_WRITE_IDX_HMAC, TARGET, KEY_DATA, ALL_DEST);
                    settle();
                    for (int entry = 0; entry < KV_NUM_KEYS; entry++) begin
                        // Include the addressed target first, not an unrelated lock.
                        rank = (entry == TARGET) ? 0 : ((entry < TARGET) ? entry + 1 : entry);
                        lock_write = rank < counts[write_index];
                        lock_use = rank < counts[use_index];
                        control(entry, lock_write, lock_use, 0);
                        reg_model.kv_reg_rm.KEY_CTRL[entry].read(
                            status, actual, UVM_FRONTDOOR, reg_model.kv_AHB_map, this);
                        if (status != UVM_IS_OK ||
                            actual[reg_model.kv_reg_rm.KEY_CTRL[entry].lock_wr.get_lsb_pos()] !== lock_write ||
                            actual[reg_model.kv_reg_rm.KEY_CTRL[entry].lock_use.get_lsb_pos()] !== lock_use)
                            `uvm_fatal("KV_POLICY", $sformatf(
                                "Lock population mismatch at entry %0d", entry))
                    end
                    settle();
                    lock_write = counts[write_index] != 0;
                    lock_use = counts[use_index] != 0;
                    protected_entry = lock_write || lock_use;
                    check_control(TARGET, lock_write, lock_use, ALL_DEST);
                    read_all(TARGET, lock_use ? '0 : KEY_DATA, lock_use);
                    park_reads();
                    if (counts[write_index] == 2 && counts[use_index] == 0) begin
                        denied_writes(1, 0);
                        read_all(TARGET, KEY_DATA, 0);
                        park_reads();
                    end
                    control(TARGET, lock_write, lock_use, 1);
                    settle();
                    check_control(TARGET, lock_write, lock_use,
                                  protected_entry ? ALL_DEST : '0,
                                  protected_entry ? WORD : 0);
                    read_all(TARGET, protected_entry && !lock_use ? KEY_DATA : '0,
                             !protected_entry || lock_use, protected_entry ? WORD : 0);
                    park_reads();
                end
            end
        end
    endtask

    function logic [KV_DATA_W-1:0] protected_word_data(int entry, int offset);
        return KEY_DATA ^ KV_DATA_W'((entry << KV_ENTRY_SIZE_W) | offset);
    endfunction

    task cpu_write_protection_sweep();
        uvm_status_e status;
        logic [KV_DATA_W-1:0] attempted_data;
        `uvm_info("KV_POLICY", "Checking denied CPU writes at every key-data address", UVM_LOW)
        for (int entry = 0; entry < KV_NUM_KEYS; entry++) begin
            check_control(entry, 0, 0, '0, 0);
            for (int offset = 0; offset < KV_NUM_DWORDS; offset++)
                write_word(KV_WRITE_IDX_HMAC, entry,
                           protected_word_data(entry, offset), ALL_DEST, offset);
            settle();
            check_control(entry, 0, 0, ALL_DEST, KV_NUM_DWORDS - 1);
        end
        for (int phase = 0; phase < 2; phase++) begin
            attempted_data = phase ? '1 : '0;
            for (int entry = 0; entry < KV_NUM_KEYS; entry++) begin
                for (int offset = 0; offset < KV_NUM_DWORDS; offset++) begin
                    reg_model.kv_reg_rm.KEY_ENTRY[entry][offset].write(
                        status, attempted_data, UVM_FRONTDOOR, reg_model.kv_AHB_map, this);
                    if (status != UVM_IS_OK)
                        `uvm_fatal("KV_POLICY", $sformatf(
                            "Raw CPU write failed for KEY_ENTRY[%0d][%0d]", entry, offset))
                    checked_read(reader_config(KV_DEST_IDX_HMAC_KEY), entry, offset,
                                 protected_word_data(entry, offset), 0, KV_NUM_DWORDS - 1);
                end
                check_control(entry, 0, 0, ALL_DEST, KV_NUM_DWORDS - 1);
            end
            // Catch aliases that could corrupt an address already checked above.
            for (int entry = 0; entry < KV_NUM_KEYS; entry++)
                for (int offset = 0; offset < KV_NUM_DWORDS; offset++)
                    checked_read(reader_config(KV_DEST_IDX_HMAC_KEY), entry, offset,
                                 protected_word_data(entry, offset), 0, KV_NUM_DWORDS - 1);
        end
        `uvm_info("KV_POLICY", "All denied CPU key-data writes preserved storage and metadata", UVM_LOW)
    endtask

    virtual task body();
        uvm_status_e status;
        reg_model = configuration.kv_rm;
        `uvm_info("KV_POLICY", "Deterministic populated-entry policy cases", UVM_LOW)

        reset_state(0, 1, 1, 0);
        reset_state(1, 1, 1, 0);
        reset_state(1, 0, 0, 0);
        park_reads();
        write_word(KV_WRITE_IDX_HMAC, TARGET, KEY_DATA, ALL_DEST);
        settle();
        write_word(KV_WRITE_IDX_HMAC, DENIED, DENIED_DATA, '0);
        settle();
        check_control(TARGET, 0, 0, ALL_DEST);
        check_control(DENIED, 0, 0, '0);
        read_all(TARGET, KEY_DATA, 0);
        read_all(DENIED, '0, 1);
        park_reads();

        control(OTHER, 0, 1, 0);
        settle();
        check_control(OTHER, 0, 1, '0, 0);
        read_all(TARGET, KEY_DATA, 0);
        park_reads();
        core_reset();

        control(TARGET, 1, 0, 0);
        settle();
        denied_writes(1, 0);
        read_all(TARGET, KEY_DATA, 0);
        park_reads();
        core_reset();

        control(TARGET, 0, 1, 0);
        control(DENIED, 0, 1, 0);
        settle();
        denied_writes(0, 1);
        check_control(DENIED, 0, 1, '0);
        read_all(TARGET, '0, 1);
        read_all(DENIED, '0, 1);
        park_reads();
        core_reset();
        read_all(TARGET, KEY_DATA, 0);
        park_reads();

        control(TARGET, 1, 1, 0);
        settle();
        denied_writes(1, 1);
        park_reads();
        core_reset();
        read_all(TARGET, KEY_DATA, 0);
        park_reads();

        for (int client = 0; client < KV_NUM_WRITE; client++)
            clear_overlap(client);
        for (int entry = 0; entry < KV_NUM_KEYS; entry++)
            if (entry != TARGET)
                clear_overlap(KV_WRITE_IDX_HMAC, entry);

        for (int client = 0; client < KV_NUM_WRITE; client++) begin
            core_reset();
            lock_overlap(client);
        end
        core_reset();

        write_word(KV_WRITE_IDX_HMAC, TARGET, KEY_DATA, ALL_DEST);
        settle();
        // Keep the stored lock for the crypto register predictor, which has no
        // FW-window gate. RTL masks effective locks while FW is high (kv.sv).
        control(TARGET, 1, 0, 0);
        settle();
        check_control(TARGET, 1, 0, ALL_DEST);
        reset_state(1, 0, 0, 1);
        for (int client = 0; client < KV_NUM_WRITE; client++) begin
            kv_write_configuration cfg;
            kv_write_t request;
            cfg = writer_config(client);
            fork
                write_word(client, TARGET, ~KEY_DATA ^ KV_DATA_W'(client), '0);
                begin
                    @(posedge cfg.monitor_bfm.clk_i);
                    request = kv_write_t'(cfg.monitor_bfm.kv_write_i);
                    if (configuration.kv_rst_agent_config.monitor_bfm.cptra_pwrgood_i !== 1'b1 ||
                        configuration.kv_rst_agent_config.monitor_bfm.rst_b_i !== 1'b1 ||
                        configuration.kv_rst_agent_config.monitor_bfm.fw_update_rst_window_i !== 1'b1 ||
                        request !== {1'b1, KV_ENTRY_ADDR_W'(TARGET), KV_ENTRY_SIZE_W'(WORD),
                                     (~KEY_DATA ^ KV_DATA_W'(client)), {KV_NUM_READ{1'b0}}} ||
                        cfg.monitor_bfm.kv_wr_resp_i !== 1'b1)
                        `uvm_error("KV_POLICY", $sformatf(
                            "Writer %0d did not observe a live FW-window denial", client))
                end
            join
            settle();
        end
        read_all(TARGET, '0, 1);
        park_reads();
        reset_state(1, 0, 0, 0);
        check_control(TARGET, 1, 0, ALL_DEST);
        read_all(TARGET, KEY_DATA, 0);
        park_reads();
        core_reset();
        write_word(KV_WRITE_IDX_AES, TARGET, DENIED_DATA, ALL_DEST);
        settle();
        check_control(TARGET, 0, 0, ALL_DEST);
        read_all(TARGET, DENIED_DATA, 0);

        // Keep real consumers selecting the known word across the CPU write.
        // Check their pins, not the write-only KEY_ENTRY software mirror.
        reg_model.kv_reg_rm.KEY_ENTRY[TARGET][WORD].write(
            status, ~DENIED_DATA, UVM_FRONTDOOR, reg_model.kv_AHB_map, this);
        if (status != UVM_IS_OK)
            `uvm_fatal("KV_POLICY", "Raw CPU KEY_ENTRY write did not complete")
        settle();
        check_control(TARGET, 0, 0, ALL_DEST);
        read_all(TARGET, DENIED_DATA, 0);
        park_reads();

        // Reinitialize through real reset, including any CPU write-only mirror.
        reset_state(0, 1, 1, 0);
        reset_state(1, 1, 1, 0);
        reset_state(1, 0, 0, 0);
        write_word(KV_WRITE_IDX_HMAC, TARGET, KEY_DATA, ALL_DEST);
        write_word(KV_WRITE_IDX_HMAC, DENIED, DENIED_DATA, ALL_DEST);
        settle();
        for (int client = 0; client < KV_NUM_WRITE; client++)
            for (int selection = 0; selection < 2; selection++)
                cpu_read_overlap(client, bit'(selection));
        lock_population_sweep();
        reset_state(0, 1, 1, 0);
        reset_state(1, 1, 1, 0);
        reset_state(1, 0, 0, 0);
        cpu_write_protection_sweep();
        reset_state(0, 1, 1, 0);
        reset_state(1, 1, 1, 0);
        reset_state(1, 0, 0, 0);
        `uvm_info("KV_POLICY", "Deterministic policy phase completed", UVM_LOW)
    endtask

endclass
