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
// DESCRIPTION: PV AHB decode isolation, clear/reset behavior, and register
// access policies, checked with real bus and crypto-interface responses.
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//

class pv_wr_rd_ahb_sequence #(
    type CONFIG_T
) extends pv_env_sequence_base #(.CONFIG_T(CONFIG_T));

    `uvm_object_param_utils(pv_wr_rd_ahb_sequence #(CONFIG_T));

    typedef pv_rst_poweron_sequence pv_rst_agent_poweron_sequence_t;
    pv_rst_agent_poweron_sequence_t pv_rst_agent_poweron_seq;

    typedef pv_write_pcr_entry_sequence pv_write_agent_pcr_entry_sequence_t;
    pv_write_agent_pcr_entry_sequence_t sha512_write_seq;

    typedef pv_read_pcr_entry_sequence pv_read_agent_pcr_entry_sequence_t;
    pv_read_agent_pcr_entry_sequence_t sha512_block_read_seq;

    rand reg [PV_ENTRY_ADDR_W-1:0] sha512_write_entry;    
    rand reg[2:0] lock_data;


    function new(string name = "");
        super.new(name);
        pv_rst_agent_poweron_seq = pv_rst_agent_poweron_sequence_t::type_id::create("pv_rst_agent_poweron_seq");
        if(!this.randomize()) `uvm_error("PV_WR_RD_LOCK", "Failed to randomize PV RST poweron seq");
        
        sha512_write_seq = pv_write_agent_pcr_entry_sequence_t::type_id::create("sha512_write_seq");
        if(!this.randomize()) `uvm_error("PV_WR_RD_LOCK", "Failed to randomize PV WRITE seq");
        
        sha512_block_read_seq = pv_read_agent_pcr_entry_sequence_t::type_id::create("sha512_block_read_seq");
        if(!this.randomize()) `uvm_error("PV_WR_RD_LOCK", "Failed to randomize PV READ seq");
        
    endfunction

    // pragma uvmf custom class_item_additional begin
    localparam uvm_reg_addr_t HIGH_ALIAS_BIT =
        uvm_reg_addr_t'(1) << pv_reg_pkg::PV_REG_ADDR_WIDTH;

    function string get_pv_dut_path();
        string path = "hdl_top.dut";
        void'(uvm_config_db#(string)::get(null, configuration.get_full_name(),
                                        "pv_dut_path", path));
        return path;
    endfunction

    task raw_high_address_access(uvm_reg reference, uvm_access_e kind,
                                 logic [PV_DATA_W-1:0] data,
                                 output uvm_reg_data_t actual);
        uvm_reg_adapter adapter;
        uvm_sequencer_base sequencer;
        uvm_sequence_base parent_seq;
        uvm_object cloned_parent;
        uvm_reg_item context_item;
        uvm_sequence_item request, response;
        uvm_reg_bus_op access;
        uvm_reg_addr_t address;
        uvm_hdl_data_t pin_value;
        pv_uc_req_t observed;
        string dut_path;
        bit completed = 0, request_seen = 0;

        if (reference == null)
            `uvm_fatal("PV_HIGH_ADDR", "Missing alias reference register")
        adapter = reg_model.pv_AHB_map.get_adapter();
        sequencer = reg_model.pv_AHB_map.get_sequencer();
        if (adapter == null || sequencer == null)
            `uvm_fatal("PV_HIGH_ADDR", "Raw accesses require the configured AHB adapter and sequencer")
        address = reference.get_address(reg_model.pv_AHB_map) | HIGH_ALIAS_BIT;
        if (address >= (uvm_reg_addr_t'(1) << PV_ADDR_W) || address[1:0] != 0)
            `uvm_fatal("PV_HIGH_ADDR", "Alias address does not fit the PV AHB port")
        parent_seq = this;
        if (adapter.parent_sequence != null) begin
            cloned_parent = adapter.parent_sequence.clone();
            if (!$cast(parent_seq, cloned_parent))
                `uvm_fatal("PV_HIGH_ADDR", "Cannot clone the adapter's parent sequence")
            parent_seq.set_parent_sequence(this);
        end
        // Supply normal adapter context without mapping or predicting a fake register.
        context_item = uvm_reg_item::type_id::create("high_address_context");
        context_item.element_kind = UVM_REG;
        context_item.element = reference;
        context_item.kind = kind;
        context_item.map = reg_model.pv_AHB_map;
        context_item.local_map = reg_model.pv_AHB_map;
        context_item.path = UVM_FRONTDOOR;
        context_item.parent = parent_seq;
        context_item.value = new[1];
        context_item.value[0] = data;
        access.kind = kind;
        access.addr = address;
        access.data = data;
        access.n_bits = PV_DATA_W;
        access.byte_en = '1;
        adapter.m_set_item(context_item);
        request = adapter.reg2bus(access);
        adapter.m_set_item(null);
        if (request == null)
            `uvm_fatal("PV_HIGH_ADDR", "AHB adapter returned no request")
        request.set_sequencer(sequencer);
        dut_path = get_pv_dut_path();
        fork : bounded_high_address
            begin
                fork
                    begin
                        parent_seq.start_item(request);
                        parent_seq.finish_item(request);
                        request.end_event.wait_on();
                        access.status = UVM_NOT_OK;
                        if (adapter.provides_responses) begin
                            parent_seq.get_base_response(response);
                            adapter.bus2reg(response, access);
                        end
                        else
                            adapter.bus2reg(request, access);
                        completed = 1;
                    end
                    begin
                        while (!completed) begin
                            @(posedge configuration.pv_rst_agent_config.monitor_bfm.clk_i);
                            if (!uvm_hdl_read({dut_path, ".uc_req_dv"}, pin_value))
                                `uvm_fatal("PV_INPUT_PATH", "Cannot observe raw AHB request validity")
                            if (pin_value[0] === 1'b1) begin
                                if (!uvm_hdl_read({dut_path, ".uc_req"}, pin_value))
                                    `uvm_fatal("PV_INPUT_PATH", "Cannot observe raw AHB request")
                                observed = pv_uc_req_t'(pin_value);
                                if (observed.addr === PV_ADDR_W'(address) &&
                                    observed.write === (kind == UVM_WRITE)) begin
                                    request_seen = 1;
                                    if (kind == UVM_WRITE && observed.wdata !== data)
                                        `uvm_error("PV_HIGH_ADDR", "Raw write payload differs at the DUT")
                                    if (kind == UVM_READ) begin
                                        if (!uvm_hdl_read({dut_path, ".uc_req_rdata"}, pin_value))
                                            `uvm_fatal("PV_INPUT_PATH", "Cannot observe rejected read response")
                                        if (pin_value[PV_DATA_W-1:0] !== '0)
                                            `uvm_error("PV_HIGH_ADDR", "High-address read exposed data at the DUT")
                                        if (!uvm_hdl_read({dut_path, ".hrdata_o"}, pin_value))
                                            `uvm_fatal("PV_INPUT_PATH", "Cannot observe rejected AHB read data")
                                        if (pin_value[ahb_lite_slave_0_params::AHB_RDATA_WIDTH-1:0] !== '0)
                                            `uvm_error("PV_HIGH_ADDR", "High-address AHB read returned nonzero or unknown data")
                                    end
                                end
                            end
                        end
                    end
                join
            end
            begin
                repeat (96) @(posedge configuration.pv_rst_agent_config.monitor_bfm.clk_i);
                `uvm_fatal("PV_HIGH_ADDR_TIMEOUT", "Raw high-address AHB transfer timed out")
            end
        join_any
        disable bounded_high_address;
        if (parent_seq != this)
            sequencer.m_sequence_exiting(parent_seq);
        if (!completed || !request_seen)
            `uvm_fatal("PV_HIGH_ADDR", $sformatf(
                "No completed live DUT request for %s at 0x%0h", kind.name(), address))
        actual = access.data;
        if (access.status != UVM_IS_OK || (kind == UVM_READ && actual !== 0))
            `uvm_error("PV_HIGH_ADDR", $sformatf(
                "%s at 0x%0h: status=%s data=%h, expected successful rejection",
                kind.name(), address, access.status.name(), actual))
    endtask

    task high_address_checks();
        int entries[3] = '{0, 1, PV_NUM_PCR-1};
        int offsets[3] = '{0, 1, PV_NUM_DWORDS-1};
        logic [PV_DATA_W-1:0] expected[PV_NUM_PCR][PV_NUM_DWORDS];
        uvm_reg_data_t actual, controls[PV_NUM_PCR];
        uvm_status_e sts;
        `uvm_info("PV_HIGH_ADDR", "Checking high-address rejection and low-address isolation", UVM_LOW)
        foreach (expected[entry, word]) expected[entry][word] = 0;
        foreach (controls[entry]) controls[entry] = 0;
        foreach (entries[index]) begin
            int entry = entries[index];
            for (int word = 0; word < PV_NUM_DWORDS; word++) begin
                expected[entry][word] = 32'h93a5_0001 ^ (entry << 12) ^ word;
                write_pcr_word(entry, word, expected[entry][word]);
            end
            controls[entry] = 'ha4;
            reg_model.pv_reg_rm.PCR_CTRL[entry].write(
                sts, controls[entry], UVM_FRONTDOOR, reg_model.pv_AHB_map, this);
            if (sts != UVM_IS_OK) `uvm_fatal("PV_HIGH_ADDR", "Alias fixture CTRL write failed")
        end
        expected[2][0] = 32'h6b4e_1357;
        write_pcr_word(2, 0, expected[2][0]);
        `uvm_info("PV_CTRL_HISTORY", "Checking bit-2 set/rewrite history at every PCR control", UVM_LOW)
        foreach (controls[entry]) begin
            uvm_reg_data_t control_data;
            if (controls[entry][1:0] !== 2'b00)
                `uvm_fatal("PV_CTRL_HISTORY", "Control history requires unlocked, uncleared fixtures")
            for (int phase = 0; phase < 3; phase++) begin
                if (phase == 2 && !controls[entry][2]) continue;
                control_data = controls[entry];
                if (phase < 2) control_data[2] = (phase == 0);
                reg_model.pv_reg_rm.PCR_CTRL[entry].write(
                    sts, control_data, UVM_FRONTDOOR, reg_model.pv_AHB_map, this);
                if (sts != UVM_IS_OK)
                    `uvm_fatal("PV_CTRL_HISTORY", $sformatf("PCR%0d phase%0d write failed", entry, phase))
                reg_model.pv_reg_rm.PCR_CTRL[entry].read(
                    sts, actual, UVM_FRONTDOOR, reg_model.pv_AHB_map, this);
                if (sts != UVM_IS_OK || actual !== control_data)
                    `uvm_error("PV_CTRL_HISTORY", $sformatf(
                        "PCR%0d phase%0d: status=%s readback=%h expected=%h",
                        entry, phase, sts.name(), actual, control_data))
            end
        end
        `uvm_info("PV_CTRL_HISTORY", "All PCR control set/rewrite histories checked", UVM_LOW)
        foreach (entries[index]) begin
            int entry = entries[index];
            reg_model.pv_reg_rm.PCR_CTRL[entry].read(
                sts, actual, UVM_FRONTDOOR, reg_model.pv_AHB_map, this);
            if (sts != UVM_IS_OK || actual !== controls[entry])
                `uvm_error("PV_HIGH_ADDR", "Nonzero alias fixture control was not established")
            raw_high_address_access(reg_model.pv_reg_rm.PCR_CTRL[entry], UVM_READ, 0, actual);
            raw_high_address_access(reg_model.pv_reg_rm.PCR_CTRL[entry], UVM_WRITE, 'h5b, actual);
            foreach (offsets[word_index]) begin
                int word = offsets[word_index];
                check_pcr_word(entry, word, expected[entry][word]);
                raw_high_address_access(reg_model.pv_reg_rm.PCR_ENTRY[entry][word],
                                        UVM_READ, 0, actual);
                raw_high_address_access(reg_model.pv_reg_rm.PCR_ENTRY[entry][word],
                                        UVM_WRITE, ~expected[entry][word], actual);
            end
        end
        // A complete readback also catches aliases into an unrelated or earlier address.
        for (int entry = 0; entry < PV_NUM_PCR; entry++) begin
            reg_model.pv_reg_rm.PCR_CTRL[entry].read(
                sts, actual, UVM_FRONTDOOR, reg_model.pv_AHB_map, this);
            if (sts != UVM_IS_OK || actual !== controls[entry])
                `uvm_error("PV_HIGH_ADDR", $sformatf("PCR%0d control changed through a high alias", entry))
            for (int word = 0; word < PV_NUM_DWORDS; word++)
                check_pcr_word(entry, word, expected[entry][word]);
        end
        `uvm_info("PV_HIGH_ADDR", "High-address rejection checks completed", UVM_LOW)
    endtask

    task clear_core_reset_checks();
        uvm_reg_data_t actual;
        uvm_status_e sts;
        pv_rst_transaction reset_request;
        pv_uc_req_t accepted_request;
        uvm_hdl_data_t pin_value;
        string dut_path;
        bit address_seen = 0, clear_accepted = 0;
        bit clear_done = 0, reset_done = 0, overlap_seen = 0;
        dut_path = get_pv_dut_path();
        `uvm_info("PV_CLEAR_CORE", "Checking accepted clear across a core-only reset", UVM_LOW)
        for (int word = 0; word < PV_NUM_DWORDS; word++) begin
            write_pcr_word(0, word, 32'he100_0101 ^ word);
            write_pcr_word(1, word, 32'he200_0101 ^ word);
        end
        reg_model.pv_reg_rm.PCR_CTRL[0].write(
            sts, 0, UVM_FRONTDOOR, reg_model.pv_AHB_map, this);
        if (sts != UVM_IS_OK) `uvm_fatal("PV_CLEAR_CORE", "Target control setup failed")
        reg_model.pv_reg_rm.PCR_CTRL[1].write(
            sts, 1, UVM_FRONTDOOR, reg_model.pv_AHB_map, this);
        if (sts != UVM_IS_OK) `uvm_fatal("PV_CLEAR_CORE", "Witness lock setup failed")
        select_pcr_word(0, 0);
        repeat (3) @(posedge configuration.pv_rst_agent_config.monitor_bfm.clk_i);
        fork : bounded_clear_core
            begin
                fork
                    begin
                        reg_model.pv_reg_rm.PCR_CTRL[0].write(
                            sts, 2, UVM_FRONTDOOR, reg_model.pv_AHB_map, this);
                        if (sts != UVM_IS_OK)
                            `uvm_fatal("PV_CLEAR_CORE", "Clear transfer failed")
                        clear_done = 1;
                    end
                    begin
                        // The reset driver takes two rising edges to assert core reset.
                        // Start at the preceding AHB address phase, before clear commits.
                        while (!address_seen) begin
                            @(negedge configuration.pv_rst_agent_config.monitor_bfm.clk_i);
                            uvm_wait_for_nba_region();
                            if (!uvm_hdl_read({dut_path, ".hsel_i"}, pin_value))
                                `uvm_fatal("PV_INPUT_PATH", "Cannot observe AHB selection")
                            if (pin_value[0] !== 1'b1) continue;
                            if (!uvm_hdl_read({dut_path, ".hready_i"}, pin_value))
                                `uvm_fatal("PV_INPUT_PATH", "Cannot observe AHB readiness")
                            if (pin_value[0] !== 1'b1) continue;
                            if (!uvm_hdl_read({dut_path, ".hwrite_i"}, pin_value))
                                `uvm_fatal("PV_INPUT_PATH", "Cannot observe AHB direction")
                            if (pin_value[0] !== 1'b1) continue;
                            if (!uvm_hdl_read({dut_path, ".htrans_i"}, pin_value))
                                `uvm_fatal("PV_INPUT_PATH", "Cannot observe AHB transfer type")
                            if (!(pin_value[1:0] inside {2'b10, 2'b11})) continue;
                            if (!uvm_hdl_read({dut_path, ".haddr_i"}, pin_value))
                                `uvm_fatal("PV_INPUT_PATH", "Cannot observe AHB address")
                            address_seen = pin_value[PV_ADDR_W-1:0] === PV_ADDR_W'(
                                reg_model.pv_reg_rm.PCR_CTRL[0].get_address(reg_model.pv_AHB_map));
                        end
                        reset_request = pv_rst_transaction::type_id::create("clear_core_assert");
                        start_item(reset_request, -1, configuration.pv_rst_agent_config.sequencer);
                        reset_request.set_pwrgood = 1;
                        reset_request.assert_rst = 0;
                        reset_request.assert_core_rst = 1;
                        reset_request.wait_cycles = 4;
                        finish_item(reset_request);
                        reset_request = pv_rst_transaction::type_id::create("clear_core_release");
                        start_item(reset_request, -1, configuration.pv_rst_agent_config.sequencer);
                        reset_request.set_pwrgood = 1;
                        reset_request.assert_rst = 0;
                        reset_request.assert_core_rst = 0;
                        reset_request.wait_cycles = 4;
                        finish_item(reset_request);
                        reset_done = 1;
                    end
                    begin
                        while (!(clear_done && reset_done)) begin
                            @(posedge configuration.pv_rst_agent_config.monitor_bfm.clk_i);
                            if (configuration.pv_rst_agent_config.monitor_bfm.cptra_pwrgood_i !== 1'b1 ||
                                configuration.pv_rst_agent_config.monitor_bfm.rst_b_i !== 1'b1)
                                `uvm_fatal("PV_CLEAR_CORE", "Powergood or main reset changed during core-only test")
                            if (!uvm_hdl_read({dut_path, ".uc_req_dv"}, pin_value))
                                `uvm_fatal("PV_INPUT_PATH", "Cannot observe clear request validity")
                            if (pin_value[0] === 1'b1) begin
                                if (!uvm_hdl_read({dut_path, ".uc_req"}, pin_value))
                                    `uvm_fatal("PV_INPUT_PATH", "Cannot observe accepted clear request")
                                accepted_request = pv_uc_req_t'(pin_value);
                                if (accepted_request.write === 1'b1 &&
                                    accepted_request.addr === PV_ADDR_W'(0) &&
                                    accepted_request.wdata === PV_DATA_W'(2)) begin
                                    if (configuration.pv_rst_agent_config.monitor_bfm.core_only_rst_b_i !== 1'b1)
                                        `uvm_fatal("PV_CLEAR_CORE", "Clear was not accepted before core reset")
                                    clear_accepted = 1;
                                end
                            end
                            if (configuration.pv_rst_agent_config.monitor_bfm.core_only_rst_b_i === 1'b0) begin
                                if (!uvm_hdl_read(
                                    {dut_path, ".pv_reg_hwif_out.PCR_CTRL[0].clear.value"}, pin_value))
                                    `uvm_fatal("PV_INPUT_PATH", "Cannot observe the actual PCR clear pulse")
                                if (pin_value[0] === 1'b1) begin
                                    overlap_seen = 1;
                                    @(negedge configuration.pv_rst_agent_config.monitor_bfm.clk_i);
                                    check_pcr_pins(0, 0, 0);
                                end
                            end
                        end
                    end
                join
            end
            begin
                repeat (96) @(posedge configuration.pv_rst_agent_config.monitor_bfm.clk_i);
                `uvm_fatal("PV_CLEAR_CORE_TIMEOUT", "Clear/core-reset overlap timed out")
            end
        join_any
        disable bounded_clear_core;
        if (!clear_done || !reset_done || !clear_accepted || !overlap_seen)
            `uvm_fatal("PV_CLEAR_CORE", "Did not observe actual clear active while only core reset was low")
        for (int entry = 0; entry < 2; entry++) begin
            reg_model.pv_reg_rm.PCR_CTRL[entry].read(
                sts, actual, UVM_FRONTDOOR, reg_model.pv_AHB_map, this);
            if (sts != UVM_IS_OK || actual !== 0)
                `uvm_error("PV_CLEAR_CORE", "Clear pulse or witness lock survived core-reset completion")
            for (int word = 0; word < PV_NUM_DWORDS; word++)
                check_pcr_word(entry, word, entry == 0 ? 0 : (32'he200_0101 ^ word));
        end
        `uvm_info("PV_CLEAR_CORE", "Checked clear/core-reset overlap and unrelated data retention", UVM_LOW)
    endtask

    // Directed contract checks in the existing nightly-selected test.
    task clear_write_checks();
        logic [PV_DATA_W-1:0] expected[PV_NUM_PCR][PV_NUM_DWORDS];
        logic [PV_DATA_W-1:0] collision_data, locked_data;
        uvm_status_e sts;
        uvm_reg_data_t ctrl;
        pv_rst_core_rst_sequence core_reset;
        bit clear_done;
        int word, neighbor;

        if (reg_model == null)
            `uvm_fatal("PV_DIRECTED", "Directed PV checks require a register model")
        if (reg_model.pv_AHB_map == null ||
            configuration.pv_sha512_write_agent_config.sequencer == null ||
            configuration.pv_sha512_block_read_agent_config.sequencer == null ||
            configuration.pv_rst_agent_config.sequencer == null)
            `uvm_fatal("PV_DIRECTED", "Directed PV checks require an AHB map and active PV agents")
        high_address_checks();
        clear_core_reset_checks();

        // Real SHA pins fill every permitted word. SS PCR4/5 have no ICCM
        // driver in this bench: verify the SHA DROP, do not fake a nonzero fill.
        for (int entry = 0; entry < PV_NUM_PCR; entry++) begin
            reg_model.pv_reg_rm.PCR_CTRL[entry].write(
                sts, 0, UVM_FRONTDOOR, reg_model.pv_AHB_map, this);
            if (sts != UVM_IS_OK) `uvm_error("PV_PREFILL", "CTRL write failed")
            for (int offset = 0; offset < PV_NUM_DWORDS; offset++) begin
                expected[entry][offset] = 32'h9a00_0101 | (entry << 12) | (offset << 4);
                write_pcr_word(entry, offset, expected[entry][offset]);
                if (!sha_write_permitted(entry)) expected[entry][offset] = 0;
            end
        end
        configuration.pv_sha512_write_agent_config.wait_for_num_clocks(3);

        for (int entry = 0; entry < PV_NUM_PCR; entry++) begin
            word = entry % PV_NUM_DWORDS;
            neighbor = (entry + 1) % PV_NUM_PCR;
            collision_data = 32'hc100_0101 | (entry << 12);
            for (int offset = 0; offset < PV_NUM_DWORDS; offset++)
                check_pcr_word(entry, offset, expected[entry][offset]);
            select_pcr_word(entry, word);
            configuration.pv_sha512_block_read_agent_config.wait_for_num_clocks(3);

            clear_done = 0;
            fork : bounded_overlap
                begin
                    fork
                        write_pcr_word(entry, word, collision_data, 64);
                        begin
                            repeat (4) @(posedge configuration.pv_sha512_write_agent_config.monitor_bfm.clk_i);
                            @(negedge configuration.pv_sha512_write_agent_config.monitor_bfm.clk_i);
                            check_sha_request(entry, word, collision_data);
                            // A single frontdoor CSR write, not a RAL write to
                            // the RO PCR data. Stream spans its registered pulse.
                            reg_model.pv_reg_rm.PCR_CTRL[entry].write(
                                sts, 2, UVM_FRONTDOOR, reg_model.pv_AHB_map, this);
                            if (sts != UVM_IS_OK) `uvm_error("PV_OVERLAP", "Clear write failed")
                            repeat (3) begin
                                @(posedge configuration.pv_sha512_write_agent_config.monitor_bfm.clk_i);
                                check_sha_request(entry, word, collision_data);
                            end
                            clear_done = 1;
                        end
                        begin
                            repeat (4) @(posedge configuration.pv_sha512_write_agent_config.monitor_bfm.clk_i);
                            // Validate every request edge spanning the AHB
                            // transfer and its CSR-clear pipeline, not only
                            // the request at the end of the stream.
                            while (!clear_done) begin
                                @(posedge configuration.pv_sha512_write_agent_config.monitor_bfm.clk_i);
                                check_sha_request(entry, word, collision_data);
                                @(negedge configuration.pv_sha512_write_agent_config.monitor_bfm.clk_i);
                                // Check EVERY post-NBA result during overlap:
                                // a clear-wins bug cannot be hidden by a later
                                // beat rewriting the same word before readback.
                                check_pcr_pins(entry, word,
                                    sha_write_permitted(entry) ? collision_data : 0);
                            end
                        end
                    join
                    if (!clear_done) `uvm_fatal("PV_OVERLAP", "Clear did not finish within stream")
                end
                begin
                    // The BFM clock helper has static arguments shared by concurrent calls.
                    repeat (96) @(posedge configuration.pv_sha512_write_agent_config.monitor_bfm.clk_i);
                    `uvm_fatal("PV_OVERLAP_TIMEOUT", "Bounded AHB clear/write overlap timed out")
                end
            join_any
            disable bounded_overlap;
            configuration.pv_sha512_write_agent_config.wait_for_num_clocks(3);
            for (int offset = 0; offset < PV_NUM_DWORDS; offset++) begin
                expected[entry][offset] =
                    sha_write_permitted(entry) && offset == word ? collision_data : 0;
                check_pcr_word(entry, offset, expected[entry][offset]);
                check_pcr_word(neighbor, offset, expected[neighbor][offset]);
            end
            reg_model.pv_reg_rm.PCR_CTRL[entry].read(
                sts, ctrl, UVM_FRONTDOOR, reg_model.pv_AHB_map, this);
            if (sts != UVM_IS_OK || ctrl !== 0)
                `uvm_error("PV_CLEAR_PULSE", $sformatf("PCR%0d CTRL=%h, expected zero", entry, ctrl))

            // PV lock blocks SW clear/lock writes, NOT SHA reads/writes.
            reg_model.pv_reg_rm.PCR_CTRL[entry].write(
                sts, 1, UVM_FRONTDOOR, reg_model.pv_AHB_map, this);
            if (sts != UVM_IS_OK) `uvm_error("PV_LOCK", "Lock write failed")
            reg_model.pv_reg_rm.PCR_CTRL[entry].write(
                sts, 2, UVM_FRONTDOOR, reg_model.pv_AHB_map, this);
            if (sts != UVM_IS_OK) `uvm_error("PV_LOCK", "Denied clear bus transfer failed")
            locked_data = 32'hd200_0101 | (entry << 12);
            word = (word + 1) % PV_NUM_DWORDS;
            write_pcr_word(entry, word, locked_data);
            configuration.pv_sha512_write_agent_config.wait_for_num_clocks(3);
            if (sha_write_permitted(entry)) expected[entry][word] = locked_data;
            for (int offset = 0; offset < PV_NUM_DWORDS; offset++)
                check_pcr_word(entry, offset, expected[entry][offset]);
            reg_model.pv_reg_rm.PCR_CTRL[entry].read(
                sts, ctrl, UVM_FRONTDOOR, reg_model.pv_AHB_map, this);
            if (sts != UVM_IS_OK || ctrl !== 1)
                `uvm_error("PV_STICKY_LOCK", $sformatf("PCR%0d CTRL=%h, expected lock=1 clear=0", entry, ctrl))
        end

        // Actual core-only reset pins, after the clears, no contradictory flags
        // and no AHB traffic during the FW-update window. Data must survive.
        core_reset = pv_rst_core_rst_sequence::type_id::create("core_reset");
        fork
            core_reset.start(configuration.pv_rst_agent_config.sequencer);
            begin
                // The existing driver asserts core reset after two edges and
                // holds it through the first transaction's wait_cycles.
                configuration.pv_rst_agent_config.wait_for_num_clocks(3);
                @(negedge configuration.pv_rst_agent_config.monitor_bfm.clk_i);
                if (configuration.pv_rst_agent_config.monitor_bfm.cptra_pwrgood_i !== 1'b1 ||
                    configuration.pv_rst_agent_config.monitor_bfm.rst_b_i !== 1'b1 ||
                    configuration.pv_rst_agent_config.monitor_bfm.core_only_rst_b_i !== 1'b0 ||
                    configuration.pv_rst_agent_config.monitor_bfm.fw_update_rst_window_i !== 1'b1)
                    `uvm_error("PV_CORE_RESET_PINS", "Expected core-only reset, powergood/main reset unchanged")
            end
        join
        configuration.pv_rst_agent_config.wait_for_num_clocks(3);
        for (int entry = 0; entry < PV_NUM_PCR; entry++) begin
            reg_model.pv_reg_rm.PCR_CTRL[entry].read(
                sts, ctrl, UVM_FRONTDOOR, reg_model.pv_AHB_map, this);
            if (sts != UVM_IS_OK || ctrl !== 0)
                `uvm_error("PV_CORE_RESET", $sformatf("PCR%0d lock did not clear: %h", entry, ctrl))
            for (int offset = 0; offset < PV_NUM_DWORDS; offset++)
                check_pcr_word(entry, offset, expected[entry][offset]);
        end
    endtask

    // pragma uvmf custom class_item_additional end
    virtual task body();
        uvm_status_e sts;
        int write_entry = 0; 
        int write_offset = 0;
        int read_entry = 0; 
        int read_offset = 0;
        reg [31:0] wr_data, rd_data;
        reg_model = configuration.pv_rm;

        std::randomize(sha512_write_entry);

        //Issue and wait for reset
        if(configuration.pv_rst_agent_config.sequencer != null)
            pv_rst_agent_poweron_seq.start(configuration.pv_rst_agent_config.sequencer);
        else
            `uvm_error("PV_WR_RD_LOCK", "pv_rst_agent_config.sequencer is null!")

        clear_write_checks();
        
        //Write to all regs with random data
        for (write_entry = 0; write_entry < PV_NUM_PCR; write_entry++) begin
            for(write_offset = 0; write_offset < PV_NUM_DWORDS; write_offset++) begin
                uvm_config_db#(reg [PV_ENTRY_ADDR_W-1:0])::set(null, "uvm_test_top.environment.pv_sha512_write_agent.sequencer.sha512_write_seq", "local_write_entry",write_entry);
                uvm_config_db#(reg [PV_ENTRY_SIZE_WIDTH-1:0])::set(null, "uvm_test_top.environment.pv_sha512_write_agent.sequencer.sha512_write_seq", "local_write_offset",write_offset);
                sha512_write_seq.start(configuration.pv_sha512_write_agent_config.sequencer);
            end 
        end

        //Write to all entries, all offsets via AHB interface - should not go through
        for(write_entry = 0; write_entry < PV_NUM_PCR; write_entry++) begin
            for(write_offset = 0; write_offset < PV_NUM_DWORDS; write_offset++) begin
                std::randomize(wr_data);
                reg_model.pv_reg_rm.PCR_ENTRY[write_entry][write_offset].write(sts, wr_data, UVM_FRONTDOOR, reg_model.pv_AHB_map, this);
                assert(sts == UVM_IS_OK) else `uvm_error("AHB_WRITE", $sformatf("Failed when writing to PCR_ENTRY[%d][%d]",write_entry, write_offset))
            end
        end

        //Read from all entries and offsets via AHB interface
        for (read_entry = 0; read_entry < PV_NUM_PCR; read_entry++) begin
            for (read_offset = 0; read_offset < PV_NUM_DWORDS; read_offset++) begin
                reg_model.pv_reg_rm.PCR_ENTRY[read_entry][read_offset].read(sts, rd_data, UVM_FRONTDOOR, reg_model.pv_AHB_map, this);
                assert(sts == UVM_IS_OK) else `uvm_error("AHB_READ", $sformatf("Failed when reading from PCR_ENTRY[%d][%d]",read_entry, read_offset))
            end
        end

        //Write to all CTRL, all offsets via AHB interface
        for(write_entry = 0; write_entry < PV_NUM_PCR; write_entry++) begin
            std::randomize(wr_data);
            reg_model.pv_reg_rm.PCR_CTRL[write_entry].write(sts, wr_data, UVM_FRONTDOOR, reg_model.pv_AHB_map, this);
            assert(sts == UVM_IS_OK) else `uvm_error("AHB_WRITE", $sformatf("Failed when writing to PCR_CTRL[%d]",write_entry))
        end

        //Read from all CTRL and offsets via AHB interface
        for (read_entry = 0; read_entry < PV_NUM_PCR; read_entry++) begin
            reg_model.pv_reg_rm.PCR_CTRL[read_entry].read(sts, rd_data, UVM_FRONTDOOR, reg_model.pv_AHB_map, this);
            assert(sts == UVM_IS_OK) else `uvm_error("AHB_READ", $sformatf("Failed when reading from PCR_CTRL[%d]",read_entry))
        end

    endtask

endclass