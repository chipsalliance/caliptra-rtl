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
// Directed DCLS controller, included inside the standalone SoC BFM.
`define DCLS_LS `CPTRA_TOP_PATH.rvtop.lockstep
`define DCLS_SHADOW_GPR `DCLS_LS.xshadow_core.dec.arf

localparam int DCLS_STEP_TIMEOUT = 4096;
localparam int DCLS_BOOT_TIMEOUT = 200000;
localparam logic [31:0] DCLS_FATAL_MASK = `SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_RV_DCLS_ERR_MASK;
int unsigned dcls_boot_count = 0;
logic [31:0] dcls_fault_word;
string dcls_scenario;
bit dcls_output_fault_active = 0;
bit dcls_regfile_fault_active = 0;
bit dcls_invalid_active = 0;
bit dcls_assets_prepared = 0;

always @(posedge core_clk) begin
    if (dcls_test_start) dcls_boot_count <= dcls_boot_count + 1;
    if (dcls_suite_owner && cptra_rst_b && dcls_bringup_done && cptra_error_non_fatal)
        $fatal(1, "DCLS: unexpected nonfatal error");
end

task automatic dcls_read(input logic [31:0] addr, output logic [31:0] data);
    axi_resp_e resp;
    logic [`CALIPTRA_AXI_USER_WIDTH-1:0] resp_user;
    bit completed = 0;
    fork : read_guard
        begin
            m_axi_bfm_if.axi_read_single(.addr(addr), .data(data), .resp(resp), .resp_user(resp_user));
            completed = 1;
        end
        begin
            repeat (DCLS_STEP_TIMEOUT) @(negedge core_clk);
        end
    join_any
    disable read_guard;
    if (!completed || resp != AXI_RESP_OKAY)
        $fatal(1, "DCLS: AXI read failed/timed out at %h (resp %0d)", addr, resp);
endtask

task automatic dcls_write(input logic [31:0] addr, input logic [31:0] data);
    axi_resp_e resp;
    logic [`CALIPTRA_AXI_USER_WIDTH-1:0] resp_user;
    bit completed = 0;
    fork : write_guard
        begin
            m_axi_bfm_if.axi_write_single(.addr(addr), .data(data), .resp(resp), .resp_user(resp_user));
            completed = 1;
        end
        begin
            repeat (DCLS_STEP_TIMEOUT) @(negedge core_clk);
        end
    join_any
    disable write_guard;
    if (!completed || resp != AXI_RESP_OKAY)
        $fatal(1, "DCLS: AXI write failed/timed out at %h (resp %0d)", addr, resp);
endtask

task automatic dcls_wait_boot(input int unsigned previous_boot);
    bit seen = 0;
    for (int i = 0; i < DCLS_BOOT_TIMEOUT; i++) begin
        @(negedge core_clk);
        if (dcls_boot_count > previous_boot && dcls_bringup_done && `DCLS_LS.rst_n) begin
            seen = 1;
            break;
        end
    end
    if (!seen) $fatal(1, "DCLS: firmware/bringup handshake timed out");
    // Let the x20 loop and comparator settle.
    repeat (64) @(negedge core_clk);
    if (`CPTRA_TOP_PATH.rvtop.lockstep_err_injection_en_i !== el2_mubi_pkg::El2MuBiFalse)
        $fatal(1, "DCLS: explicit error injection must remain false");
endtask

task automatic dcls_check_config(input bit enabled);
    logic [31:0] data;
    dcls_read(`CLP_SOC_IFC_REG_CPTRA_HW_CONFIG, data);
    if (((data & `SOC_IFC_REG_CPTRA_HW_CONFIG_DCLS_EN_MASK) != 0) != enabled)
        $fatal(1, "DCLS: enable readback mismatch: %h expected %0d", data, enabled);
`ifdef CALIPTRA_MODE_SUBSYSTEM
    if (!(data & `SOC_IFC_REG_CPTRA_HW_CONFIG_SUBSYSTEM_MODE_EN_MASK))
        $fatal(1, "DCLS: subsystem profile readback is passive");
`else
    if (data & `SOC_IFC_REG_CPTRA_HW_CONFIG_SUBSYSTEM_MODE_EN_MASK)
        $fatal(1, "DCLS: passive profile readback is subsystem");
`endif
endtask

task automatic dcls_set_enable(input bit enabled);
    @(negedge core_clk);
    ss_dcls_en = enabled;
    repeat (8) @(negedge core_clk);
    dcls_check_config(enabled);
    $display("DCLS: reporting enable=%0d", enabled);
endtask

task automatic dcls_check_status(input bit status, input bit fatal_output);
    logic [31:0] data;
    dcls_read(`CLP_SOC_IFC_REG_CPTRA_HW_ERROR_FATAL, data);
    if (data !== (status ? DCLS_FATAL_MASK : 32'h0) || cptra_error_fatal !== fatal_output)
        $fatal(1, "DCLS: status=%h/output=%0b expected status=%h/output=%0b",
               data, cptra_error_fatal, status ? DCLS_FATAL_MASK : 32'h0, fatal_output);
endtask

task automatic dcls_quiet(input int cycles = 64);
    repeat (cycles) begin
        @(negedge core_clk);
        if (!el2_mubi_pkg::mubi_check_false(`DCLS_LS.corruption_detected_o) || cptra_error_fatal)
            $fatal(1, "DCLS: unexpected mismatch report during clean/suppressed execution");
    end
    dcls_check_status(0, 0);
endtask

// Seed KV through its hardware write interface; release forces before faults.
task automatic dcls_prepare_assets;
    if (cptra_rst_b && `CPTRA_TOP_PATH.cptra_uc_rst_b && !cptra_error_fatal) begin
        @(negedge core_clk);
        force `CPTRA_TOP_PATH.key_vault1.kv_reg_hwif_in.KEY_ENTRY[0][0].data.we = 1'b1;
        force `CPTRA_TOP_PATH.key_vault1.kv_reg_hwif_in.KEY_ENTRY[0][0].data.next = 32'hdca15afe;
        force `CPTRA_TOP_PATH.key_vault1.kv_reg_hwif_in.KEY_CTRL[0].dest_valid.we = 1'b1;
        force `CPTRA_TOP_PATH.key_vault1.kv_reg_hwif_in.KEY_CTRL[0].dest_valid.next = 9'h001;
        repeat (2) @(negedge core_clk);
        release `CPTRA_TOP_PATH.key_vault1.kv_reg_hwif_in.KEY_ENTRY[0][0].data.we;
        release `CPTRA_TOP_PATH.key_vault1.kv_reg_hwif_in.KEY_ENTRY[0][0].data.next;
        release `CPTRA_TOP_PATH.key_vault1.kv_reg_hwif_in.KEY_CTRL[0].dest_valid.we;
        release `CPTRA_TOP_PATH.key_vault1.kv_reg_hwif_in.KEY_CTRL[0].dest_valid.next;
        repeat (2) @(negedge core_clk);
        if (`CPTRA_TOP_PATH.key_vault1.kv_reg_hwif_out.KEY_ENTRY[0][0].data.value !== 32'hdca15afe ||
            `CPTRA_TOP_PATH.key_vault1.kv_reg_hwif_out.KEY_CTRL[0].dest_valid.value !== 9'h001 ||
            $isunknown({`CPTRA_TOP_PATH.obf_uds_seed, `CPTRA_TOP_PATH.obf_field_entropy,
                        `CPTRA_TOP_PATH.cptra_obf_key_reg}) ||
            `CPTRA_TOP_PATH.obf_uds_seed === '0 ||
            `CPTRA_TOP_PATH.obf_field_entropy === '0 ||
            `CPTRA_TOP_PATH.cptra_obf_key_reg === '0)
            $fatal(1, "DCLS: valid KV/nonzero boot-secret clearing preconditions were not established");
        dcls_assets_prepared = 1;
    end
endtask

task automatic dcls_start_fault(input bit regfile_fault);
    dcls_prepare_assets();
    @(negedge core_clk);
    if (`CPTRA_TOP_PATH.rvtop.lockstep_err_injection_en_i !== el2_mubi_pkg::El2MuBiFalse)
        $fatal(1, "DCLS: explicit error injection is active");
    if (regfile_fault) begin
`ifdef RV_LOCKSTEP_REGFILE_ENABLE
`ifdef RV_LOCKSTEP_REGFILE_READ_ENABLE
        // Corrupt shadow x20 for the register-file comparator.
        if (`DCLS_SHADOW_GPR.gpr_out[20] !== 32'hdca15afe)
            $fatal(1, "DCLS: firmware did not initialize shadow x20: %h", `DCLS_SHADOW_GPR.gpr_out[20]);
        dcls_fault_word = 32'hdca15aff;
        force `DCLS_SHADOW_GPR.gpr_out[20] = dcls_fault_word;
        dcls_regfile_fault_active = 1;
`else
        $fatal(1, "DCLS: x20 test requires RV_LOCKSTEP_REGFILE_READ_ENABLE");
`endif
`else
        $fatal(1, "DCLS: register-file comparator is absent");
`endif
    end else begin
        // Corrupt ECC status without changing retired trace.
        force `DCLS_LS.shadow_core_outputs.iccm_ecc_single_error =
              ~`DCLS_LS.delayed_main_core_outputs.iccm_ecc_single_error;
        dcls_output_fault_active = 1;
    end
endtask

task automatic dcls_observe_fault(input bit regfile_fault);
    bit observed = 0;
    for (int i = 0; i < DCLS_STEP_TIMEOUT; i++) begin
        @(negedge core_clk);
        if (`CPTRA_TOP_PATH.rvtop.lockstep_err_injection_en_i !== el2_mubi_pkg::El2MuBiFalse)
            $fatal(1, "DCLS: explicit injection changed during comparator test");
        if (regfile_fault) begin
`ifdef RV_LOCKSTEP_REGFILE_ENABLE
`ifdef RV_LOCKSTEP_REGFILE_READ_ENABLE
            if (`DCLS_LS.regfile_corrupted &&
                (`DCLS_SHADOW_GPR.raddr0 == 5'd20 || `DCLS_SHADOW_GPR.raddr1 == 5'd20) &&
                `DCLS_LS.delayed_regfile.delayed_main_core_regfile[`DCLS_LS.LockstepDelayPipeStages].gpr !=
                `DCLS_LS.shadow_core_regfile.gpr) begin
                observed = 1;
                break;
            end
`endif
`endif
        end else if (`DCLS_LS.outputs_corrupted &&
                     `DCLS_LS.delayed_main_core_outputs.iccm_ecc_single_error !=
                     `DCLS_LS.shadow_core_outputs.iccm_ecc_single_error) begin
            observed = 1;
            break;
        end
    end
    if (!observed) $fatal(1, "DCLS: raw %s comparator mismatch was not observed", regfile_fault ? "GPR" : "output");
    $display("DCLS: observed raw %s comparator divergence (explicit injection false)", regfile_fault ? "GPR" : "output");
endtask

task automatic dcls_release_faults;
    @(negedge core_clk);
    if (dcls_output_fault_active) begin
        release `DCLS_LS.shadow_core_outputs.iccm_ecc_single_error;
        dcls_output_fault_active = 0;
    end
`ifdef RV_LOCKSTEP_REGFILE_ENABLE
    if (dcls_regfile_fault_active) begin
        release `DCLS_SHADOW_GPR.gpr_out[20];
        dcls_regfile_fault_active = 0;
    end
`endif
    if (dcls_invalid_active) begin
        release `DCLS_LS.disable_corruption_detection_i;
        dcls_invalid_active = 0;
    end
    repeat (16) @(negedge core_clk);
endtask

task automatic dcls_wait_fatal;
    bit seen = 0;
    for (int i = 0; i < DCLS_STEP_TIMEOUT; i++) begin
        @(negedge core_clk);
        if (cptra_error_fatal) begin
            seen = 1;
            break;
        end
    end
    if (!seen) $fatal(1, "DCLS: expected fatal output did not assert");
    repeat (8) @(negedge core_clk);
    dcls_check_status(1, 1);
    if (!dcls_assets_prepared) $fatal(1, "DCLS: fatal asset clearing has no prepared secret marker");
    if (!`CPTRA_TOP_PATH.clear_obf_secrets_debugScanQ ||
        !`CPTRA_TOP_PATH.debug_lock_or_scan_mode_switch ||
        `CPTRA_TOP_PATH.obf_uds_seed !== '0 || `CPTRA_TOP_PATH.obf_field_entropy !== '0 ||
        `CPTRA_TOP_PATH.cptra_obf_key_reg !== '0)
        $fatal(1, "DCLS: fatal did not clear obfuscated secrets");
    for (int entry = 0; entry < KV_NUM_KEYS; entry++) begin
        for (int dw = 0; dw < KV_NUM_DWORDS; dw++) begin
            if (`CPTRA_TOP_PATH.key_vault1.kv_reg_hwif_out.KEY_ENTRY[entry][dw].data.value !==
                (`CPTRA_TOP_PATH.key_vault1.kv_reg_hwif_out.CLEAR_SECRETS.sel_debug_value.value ?
                 32'h55555555 : 32'haaaaaaaa))
                $fatal(1, "DCLS: fatal KV clearing failed for entry %0d dword %0d", entry, dw);
        end
    end
    dcls_assets_prepared = 0;
    $display("DCLS: fatal bit 7/output and secret/KV clearing verified");
endtask

task automatic dcls_clear_status(input bit expected_fatal_output);
    dcls_write(`CLP_SOC_IFC_REG_CPTRA_HW_ERROR_FATAL, DCLS_FATAL_MASK);
    repeat (8) @(negedge core_clk);
    dcls_check_status(0, expected_fatal_output);
endtask

task automatic dcls_warm_reset(input bit retained_status);
    int unsigned previous_boot = dcls_boot_count;
    dcls_release_faults();
    @(negedge core_clk); dcls_assert_warm_rst = 1;
    repeat (32) @(negedge core_clk);
    if (cptra_rst_b !== 0) $fatal(1, "DCLS: warm reset request was not applied");
    dcls_assert_warm_rst = 0;
    dcls_deassert_warm_rst = 1;
    repeat (4) @(negedge core_clk);
    dcls_deassert_warm_rst = 0;
    dcls_wait_boot(previous_boot);
    dcls_check_config(ss_dcls_en);
    dcls_check_status(retained_status, 0);
    $display("DCLS: warm reset retained status=%0d and cleared fatal output", retained_status);
endtask

task automatic dcls_power_reset;
    int unsigned previous_boot = dcls_boot_count;
    dcls_release_faults();
    @(negedge core_clk); dcls_assert_hard_rst = 1;
    repeat (32) @(negedge core_clk);
    if (cptra_pwrgood !== 0 || cptra_rst_b !== 0)
        $fatal(1, "DCLS: power-good reset request was not applied");
    dcls_assert_hard_rst = 0;
    dcls_deassert_hard_rst = 1;
    repeat (4) @(negedge core_clk);
    dcls_deassert_hard_rst = 0;
    dcls_deassert_warm_rst = 1;
    repeat (4) @(negedge core_clk);
    dcls_deassert_warm_rst = 0;
    dcls_wait_boot(previous_boot);
    dcls_check_config(ss_dcls_en);
    dcls_check_status(0, 0);
    $display("DCLS: power-good reset cleared status/output");
endtask

task automatic dcls_core_reset(input bit status, input bit fatal_output);
    int unsigned previous_boot = dcls_boot_count;
    bit reset_seen = 0;
    dcls_release_faults();
    @(negedge core_clk);
    force `CPTRA_TOP_PATH.soc_ifc_top1.i_soc_ifc_boot_fsm.fw_update_rst = 1'b1;
    for (int i = 0; i < DCLS_STEP_TIMEOUT; i++) begin
        @(negedge core_clk);
        if (!`CPTRA_TOP_PATH.cptra_uc_rst_b) begin reset_seen = 1; break; end
    end
    if (!reset_seen) $fatal(1, "DCLS: firmware-update core reset did not assert");
    repeat (5) @(negedge core_clk);
    release `CPTRA_TOP_PATH.soc_ifc_top1.i_soc_ifc_boot_fsm.fw_update_rst;
    dcls_check_status(status, fatal_output);
    dcls_wait_boot(previous_boot);
    if (`DCLS_LS.dbg_detected !== el2_mubi_pkg::El2MuBiFalse)
        $fatal(1, "DCLS: core reset did not clear debug history");
    dcls_check_status(status, fatal_output);
    $display("DCLS: core reset rearmed debug qualification and preserved fatal state");
endtask

task automatic dcls_debug_enter;
    bit acknowledged = 0;
    @(negedge core_clk);
    force `CPTRA_TOP_PATH.rvtop.mpc_debug_run_req = 1'b0;
    force `CPTRA_TOP_PATH.rvtop.mpc_debug_halt_req = 1'b1;
    for (int i = 0; i < DCLS_STEP_TIMEOUT; i++) begin
        @(negedge core_clk);
        if (`CPTRA_TOP_PATH.mpc_debug_halt_ack) acknowledged = 1;
        if (acknowledged && `CPTRA_TOP_PATH.o_debug_mode_status) break;
    end
    if (!acknowledged || !`CPTRA_TOP_PATH.o_debug_mode_status)
        $fatal(1, "DCLS: MPC halt did not enter actual debug mode");
    repeat (16) @(negedge core_clk);
    if (`DCLS_LS.dbg_detected !== el2_mubi_pkg::El2MuBiTrue)
        $fatal(1, "DCLS: debug-entry history was not latched");
    $display("DCLS: actual debug entry observed through MPC halt");
endtask

task automatic dcls_debug_exit;
    bit acknowledged = 0;
    @(negedge core_clk);
    release `CPTRA_TOP_PATH.rvtop.mpc_debug_halt_req;
    force `CPTRA_TOP_PATH.rvtop.mpc_debug_run_req = 1'b1;
    for (int i = 0; i < DCLS_STEP_TIMEOUT; i++) begin
        @(negedge core_clk);
        if (`CPTRA_TOP_PATH.mpc_debug_run_ack) acknowledged = 1;
        if (acknowledged && !`CPTRA_TOP_PATH.o_debug_mode_status) break;
    end
    release `CPTRA_TOP_PATH.rvtop.mpc_debug_run_req;
    if (!acknowledged || `CPTRA_TOP_PATH.o_debug_mode_status)
        $fatal(1, "DCLS: MPC run did not exit actual debug mode");
    repeat (32) @(negedge core_clk);
    if (`DCLS_LS.dbg_detected !== el2_mubi_pkg::El2MuBiTrue)
        $fatal(1, "DCLS: debug-history suppression disappeared on debug exit");
    $display("DCLS: debug exit retains reporting suppression until core reset");
endtask

task automatic dcls_invalid_disable;
    dcls_prepare_assets();
    @(negedge core_clk);
    force `DCLS_LS.disable_corruption_detection_i = 4'h0;
    dcls_invalid_active = 1;
    repeat (2) @(negedge core_clk);
    if (`DCLS_LS.disable_detection_invalid !== el2_mubi_pkg::El2MuBiTrue)
        $fatal(1, "DCLS: invalid MuBi disable was not recognized");
endtask

task automatic dcls_comparator_case(input bit regfile_fault);
    dcls_quiet();
    dcls_set_enable(0);
    dcls_start_fault(regfile_fault);
    dcls_observe_fault(regfile_fault);
    dcls_quiet();
    dcls_release_faults();
    dcls_set_enable(1);
    dcls_quiet(); // Removed disabled faults are not reported retrospectively.
    dcls_start_fault(regfile_fault);
    dcls_observe_fault(regfile_fault);
    dcls_wait_fatal();
    dcls_release_faults();
endtask

task automatic dcls_outputs_scenario;
    dcls_comparator_case(0);
    dcls_set_enable(0);
    dcls_check_status(1, 1); // Disable never clears a latched fatal.
    dcls_core_reset(1, 1);
    dcls_warm_reset(1);
    dcls_clear_status(0);
    dcls_power_reset();
    dcls_set_enable(1);
    dcls_start_fault(0);
    dcls_observe_fault(0);
    dcls_wait_fatal();
    dcls_release_faults();
    dcls_clear_status(1); // W1C clears status independently of output.
    dcls_core_reset(0, 1);
    dcls_power_reset();
    dcls_quiet();
endtask

task automatic dcls_regfile_scenario;
    dcls_comparator_case(1);
    dcls_power_reset();
    dcls_quiet();
endtask

task automatic dcls_control_scenario;
    dcls_set_enable(0);
    dcls_quiet();
    dcls_start_fault(0);
    dcls_observe_fault(0);
    dcls_quiet();
    dcls_release_faults();
    dcls_set_enable(1);
    dcls_quiet();
    dcls_set_enable(0);
    dcls_start_fault(0);
    dcls_observe_fault(0);
    dcls_quiet();
    dcls_set_enable(1); // A mismatch still present when enabling must report.
    dcls_wait_fatal();
    dcls_release_faults();
    dcls_set_enable(0);
    dcls_check_status(1, 1);
    dcls_clear_status(1);
    dcls_power_reset();
    repeat (3) begin
        dcls_set_enable(1); dcls_quiet();
        dcls_set_enable(0); dcls_quiet();
    end
endtask

task automatic dcls_qualifications_scenario;
    int unsigned previous_boot;
    dcls_set_enable(1);
    dcls_debug_enter();
    dcls_start_fault(0); dcls_observe_fault(0); dcls_quiet(); dcls_release_faults();
    dcls_debug_exit();
    dcls_start_fault(0); dcls_observe_fault(0); dcls_quiet(); dcls_release_faults();
    dcls_set_enable(0); dcls_set_enable(1);
    dcls_start_fault(0); dcls_observe_fault(0); dcls_quiet(); dcls_release_faults();
    dcls_core_reset(0, 0);
    dcls_start_fault(0); dcls_observe_fault(0); dcls_wait_fatal();
    dcls_power_reset();

    // Invalid MuBi bypasses enable and debug suppression.
    dcls_set_enable(0);
    dcls_invalid_disable(); dcls_wait_fatal(); dcls_power_reset();
    dcls_set_enable(1);
    dcls_debug_enter(); dcls_debug_exit();
    dcls_set_enable(0);
    dcls_invalid_disable(); dcls_wait_fatal(); dcls_power_reset();

    // Keep reporting enabled to isolate reset qualification.
    dcls_set_enable(1);
    previous_boot = dcls_boot_count;
    @(negedge core_clk);
    force `CPTRA_TOP_PATH.soc_ifc_top1.i_soc_ifc_boot_fsm.fw_update_rst_wait_cycles = 8'hff;
    force `CPTRA_TOP_PATH.soc_ifc_top1.i_soc_ifc_boot_fsm.fw_update_rst = 1'b1;
    begin : wait_core_qualification_reset
        bit seen = 0;
        for (int i = 0; i < DCLS_STEP_TIMEOUT; i++) begin
            @(negedge core_clk);
            if (!`DCLS_LS.rst_n) begin seen = 1; break; end
        end
        if (!seen) $fatal(1, "DCLS: core/shadow reset did not assert");
    end
    release `CPTRA_TOP_PATH.soc_ifc_top1.i_soc_ifc_boot_fsm.fw_update_rst;
    dcls_check_config(1);
    dcls_start_fault(0); dcls_observe_fault(0);
    repeat (32) begin
        @(negedge core_clk);
        if (`DCLS_LS.rst_n !== 0 ||
            `DCLS_LS.disable_corruption_detection_i !== el2_mubi_pkg::El2MuBiFalse ||
            !el2_mubi_pkg::mubi_check_false(`DCLS_LS.corruption_detected_o) || cptra_error_fatal)
            $fatal(1, "DCLS: enabled normal mismatch escaped core-reset qualification");
    end
    dcls_invalid_disable();
    repeat (32) begin
        @(negedge core_clk);
        if (`DCLS_LS.rst_n !== 0 ||
            !el2_mubi_pkg::mubi_check_false(`DCLS_LS.corruption_detected_o) || cptra_error_fatal)
            $fatal(1, "DCLS: invalid MuBi disable escaped reset qualification");
    end
    dcls_release_faults();
    release `CPTRA_TOP_PATH.soc_ifc_top1.i_soc_ifc_boot_fsm.fw_update_rst_wait_cycles;
    dcls_wait_boot(previous_boot);
    dcls_check_status(0, 0);
    dcls_quiet();
endtask

initial begin : directed_dcls_controller
    if ($test$plusargs("CALIPTRA_TEST_DCLS")) begin
        if (!$value$plusargs("DCLS_SCENARIO=%s", dcls_scenario) ||
            !(dcls_scenario inside {"outputs", "regfile", "control", "qualifications"}))
            $fatal(1, "DCLS: require DCLS_SCENARIO=outputs|regfile|control|qualifications");
        dcls_wait_boot(0);
        dcls_check_config(1);
        dcls_quiet();
        case (dcls_scenario)
            "outputs": dcls_outputs_scenario();
            "regfile": dcls_regfile_scenario();
            "control": dcls_control_scenario();
            "qualifications": dcls_qualifications_scenario();
        endcase
        dcls_release_faults();
        $display("DCLS: scenario=%s profile=%s completed", dcls_scenario,
`ifdef CALIPTRA_MODE_SUBSYSTEM
                 "subsystem");
`else
                 "passive");
`endif
        $display("* TESTCASE PASSED");
        $finish;
    end
end
initial begin : directed_dcls_timeout
    if ($test$plusargs("CALIPTRA_TEST_DCLS")) begin
        repeat (2000000) @(negedge core_clk);
        $fatal(1, "DCLS: overall test timeout");
    end
end
`undef DCLS_SHADOW_GPR
`undef DCLS_LS
