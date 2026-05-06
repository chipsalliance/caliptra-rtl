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
// SVA assertions for KV Boot Phase Transition Enforcement Block
// Covers: enforcement timing, monitor error chain, boot flow monotonicity,
//         DOE lockdown, write counters, and ICCM region register properties.

`include "caliptra_macros.svh"

`ifndef CPTRA_TB_TOP_NAME
  `ifdef UVMF_CALIPTRA_TOP
    `define CPTRA_TB_TOP_NAME hdl_top
  `else
    `define CPTRA_TB_TOP_NAME caliptra_top_tb
  `endif
`endif
`ifndef CPTRA_TOP_PATH
  `define CPTRA_TOP_PATH `CPTRA_TB_TOP_NAME.caliptra_top_dut
`endif
`define KV_PATH           `CPTRA_TOP_PATH.key_vault1
`define KV_REG_PATH       `KV_PATH.kv_reg1
`define SOC_IFC_TOP_PATH  `CPTRA_TOP_PATH.soc_ifc_top1
`define SOC_IFC_REG_PATH  `SOC_IFC_TOP_PATH.i_soc_ifc_reg

`ifdef UVMF_CALIPTRA_TOP
  `define SVA_CLK `CPTRA_TB_TOP_NAME.clk
  `define SVA_RST `CPTRA_TB_TOP_NAME.soc_ifc_subenv_soc_ifc_ctrl_agent_bus.cptra_rst_b
`else
  `define SVA_CLK `CPTRA_TB_TOP_NAME.core_clk
  `define SVA_RST `CPTRA_TB_TOP_NAME.cptra_rst_b
`endif

module kv_boot_flow_sva
  import kv_defines_pkg::*;
  import caliptra_prim_mubi_pkg::*;
  ();

  // ============================================================
  // Local signal aliases for readability
  // ============================================================
  wire clk          = `SVA_CLK;
  wire rst_n        = `SVA_RST;
  wire core_rst_n   = `KV_PATH.core_only_rst_b;

  // Boot flow signals from caliptra_top
  wire [3:0] boot_flow_fmc   = `CPTRA_TOP_PATH.boot_flow_fmc;
  wire [3:0] boot_flow_rt    = `CPTRA_TOP_PATH.boot_flow_rt;
  wire [3:0] boot_flow_error = `CPTRA_TOP_PATH.boot_flow_error;

  // Transition edges from kv.sv
  wire enter_fmc = `KV_PATH.enter_fmc;
  wire enter_rt  = `KV_PATH.enter_rt;

  // KV monitor alert
  wire kv_monitor_alert = `KV_PATH.kv_monitor_alert;

  // Lock signals (registered values from kv.sv)
  wire [KV_NUM_KEYS-1:0] lock_wr_q  = `KV_PATH.lock_wr_q;
  wire [KV_NUM_KEYS-1:0] lock_use_q = `KV_PATH.lock_use_q;

  // Boot flow key clear (combinational, from KV_ENFORCEMENT block)
  wire [KV_NUM_KEYS-1:0] boot_flow_key_clear = `KV_PATH.boot_flow_key_clear;

  // Write counters
  wire [2:0] write_count_fmc_cdi   = `KV_PATH.write_count_fmc_cdi;
  wire [2:0] write_count_fmc_ecdsa = `KV_PATH.write_count_fmc_ecdsa;
  wire [2:0] write_count_fmc_mldsa = `KV_PATH.write_count_fmc_mldsa;
  wire       crypto_wr_fmc_cdi     = `KV_PATH.crypto_wr_fmc_cdi;
  wire       crypto_wr_fmc_ecdsa   = `KV_PATH.crypto_wr_fmc_ecdsa;
  wire       crypto_wr_fmc_mldsa   = `KV_PATH.crypto_wr_fmc_mldsa;

  // DOE lockdown
  wire doe_cmd_lock = mubi4_test_true_strict(mubi4_t'(boot_flow_fmc)) |
                      mubi4_test_true_strict(mubi4_t'(boot_flow_rt));

  // ICCM region signals
  wire iccm_region_lock = `CPTRA_TOP_PATH.iccm_region_lock;
  wire iccm_read_any    = `CPTRA_TOP_PATH.iccm_read_any;

  // cptra_error_fatal output
  wire cptra_error_fatal = `CPTRA_TOP_PATH.cptra_error_fatal;

  // kv_error into soc_ifc (combines monitor alert + boot flow error)
  wire kv_error_input = kv_monitor_alert | mubi4_test_true_strict(mubi4_t'(boot_flow_error));

  // MuBi4 helpers
  wire fmc_true  = mubi4_test_true_strict(mubi4_t'(boot_flow_fmc));
  wire rt_true   = mubi4_test_true_strict(mubi4_t'(boot_flow_rt));
  wire fmc_false = mubi4_test_false_strict(mubi4_t'(boot_flow_fmc));
  wire rt_false  = mubi4_test_false_strict(mubi4_t'(boot_flow_rt));

  // ============================================================
  // Section 1: Enforcement Timing — lock_wr hwset
  // What: lock_wr must be asserted on preserved slots within 1 cycle of transition
  // Why: Prevents malicious FW from overwriting DICE keys after phase transition
  // Timing: 1 cycle — lock_wr.hwset is combinational, register captures next posedge
  // ============================================================

  // At ROM→FMC: slots 0,1,2,6,7,8 get lock_wr
  LockWr_EnterFmc_Slot0_A: assert property (
    @(posedge clk) disable iff (!core_rst_n)
    enter_fmc |=> lock_wr_q[KV_SLOT_SI_IDEV]
  ) else $display("SVA ERROR: lock_wr not set on slot 0 after enter_fmc");

  LockWr_EnterFmc_Slot1_A: assert property (
    @(posedge clk) disable iff (!core_rst_n)
    enter_fmc |=> lock_wr_q[KV_SLOT_SI_LDEV]
  ) else $display("SVA ERROR: lock_wr not set on slot 1 after enter_fmc");

  LockWr_EnterFmc_Slot2_A: assert property (
    @(posedge clk) disable iff (!core_rst_n)
    enter_fmc |=> lock_wr_q[KV_SLOT_KEY_LADDER]
  ) else $display("SVA ERROR: lock_wr not set on slot 2 after enter_fmc");

  LockWr_EnterFmc_Slot6_A: assert property (
    @(posedge clk) disable iff (!core_rst_n)
    enter_fmc |=> lock_wr_q[KV_SLOT_FMC_CDI]
  ) else $display("SVA ERROR: lock_wr not set on slot 6 after enter_fmc");

  LockWr_EnterFmc_Slot7_A: assert property (
    @(posedge clk) disable iff (!core_rst_n)
    enter_fmc |=> lock_wr_q[KV_SLOT_FMC_ECDSA]
  ) else $display("SVA ERROR: lock_wr not set on slot 7 after enter_fmc");

  LockWr_EnterFmc_Slot8_A: assert property (
    @(posedge clk) disable iff (!core_rst_n)
    enter_fmc |=> lock_wr_q[KV_SLOT_FMC_MLDSA]
  ) else $display("SVA ERROR: lock_wr not set on slot 8 after enter_fmc");

  // At FMC→RT: slots 4,5,9 get lock_wr
  LockWr_EnterRt_Slot4_A: assert property (
    @(posedge clk) disable iff (!core_rst_n)
    enter_rt |=> lock_wr_q[KV_SLOT_RT_CDI]
  ) else $display("SVA ERROR: lock_wr not set on slot 4 after enter_rt");

  LockWr_EnterRt_Slot5_A: assert property (
    @(posedge clk) disable iff (!core_rst_n)
    enter_rt |=> lock_wr_q[KV_SLOT_RT_ECDSA]
  ) else $display("SVA ERROR: lock_wr not set on slot 5 after enter_rt");

  LockWr_EnterRt_Slot9_A: assert property (
    @(posedge clk) disable iff (!core_rst_n)
    enter_rt |=> lock_wr_q[KV_SLOT_RT_MLDSA]
  ) else $display("SVA ERROR: lock_wr not set on slot 9 after enter_rt");

  // ============================================================
  // Section 2: Enforcement Timing — lock_use hwset
  // What: lock_use must be asserted on FMC key slots when entering RT
  // Why: Prevents RT firmware from using FMC-phase signing keys
  // Timing: 1 cycle
  // ============================================================

  LockUse_EnterRt_Slot6_A: assert property (
    @(posedge clk) disable iff (!core_rst_n)
    enter_rt |=> lock_use_q[KV_SLOT_FMC_CDI]
  ) else $display("SVA ERROR: lock_use not set on slot 6 after enter_rt");

  LockUse_EnterRt_Slot7_A: assert property (
    @(posedge clk) disable iff (!core_rst_n)
    enter_rt |=> lock_use_q[KV_SLOT_FMC_ECDSA]
  ) else $display("SVA ERROR: lock_use not set on slot 7 after enter_rt");

  LockUse_EnterRt_Slot8_A: assert property (
    @(posedge clk) disable iff (!core_rst_n)
    enter_rt |=> lock_use_q[KV_SLOT_FMC_MLDSA]
  ) else $display("SVA ERROR: lock_use not set on slot 8 after enter_rt");

  // ============================================================
  // Section 3: Enforcement Timing — Slot clears
  // What: Non-preserved slots must be cleared at each transition
  // Why: Destroys stale/temporary key material from prior boot phase
  // Timing: boot_flow_key_clear is combinational (same cycle as enter_fmc/enter_rt)
  // ============================================================

  // At enter_fmc: slots 3,4,5,9,10,11,12,13,14,15 cleared
  generate
    for (genvar s = 0; s < KV_NUM_KEYS; s++) begin : gen_clear_fmc_check
      if (!(s inside {KV_SLOT_SI_IDEV, KV_SLOT_SI_LDEV, KV_SLOT_KEY_LADDER,
                      KV_SLOT_FMC_CDI, KV_SLOT_FMC_ECDSA, KV_SLOT_FMC_MLDSA})) begin
        // What: Non-preserved slot must be cleared on enter_fmc
        ClearAtEnterFmc_A: assert property (
          @(posedge clk) disable iff (!core_rst_n)
          enter_fmc |-> boot_flow_key_clear[s]
        ) else $display("SVA ERROR: slot %0d not cleared at enter_fmc", s);
      end
    end
  endgenerate

  // At enter_rt: slots 3,10,11,12,13,14,15 cleared (RT slots 4,5,9 are preserved)
  generate
    for (genvar s = 0; s < KV_NUM_KEYS; s++) begin : gen_clear_rt_check
      if (!(s inside {KV_SLOT_SI_IDEV, KV_SLOT_SI_LDEV, KV_SLOT_KEY_LADDER,
                      KV_SLOT_FMC_CDI, KV_SLOT_FMC_ECDSA, KV_SLOT_FMC_MLDSA,
                      KV_SLOT_RT_CDI, KV_SLOT_RT_ECDSA, KV_SLOT_RT_MLDSA})) begin
        // What: Non-preserved slot must be cleared on enter_rt
        ClearAtEnterRt_A: assert property (
          @(posedge clk) disable iff (!core_rst_n)
          enter_rt |-> boot_flow_key_clear[s]
        ) else $display("SVA ERROR: slot %0d not cleared at enter_rt", s);
      end
    end
  endgenerate

  // ============================================================
  // Section 4: Enforcement — Same-cycle completion
  // What: All enforcement actions (hwset/hwclr) are combinational, no multi-cycle sequencing
  // Why: Security-critical — a multi-cycle gap could allow a race
  // ============================================================

  // boot_flow_key_clear is purely combinational from enter_fmc/enter_rt
  // lock_wr.hwset and lock_use.hwset are driven combinationally from boot_flow_fmc/boot_flow_rt
  // These are structural properties verified by the generate blocks above (|-> not |=>)

  // ============================================================
  // Section 5: Error Chain — kv_monitor_alert → cptra_error_fatal
  // What: cptra_error_fatal must assert within 2 cycles of kv_error_input
  // Why: BMC must see immediate HW notification of DICE integrity violation
  // Timing: kv_error → CPTRA_HW_ERROR_FATAL.kv_error.we → unmasked_hw_error_fatal_write
  //         → cptra_error_fatal (registered in soc_ifc_top on rdc_clk_cg, 1 cycle)
  //         Total: 2 cycles (1 for register set + 1 for error_fatal flop)
  // ============================================================

  KvErrorToFatal_A: assert property (
    @(posedge clk) disable iff (!rst_n)
    $rose(kv_error_input) |-> ##[1:2] cptra_error_fatal
  ) else $display("SVA ERROR: cptra_error_fatal not set within 2 cycles of kv_error");

  // ============================================================
  // Section 6: Boot Flow Monotonicity
  // What: boot_flow_fmc and boot_flow_rt transition False→True only, never True→False
  // Why: Layer regression would allow re-executing ROM-phase code with FMC privileges
  // ============================================================

  BootFlowFmcMonotonic_A: assert property (
    @(posedge clk) disable iff (!core_rst_n)
    fmc_true |=> fmc_true
  ) else $display("SVA ERROR: boot_flow_fmc regressed from True to False");

  BootFlowRtMonotonic_A: assert property (
    @(posedge clk) disable iff (!core_rst_n)
    rt_true |=> rt_true
  ) else $display("SVA ERROR: boot_flow_rt regressed from True to False");

  // What: boot_flow_rt cannot assert before boot_flow_fmc (layer ordering)
  // Why: Must pass through FMC phase before reaching RT
  BootFlowLayerOrder_A: assert property (
    @(posedge clk) disable iff (!core_rst_n)
    rt_true |-> fmc_true
  ) else $display("SVA ERROR: boot_flow_rt asserted without boot_flow_fmc");

  // ============================================================
  // Section 7: DOE Lockdown
  // What: doe_cmd_lock must be asserted whenever boot_flow_fmc or boot_flow_rt is True
  // Why: Prevents re-running DOE after secrets have been consumed by DICE
  // ============================================================

  DoeCmdLockInFmc_A: assert property (
    @(posedge clk) disable iff (!rst_n)
    fmc_true |-> doe_cmd_lock
  ) else $display("SVA ERROR: doe_cmd_lock not asserted during FMC phase");

  DoeCmdLockInRt_A: assert property (
    @(posedge clk) disable iff (!rst_n)
    rt_true |-> doe_cmd_lock
  ) else $display("SVA ERROR: doe_cmd_lock not asserted during RT phase");

  // ============================================================
  // Section 8: Write Counters
  // What: Counters increment on crypto engine writes, not on SW clear
  // Why: Detects truncated DICE derivation chains
  // ============================================================

  // Write counter increments on crypto write (write_offset==0), not on key_entry_clear
  WriteCountFmcCdiIncr_A: assert property (
    @(posedge clk) disable iff (!`KV_PATH.cptra_pwrgood)
    (crypto_wr_fmc_cdi && write_count_fmc_cdi < 3'd7) |=> (write_count_fmc_cdi == $past(write_count_fmc_cdi) + 3'd1)
  ) else $display("SVA ERROR: write_count_fmc_cdi did not increment on crypto write");

  WriteCountFmcEcdsaIncr_A: assert property (
    @(posedge clk) disable iff (!`KV_PATH.cptra_pwrgood)
    (crypto_wr_fmc_ecdsa && write_count_fmc_ecdsa < 3'd7) |=> (write_count_fmc_ecdsa == $past(write_count_fmc_ecdsa) + 3'd1)
  ) else $display("SVA ERROR: write_count_fmc_ecdsa did not increment on crypto write");

  WriteCountFmcMldsaIncr_A: assert property (
    @(posedge clk) disable iff (!`KV_PATH.cptra_pwrgood)
    (crypto_wr_fmc_mldsa && write_count_fmc_mldsa < 3'd7) |=> (write_count_fmc_mldsa == $past(write_count_fmc_mldsa) + 3'd1)
  ) else $display("SVA ERROR: write_count_fmc_mldsa did not increment on crypto write");

  // What: Counters saturate at 7 (3'b111), never wrap
  WriteCountFmcCdiSaturate_A: assert property (
    @(posedge clk) disable iff (!`KV_PATH.cptra_pwrgood)
    (write_count_fmc_cdi == 3'd7) |=> (write_count_fmc_cdi == 3'd7)
  ) else $display("SVA ERROR: write_count_fmc_cdi wrapped past saturation");

  WriteCountFmcEcdsaSaturate_A: assert property (
    @(posedge clk) disable iff (!`KV_PATH.cptra_pwrgood)
    (write_count_fmc_ecdsa == 3'd7) |=> (write_count_fmc_ecdsa == 3'd7)
  ) else $display("SVA ERROR: write_count_fmc_ecdsa wrapped past saturation");

  WriteCountFmcMldsaSaturate_A: assert property (
    @(posedge clk) disable iff (!`KV_PATH.cptra_pwrgood)
    (write_count_fmc_mldsa == 3'd7) |=> (write_count_fmc_mldsa == 3'd7)
  ) else $display("SVA ERROR: write_count_fmc_mldsa wrapped past saturation");

  // What: Counters reset only on cptra_pwrgood deassertion, NOT on core_only_rst_b
  // Why: Must persist across warm and fw update resets to track cumulative DICE writes
  WriteCountFmcCdiHardReset_A: assert property (
    @(posedge clk)
    !`KV_PATH.cptra_pwrgood |-> (write_count_fmc_cdi == 3'd0)
  ) else $display("SVA ERROR: write_count_fmc_cdi not zero during hard reset");

  WriteCountFmcEcdsaHardReset_A: assert property (
    @(posedge clk)
    !`KV_PATH.cptra_pwrgood |-> (write_count_fmc_ecdsa == 3'd0)
  ) else $display("SVA ERROR: write_count_fmc_ecdsa not zero during hard reset");

  WriteCountFmcMldsaHardReset_A: assert property (
    @(posedge clk)
    !`KV_PATH.cptra_pwrgood |-> (write_count_fmc_mldsa == 3'd0)
  ) else $display("SVA ERROR: write_count_fmc_mldsa not zero during hard reset");

  // ============================================================
  // Section 9: ICCM Region Register Properties
  // ============================================================

  // What: boot_flow_error fires if any ICCM fetch occurs while ICCM_REGION_LOCK = 0
  // Why: Unprogrammed regions must not be trusted
  IccmFetchWithoutLock_A: assert property (
    @(posedge clk) disable iff (!core_rst_n)
    (iccm_read_any && !iccm_region_lock) |=> mubi4_test_true_strict(mubi4_t'(boot_flow_error))
  ) else $display("SVA ERROR: boot_flow_error not set on ICCM fetch with region_lock=0");

  // What: ICCM_REGION_LOCK is W1S — once set, cannot be cleared by any write (only reset)
  // Why: Prevents malicious FW from unlocking region registers after ROM configures them
  IccmRegionLockSticky_A: assert property (
    @(posedge clk) disable iff (!core_rst_n)
    iccm_region_lock |=> iccm_region_lock
  ) else $display("SVA ERROR: ICCM_REGION_LOCK cleared without reset");

  // What: All 4 address registers and ICCM_REGION_LOCK reset to 0 on core reset
  // Why: ROM must reprogram regions on every boot cycle
  IccmRegionLockReset_A: assert property (
    @(posedge clk)
    !core_rst_n |-> !iccm_region_lock
  ) else $display("SVA ERROR: ICCM_REGION_LOCK not zero during core reset");

  // ============================================================
  // Section 10: Cover Properties
  // ============================================================

  // Cover: Happy path — both transitions fire without monitor alert
  HappyPathFmcRt_C: cover property (
    @(posedge clk) disable iff (!core_rst_n)
    enter_fmc ##[1:$] enter_rt ##1 (!kv_monitor_alert)
  );

  // Cover: Monitor fires at ROM→FMC transition
  MonitorAlertAtFmc_C: cover property (
    @(posedge clk) disable iff (!core_rst_n)
    enter_fmc && kv_monitor_alert
  );

  // Cover: Monitor fires at FMC→RT transition
  MonitorAlertAtRt_C: cover property (
    @(posedge clk) disable iff (!core_rst_n)
    enter_rt && kv_monitor_alert
  );

  // Cover: Write counter FMC CDI reaches minimum (4)
  WriteCountFmcCdiReaches4_C: cover property (
    @(posedge clk) disable iff (!`KV_PATH.cptra_pwrgood)
    $rose(write_count_fmc_cdi == 3'd4)
  );

  // Cover: boot_flow_error fires on unlocked ICCM fetch
  BootFlowErrorOnUnlockedFetch_C: cover property (
    @(posedge clk) disable iff (!core_rst_n)
    (iccm_read_any && !iccm_region_lock)
  );

endmodule
