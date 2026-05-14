# Caliptra Pre-release Feature Test Plan

This document tracks test coverage for features under development, planned for a future release.

---

## Key Vault Boot Flow Transition Enforcement

### Feature Summary

Hardware-enforced DICE key integrity monitoring and slot access control across ROM->FMC->RT boot phase transitions. Comprises a boot flow monitor (ICCM fetch detection), KV monitor (dest_valid/write count validation), KV enforcement (lock/clear), DOE lockdown, and ICCM region shadow registers with SoC write protection.

### Test Suite

| Test | Category | Description |
| :--- | :------- | :---------- |
| `smoke/kv_boot_flow_monitor` | Smoke | Full DICE derivation through cold boot, warm reset, and FW update reset cycles |
| `directed/kv_enforcement` | Directed | Verifies lock_wr, lock_use, slot clearing, DOE lockdown, and ROM callback behavior |
| `directed/kv_iccm_region` | Directed | ICCM region register programming, locking, reset behavior, and shadow negative cases |
| `directed/kv_monitor_neg` | Directed | Deliberate faults in dest_valid and write counts trigger monitor alerts |

### Test Cases

#### `smoke/kv_boot_flow_monitor`

| Scenario | Description | Pass Criteria |
| :------- | :---------- | :------------ |
| Cold boot happy path | Full DICE derivation (DOE, HMAC, ECC, MLDSA), program ICCM regions, jump to FMC then RT | No kv_error; FMC/RT execute successfully |
| Warm reset cycle | After RT, warm reset triggers re-derivation of all DICE keys | Monitor re-arms; transitions succeed again |
| FW update reset | FW update reset preserves ICCM region registers; ROM skips re-derivation | ICCM lock persists; boot flow succeeds |

#### `directed/kv_enforcement`

| Scenario | Phase | Description | Pass Criteria |
| :------- | :---- | :---------- | :------------ |
| lock_wr prevents overwrite | FMC | HMAC write to locked slot 0 (UDS) | Write has no effect; dest_valid unchanged |
| Cleared slots empty | FMC | Read dest_valid of slots 3,4,5,9 | All return 0 |
| ROM callback no re-trigger | FMC | FMC calls ROM-resident function and returns | No kv_error; boot_flow_fmc stays True |
| DOE lockdown (FMC) | FMC | Issue DOE command after FMC entry | Command rejected; DOE not busy |
| lock_wr prevents overwrite | RT | HMAC write to locked slot 4 (RT_CDI) | Write has no effect |
| lock_use prevents read | RT | Read slot 6 (FMC_CDI) as HMAC key | KV read fails with error |
| DOE lockdown (RT) | RT | Issue DOE command after RT entry | Command rejected |
| Counter stable on lock_wr write | FMC | Set lock_wr on slot 6, then issue crypto write to slot 6 | write_count_fmc_cdi unchanged; key data unchanged |
| Counter stable on lock_use write | RT | Set lock_use on slot 7, then issue crypto write to slot 7 | write_count_fmc_ecdsa unchanged |
| Counter stable on locked slot (both) | FMC | Set lock_wr and lock_use on slot 8, then issue crypto write | write_count_fmc_mldsa unchanged |
| Counter clears on flush | ROM | Write to slot 6 (count=1), then trigger debug unlock (flush) | write_count_fmc_cdi returns to 0 |
| Counter clears on scan mode | ROM | Write to slots 6,7,8, then enter scan mode | All 3 counters return to 0 |
| Counter no increment during clear | ROM | Issue key_entry_clear on slot 6 simultaneously with crypto write | write_count_fmc_cdi unchanged; slot cleared |

#### `directed/kv_iccm_region`

| Iter | Description | Pass Criteria |
| :--- | :---------- | :------------ |
| 0 | Program regions, lock, verify readback, attempt overwrite after lock | Overwrite blocked; lock=1 persists |
| 1 | Warm reset -- verify all registers and lock clear to 0 | All read back as 0 |
| 2 | FW update reset -- verify registers and lock persist | Values unchanged after reset |
| 3 | ICCM fetch with lock=0 -- jump to ICCM without setting lock | boot_flow_error fires; kv_error set |
| 4 | Lock without programming addresses (all=0), FMC entry at nonzero addr | boot_flow_error fires (out-of-range) |
| 5 | Single write only (no commit) -- shadow phase stays 0 | iccm_all_shadows_committed=0; effective lock=0 |
| 6 | Mismatched 2-phase write -- different values for phase 0 and phase 1 | shadow_update_err (NON_FATAL[3]) fires |
| 7 | SoC write attempt -- write ICCM region register from SoC interface | Write rejected; register value unchanged |
| 8 | SoC write to iccm_region_lock -- attempt to set lock from SoC | Write rejected (swwel=soc_req); lock remains 0 |
| 9 | Out-of-range ICCM fetch after lock -- jump to address outside both FMC and RT regions | boot_flow_error fires; kv_error set |

#### `directed/kv_monitor_neg`

| Iter | Fault Injected | Pass Criteria |
| :--- | :------------- | :------------ |
| 0 | Skip slot 0 (UDS) -- leave empty | kv_error fires at FMC transition |
| 1 | Slot 0 wrong dest_valid (HMAC_KEY instead of AES_KEY) | kv_error fires at FMC transition |
| 2 | Skip slot 6 (FMC_CDI) -- leave empty | kv_error fires at FMC transition |
| 3 | Slot 2 (Key Ladder) wrong dest_valid (AES_KEY instead of HMAC_KEY) | kv_error fires at FMC transition |
| 4 | Skip slot 4 (RT_CDI) for RT transition | kv_error fires at RT transition |
| 5 | Slot 9 (RT_MLDSA) wrong dest_valid at RT transition | kv_error fires at RT transition |
| 6 | Slot 7 write count=1 (skip FMC Alias ECC keygen) | kv_error fires at FMC transition |
| 7 | Slot 8 write count=1 (skip FMC Alias MLDSA keygen) | kv_error fires at FMC transition |

### SVA Assertions

31 assertions in `src/integration/asserts/kv_boot_flow_sva.sv`:

| Category | Count | Coverage |
| :------- | :---- | :------- |
| Enforcement timing (lock_wr) | 9 | One per DICE slot locked at FMC/RT |
| Enforcement timing (lock_use) | 3 | FMC slots locked for use at RT |
| Slot clearing | 6 | Correct slots cleared at each transition |
| Error chain | 2 | kv_error -> CPTRA_HW_ERROR_FATAL propagation |
| Monotonicity | 3 | boot_flow_fmc/rt non-regression, layer ordering |
| DOE lockdown | 2 | DOE_CTRL.CMD cleared in FMC and RT |
| Write counters | 4 | Increment, saturation, hard-reset clear, flush clear |
| ICCM region | 2 | Fetch-without-lock -> error, W1S sticky lock |

### Coverage Gaps (Not Yet Implemented)

| Area | Description | Priority |
| :--- | :---------- | :------- |
| SoC write rejection | Directed test exercising SoC AXI writes to ICCM region registers (iters 7-8 above) | High |
| Warm reset happy path | Dedicated test for warm reset -> full re-derivation -> monitor re-arms | Medium |
| Glitch injection | Force MuBi4 invalid encoding on boot_flow signals | Low |
| Multi-error interaction | boot_flow_error + kv_multi_write_err simultaneously | Low |
| Shadow storage fault injection | Force bit-flip in shadow register to trigger err_storage lockout | Medium |
| FW update reset with active monitor | Verify monitor state after FW update reset (region regs persist, boot_flow clears) | Medium |

### Covergroups

Location: `src/keyvault/coverage/kv_boot_flow_cov.sv` (KV-side) and `src/soc_ifc/coverage/soc_ifc_iccm_shadow_cov.sv` (shadow regs)

Covergroups with crosses provide combinatorial coverage of the slot × transition × action state space. These complement the temporal cover properties in `kv_boot_flow_sva.sv`.

| Covergroup | File | Sample Event | Key Crosses | Purpose |
| :--------- | :--- | :----------- | :---------- | :------ |
| `cg_enforcement_action` | `kv_boot_flow_cov.sv` | `enter_fmc`, `enter_rt` | transition × lock_wr_count, lock_use_count, cleared_count, alert | Enforcement combos exercised per transition |
| `cg_monitor_check` | `kv_boot_flow_cov.sv` | `enter_fmc`, `enter_rt` | transition × pass/fail | Monitor validation at both boundaries |
| `cg_error_escalation` | `kv_boot_flow_cov.sv` | Rising edge of any error | error_source × boot_phase | Correct escalation per error type per phase |
| `cg_write_counter` | `kv_boot_flow_cov.sv` | Crypto write to slots 6,7,8 | slot × count_value, slot × boot_phase | Counter progression per slot |
| `cg_iccm_shadow_reg` | `soc_ifc_iccm_shadow_cov.sv` | Shadow reg write/read strobe | register × operation, operation × committed, operation × err_update/err_storage, register × locked | All registers through all operation/error paths |

### Security Enforcement

| Mechanism | RTL Location | Description |
| :-------- | :----------- | :---------- |
| SoC write rejection (ICCM regs) | `soc_ifc_top.sv` line 1109-1112 | `iccm_shadow_we` gated by `~soc_ifc_reg_req_data.soc_req` -- external registers reject SoC writes |
| SoC write rejection (region lock) | `soc_ifc_internal_reg.rdl` | `swwel = soc_req` on `internal_iccm_region_lock.lock` field |
| Shadow 2-phase protocol | `caliptra_prim_subreg_shadow` | Requires two identical writes to commit; mismatched second write sets CPTRA_HW_ERROR_NON_FATAL.shadow_update_err[3] |
| Shadow storage fault detection | `caliptra_prim_subreg_shadow` | Continuous background comparison of primary/shadow copy sets CPTRA_HW_ERROR_FATAL.shadow_storage_err[5] on mismatch |
| Region lock (post-commit) | `soc_ifc_top.sv` | `iccm_shadow_we` gated by `~iccm_region_lock` -- no writes after ROM locks |

### Regression

- `src/integration/stimulus/L0_regression.yml` -- smoke/kv_boot_flow_monitor
- `src/integration/stimulus/testsuites/caliptra_top_nightly_directed_regression.yml` -- all 4 tests
