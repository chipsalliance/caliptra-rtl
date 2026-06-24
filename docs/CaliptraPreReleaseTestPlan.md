# Caliptra Pre-release Feature Test Plan

This document tracks test coverage for features under development, planned for a future release.

---

## Key Vault Boot Flow Transition Enforcement

### Feature Summary

Hardware-enforced DICE key integrity monitoring and slot access control across ROM->FMC->RT boot phase transitions. Comprises a boot flow monitor (ICCM fetch detection), KV monitor (dest_valid/write count validation), KV enforcement (lock/clear), DOE lockdown, and ICCM region shadow registers with SoC write protection.

### Test Suite

| Test | Category | Description |
| :--- | :------- | :---------- |
| `smoke_test_kv_boot_flow_monitor` | Smoke | Full DICE derivation through cold boot, warm reset, and FW update reset cycles |
| `directed_kv_enforcement` | Directed | Verifies lock_wr, lock_use, slot clearing, DOE lockdown, and ROM callback behavior |
| `directed_kv_iccm_region` | Directed | ICCM region register programming, locking, reset behavior, and shadow negative cases |
| `directed_kv_monitor_neg` | Directed | Deliberate faults in dest_valid and write counts trigger monitor alerts |
| `directed_kv_debug_scan_bypass` | Directed | Verifies monitor is disabled in debug unlock and scan mode (no false alerts) |
| `directed_kv_glitch_inject` | Directed | MuBi4 invalid encoding fail-safe and shadow register bit-flip lockout |

### Test Cases

#### `smoke_test_kv_boot_flow_monitor`

| Scenario | Description | Pass Criteria |
| :------- | :---------- | :------------ |
| Cold boot happy path | Full DICE derivation (DOE, HMAC, ECC, MLDSA), program ICCM regions, jump to FMC then RT | No kv_error; FMC/RT execute successfully |
| Warm reset cycle | After RT, warm reset triggers re-derivation of all DICE keys | Monitor re-arms; transitions succeed again |
| FW update reset | FW update reset preserves ICCM region registers; ROM skips re-derivation | ICCM lock persists; boot flow succeeds |

#### `directed_kv_enforcement`

| Scenario | Phase | Description | Pass Criteria |
| :------- | :---- | :---------- | :------------ |
| lock_wr prevents overwrite | FMC | HMAC write to locked slot 0 (UDS) | Write has no effect; dest_valid unchanged |
| Cleared slots empty | FMC | Read dest_valid of slots 3,4,5,9 | All return 0 |
| ROM callback no re-trigger | FMC | FMC calls ROM-resident function and returns | No kv_error; boot_flow_fmc stays True |
| DOE lockdown (FMC) | FMC | Issue DOE command after FMC entry | Command rejected; DOE not busy |
| Counter stable on lock_wr (slot 6) | FMC | Crypto write to lock_wr'd slot 6 | write_count_fmc_cdi unchanged (SVA + no kv_error at RT) |
| Counter stable on lock_wr (slot 8) | FMC | Crypto write to lock_wr'd slot 8 | write_count_fmc_mldsa unchanged (SVA + no kv_error at RT) |
| lock_wr prevents overwrite | RT | HMAC write to locked slot 4 (RT_CDI) | Write has no effect |
| lock_use prevents read | RT | Read slot 6 (FMC_CDI) as HMAC key | KV read fails with error |
| Counter stable on lock_use (slot 7) | RT | Crypto write to lock_use'd slot 7 | write_count_fmc_ecdsa unchanged (SVA) |
| DOE lockdown (RT) | RT | Issue DOE command after RT entry | Command rejected |


#### `directed_kv_iccm_region`

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

#### `directed_kv_monitor_neg`

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

#### `directed_kv_debug_scan_bypass`

| Iter | Description | Pass Criteria |
| :--- | :---------- | :------------ |
| 0 | Happy path DICE derivation + FMC jump, then debug unlock + warm reset | Normal FMC transition succeeds; debug unlock propagates on warm reset |
| 1 | Boot with debug_locked=0 (from iter 0), DICE derivation + FMC jump | No kv_fault (monitor disabled in debug mode) |
| 2 | Re-locked debug, DICE derivation, enter scan mode, FMC jump | No kv_fault (monitor disabled in scan mode) |

#### `directed_kv_glitch_inject`

| Iter | Description | Pass Criteria |
| :--- | :---------- | :------------ |
| 0 | Force boot_flow_fmc to invalid MuBi4 (4'hA), verify no spurious fault, then normal FMC jump | No kv_fault during glitch (fail-safe); normal FMC transition succeeds after release |
| 1 | Force shadow register bit-flip on fmc_start, verify err_storage detection and write lockout | shadow_storage_err set in HW_ERROR_FATAL; writes rejected (err_storage permanent until reset) |
| 2 | After warm reset, verify fatal bit persisted and W1C clears it | shadow_storage_err survives warm reset (pwrgood domain); W1C succeeds after err_storage cleared by reset |

### SVA Assertions

44 assertions in `src/integration/asserts/kv_boot_flow_sva.sv`:

| Category | Count | Coverage |
| :------- | :---- | :------- |
| Enforcement timing (lock_wr) | 9 | One per DICE slot locked at FMC/RT |
| Enforcement timing (lock_use) | 3 | FMC slots locked for use at RT |
| Slot clearing | 6 | Correct slots cleared at each transition |
| Error chain | 2 | kv_error -> CPTRA_HW_ERROR_FATAL propagation |
| Monotonicity | 3 | boot_flow_fmc/rt non-regression, layer ordering |
| DOE lockdown | 2 | DOE_CTRL.CMD cleared in FMC and RT |
| Write counters | 13 | Increment, saturation, hard-reset clear, flush clear, stable-when-locked, stable-during-clear (3 slots) |
| ICCM region | 2 | Fetch-without-lock -> error, W1S sticky lock |
| Cover properties | 1 | flush_keyvault with non-zero counters |

### Coverage Gaps (Not Yet Implemented)

| Area | Description | Priority |
| :--- | :---------- | :------- |
| Counter clears on flush | Write to slot 6 (count=1), trigger debug unlock (flush) -- counter returns to 0 | Low |
| Counter clears on scan mode | Write to slots 6,7,8, enter scan mode -- all 3 counters return to 0 | Low |
| Counter no increment during clear | key_entry_clear on slot 6 simultaneous with crypto write -- counter unchanged | Low |

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

---

## ICCM Write Hash Measurement (PCR4/PCR5)

### Feature Summary

Hardware-only SHA-384 measurement of all data written to ICCM during firmware loading. The SHA-512 accelerator captures every ICCM write in real-time, computes the hash, and extends the result into two dedicated PCRs: PCR4 (Current — cleared each boot) and PCR5 (Journey — accumulates across FW updates). This closes the gap between "image was verified" and "image was correctly copied to ICCM."

### Test Suite

| Test | Category | Description |
| :--- | :------- | :---------- |
| `smoke_test_iccm_hash` | Smoke | Write 4 known words to ICCM, verify PCR4 matches expected extend result, cross-check PCR0 extend with same digest |
| `directed_test_iccm_hash` | Directed | 6 sequences (multi-block, extra pad, zero-length, exact boundary, large, tight memcpy) with fw_update_reset between each |
| `directed_test_iccm_pcr5_journey` | Directed | 3 boots separated by `fw_update_reset`; PCR4 clears each boot, PCR5 chains across boots (Journey property) |
| `directed_test_iccm_fw_write_block` | Directed | FW AHB writes to PCR4/PCR5 are dropped both pre-hash (zero) and post-hash (populated digest unchanged) |
| `directed_test_iccm_sha_ctrl_block` | Directed | `sha512_ctrl` `pcr_hash_extend` targeting PCR4 / PCR5 is blocked by `pv.sv` guard; same flow against PCR0 succeeds (control) |
| `directed_test_iccm_clear_hatch` | Directed | `PCR_CTRL[4,5].clear` zeros PCR4/PCR5, then FW AHB writes and SHA-ctrl extends are still blocked on the cleared entries |
| `directed_test_iccm_sha_acc_reuse` | Directed | After ICCM hash completes, SHA acc lock is released and a streaming SHA-384 produces a matching digest |
| `directed_test_iccm_cold_reset_pcr5` | Directed | PCR5 populated in Boot 0; after cold reset (Boot 1) PCR5 reads back zero (new Journey chain) |
| `directed_test_iccm_replay_block` | Directed | After the measurement completes, additional ICCM writes in the same boot do not perturb PCR4/PCR5 |

### Test Iterations

#### `smoke_test_iccm_hash`

Single iteration:
1. Write 4 words {0x1, 0x2, 0x3, 0x4} to ICCM (HW autonomously arms on the first write)
2. Lock ICCM → triggers hash finalization + PCR4/PCR5 extend
3. Verify PCR4 matches expected `SHA-384(zeros || SHA-384(LE_iccm_data))`
4. Extend PCR0 via normal SHA512 `pcr_hash_extend` with same ICCM digest
5. Verify PCR0 == PCR4 (byte-ordering consistency between extend paths)

#### `directed_test_iccm_hash`

| Iter | Sequence | Description | Pass Criteria |
| :--- | :------- | :---------- | :------------ |
| 0 | 64 words {0x10..0x4F} | Multi-block (256 bytes, 2 SHA blocks + padding block) | PCR4 matches expected |
| 1 | 28 words {0xBB00..0xBB1B} | Extra padding block required (112 bytes) | PCR4 matches expected |
| 2 | 0 words | Zero-length hash (lock immediately after trigger) | PCR4 matches expected |
| 3 | 32 words {0xC000..0xC01F} | Exact SHA-384 block boundary (128 bytes) | PCR4 matches expected |
| 4 | 260 words {0xD000..0xD103} | Large (1040 bytes, >1KB) | PCR4 matches expected |
| 5 | 64 words {0x10..0x4F} tight | Back-to-back `sw` pairs via inline asm (LSU merge test) | PCR4 matches seq 0 |

Each iteration ends with `fw_update_reset`, which clears PCR4 via `pcr4_hwclr` and resets ICCM mode for the next sequence.

#### `directed_test_iccm_pcr5_journey`

3 boots separated by `fw_update_reset`, sequenced by a counter in `.dccm.persistent`:
1. Boot 0: run default ICCM hash → PCR5 holds the Boot-0 digest
2. Boot 1: assert PCR4 was cleared and PCR5 still equals Boot-0 value, then run hash → PCR5 chains
3. Boot 2: same pre-checks, then run hash → PCR5 chains again

Expected PCR4 (per boot) and PCR5 (chained) values are hardcoded in the test.

#### `directed_test_iccm_fw_write_block`

Single iteration, 3 steps:
1. Pre-hash: write `0xDEADBEEF` to every dword of PCR4 and PCR5 → both must still read all zeros
2. Run default ICCM hash → PCR4 / PCR5 populated with digest
3. Post-hash: write `0xDEADBEEF` to every dword of PCR4 and PCR5 again → digests must be unchanged

#### `directed_test_iccm_sha_ctrl_block`

Three independent SHA-ctrl `pcr_hash_extend` attempts from FW:
1. Extend targeting PCR4 → PCR4 must remain zero (`pv.sv` guard drops `pv_write[0]` to entry 4)
2. Extend targeting PCR5 → PCR5 must remain zero
3. Extend targeting PCR0 (control) → PCR0 must change, proving the extend path itself works

#### `directed_test_iccm_clear_hatch`

Single iteration, 4 steps:
1. Run default ICCM hash → PCR4 / PCR5 populated
2. Write `PCR_CTRL[4].clear` and `PCR_CTRL[5].clear` → both PCRs read zero
3. FW AHB write `0xDEADBEEF` to every dword of PCR4 / PCR5 → both still read zero
4. SHA-ctrl `pcr_hash_extend` targeting PCR4 then PCR5 → both still read zero

#### `directed_test_iccm_sha_acc_reuse`

Single iteration, 3 steps:
1. Run default ICCM hash → completes, releases SHA acc lock
2. Re-acquire SHA acc lock via normal FW handshake (release then read-to-acquire)
3. Streaming SHA-384 of `{0x01, 0x02, 0x03, 0x04}` → digest must match the expected SHA-384

#### `directed_test_iccm_cold_reset_pcr5`

2 boots separated by a cold reset, sequenced by a counter in `.dccm.persistent`:
1. Boot 0: run default ICCM hash → PCR5 non-zero, then trigger cold reset
2. Boot 1: PCR5 must read all zeros (new Journey chain after cold reset)

#### `directed_test_iccm_replay_block`

Single iteration, 3 steps:
1. Run default ICCM hash → PCR4 / PCR5 populated, snapshot both
2. Write a different pattern to ICCM (no `fw_update_reset`) and re-assert `INTERNAL_ICCM_LOCK`
3. Re-read PCR4 and PCR5 → both must match the snapshots byte-for-byte

### Security Enforcement

| Mechanism | RTL Location | Description |
| :-------- | :----------- | :---------- |
| PCR4/PCR5 write guard | `pv.sv` | `pv_write[0]` (sha512_ctrl) blocked from targeting entry 4 or 5; only `pv_write[1]` (ICCM hash) can write |
| Autonomous arming | `sha512_acc_top.sv` | `iccm_armed` sticky flop set combinationally by the first ICCM-write snoop; HW also acquires the SHA acc LOCK in the same cycle via `LOCK.hwclr` |
| Hash measurement single-shot | `sha512_acc_top.sv` | `iccm_mode_done` sticky flag prevents re-trigger until `iccm_unlock` (which fires on `fw_update_reset`) |
| PCR4 clear on FW update | `caliptra_top.sv` | `pcr4_hwclr = iccm_unlock` clears PCR4 on fw_update_reset |
| FW isolation | `sha512_acc_top.sv` | All extend FSM control signals (pv_read, write_entry, init) driven by HW state only — no CSR interface |
| PCR extend correctness | `sha512_acc_top.sv` | Extend FSM uses same `kv_read_client` + `sha512_core` + `kv_write_client` pattern as sha512.sv PCR extend |

### Regression

- `src/integration/stimulus/L0_regression.yml` -- smoke_test_iccm_hash
- `src/integration/stimulus/testsuites/caliptra_top_nightly_directed_regression.yml` -- directed_test_iccm_hash, directed_test_iccm_pcr5_journey, directed_test_iccm_fw_write_block, directed_test_iccm_sha_ctrl_block, directed_test_iccm_clear_hatch, directed_test_iccm_sha_acc_reuse, directed_test_iccm_cold_reset_pcr5, directed_test_iccm_replay_block
