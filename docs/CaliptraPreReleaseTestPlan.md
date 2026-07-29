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
| 4 | Lock without programming addresses (all=0), shadow not committed | boot_flow_error fires (effective_lock=0) |
| 5 | Single write only (no commit) -- shadow phase stays 0 | iccm_all_shadows_committed=0; effective lock=0 |
| 6 | Mismatched 2-phase write -- different values for phase 0 and phase 1 | shadow_update_err (NON_FATAL[3]) fires |
| 7 | Out-of-range ICCM fetch from ROM -- jump to address outside FMC/RT regions | boot_flow_error fires in ROM phase; kv_error set |
| 8 | Out-of-range ICCM fetch from FMC -- normal boot then FMC jumps to OOR | boot_flow_error fires in FMC phase; kv_error set |
| 9 | Out-of-range ICCM fetch from RT -- normal boot, FMC→RT, then RT jumps to OOR | boot_flow_error fires in RT phase; kv_error set |

#### `directed_kv_monitor_neg`

| Iter | Fault Injected | Pass Criteria |
| :--- | :------------- | :------------ |
| 0 | Skip slot 0 (UDS) -- leave empty | kv_error fires at FMC transition |
| 1 | Slot 0 wrong dest_valid (HMAC_KEY instead of AES_KEY) | kv_error fires at FMC transition |
| 2 | Skip slot 6 (FMC_CDI) -- leave empty | kv_error fires at FMC transition |
| 3 | Slot 2 (Key Ladder) wrong dest_valid (AES_KEY instead of HMAC_KEY) | kv_error fires at FMC transition |
| 4 | Skip slot 4 (RT_CDI) for RT transition | kv_error fires at RT transition |
| 5 | Slot 9 (RT_MLDSA) wrong dest_valid at RT transition | kv_error fires at RT transition |
| 6 | Slot 7 write count too low (1 instead of ==2, skip FMC Alias ECC) | kv_error fires at FMC transition |
| 7 | Slot 8 write count too low (1 instead of ==2, skip FMC Alias MLDSA) | kv_error fires at FMC transition |
| 8 | Slot 7 write count too high (3 instead of ==2, extra ECC keygen) | kv_error fires at FMC transition |
| 9 | Slot 6 write count too high (5 instead of ==4, extra CDI write) | kv_error fires at FMC transition |
| 10 | Slot 8 write count too high (3 instead of ==2, extra MLDSA keygen) | kv_error fires at FMC transition |

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
| Write counters | 13 | Increment, saturation, hard-reset clear, warm-reset clear, flush clear, stable-when-locked, stable-during-clear (3 slots) |
| ICCM region | 4 | Fetch-without-lock -> error, W1S sticky lock, OOR fetch in FMC phase, OOR fetch in RT phase |
| Cover properties | 1 | flush_keyvault with non-zero counters |

### Coverage Gaps (Not Yet Implemented)

| Area | Description | Priority |
| :--- | :---------- | :------- |
| Stable owner key preservation | Enable `stable_owner_key_en` strap (SS_STRAP_GENERIC[3] bit 0) and verify slot 15 preserved at enter_fmc (`StableOwnerPreservedAtFmc_C`) | Medium |
| OCP Lock slot preservation | Enable `ocp_lock_mode_en` straps and verify MDK/HEK slots preserved at enter_fmc (`OcpLockMdkPreservedAtFmc_C`, `OcpLockHekPreservedAtFmc_C`) | Medium |
| Multi-write arbitration | Trigger >1 crypto engine writing same KV slot simultaneously (`cg_multi_write`) | Low |
| Counter clears on scan mode | Write to slots 6,7,8, enter scan mode -- all 3 counters return to 0 | Low |
| Counter no increment during clear | key_entry_clear on slot 6 simultaneous with crypto write -- counter unchanged | Low |

### Covergroups

Location: `src/keyvault/coverage/kv_boot_flow_cov.sv` (KV-side) and `src/soc_ifc/coverage/soc_ifc_iccm_shadow_cov.sv` (shadow regs)

Covergroups verify enforcement correctness, flush source attribution, monitor pass/fail, write counter thresholds, and multi-write arbitration errors. These complement the temporal cover properties in `kv_boot_flow_sva.sv`.

| Covergroup | File | Sample Event | Key Crosses | Purpose |
| :--------- | :--- | :----------- | :---------- | :------ |
| `cg_enforcement_result` | `kv_boot_flow_cov.sv` | 1 cycle after `enter_fmc`/`enter_rt` | transition × lock_wr_correct, lock_use_correct | Verifies enforcement sets correct lock bits per transition |
| `cg_monitor_check` | `kv_boot_flow_cov.sv` | `enter_fmc`, `enter_rt` | transition × pass/fail | Monitor validation at both boundaries |
| `cg_flush_source` | `kv_boot_flow_cov.sv` | Rising edge of boot_flow_error or monitor_alert | source × phase (rom/fmc/rt) | Which error source triggered KV flush, in which boot phase |
| `cg_write_counter_threshold` | `kv_boot_flow_cov.sv` | `enter_fmc` | per-slot threshold × alert (3 independent crosses) | Each DICE slot's write count independently triggers/passes monitor (below, met, above) |
| `cg_multi_write` | `keyvault_cov_if.sv` | Rising edge of multi-write error | detected | Bus arbitration error (>1 write client simultaneously) |
| `cg_iccm_shadow_reg` | `soc_ifc_iccm_shadow_cov.sv` | Shadow reg write/read strobe | register × operation, operation × committed, operation × err_storage, register × locked | All registers through all operation/error paths |

### Security Enforcement

| Mechanism | RTL Location | Description |
| :-------- | :----------- | :---------- |
| SoC write rejection (ICCM regs) | `soc_ifc_top.sv` line 1109-1112 | `iccm_shadow_we` gated by `~soc_ifc_reg_req_data.soc_req` -- external registers reject SoC writes |
| SoC write rejection (region lock) | `soc_ifc_internal_reg.rdl` | `swwel = soc_req` on `internal_iccm_region_lock.lock` field |
| Shadow 2-phase protocol | `caliptra_prim_subreg_shadow` | Requires two identical writes to commit; mismatched second write sets CPTRA_HW_ERROR_NON_FATAL.shadow_update_err[3] |
| Shadow storage fault detection | `caliptra_prim_subreg_shadow` | Continuous background comparison of primary/shadow copy sets CPTRA_HW_ERROR_FATAL.shadow_storage_err[5] on mismatch |
| Region lock (post-commit) | `soc_ifc_top.sv` | `iccm_shadow_we` gated by `~iccm_region_lock` -- no writes after ROM locks |
| Write counter exact match | `kv.sv` KV_MONITOR | Counters must equal `KV_EXPECTED_WRITES_*` at `enter_fmc` -- detects both truncated DICE chains (too few writes) and glitch-replayed operations (too many writes that could roll back to an earlier intermediate key) |

### Regression

- `src/integration/stimulus/L0_regression.yml` -- smoke/kv_boot_flow_monitor
- `src/integration/stimulus/testsuites/caliptra_top_nightly_directed_regression.yml` -- all 4 tests

---

## Dual-iTRNG SHA3-384 Entropy Combiner

### Feature Summary

A second internal TRNG (secondary `entropy_src`, ES1) is added alongside the primary
(ES0) to support different noise-generation technologies. To keep a single CSRNG,
a SHA3-384 `entropy_combiner` is inserted between the two `entropy_src` blocks and
CSRNG: when the secondary source is enabled (`dual_iTRNG_en` strap =
`CPTRA_HW_CONFIG.dual_iTRNG_en`, subsystem-mode only) the combiner delivers
`seed = SHA3-384(ES0 || ES1)`; otherwise it bypasses ES1 and passes the ES0 seed
through unchanged. The combiner also exposes an AHB slave used only by ROM for a
power-on SHA3-384 KAT; after the KAT, ROM sets a W1S MuBi4 `AHB_LOCK` that scrubs
the KAT registers and freezes the FIPS combine policy so RT FW cannot read KAT
residuals or weaken the policy. The combiner never exposes raw entropy on any
readable register (ES0/ES1 -> SHA3 -> CSRNG is internal only).

### Test Suite

| Test | Category | Description |
| :--- | :------- | :---------- |
| `smoke_test_entropy_combiner` | Smoke | End-to-end combine: 2x `entropy_src` (raw/bypass) -> combiner -> CSRNG, genbits vs golden `SHA3-384(IS0\|\|IS1)` |
| `smoke_test_entropy_combiner_kat` | Smoke | Combiner power-on SHA3-384 KAT (incl. empty message), identity (NAME/VERSION), FIPS-policy sweep, and MuBi4 `AHB_LOCK` enforcement |
| `smoke_test_entropy_combiner_lock_op` | Directed | Operational-after-lock: combine datapath still produces a seed while the combiner is AHB-locked; lock enforcement persists |
| `smoke_test_entropy_combiner_conditioned` | Directed | Conditioner-ENABLED (FIPS) combine with deterministic entropy; power-on KAT -> lock -> conditioned combine through the locked combiner |
| `smoke_test_entropy_combiner_multiseed` | Directed | Back-to-back multi-seed: 4 consecutive combined seeds (startup + steady-state) exercise the FSM re-request path |

Build/run notes: combine mode requires the subsystem build
(`caliptra_top_ss_mode_tb`: `CALIPTRA_MODE_SUBSYSTEM` + `CALIPTRA_INTERNAL_TRNG`)
plus `+CLP_ITRNG1_EN`. `smoke_test_entropy_combiner_kat` runs in the default
`caliptra_top_tb` build (no plusargs) since the combiner KAT/AHB path is
independent of the ES/CSRNG datapath. The conditioned and multiseed tests add
`+CLP_DETERMINISTIC_RNG` to select the deterministic RNG model
(`physical_rng_deterministic`) so the conditioned output is reproducible.

### Test Cases

#### `smoke_test_entropy_combiner`

| Scenario | Description | Pass Criteria |
| :------- | :---------- | :------------ |
| Combine genbits | Enable ES0/ES1 raw, CSRNG instantiate-from-entropy, generate 128b | genbits == golden `EXP_GENBITS_COMBINE` |
| ES config readback | Read back `CONF`/`MODULE_ENABLE`/`RECOV_ALERT_STS` on both ES | Config took; no recoverable alert |
| Combine topology | Read `COMBINER_STATUS.combine_en` and `COMBINER_CTRL` (policy) | combine_en=1; policy at reset default |

#### `smoke_test_entropy_combiner_kat`

| Scenario | Description | Pass Criteria |
| :------- | :---------- | :------------ |
| Identity | Read `COMBINER_NAME_0/1`, `COMBINER_VERSION_0/1` | Match "sha3comb" / "2.20" reset constants |
| KAT vectors A-D | Program `KAT_MSG[0..23]`, `KAT_MSG_LEN=96`, pulse START, poll VALID | `KAT_DIGEST` == `SHA3-384(ES0\|\|ES1)` golden (ordering guards) |
| KAT empty message | `KAT_MSG_LEN=0`, START | `KAT_DIGEST` == `SHA3-384("")`; `KAT_MSG_LEN` reads back per value |
| Policy sweep | Write `COMBINER_CTRL.es_fips_policy`/`es_fips_cfg` = {0,1,2,3, cfg} unlocked | Each value reads back |
| Lock + scrub | Write `AHB_LOCK`=MuBi4True | `KAT_DIGEST`/`KAT_STATUS` read 0; lock reads locked |
| KAT blocked when locked | Program fresh message + START while locked | `KAT_STATUS` never busy/valid; digest stays 0 |
| Policy frozen | Write different policy while locked | Read back unchanged (swwe=!lock) |
| Lock sticky | Write MuBi4False (unlock) while locked | Reads back still locked (clears only on reset) |

#### `smoke_test_entropy_combiner_lock_op`

| Scenario | Description | Pass Criteria |
| :------- | :---------- | :------------ |
| Bring-up (bypass) | Enable ES0/ES1 raw (one boot seed each), no instantiate yet | Both ES boot-done |
| Pre-lock policy | Program `COMBINER_CTRL.es_fips_policy` unlocked | Reads back programmed value |
| Lock | Set `AHB_LOCK`=MuBi4True | Reads locked |
| Enforcement (pre-combine) | KAT scrubbed, policy frozen, lock sticky | All hold |
| Combine while locked | Instantiate-from-entropy + generate through the locked combiner | genbits == golden `EXP_GENBITS_COMBINE`; no CSRNG exception/error |
| Enforcement (post-combine) | Re-check KAT scrubbed / policy frozen / lock sticky | Live combine did not disturb the lock |

#### `smoke_test_entropy_combiner_conditioned`

| Scenario | Description | Pass Criteria |
| :------- | :---------- | :------------ |
| Power-on KAT | Empty-message KAT before lock (populates `KAT_DIGEST`) | `KAT_DIGEST` == `SHA3-384("")` |
| Program policy + lock | Program `es_fips_policy`, set `AHB_LOCK` before entropy flows | Policy took; reads locked |
| FIPS ES config | Both ES: `CONF.FIPS_ENABLE`=MuBi4True, `FIPS_WINDOW=1024`, widen REPCNT/ADAPTP | Config readback OK; `RECOV_ALERT_STS`=0 |
| Conditioned combine (locked) | Instantiate + generate through the locked combiner | genbits == golden `EXP_GENBITS_CONDITIONED` (from `es_conditioner_model.py`) |
| Post-lock enforcement | KAT digest scrubbed to 0, policy frozen, lock sticky | All hold (confidential KAT data not readable) |

#### `smoke_test_entropy_combiner_multiseed`

| Scenario | Description | Pass Criteria |
| :------- | :---------- | :------------ |
| FIPS ES config | Configure both ES in FIPS/conditioned mode | Config readback OK |
| Seed 0 (startup) | Instantiate + generate; startup seed absorbs 2x`FIPS_WINDOW` | genbits == `EXP_GENBITS_SEED_0` |
| Seeds 1-3 (steady-state) | uninstantiate -> re-instantiate -> generate per seed | genbits == `EXP_GENBITS_SEED_k`; no CSRNG exception/error |
| Re-request path | Consecutive combines re-arm the combiner FSM | Each seed distinct and correct |

### Direct (Unit-level) Testbenches

Location: `src/entropy_combiner/tb/`

| Testbench | Description |
| :-------- | :---------- |
| `entropy_combiner_tb.sv` | Combiner datapath TB: combine (`SHA3-384(ES0\|\|ES1)`) and bypass (ES1 ignored) modes against file vectors |
| `entropy_combiner_align_tb.sv` | ES0/ES1 arrival-skew stress (directed matrix + randomized); checks digest correctness and ES/CSRNG ack ordering |
| `entropy_combiner_es_integration_tb.sv` | 2x real `entropy_src` -> combiner, ES0/ES1 arrival-timing sweep via itrng release gates |
| `entropy_combiner_es_csrng_tb.sv` | Full chain 2x `entropy_src` -> combiner -> real CSRNG; 5 cases (see below) |

#### `entropy_combiner_es_csrng_tb.sv` cases

| Case | Description | Pass Criteria |
| :--- | :---------- | :------------ |
| case1 ES1-faster-than-ES2 | Combine; release ES0 first, ES1 after a skew | seed==`EXP_SEED_COMBINE`; genbits==`EXP_GENBITS_COMBINE` |
| case2 ES1-slower-than-ES2 | Combine; release ES1 first, ES0 after a skew | seed/genbits match combine golden |
| case3 both-same-time | Combine; ES0/ES1 released together | seed/genbits match combine golden |
| case4 ES2-disabled | Bypass (`combine_en=0`); ES1 disabled | seed==`EXP_SEED_BYPASS`(=IS0); genbits==`EXP_GENBITS_BYPASS` |
| case5 force-fsm-error | Glitch the combiner sparse-FSM state to an undefined code mid-combine | FSM traps to `combiner_st_error` and holds; NO `es_ack` to CSRNG (no corrupt/partial seed); only reset recovers to `combiner_st_idle` (VCS-only; CM assertions silenced around the forced fault) |

### Reference Models

Location: `src/entropy_combiner/tb/`

| Model | Purpose |
| :---- | :------ |
| `gen_test_vectors.py` | SHA3-384 combiner reference: generates `entropy_combiner_test_vectors.hex` (ES0, ES1, digest) |
| `csrng_drbg_model.py` | AES-256 CTR_DRBG (CSRNG) + combiner digest; validated against AES FIPS-197 and CSRNG KATs |
| `es_conditioner_model.py` | `entropy_src` SHA3-384 conditioner front-end (startup = 2x window, little-nibble packing) + full chain; emits conditioned/multi-seed goldens (sim-validated at `FIPS_WINDOW=1024`) |

### Deterministic RNG Infrastructure

| Component | Location | Description |
| :-------- | :------- | :---------- |
| `physical_rng_deterministic` | `src/entropy_src/tb/physical_rng_deterministic.sv` | Fully deterministic LFSR nibble stream (holds on disable), for reproducible conditioned/multi-seed tests |
| RNG source MUX | `src/integration/tb/caliptra_top_tb.sv` | Per-source MUX between `physical_rng` and `physical_rng_deterministic`, selected by `+CLP_DETERMINISTIC_RNG` (default off, existing tests unaffected) |

### Security Enforcement

| Mechanism | RTL Location | Description |
| :-------- | :----------- | :---------- |
| KAT register scrub on lock | `entropy_combiner.sv` | On W1S `AHB_LOCK`, `KAT_MSG`/`KAT_MSG_LEN`/`KAT_DIGEST`/`KAT_STATUS` are held 0 so RT FW cannot read KAT residuals |
| KAT blocked when locked | `entropy_combiner.sv` | `kat_start_cmd = start && !ahb_locked` -- no KAT can run once locked |
| FIPS policy freeze | `entropy_combiner.sv` | `COMBINER_CTRL.es_fips_policy/es_fips_cfg` `swwe = !ahb_locked` -- ROM freezes the combine policy after lock |
| Lock write-once-sticky | `entropy_combiner_reg.rdl` | MuBi4 `AHB_LOCK` `swwe=strict-False`; any non-strict-False code is treated as locked (fail-safe); clears only on reset |
| No raw entropy on bus | `entropy_combiner.sv` | ES0/ES1 -> SHA3 -> CSRNG is internal only; no readable register exposes raw entropy |
| Sparse-FSM fail-safe | `entropy_combiner.sv` | An undefined FSM state traps to `combiner_st_error` (self-loop), emits no CSRNG ack, and recovers only on reset (verified by `entropy_combiner_es_csrng_tb` case5) |

### Regression

- Standalone: the combiner C tests are launched directly (subsystem build +
  plusargs as noted above); `smoke_test_entropy_combiner_kat` runs in the default
  build.

