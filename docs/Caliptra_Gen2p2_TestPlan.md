# Caliptra 2.2 Feature Test Plan

This document tracks test content for the following Caliptra 2.2 release features.
Test listings identify implemented stimulus and expected checks, not recorded
regression passes or coverage closure. A PASS from a skipped or unsupported
configuration does not count as feature coverage.

| Release Feature | Test Plan Section |
| :-------------- | :---------------- |
| VeeR DCLS in Passive and Subsystem modes | [DCLS reporting](#dcls-reporting-in-passive-and-subsystem-profiles) |
| Fault injection countermeasures for FSMs, debug controls, and ICCM regions | [Fault injection countermeasures](#fault-injection-countermeasures-for-fsms-debug-controls-and-iccm-regions) |
| Key Vault boot flow monitoring, enforcement, and key-length checks | [Key Vault](#key-vault-boot-flow-monitoring-enforcement-and-key-length-checks) |
| HMAC512 area optimization and multi-block interface updates | [HMAC512](#hmac512-area-optimization-and-multi-block-interface) |
| CSR HMAC key lock | [CSR HMAC key lock](#csr-hmac-key-lock) |
| ECC area optimization, zeroization, and Key Vault operand clearing | [ECC operation boundaries](#ecc-area-optimization-zeroization-and-key-vault-operand-clearing) |
| ECC and ML-DSA verification-pass status | [Verification status](#ecc-and-ml-dsa-verification-pass-status) |
| Hardware ICCM measurement and PCR4/PCR5 updates | [ICCM write hash](#iccm-write-hash-measurement-pcr4pcr5) |
| Dual iTRNG entropy combiner | [Entropy combiner](#dual-itrng-sha3-384-entropy-combiner) |
| Entropy source and health-test register map | Entropy source |
| Stash-measurement register bank | [Stash bank](#stash-measurement-register-bank) |

Firmware test names below refer to `src/integration/test_suites/`, with YAML
variants and unit/UVMF tests identified separately. Area-optimization entries
identify functional regressions; area and timing comparisons require separate
implementation results.

---

## Key Vault Boot Flow Monitoring, Enforcement, and Key-Length Checks

### Feature Summary

Hardware-enforced DICE key integrity monitoring and slot access control across ROM->FMC->RT boot phase transitions. Comprises a boot flow monitor (ICCM fetch detection), KV monitor (dest_valid/write count validation), KV enforcement (lock/clear), DOE lockdown, and ICCM region shadow registers with SoC write protection. Crypto clients also check stored key length, and reject short entries before using them.

### Test Suite

| Test | Category | Description |
| :--- | :------- | :---------- |
| `smoke_test_kv_boot_flow_monitor` | Smoke | Synthetic DICE-slot population through cold boot, warm reset, and FW update reset cycles |
| `directed_kv_enforcement` | Directed | Verifies lock_wr, lock_use, slot clearing, DOE lockdown, and ROM callback behavior |
| `directed_kv_iccm_region` | Directed | ICCM region register programming, locking, reset behavior, and shadow negative cases |
| `directed_kv_monitor_neg` | Directed | Deliberate faults in dest_valid and write counts trigger monitor alerts |
| `directed_kv_debug_scan_bypass` | Directed | Verifies monitor is disabled in debug unlock and scan mode (no false alerts) |
| `directed_kv_glitch_inject` | Directed | Testbench-driven MuBi glitch/recovery and shadow register bit-flip lockout |
| `directed_kv_fw_update_reset_abort` | Directed | FW-update reset during locked/unlocked HMAC writes, DOE writes, and HMAC key reads |

The boot-flow helper in `src/integration/test_suites/libs/kv_boot_flow/`
uses HMAC-only dummy writes to populate expected slot permissions and write
counts. These tests exercise monitoring and enforcement, not a complete
DOE/ECC/ML-DSA DICE derivation.

### Test Cases

#### `smoke_test_kv_boot_flow_monitor`

| Scenario | Description | Pass Criteria |
| :------- | :---------- | :------------ |
| Cold boot happy path | Populate synthetic DICE-slot metadata/write counts, program ICCM regions, jump to FMC then RT | No kv_error; FMC/RT checks succeed |
| Warm reset cycle | Skip ROM derivation and re-enter the monitored boot flow | Retained derivation state is accepted; transitions succeed |
| FW update reset | Retain region addresses, clear region lock, and re-commit/re-lock before FMC entry; skip ROM derivation | Region configuration and phase checks succeed |

#### `directed_kv_enforcement`

| Scenario | Phase | Description | Pass Criteria |
| :------- | :---- | :---------- | :------------ |
| lock_wr prevents overwrite | FMC | HMAC write to locked slot 0 (SI_IDEV) | Write has no effect; dest_valid unchanged |
| Cleared slots empty | FMC | Read dest_valid of slots 3,4,5,9 | All return 0 |
| ROM callback no re-trigger | FMC | FMC calls ROM-resident function and returns | No kv_error; boot_flow_fmc stays True |
| DOE lockdown (FMC) | FMC | Issue DOE command after FMC entry | Command rejected; DOE not busy |
| Counter stable on lock_wr (slot 6) | FMC | Crypto write to lock_wr'd slot 6 | write_count_fmc_cdi unchanged (SVA + no kv_error at RT) |
| Counter stable on lock_wr (slot 8) | FMC | Crypto write to lock_wr'd slot 8 | write_count_fmc_mldsa unchanged (SVA + no kv_error at RT) |
| lock_wr prevents overwrite | RT | HMAC write to locked slot 4 (RT_CDI) | Write has no effect |
| lock_use prevents read | RT | Read slot 6 (FMC_CDI) as HMAC key | KV read fails with error |
| Counter stable on lock_use (slot 7) | RT | Crypto write to lock_use'd slot 7 | write_count_fmc_ecdsa unchanged (SVA) |
| DOE lockdown (RT) | RT | Issue DOE command after RT entry | Command rejected |
| Stable owner preservation | FMC/RT | Enable the stable-owner configuration and check the conditional preservation path | Conditional slot-preservation checks pass |
| OCP LOCK preservation | FMC/RT | Enable OCP LOCK and check conditional key-slot preservation | Conditional MDK/HEK preservation checks pass |

The preservation checks are implemented conditionally in the test/helper.
Enabled configurations and corresponding cover-property hits must be qualified
before crediting those branches.

#### `directed_kv_iccm_region`

| Iter | Description | Pass Criteria |
| :--- | :---------- | :------------ |
| 0 | Program regions, lock, verify readback, attempt overwrite after lock | Overwrite blocked; lock=1 persists |
| 1 | Reset-clear case; current firmware requests a cold reset | Region addresses and lock read back as 0 |
| 2 | FW update reset -- verify region addresses retained and lock cleared; re-commit/re-lock | Retained addresses match; lock is 0 before re-lock |
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
| 6 | Slot 7 write count too low (1 instead of ==2) | kv_error fires at FMC transition |
| 7 | Slot 8 write count too low (1 instead of ==2) | kv_error fires at FMC transition |
| 8 | Slot 7 write count too high (3 instead of ==2) | kv_error fires at FMC transition |
| 9 | Slot 6 write count too high (5 instead of ==4, extra CDI write) | kv_error fires at FMC transition |
| 10 | Slot 8 write count too high (3 instead of ==2) | kv_error fires at FMC transition |

#### `directed_kv_debug_scan_bypass`

| Iter | Description | Pass Criteria |
| :--- | :---------- | :------------ |
| 0 | Synthetic DICE-slot setup + FMC jump, then debug unlock + warm reset | Normal FMC transition succeeds; debug unlock propagates on warm reset |
| 1 | Boot with debug_locked=0 (from iter 0), synthetic slot setup + FMC jump | No kv_fault (monitor disabled in debug mode) |
| 2 | Re-locked debug, synthetic slot setup, enter scan mode, FMC jump | No kv_fault (monitor disabled in scan mode) |

#### `directed_kv_glitch_inject`

| Iter | Description | Pass Criteria |
| :--- | :---------- | :------------ |
| 0 | Request the testbench MuBi glitch, then perform a normal FMC jump | Current test expects no spurious kv_fault and a successful transition after release |
| 1 | Force shadow register bit-flip on fmc_start, verify err_storage detection and write lockout | shadow_storage_err set in HW_ERROR_FATAL; writes rejected (err_storage permanent until reset) |
| 2 | After warm reset, verify fatal bit persisted and W1C clears it | shadow_storage_err survives warm reset (pwrgood domain); W1C succeeds after err_storage cleared by reset |

#### `directed_kv_fw_update_reset_abort`

Four reset-aligned cases over five firmware boots exercise reset during a locked
HMAC write, an unlocked HMAC write, a DOE write, and a HMAC key read. The checks
cover retained destination permissions, prevention of a completed DOE overwrite,
and nonzero aborted-read status. The read-abort case checks status, not a golden
comparison of key contents.

### Key-Length and In-flight Control Tests

| Test | Category | Checks |
| :--- | :------- | :----- |
| `smoke_test_kv_len_mismatch_hmac` | Randomized | HMAC384/512 KEY lengths; short keys return length-mismatch status and do not start the engine |
| `smoke_test_kv_len_mismatch_ecc` | Randomized | ECC seed/private-key lengths against the 12-dword requirement |
| `smoke_test_kv_len_mismatch_aes` | Randomized | AES128/192/256 key lengths and read-versus-length-programming ordering |
| `smoke_test_kv_len_mismatch_abr` | Randomized | ML-DSA seed and ML-KEM seed/message lengths |
| `smoke_test_kv_len_mismatch_dma` | Incomplete | Skeleton only: no key-release trigger or checked counter comparison; not credited as length-mismatch coverage |
| `smoke_test_kv_swwe_lock` | Directed | Busy HMAC/ECC KV control writes are blocked; idle writes and PCR hash-extend control protection |
| `smoke_test_kv_wr_ctrl_zeroize` | Directed | HMAC/ECC zeroize clears stale KV write controls/VALID before the next operation |
| `smoke_test_kv_lock_use_mid_read` | Directed | Set lock_use after starting a HMAC key read; require a read error and sticky lock |
| `smoke_test_kv_mldsa` / `smoke_test_mldsa_kv_ocp_progress` / `smoke_test_mlkem_kv_ocp_progress` | Compatibility | Existing KV-seed flows inherit checked success/error status and engine-not-started checks after rejected reads |
| `smoke_test_kv_rules_ocp_lock` | Compatibility | Existing HMAC/ML-KEM cross-region flows inherit strict KV read-status and rejected-read readiness checks |

The HMAC length test covers KEY reads, not BLOCK-length rejection. The write-control
zeroize test covers HMAC and ECC, not AES. The mid-read test's transaction timing
must be confirmed with the bench/assertions; software delay alone does not prove
the lock changed during an active transfer.

### SVA Assertions

Source: `src/integration/asserts/kv_boot_flow_sva.sv`.

| Check Family | Coverage |
| :----------- | :------- |
| Enforcement timing | Expected lock_wr/lock_use changes at FMC and RT boundaries |
| Slot clearing | Required slots are cleared at phase transitions |
| Error chain | Boot-flow/monitor errors propagate to the fatal status and KV flush |
| Monotonicity | Boot phases do not regress or bypass FMC |
| DOE lockdown | DOE commands are cleared/rejected in FMC and RT |
| Write counters | Increment, saturation, hard-reset/flush clearing, reset retention, and stability under locking/clearing |
| ICCM regions | Unlocked/out-of-range fetch errors and sticky region lock |
| Cover properties | Flush with nonzero counters and conditional stable-owner/OCP slot preservation |

Track assertion and cover families separately rather than treating a fixed source
count as an elaborated coverage result.

### Coverage to Qualify

| Area | Follow-up |
| :--- | :-------- |
| Stable owner / OCP preservation | Run enabled configurations and confirm `StableOwnerPreservedAtFmc_C`, `OcpLockMdkPreservedAtFmc_C`, and `OcpLockHekPreservedAtFmc_C` hits |
| Region warm-reset stimulus | The region test's reset-clear iteration currently requests cold reset; do not label it as a dedicated warm-reset case |
| DMA key length | Complete the skeleton's key-release stimulus and checked result before crediting it |
| Multi-write arbitration | Confirm simultaneous same-slot crypto writers exercise `cg_multi_write` |
| Scan/clear counter interactions | Confirm scan clears counters and concurrent clear/write does not increment them |

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
| SoC write rejection (ICCM regs) | `soc_ifc_top.sv` | `iccm_shadow_we` gated by `~soc_ifc_reg_req_data.soc_req` -- external registers reject SoC writes |
| SoC write rejection (region lock) | `soc_ifc_internal_reg.rdl` | `swwel = soc_req` on `internal_iccm_region_lock.lock` field |
| Shadow 2-phase protocol | `caliptra_prim_subreg_shadow` | Requires two identical writes to commit; mismatched second write sets CPTRA_HW_ERROR_NON_FATAL.shadow_update_err[3] |
| Shadow storage fault detection | `caliptra_prim_subreg_shadow` | Continuous background comparison of primary/shadow copy sets CPTRA_HW_ERROR_FATAL.shadow_storage_err[5] on mismatch |
| Region lock (post-commit) | `soc_ifc_top.sv` | `iccm_shadow_we` gated by `~iccm_region_lock` -- no writes after ROM locks |
| Write counter exact match | `kv.sv` KV_MONITOR | Counters must equal `KV_EXPECTED_WRITES_*` at `enter_fmc` -- detects both truncated DICE chains (too few writes) and glitch-replayed operations (too many writes that could roll back to an earlier intermediate key) |

### Regression

- `src/integration/stimulus/L0_regression.yml` -- boot-flow smoke and mid-read lock test
- `src/integration/stimulus/testsuites/caliptra_top_nightly_directed_regression.yml` -- seven boot-flow programs plus the in-flight control tests
- `src/integration/stimulus/testsuites/caliptra_top_kv_monitor_regression.yml` -- six boot-flow programs; does not include `directed_kv_fw_update_reset_abort`
- `src/integration/stimulus/testsuites/caliptra_top_tb_nightly_random_regression.yml` -- five length-test configurations, including the incomplete DMA entry

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
power-on SHA3-384 KAT; after the KAT, ROM sets a W1S MuBi4 `AHB_LOCK` that clears
internal KAT message/length/digest snapshots, masks digest/status readback, and
freezes the FIPS combine policy. The software-owned `KAT_MSG` and `KAT_MSG_LEN`
input registers are not cleared by locking; their hardware clear is driven by
zeroize. The combiner never exposes raw entropy on any
readable register (ES0/ES1 -> SHA3 -> CSRNG is internal only). Boot-phase
`rt_active_i` also locks the AHB interface without a software lock write; this
lock must not interrupt the operational entropy path.

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
plus `+CLP_ITRNG1_EN`. `smoke_test_entropy_combiner_kat` does not need the dual-source
plusarg and can also run in the default `caliptra_top_tb` build, but requires the
internal TRNG build; its firmware skips when that hardware is absent. The
conditioned and multiseed tests add
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
| Lock + result masking | Write `AHB_LOCK`=MuBi4True | `KAT_DIGEST`/`KAT_STATUS` read 0; lock reads locked; no input-register scrub is implied |
| KAT blocked when locked | Program fresh message + START while locked | `KAT_STATUS` never busy/valid; digest stays 0 |
| Policy frozen | Write different policy while locked | Read back unchanged (swwe=!lock) |
| Lock sticky | Write MuBi4False (unlock) while locked | Reads back still locked (clears only on reset) |

#### `smoke_test_entropy_combiner_lock_op`

| Scenario | Description | Pass Criteria |
| :------- | :---------- | :------------ |
| Bring-up (bypass) | Enable ES0/ES1 raw (one boot seed each), no instantiate yet | Both ES boot-done |
| Pre-lock policy | Program `COMBINER_CTRL.es_fips_policy` unlocked | Reads back programmed value |
| Lock | Set `AHB_LOCK`=MuBi4True | Reads locked |
| Enforcement (pre-combine) | Digest/status readback masked, policy frozen, lock sticky | All hold |
| Combine while locked | Instantiate-from-entropy + generate through the locked combiner | genbits == golden `EXP_GENBITS_COMBINE`; no CSRNG exception/error |
| Enforcement (post-combine) | Re-check digest/status masking, policy freeze, and sticky lock | Live combine did not disturb the lock |

#### `smoke_test_entropy_combiner_conditioned`

| Scenario | Description | Pass Criteria |
| :------- | :---------- | :------------ |
| Power-on KAT | Empty-message KAT before lock (populates `KAT_DIGEST`) | `KAT_DIGEST` == `SHA3-384("")` |
| Program policy + lock | Program `es_fips_policy`, set `AHB_LOCK` before entropy flows | Policy took; reads locked |
| FIPS ES config | Both ES: `CONF.FIPS_ENABLE`=MuBi4True, `FIPS_WINDOW=1024`, widen REPCNT/ADAPTP | Config readback OK; `RECOV_ALERT_STS`=0 |
| Conditioned combine (locked) | Instantiate + generate through the locked combiner | genbits == golden `EXP_GENBITS_CONDITIONED` (from `es_conditioner_model.py`) |
| Post-lock enforcement | KAT digest readback masked to 0, policy frozen, lock sticky | All hold; no input-register scrub is implied |

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
| `entropy_combiner_es_csrng_tb.sv` | Full chain 2x `entropy_src` -> combiner -> real CSRNG; 12 cases (see below) |

#### `entropy_combiner_es_csrng_tb.sv` cases

| Case | Description | Pass Criteria |
| :--- | :---------- | :------------ |
| case1 ES1-faster-than-ES2 | Combine; release ES0 first, ES1 after a skew | seed==`EXP_SEED_COMBINE`; genbits==`EXP_GENBITS_COMBINE` |
| case2 ES1-slower-than-ES2 | Combine; release ES1 first, ES0 after a skew | seed/genbits match combine golden |
| case3 both-same-time | Combine; ES0/ES1 released together | seed/genbits match combine golden |
| case4 ES2-disabled | Bypass (`combine_en=0`); ES1 disabled | seed==`EXP_SEED_BYPASS`(=IS0); genbits==`EXP_GENBITS_BYPASS` |
| case5 force-fsm-error | Glitch the combiner sparse-FSM state to an undefined code mid-combine | FSM traps to `combiner_st_error` and holds; NO `es_ack` to CSRNG (no corrupt/partial seed); only reset recovers to `combiner_st_idle` (VCS-only; CM assertions silenced around the forced fault) |
| case6 rt-active-ahb-lock | Assert runtime-active without a ROM AHB_LOCK write, then deassert runtime-active | AHB locks automatically and remains locked |
| case7 combine-while-rt-active | Combine with runtime-active asserted | Seed/genbits match the case3 golden despite AHB locking |
| case8 zeroize-idle | Zeroize while idle | No hang; unit-bench zeroize checks pass |
| case9 zeroize-both-es-outstanding | Zeroize while both source requests are outstanding | No hang; unit-bench zeroize checks pass |
| case10 zeroize-one-es-outstanding | Zeroize after only one source has responded | No hang; unit-bench zeroize checks pass |
| case11 zeroize-sha3-running | Zeroize during SHA3 processing | No hang; unit-bench zeroize checks pass |
| case12 zeroize-random | Randomize zeroize timing during combines | All randomized iterations complete without checker errors |

The bench's legacy ES1/ES2 case labels correspond to hardware ES0/ES1.

### Reference Models

Location: `src/entropy_combiner/tb/`

| Model | Purpose |
| :---- | :------ |
| `gen_test_vectors.py` | SHA3-384 combiner reference: generates `entropy_combiner_test_vectors.hex` (ES0, ES1, digest) |
| `csrng_drbg_model.py` | AES-256 CTR_DRBG reference for CSRNG output following the combiner digest |
| `es_conditioner_model.py` | `entropy_src` SHA3-384 conditioner front-end (startup = 2x window, little-nibble packing) + full chain; emits conditioned/multi-seed goldens for `FIPS_WINDOW=1024` |

### Deterministic RNG Infrastructure

| Component | Location | Description |
| :-------- | :------- | :---------- |
| `physical_rng_deterministic` | `src/entropy_src/tb/physical_rng_deterministic.sv` | Fully deterministic LFSR nibble stream (holds on disable), for reproducible conditioned/multi-seed tests |
| RNG source MUX | `src/integration/tb/caliptra_top_tb.sv` | Per-source MUX between `physical_rng` and `physical_rng_deterministic`, selected by `+CLP_DETERMINISTIC_RNG` (default off, existing tests unaffected) |

Functional coverage, including zeroize scenarios, is collected by
`src/entropy_combiner/coverage/entropy_combiner_cov_if.sv`. Source declarations
and implemented cases must be checked against the merged coverage results.

### Security Enforcement

| Mechanism | RTL Location | Description |
| :-------- | :----------- | :---------- |
| Internal KAT snapshot clearing on lock | `entropy_combiner.sv` | `ahb_locked` synchronously clears and holds `kat_msg_q`, `kat_msg_len_q`, `kat_digest_q`, and `kat_digest_valid_q` at zero |
| KAT result/status masking on lock | `entropy_combiner.sv` | `KAT_DIGEST` readback and `KAT_STATUS.busy/valid` are forced to zero while locked |
| Software-owned KAT input clearing | `entropy_combiner.sv` | `KAT_MSG` and `KAT_MSG_LEN` hardware clear inputs are driven by zeroize, not `ahb_locked`; locking does not clear or hold these registers at zero |
| KAT blocked when locked | `entropy_combiner.sv` | `kat_start_cmd = start && !ahb_locked` -- no KAT can run once locked |
| FIPS policy freeze | `entropy_combiner.sv` | `COMBINER_CTRL.es_fips_policy/es_fips_cfg` `swwe = !ahb_locked` -- ROM freezes the combine policy after lock |
| Lock write-once-sticky | `entropy_combiner_reg.rdl` | MuBi4 `AHB_LOCK` `swwe=strict-False`; any non-strict-False code is treated as locked (fail-safe); clears only on reset |
| Boot-phase automatic lock | `entropy_combiner.sv` | Runtime-active locks AHB without ROM writing AHB_LOCK; deasserting runtime-active does not unlock it |
| No raw entropy on bus | `entropy_combiner.sv` | ES0/ES1 -> SHA3 -> CSRNG is internal only; no readable register exposes raw entropy |
| Sparse-FSM fail-safe | `entropy_combiner.sv` | An undefined FSM state traps to `combiner_st_error` (self-loop), emits no CSRNG ack, and recovers only on reset (verified by `entropy_combiner_es_csrng_tb` case5) |

### Regression

- `src/integration/stimulus/L0_ss_mode_regression.yml` -- all five combiner firmware tests
- `src/entropy_combiner/stimulus/testsuites/entropy_combiner_nightly_directed_regression.yml` -- full-chain unit bench
- Unit-bench build targets and directed YAMLs are under `src/entropy_combiner/config/` and `src/entropy_combiner/stimulus/tests/directed/`

---

## ICCM Write Hash Measurement (PCR4/PCR5)

### Feature Summary

Subsystem-only hardware SHA-384 measurement of ICCM writes during firmware loading. The SHA-512 accelerator computes the hash and extends it into PCR4 (Current, cleared through `iccm_unlock` for a new load) and PCR5 (Journey, retained across FW updates). Cold reset clears both; the firmware clear escape hatch is tested separately.

### Test Suite

| Test | Category | Description |
| :--- | :------- | :---------- |
| `smoke_test_iccm_hash` | Smoke | Exclude poison writes while SHA lock is held, then measure 4 known words and cross-check PCR4 against a PCR0 extend |
| `directed_test_iccm_hash` | Directed | Multi-block, extra-pad, zero-write attempt, exact-boundary, large, and tight-copy sequences; the zero-write attempt needs qualification |
| `directed_test_iccm_hash_sizes` | Directed | Size-boundary sequences (1, 60, 284 words) targeting byte-count / extra-pad coverpoint and cross bins |
| `directed_test_iccm_hash_fill` | Directed | Fill the ENTIRE ICCM (65536 dwords / 256 KiB) with an incrementing pattern; verify PCR4 & PCR5 match the full-ICCM extend-from-zero digest |
| `directed_test_iccm_hash_overflow` | Directed | Fill ICCM then explicitly rewrite `iccm[0]`; verify PCR4 & PCR5 hash all 65537 writes |
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
1. Write poison data while the SHA accelerator lock is held; these writes must not be measured
2. Fence the writes, release the SHA lock, and write {0x1, 0x2, 0x3, 0x4}; the first eligible write arms measurement
3. Lock ICCM to finalize the hash and PCR4/PCR5 extends
4. Verify PCR4 matches `SHA-384(zeros || SHA-384(LE_iccm_data))`, excluding the poison writes
5. Extend PCR0 with the same ICCM digest and require PCR0 == PCR4

#### `directed_test_iccm_hash`

| Iter | Sequence | Description | Pass Criteria |
| :--- | :------- | :---------- | :------------ |
| 0 | 64 words {0x10..0x4F} | Multi-block (256 bytes, 2 SHA blocks + padding block) | PCR4 matches expected |
| 1 | 28 words {0xBB00..0xBB1B} | Extra padding block required (112 bytes) | PCR4 matches expected |
| 2 | 0 words | Zero-write attempt; no ICCM write to arm measurement | Pending qualification; not credited as demonstrated zero-length coverage |
| 3 | 32 words {0xC000..0xC01F} | Exact SHA-384 block boundary (128 bytes) | PCR4 matches expected |
| 4 | 260 words {0xD000..0xD103} | Large (1040 bytes, >1KB) | PCR4 matches expected |
| 5 | 64 words {0x10..0x4F} tight | Back-to-back `sw` pairs via inline asm (LSU merge test) | PCR4 matches seq 0 |

The test requests `fw_update_reset` between iterations, clearing PCR4 through
`iccm_unlock` and re-arming ICCM mode for the next load.

After the primary PCR4 check, each non-zero-length iteration runs an independent **readback cross-check**: the ICCM contents are read back and re-hashed with the SHA512 *controller* (byte-swapped so its big-endian BLOCK interpretation matches the snoop's little-endian byte stream, with FW-driven padding), spare PCR0 is cleared and extended from zero with that digest via `pcr_hash_extend`, and the test asserts `PCR0 == expected vector == PCR4`.

The zero-write iteration performs no arm-triggering write but still waits for
nonzero PCR4. Resolve that sequence's arming/expected-result behavior before
crediting it; its presence in the source is not proof of working empty-message
measurement.

#### `directed_test_iccm_hash_sizes`

Size-boundary sequences (each separated by `fw_update_reset`) targeting
`iccm_hash_cov_grp` coverpoint/cross bins not targeted by the base vectors:

| Seq | Sequence | Coverage Target |
| :-- | :------- | :-------------- |
| A | 1 word (4 bytes) | `iccm_byte_count_cp.min_write`; `byte_count×extra_pad.(min_write,0)` |
| B | 60 words (240 bytes) | `byte_count×extra_pad.(multi_block,1)` — 112-byte last-block remainder forces an extra pad block |
| C | 284 words (1136 bytes) | `byte_count×extra_pad.(large_sz,1)` — 112-byte last-block remainder forces an extra pad block |

#### `directed_test_iccm_hash_fill`

Single-shot measurement (no `fw_update_reset`):
1. Fill the ENTIRE ICCM (`RV_ICCM_SIZE` = 256 KiB = 65536 dwords) with an incrementing pattern (dword `i` = `i`); HW arms on the first write
2. Lock ICCM → hash finalization over the full stream `{0, 1, ..., 65535}` + PCR4/PCR5 extend
3. Verify PCR4 (Current) and PCR5 (Journey) both equal `SHA-384(48_zeros || SHA-384(LE {0..65535}))` — both extend from zero, so PCR4 == PCR5

Passive (non-subsystem) mode: feature absent — verifies PCR4/PCR5 stay zero.

#### `directed_test_iccm_hash_overflow`

Single-shot full-buffer overwrite test (no `fw_update_reset`):
1. Fill the entire ICCM (65536 dwords), then explicitly write value 65536 to `iccm[0]`
2. Lock ICCM → the HW snoop still hashes every write, so the hashed stream is `{0, 1, ..., 65536}` (65537 dwords)
3. Verify PCR4 and PCR5 both equal the extend-from-zero digest of that write stream (PCR4 == PCR5)

This checks hashing of a repeated address, not physical wrapping of a past-end
ICCM address.

Passive mode: verifies PCR4/PCR5 stay zero.

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
| Autonomous arming | `sha512_acc_top.sv` | `iccm_armed` sticky flop set combinationally by the first ICCM-write snoop; HW also acquires the SHA acc LOCK in the same cycle via `LOCK.hwset` |
| Hash measurement single-shot | `sha512_acc_top.sv` | `iccm_mode_done` sticky flag prevents re-trigger until `iccm_unlock` (which fires on `fw_update_reset`) |
| PCR4 clear on FW update | `pv.sv` | Current-PCR hardware clear is qualified by `iccm_unlock` |
| FW isolation | `sha512_acc_top.sv` | All extend FSM control signals (pv_read, write_entry, init) driven by HW state only — no CSR interface |
| PCR extend correctness | `sha512_acc_top.sv` | Extend FSM uses same `kv_read_client` + `sha512_core` + `kv_write_client` pattern as sha512.sv PCR extend |

### Regression

- `src/integration/stimulus/L0_regression.yml` -- smoke_test_iccm_hash
- `src/integration/stimulus/testsuites/caliptra_top_nightly_directed_regression.yml` -- directed_test_iccm_hash, directed_test_iccm_pcr5_journey, directed_test_iccm_fw_write_block, directed_test_iccm_sha_ctrl_block, directed_test_iccm_clear_hatch, directed_test_iccm_sha_acc_reuse, directed_test_iccm_cold_reset_pcr5, directed_test_iccm_replay_block, directed_test_iccm_hash_sizes, directed_test_iccm_hash_fill, directed_test_iccm_hash_overflow

All twelve suites must be exercised with the Subsystem build
(`caliptra_top_ss_mode_tb`) to credit measurement behavior. Several tests skip or
only check zero PCRs in Passive mode. Confirm the nightly build/profile mapping;
the explicit subsystem L0 list does not currently enroll these ICCM tests.

---

## DCLS Reporting in Passive and Subsystem Profiles

In both profiles, verify that `dcls_en=0` suppresses normal mismatch reporting and
`dcls_en=1` enables fatal reporting, with matching `DCLS_en` readback. Enabled and
disabled runs are required in both Passive and Subsystem configurations.

| Test / YAML variant | Coverage |
| :--- | :--- |
| `smoke_test_dcls_inject` | Enabled readback and testbench-owned fatal verdict (`+CLP_DCLS_EN`) |
| `smoke_test_dcls_dis` | Disabled readback and reporting suppression (`+CLP_DCLS_DIS`) |
| `smoke_test_hw_config` | Profile and enabled readback |
| `dcls_hw_config_test` (SoC-IFC unit test) | DCLS configuration readback and transitions |
| `directed_dcls_reporting_outputs` | Output comparator mismatch and fatal handling |
| `directed_dcls_reporting_regfile` | Register-file comparator mismatch |
| `directed_dcls_reporting_control` | Runtime enable/disable transitions and sticky fatal state |
| `directed_dcls_reporting_qualifications` | Debug/reset qualifications and invalid MuBi encoding |
| `c_intr_handler_sync_rand` (YAML variant) | Interrupt regression with randomized synchronizer latency and enabled DCLS |
| `smoke_test_wdt_sync_rand` (YAML variant) | Watchdog regression with randomized synchronizer latency and enabled DCLS |

The four `directed_dcls_reporting_*` YAMLs share
`src/integration/test_suites/directed_dcls_reporting/directed_dcls_reporting.c`
and select VCS testbench scenarios; they are not four different C programs.
The randomized synchronizer variants use `+RV_SYNC_RAND_DELAY` and
`+CLP_DCLS_EN`.

### Regression and Profiles

- `src/integration/stimulus/L0_regression.yml` -- enabled/disabled firmware smoke and HW configuration readback
- `src/integration/stimulus/L0_ss_mode_regression.yml` -- enabled/disabled firmware smoke and the two randomized synchronizer variants
- `src/integration/stimulus/testsuites/caliptra_top_nightly_directed_regression.yml` -- the four directed reporting variants and smoke/configuration tests
- `src/soc_ifc/stimulus/testsuites/soc_ifc_nightly_directed_regression_1.yml` -- unit-level `dcls_hw_config_test`

Confirm both-profile execution of the four directed variants and HW configuration
test; a common nightly registration is not itself evidence of a profile sweep.

---

## Fault Injection Countermeasures for FSMs, Debug Controls, and ICCM Regions

### Feature Summary

Sparse FSM encodings, multi-bit debug/boot controls, and shadow-protected ICCM
region registers are exercised through directed fault injection and normal
debug/reset qualification. Expected outcomes are case-specific: a terminal FSM
fault, a rejected shadow update, and a qualified debug/scan transition are not
interchangeable verdicts.

### Test Content

| Test / Check | Type | Checks |
| :----------- | :--- | :----- |
| `directed_fsm_glitch_inject` | Firmware + testbench | DOE, SHA accelerator, mailbox, and boot-FSM fault requests; fatal-observed markers checked across reset-separated cases |
| `directed_kv_glitch_inject` | Firmware + testbench | MuBi glitch/recovery, shadow storage fault detection, write lockout, fatal-status persistence, and W1C after reset |
| `directed_kv_iccm_region` | Firmware | Uncommitted/locked region writes, mismatched shadow writes, unlocked fetches, and out-of-range fetches |
| `directed_kv_debug_scan_bypass` | Firmware + testbench | Monitor qualification through debug-unlock and scan-mode transitions |
| `directed_dcls_reporting_qualifications` | VCS YAML variant | DCLS debug/reset qualification and invalid multi-bit control scenarios |
| `verify-prim-swap.yml` | CI build check | Technology primitive substitution resolves and elaborates with the fake technology wrappers |

KV assertion and covergroup sources are listed in the [Key Vault section](#key-vault-boot-flow-monitoring-enforcement-and-key-length-checks).
The DCLS variants and required profile sweep are listed in the [DCLS section](#dcls-reporting-in-passive-and-subsystem-profiles).
The glitch tests rely on testbench services; their firmware PASS conditions must
be evaluated together with the testbench's injection and fatal/reset verdicts.

### Regression and Build Checks

- `src/integration/stimulus/testsuites/caliptra_top_nightly_directed_regression.yml` -- FSM and KV glitch/debug/region tests plus the DCLS qualification variant
- `src/integration/stimulus/testsuites/caliptra_top_kv_monitor_regression.yml` -- KV glitch/debug/region tests
- `.github/workflows/verify-prim-swap.yml` -- Verilator build/elaboration using `tools/ci/fake_prim/rtl`

The primitive-swap workflow runs `verilator-build`, not a simulation. It checks
wrapper/module resolution and port connectivity; it does not demonstrate runtime
fault response or physical glitch resistance.

---

## HMAC512 Area Optimization and Multi-block Interface

### Feature Summary

Functional regressions validate the area-optimized HMAC384/512 implementation
and updated multi-block command interface. Masking predates this release.
An operation begins with INIT and finishes with LAST, using INIT|LAST for a
single block or NEXT|LAST for the final block of a multi-block message.

### Test Content

| Test / Check | Type | Checks |
| :----------- | :--- | :----- |
| `smoke_test_hmac` | Firmware | HMAC384/512, CSR mode, and existing multi-block goldens with explicit LAST |
| `smoke_test_kv_hmac_multiblock_flow` | Firmware | Non-final and final commands in an existing KV-backed multi-block flow |
| `smoke_test_hmac_kv_multiblock_no_leak` | Firmware | Final-only KV writes; hidden KV intermediate/final tags; ignored key overwrites; orphan NEXT rejection; save-path visibility; blocked mid-operation KV loads and CSR provenance |
| `smoke_test_fw_kv_backtoback_hmac` | Firmware | After a KV-keyed operation, a fresh FW operation matches the independent zero-key HMAC384 golden |
| `smoke_test_hmac_errortrigger` | Firmware | LAST-alone error interrupt followed by zeroize, in addition to existing error cases |
| `hmac_ctrl_tb.sv` | Unit bench | HMAC controller sequencing and multi-block reference vectors |
| `HMAC_last_alone_error_test` | UVMF | LAST-alone command sets the expected error status and exercises the corresponding coverage |

Compatibility regressions `smoke_test_kv_hmac_flow`,
`smoke_test_hmac_kv_ocp_progress`, `smoke_test_kv_crypto_flow`,
`smoke_test_kv_crypto_flow2`, and `smoke_test_kv_doe` retain existing crypto/KV
flows with updated LAST/zeroize handling and checked KV status. Interface
adaptations are not counted as new independent algorithm scenarios.

### Expected Checks

| Scenario | Expected Result |
| :------- | :-------------- |
| INIT/NEXT/LAST sequencing | Existing single- and multi-block goldens match |
| KV provenance across blocks | KEY locking and result visibility remain protected until final completion or zeroize |
| Non-final KV operation | No premature KV result write or exposed intermediate TAG |
| Orphan NEXT or LAST alone | Expected command error, not an accepted new operation |
| Key/control write during operation | Protected settings do not change the in-flight operation |
| Operation after KV use | No unintended reuse of the previous KV operand |

Zeroize/control cross coverage is in
`src/hmac/coverage/hmac_ctrl_cov_if.sv`. Area/timing qualification is separate
from these functional comparisons.

### Regression

- `src/integration/stimulus/L0_regression.yml` -- HMAC smoke, error trigger, back-to-back, and existing KV-flow tests
- `src/integration/stimulus/testsuites/caliptra_top_nightly_directed_regression.yml` -- dedicated provenance and multi-block tests plus compatibility flows
- `src/integration/stimulus/testsuites/caliptra_top_tb_nightly_random_regression.yml` -- OCP/KV compatibility flows
- `src/hmac/config/compile.yml` -- unit-bench targets
- `src/hmac/uvmf_2022/uvmf_template_output/project_benches/HMAC/tb/tests/src/HMAC_last_alone_error_test.yml` -- UVMF LAST-alone test

---

## CSR HMAC Key Lock

### Feature Summary

ROM sets the sticky `internal_csr_hmac_key_lock` before the FMC handoff.
Locking clears the latched manufacturing CSR HMAC key and prevents later
firmware from using it. FW-update reset retains the lock; warm/cold reset
clear it.

### Test Content

`smoke_test_hmac_csr_key_lock` runs three manufacturing-state firmware boots.
The key-use oracle is the HMAC result, not raw secret-key register readback.

| Scenario | Expected Result |
| :------- | :-------------- |
| Before locking | CSR-mode HMAC matches the CSR-key golden |
| Set the lock | CSR-mode HMAC matches the zero-key golden |
| Attempt to clear a set lock | Lock remains set |
| FW-update reset | Lock remains set and the old CSR key remains unavailable |
| Warm reset | Lock reads clear |

Use the test's manufacturing-state setup and reference vectors. This entry does
not by itself qualify every lifecycle/debug/scan configuration of CSR-key
capture.

### Regression

- `src/integration/stimulus/L0_regression.yml`
- `src/integration/stimulus/testsuites/caliptra_top_nightly_directed_regression.yml`

---

## ECC Area Optimization, Zeroization, and Key Vault Operand Clearing

### Feature Summary

Existing ECC known-answer regressions validate arithmetic changes in the
area-optimized implementation. Operation-boundary tests exercise mandatory
zeroization, command/KV-control lockout, recovery, and compatibility with
KV-backed flows. Hardware clearing of KV-sourced seed/private-key operands
requires an explicit data-clearing oracle in addition to command lockout checks.

### Test Content

| Test / Check | Type | Checks |
| :----------- | :--- | :----- |
| `smoke_test_ecc_keygen` | Firmware | Existing key-generation golden after interface/zeroize adaptations |
| `smoke_test_ecc_sign` | Firmware | Existing signing golden after interface/zeroize adaptations |
| `smoke_test_ecc_verify` | Firmware | Valid signature verification and zeroize/status handling |
| `smoke_test_ecc_pcr_zeroize` | Firmware | PCR-sign golden; commands and KV controls blocked until zeroize; PCR_SIGN-alone error/lockout; successful signing after recovery |
| `smoke_test_ecc_errortrigger2` | Firmware | PCR_SIGN-alone is rejected rather than ignored; zeroize permits recovery |
| `smoke_test_ecc_errortrigger5` | Firmware | Existing invalid-key injection test enrolled with a deterministic seed; not a new arithmetic scenario |
| `smoke_test_ecc_flow1_kv_ocp_progress` / `smoke_test_ecc_flow2_kv_ocp_progress` | Firmware | Zeroize after rejected KV reads, then rerun the operation so write-side rejection checks are still exercised |
| `ecc_montgomerymultiplier_tb.sv` | Unit bench | Montgomery multiplication reference vectors for the arithmetic implementation |
| `ecc_top_cov_if.sv` | Coverage | Zeroize crossed with PCR-sign mode, command, error, and ready state |

Unit source locations are `src/ecc/tb/` and `src/ecc/coverage/`.
Verification-pass assertions in these firmware tests are detailed in the
[verification-status section](#ecc-and-ml-dsa-verification-pass-status).

### Coverage to Qualify

Mandatory-zeroize lockout, readback restrictions, and a zeroize coverpoint do
not prove that KV-sourced seed/private-key storage was cleared at each required
operation boundary. A direct operand-clearing assertion/oracle was not
established by the test-content audit; identify and qualify that check, or add
targeted content, before claiming this part of the feature closed.

Area and timing comparisons require implementation results rather than KAT
passes alone.

### Regression

- `src/integration/stimulus/testsuites/caliptra_top_nightly_directed_regression.yml` -- ECC KATs, PCR-zeroize, and error tests
- `src/integration/stimulus/testsuites/caliptra_top_tb_nightly_random_regression.yml` -- OCP/KV recovery flows
- `src/ecc/config/compile.yml` -- unit-bench targets and arithmetic vectors

---

## ECC and ML-DSA Verification-pass Status

### Feature Summary

Explicit VERIFY_PASS status distinguishes a valid signature from a normal
comparison mismatch. Tests cross-check that status against independently
checked verification results, rather than treating absence of an error
interrupt as proof of a valid signature.

### Test Content

| Test / Group | Checks |
| :----------- | :----- |
| `smoke_test_ecc_verify` | Valid verification requires VERIFY_PASS=1; zeroize clears it |
| `smoke_test_ecc_verify_fail` | Mutated message with otherwise valid inputs produces VERIFY_PASS=0 without an error interrupt |
| `smoke_test_ecc_keygen` / `smoke_test_ecc_sign` | Non-verification commands leave VERIFY_PASS=0 |
| `smoke_test_ecc_errortrigger1` / `smoke_test_ecc_errortrigger2` / `smoke_test_ecc_errortrigger3` | Errored operations do not advertise successful verification |
| `smoke_test_mldsa_keygen_sign_vfy_rand` | KEYGEN_SIGN reports 0, valid VERIFY reports 1, and zeroize clears the verdict |
| `smoke_test_mldsa_keygen_standalone_sign_vfy_rand` | Standalone KEYGEN/SIGN report 0 and valid VERIFY reports 1 |
| `smoke_test_mldsa_externalmu_keygen_sign_vfy_rand` | External-Mu KEYGEN_SIGN reports 0 and valid VERIFY reports 1 |
| `randomized_mldsa_invalid_verify` | Invalid verification requires VERIFY_PASS=0 |
| `smoke_test_mldsa_edge` | Norm-aborted verification requires VERIFY_PASS=0 with the appropriate result-data reference |
| `smoke_test_mldsa_errortrigger` | Errored/invalid-hint operations require VERIFY_PASS=0 |
| `smoke_test_mldsa` / `smoke_test_mldsa_externalmu` | Existing valid-verification flows inherit independent result-versus-status checks |

Shared checks are in `src/integration/test_suites/libs/ecc/ecc.c` and
`src/integration/test_suites/libs/mldsa/mldsa.c`. Positive, negative,
non-verification, and zeroize-cleared status are distinct checks; credit only
the cases actually present in each test.

### Regression

- `src/integration/stimulus/testsuites/caliptra_top_nightly_directed_regression.yml` -- ECC verification/status tests and ML-DSA external-Mu smoke
- `src/integration/stimulus/testsuites/caliptra_top_tb_nightly_random_regression.yml` -- ML-DSA random, invalid, edge, error, and external-Mu flows
- `src/integration/stimulus/testsuites/caliptra_top_abr_regression.yml` -- ML-DSA status consumers

---

## Stash-measurement Register Bank

### Feature Summary

The SoC-side register bank carries initial measurement stashes with
mailbox-matching AXI USER filtering, per-slot locking, end-stash control, and
Caliptra sealing. Passive mode has the multi-slot bank; Subsystem mode exposes
only slot 0 and must not permit writes through the unused slots.

### Test Content

| Test | Checks |
| :--- | :----- |
| `smoke_test_stash_bank` | Slot data/status patterns, invalid-PAUSER overwrite rejection, lock readback, and Caliptra sealing |
| `smoke_test_stash_bank_negative` | Locked-slot writes, bad PAUSER, end-stash clear attempts, and SoC attempts to change Caliptra-only lock controls |
| `smoke_test_stash_bank_cptra_lock` | Seal after partial slot-0 population; subsequent SoC data/control writes are blocked, including unlocked slots |
| `smoke_test_stash_bank_rst` | Reject FW writes to SoC-owned stash registers, check sticky locks, and verify status clearing across warm reset |
| `smoke_test_stash_bank_ss` | Slot-0 26-word pattern, only lock bit 0 implemented, slots 1-7 read zero and reject writes, and Caliptra sealing |

These are firmware plus testbench-actor flows. Use `+CALIPTRA_TEST_STASH_BANK`
and the additional negative/Caliptra-lock/reset scenario plusargs from each
YAML. Run the multi-slot checks in Passive mode and the explicit single-slot
variant with `caliptra_top_ss_mode_tb`.

### Expected Checks

| Scenario | Expected Result |
| :------- | :-------------- |
| Authorized population | Slot data and status match the testbench's complete pattern |
| Invalid identity or locked slot | Protected data/control state is unchanged |
| Caliptra seal | Later SoC writes cannot change data or protected controls |
| Ownership | FW cannot write SoC-only registers; SoC cannot change Caliptra-only locking |
| Warm reset | Tested status/lock fields return to their reset state |
| Subsystem unused slots | Read zero and cannot be populated by an otherwise valid SoC user |

### Regression

- `src/integration/stimulus/L0_regression.yml` -- normal and negative stash tests
- `src/integration/stimulus/L0_ss_mode_regression.yml` -- explicit Subsystem slot-0 test
- `src/integration/stimulus/testsuites/caliptra_top_nightly_directed_regression.yml` -- normal, negative, seal, and reset cases
