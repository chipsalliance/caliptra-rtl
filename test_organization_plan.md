# Plan: Test Suite Reorganization (caliptra-rtl)

## Problem Statement

All 169 test suites in `src/integration/test_suites/` are in a flat directory with inconsistent naming. Reorganize into:
- `smoke/` — Small directed tests ensuring basic functionality works at all
- `directed/` — Targeted tests focused on a specific feature or set of behaviors
- `random/` — Tests employing randomness for in-depth coverage

Test names inside each category drop the category prefix (e.g., `smoke_test_kv` → `smoke/kv`).

## Directory Structure (New)

```
src/integration/test_suites/
├── smoke/          # Basic functionality
├── directed/       # Feature-focused multi-scenario
├── random/         # Randomized in-depth
├── firmware/       # Pre-compiled FW images (not tests)
└── libs/           # Shared libraries (existing)
    includes/       # Shared headers (existing)
```

## Classification Rules

1. **Random**: Any test that uses randomization (random seeds, random inputs, random iteration counts) MUST be classified as `random/` regardless of its current name. Its `.yml` file MUST contain a `seed:` field. If a test currently named `smoke_test_*` or `directed_*` uses randomness, it moves to `random/`.
2. **Smoke**: Small, deterministic, single-scenario tests that verify basic module functionality. No randomness. Should pass quickly and reliably every run.
3. **Directed**: Deterministic multi-scenario or negative tests targeting specific features/behaviors. No randomness. May have multiple iterations but all inputs are fixed.

**Implication**: During implementation, every test must be inspected for random seed usage, `$random`, LFSR patterns, or test infrastructure that injects randomness. The grep results from earlier show ~48 tests reference "rand/random" — many currently classified as `smoke/` or `directed/` above may need reclassification after deeper inspection.

## Classification

### Infrastructure (not tests — keep as-is)
| Current Name | Action |
|-------------|--------|
| `includes/` | Keep as `includes/` |
| `libs/` | Keep as `libs/` |
| `c_intr_handler` | Keep as `libs/c_intr_handler` or leave as-is |
| `infinite_loop` | Keep as `libs/infinite_loop` or leave as-is (utility) |

### Pre-compiled Firmware Images → `firmware/`
| Current Name | New Name | Notes |
|-------------|----------|-------|
| `fw_test_rom` | `firmware/fw_test_rom` | Pre-compiled ROM ELF |
| `fw_test_lms24` | `firmware/fw_test_lms24` | 34 LMS parameter variants |
| `fw_test_lms32` | `firmware/fw_test_lms32` | |
| `fw_test_lms_n24_w{1,2,4,8}_h{5,10,15,20}` | `firmware/fw_test_lms_n24_w*_h*` | (16 variants) |
| `fw_test_lms_n32_w{1,2,4,8}_h{5,10,15,20}` | `firmware/fw_test_lms_n32_w*_h*` | (16 variants) |
| `caliptra_fmc` | `firmware/caliptra_fmc` | FMC image |
| `caliptra_rt` | `firmware/caliptra_rt` | Runtime image |
| `cptra_ss_test_rom` | `firmware/cptra_ss_test_rom` | SS test ROM |

### Smoke Tests → `smoke/`
Basic sanity: "does this module respond at all?"

| Current Name | New Name | Rationale |
|-------------|----------|-----------|
| `caliptra_top` | `smoke/caliptra_top` | Basic top-level boot check |
| `caliptra_demo` | `smoke/caliptra_demo` | Demo end-to-end flow |
| `hello_world_iccm` | `smoke/hello_world_iccm` | Basic ICCM exec |
| `smoke_test_kv` | `smoke/kv` | Basic KV access |
| `smoke_test_mbox` | `smoke/mbox` | Basic mailbox |
| `smoke_test_hmac` | `smoke/hmac` | Basic HMAC |
| `smoke_test_ecc_keygen` | `smoke/ecc_keygen` | Basic ECC keygen |
| `smoke_test_ecc_sign` | `smoke/ecc_sign` | Basic ECC sign |
| `smoke_test_ecc_verify` | `smoke/ecc_verify` | Basic ECC verify |
| `smoke_test_ecdh` | `smoke/ecdh` | Basic ECDH |
| `smoke_test_sha256` | `smoke/sha256` | Basic SHA-256 |
| `smoke_test_sha512` | `smoke/sha512` | Basic SHA-512 |
| `smoke_test_sha3` | `smoke/sha3` | Basic SHA-3 |
| `smoke_test_sha_accel` | `smoke/sha_accel` | Basic SHA accelerator |
| `smoke_test_mldsa` | `smoke/mldsa` | Basic MLDSA |
| `smoke_test_mldsa_kat` | `smoke/mldsa_kat` | MLDSA known-answer test |
| `smoke_test_mlkem` | `smoke/mlkem` | Basic MLKEM |
| `smoke_test_mlkem_shared_key` | `smoke/mlkem_shared_key` | Basic MLKEM shared key |
| `smoke_test_cshake` | `smoke/cshake` | Basic CSHAKE |
| `smoke_test_trng` | `smoke/trng` | Basic TRNG |
| `smoke_test_uart` | `smoke/uart` | Basic UART |
| `smoke_test_qspi` | `smoke/qspi` | Basic QSPI |
| `smoke_test_veer` | `smoke/veer` | Basic VeeR core |
| `smoke_test_wdt` | `smoke/wdt` | Basic WDT |
| `smoke_test_dma` | `smoke/dma` | Basic DMA |
| `smoke_test_hw_config` | `smoke/hw_config` | HW config readback |
| `smoke_test_strap` | `smoke/strap` | Strap sampling |
| `smoke_test_clk_gating` | `smoke/clk_gating` | Basic clock gating |
| `smoke_test_sram_ecc` | `smoke/sram_ecc` | Basic SRAM ECC |
| `smoke_test_sha256_wntz` | `smoke/sha256_wntz` | Basic SHA-256 Winternitz |
| `smoke_test_mldsa_sign_rnd` | `smoke/mldsa_sign_rnd` | Basic MLDSA sign with rnd |

### Directed Tests → `directed/`
Multi-scenario, feature-focused, or negative tests.

| Current Name | New Name | Rationale |
|-------------|----------|-----------|
| **KV Transition Enforcement** | | |
| `smoke_test_kv_boot_flow_monitor` | `directed/kv_boot_flow_monitor` | Multi-iteration boot flow |
| `smoke_test_kv_enforcement` | `directed/kv_enforcement` | 7-scenario enforcement |
| `smoke_test_kv_iccm_region` | `directed/kv_iccm_region` | 7-iteration region test |
| `smoke_test_kv_monitor_neg` | `directed/kv_monitor_neg` | 8-iteration negative test |
| **KV Crypto Flows** | | |
| `smoke_test_kv_crypto_flow` | `directed/kv_crypto_flow` | Multi-engine crypto pipeline |
| `smoke_test_kv_crypto_flow2` | `directed/kv_crypto_flow2` | Extended crypto pipeline |
| `smoke_test_kv_doe` | `directed/kv_doe` | DOE→KV flow |
| `smoke_test_kv_ecc_flow1` | `directed/kv_ecc_flow1` | ECC via KV |
| `smoke_test_kv_ecc_flow2` | `directed/kv_ecc_flow2` | ECC via KV (variant) |
| `smoke_test_kv_ecdh_flow` | `directed/kv_ecdh_flow` | ECDH via KV |
| `smoke_test_kv_hmac_flow` | `directed/kv_hmac_flow` | HMAC via KV |
| `smoke_test_kv_hmac_multiblock_flow` | `directed/kv_hmac_multiblock_flow` | Multi-block HMAC via KV |
| `smoke_test_kv_mldsa` | `directed/kv_mldsa` | MLDSA via KV |
| `smoke_test_kv_parallel_access` | `directed/kv_parallel_access` | Parallel KV access |
| **KV Security & Locking** | | |
| `smoke_test_kv_securitystate` | `directed/kv_securitystate` | KV security state checks |
| `smoke_test_kv_swwe_lock` | `directed/kv_swwe_lock` | KV SW write-enable lock |
| `smoke_test_kv_lock_use_mid_read` | `directed/kv_lock_use_mid_read` | Lock during read |
| `smoke_test_kv_uds_reset` | `directed/kv_uds_reset` | UDS reset behavior |
| `smoke_test_kv_write_scan_mode` | `directed/kv_write_scan_mode` | Write in scan mode |
| `smoke_test_kv_cg` | `directed/kv_cg` | KV clock gating |
| `smoke_test_kv_rules_ocp_lock` | `directed/kv_rules_ocp_lock` | OCP lock rule enforcement |
| **DOE** | | |
| `smoke_test_doe_cg` | `directed/doe_cg` | DOE clock gating |
| `smoke_test_doe_scan` | `directed/doe_scan` | DOE scan mode |
| `smoke_test_doe_kv_ocp_progress` | `directed/doe_kv_ocp_progress` | DOE OCP lock flow |
| **DMA / AES-GCM** | | |
| `smoke_test_dma_aes_gcm` | `directed/dma_aes_gcm` | DMA+AES-GCM flow |
| `smoke_test_dma_aes_gcm_cmd_err` | `directed/dma_aes_gcm_cmd_err` | Command error handling |
| `smoke_test_dma_aes_gcm_collision_test` | `directed/dma_aes_gcm_collision` | Collision scenario |
| `smoke_test_dma_aes_gcm_long` | `directed/dma_aes_gcm_long` | Long payload |
| `smoke_test_dma_aes_gcm_non_gcm_en_dec` | `directed/dma_aes_gcm_non_gcm` | Non-GCM enc/dec |
| `smoke_test_dma_aes_gcm_rd_enc_axi_err` | `directed/dma_aes_gcm_rd_enc_axi_err` | Read encrypt AXI error |
| `smoke_test_dma_aes_gcm_short_1_dword` | `directed/dma_aes_gcm_short_1dw` | 1 dword payload |
| `smoke_test_dma_aes_gcm_short_dword` | `directed/dma_aes_gcm_short_dw` | Short payload |
| `smoke_test_dma_aes_gcm_wr_enc_axi_err` | `directed/dma_aes_gcm_wr_enc_axi_err` | Write encrypt AXI error |
| `smoke_test_dma_aes_kv` | `directed/dma_aes_kv` | DMA+AES via KV |
| `smoke_test_aes_gcm` | `directed/aes_gcm` | AES-GCM standalone |
| **ECC** | | |
| `smoke_test_ecc_errortrigger1` | `directed/ecc_errortrigger1` | ECC error injection 1 |
| `smoke_test_ecc_errortrigger2` | `directed/ecc_errortrigger2` | ECC error injection 2 |
| `smoke_test_ecc_errortrigger3` | `directed/ecc_errortrigger3` | ECC error injection 3 |
| `smoke_test_ecc_errortrigger4` | `directed/ecc_errortrigger4` | ECC error injection 4 |
| `smoke_test_ecc_errortrigger5` | `directed/ecc_errortrigger5` | ECC error injection 5 |
| `smoke_test_ecc_flow1_kv_ocp_progress` | `directed/ecc_flow1_kv_ocp` | ECC OCP flow 1 |
| `smoke_test_ecc_flow2_kv_ocp_progress` | `directed/ecc_flow2_kv_ocp` | ECC OCP flow 2 |
| **HMAC** | | |
| `smoke_test_hmac_errortrigger` | `directed/hmac_errortrigger` | HMAC error trigger |
| `smoke_test_hmac_kv_ocp_progress` | `directed/hmac_kv_ocp` | HMAC OCP flow |
| `smoke_test_fw_kv_backtoback_hmac` | `directed/fw_kv_backtoback_hmac` | Back-to-back HMAC |
| `smoke_test_hek_flow` | `directed/hek_flow` | HEK flow |
| **MLDSA** | | |
| `smoke_test_mldsa_edge` | `directed/mldsa_edge` | Edge cases |
| `smoke_test_mldsa_errortrigger` | `directed/mldsa_errortrigger` | Error trigger |
| `smoke_test_mldsa_externalmu` | `directed/mldsa_externalmu` | External MU |
| `smoke_test_mldsa_locked_api` | `directed/mldsa_locked_api` | Locked API |
| `smoke_test_mldsa_zeroize` | `directed/mldsa_zeroize` | Zeroize |
| `smoke_test_mldsa_kv_ocp_progress` | `directed/mldsa_kv_ocp` | MLDSA OCP flow |
| `mldsa_pcr_inject_failure` | `directed/mldsa_pcr_inject_failure` | PCR inject failure |
| **MLKEM** | | |
| `smoke_test_mlkem_all_zero_seed` | `directed/mlkem_all_zero_seed` | Zero seed edge |
| `smoke_test_mlkem_errortrigger` | `directed/mlkem_errortrigger` | Error trigger |
| `smoke_test_mlkem_kv` | `directed/mlkem_kv` | MLKEM via KV |
| `smoke_test_mlkem_kv_endian` | `directed/mlkem_kv_endian` | Endianness |
| `smoke_test_mlkem_kv_ocp_progress` | `directed/mlkem_kv_ocp` | MLKEM OCP flow |
| `smoke_test_mlkem_locked_api` | `directed/mlkem_locked_api` | Locked API |
| **SHA** | | |
| `smoke_test_sha3_externalmu` | `directed/sha3_externalmu` | SHA3 external MU |
| `smoke_test_sha3_interrupt` | `directed/sha3_interrupt` | SHA3 interrupt |
| `smoke_test_sha3_regs` | `directed/sha3_regs` | SHA3 register access |
| `smoke_test_sha512_restore` | `directed/sha512_restore` | SHA-512 restore |
| **Datavault** | | |
| `smoke_test_datavault_basic` | `directed/datavault_basic` | DV basic ops |
| `smoke_test_datavault_lock` | `directed/datavault_lock` | DV lock behavior |
| `smoke_test_datavault_mini` | `directed/datavault_mini` | DV minimal test |
| `smoke_test_datavault_reset` | `directed/datavault_reset` | DV reset behavior |
| **Mailbox** | | |
| `smoke_test_mbox_byte_read` | `directed/mbox_byte_read` | Byte-level reads |
| `smoke_test_mbox_cg` | `directed/mbox_cg` | Mailbox clock gating |
| `jtag_tap_mbox` | `directed/jtag_tap_mbox` | JTAG mailbox access |
| **PCR** | | |
| `smoke_test_pcr_signing` | `directed/pcr_signing` | PCR signing |
| `smoke_test_pcr_zeroize` | `directed/pcr_zeroize` | PCR zeroize |
| `pv_hash_and_sign` | `directed/pv_hash_and_sign` | PV hash+sign flow |
| `pv_hash_reset` | `directed/pv_hash_reset` | PV hash reset |
| `pv_hash_zeroize` | `directed/pv_hash_zeroize` | PV hash zeroize |
| **ICCM / Memory** | | |
| `iccm_lock` | `directed/iccm_lock` | ICCM lock behavior |
| `smoke_test_iccm_reset` | `directed/iccm_reset` | ICCM reset |
| `memCpy_dccm_to_iccm` | `directed/memcpy_dccm_to_iccm` | DCCM→ICCM copy |
| `memCpy_ROM_to_dccm` | `directed/memcpy_rom_to_dccm` | ROM→DCCM copy |
| `kv_entry_read_err` | `directed/kv_entry_read_err` | KV read error |
| **Misc** | | |
| `smoke_test_cg_wdt` | `directed/cg_wdt` | Clock gating WDT |
| `smoke_test_wdt_rst` | `directed/wdt_rst` | WDT reset |
| `smoke_test_ras` | `directed/ras` | RAS error handling |
| `smoke_test_zeroize_crypto` | `directed/zeroize_crypto` | Crypto zeroize |
| `smoke_test_ahb_mux` | `directed/ahb_mux` | AHB mux arbitration |

### Random Tests → `random/`
Any test using randomization. Each `.yml` MUST have a `seed:` field.

| Current Name | New Name | Rationale |
|-------------|----------|-----------|
| `randomized_pcr_ecc_signing` | `random/pcr_ecc_signing` | Randomized PCR+ECC |
| `randomized_pcr_mldsa_signing` | `random/pcr_mldsa_signing` | Randomized PCR+MLDSA |
| `randomized_mldsa_invalid_verify` | `random/mldsa_invalid_verify` | Random invalid sigs |
| `rand_test_dma` | `random/dma` | Randomized DMA |
| `smoke_test_doe_rand` | `random/doe` | Randomized DOE |
| `smoke_test_aes_kv_rand` | `random/aes_kv` | Randomized AES KV |
| `smoke_test_aes_kv_out_rand` | `random/aes_kv_out` | Randomized AES KV output |
| `smoke_test_sha256_wntz_rand` | `random/sha256_wntz` | Randomized SHA256 Winternitz |
| `smoke_test_mldsa_keygen_sign_vfy_rand` | `random/mldsa_keygen_sign_vfy` | Random MLDSA full flow |
| `smoke_test_mldsa_externalmu_keygen_sign_vfy_rand` | `random/mldsa_externalmu_keygen_sign_vfy` | Random MLDSA ext-MU |
| `smoke_test_mldsa_keygen_standalone_sign_vfy_rand` | `random/mldsa_keygen_standalone_sign_vfy` | Random MLDSA standalone |

**NOTE**: The following tests from the smoke/directed tables above also use randomness and must be reclassified to `random/` after inspection confirms they have non-deterministic behavior. Candidates include:
- `smoke_test_datavault_basic` — uses random-like patterns
- `smoke_test_dma_aes_gcm_collision_test` — collision implies randomized inputs
- `smoke_test_dma_aes_gcm_long` — may use random payloads
- `smoke_test_kv_crypto_flow` / `crypto_flow2` — may randomize key material
- Any other test found to use `$random`, seeds, or LFSR-driven stimulus

These will be confirmed during implementation by grepping each test for randomness patterns.

## Implementation Approach

### What Changes Per Test
For each test rename `old_name` → `category/new_name`:
1. `mv src/integration/test_suites/old_name/ src/integration/test_suites/category/new_name/`
2. Rename `.c`, `.yml`, `.ld`, `.h` files inside to match `new_name`
3. Update `testname:` field in `.yml` to `new_name`
4. Update all regression YAML files that reference the old path
5. Update any `#include` or cross-references if applicable

### Regression YAML Updates
All files in `src/integration/stimulus/testsuites/` must be updated:
- Path references change from `smoke_test_foo/smoke_test_foo.yml` → `smoke/foo/foo.yml`

### Risks
- Any CI/CD scripts referencing old test names will break
- Pre-compiled firmware paths change
- External tools (coverage scripts, test list generators) may hardcode names
- The `.ld` linker scripts typically don't reference their own name but verify

### Execution Order
1. Create the category directories (`smoke/`, `directed/`, `random/`, `firmware/`)
2. Move and rename all tests (batch script)
3. Update all `.yml` testname fields
4. Update all regression suite YAML files
5. Update `caliptra_top_kv_transition_enforcement_regression.yml`
6. Verify no broken references (`grep` for old names)
7. Run a representative subset of tests

## Summary Stats
| Category | Count |
|----------|-------|
| Smoke | ~30 |
| Directed | ~80 |
| Random | ~11 |
| Firmware | ~37 |
| Infrastructure | ~4 |
| **Total** | **~162** |

---

# (Previous Plan: RFC Test Plan — Remaining Implementation)

## Problem Statement

Map every item in the RFC test plan (Section "Test Plan") to its current implementation status and identify what remains.

## Status Inventory

### C Tests — Happy Path

| Test | RFC Description | Status | Notes |
|------|----------------|--------|-------|
| `smoke_test_kv_boot_flow_monitor` | Cold boot happy path | ✅ Done | Includes fw update reset cycle |
| Warm reset happy path | Cold boot → RT → warm reset → repeat | ❌ Not implemented | |
| Update reset happy path | Cold boot → RT → fw update reset → re-derive | ✅ Partial | Covered in happy path test's boot 1 cycle |

### C Tests — Monitor Violations (Negative)

| Test | RFC Description | Status | Notes |
|------|----------------|--------|-------|
| dest_valid mismatch ROM→FMC (slot 0) | Wrong dest_valid on UDS slot | ✅ Done | Iter 1 in monitor_neg |
| dest_valid mismatch FMC→RT (slot 9) | Wrong dest_valid on RT_MLDSA | ✅ Done | Iter 5 in monitor_neg |
| Missing key ROM→FMC (slot 6) | Skip populating FMC_CDI | ✅ Done | Iter 2 in monitor_neg |
| Missing key FMC→RT (slot 4) | Skip populating RT_CDI | ✅ Done | Iter 4 in monitor_neg |
| Glitch simulation (slot 2) | Slot 2 wrong dest_valid | ✅ Done | Iter 3 in monitor_neg |
| Write count too low — slot 6 | Only 1 HMAC write (expect ≥4) | ✅ Done | Iter 2 skips slot 6 entirely (count=0) |
| Write count too low — slot 7 | Only 1 ECC keygen (expect ≥2) | ❌ Not implemented | Need iteration with slot 7 count=1 |
| Write count too low — slot 8 | Only 1 MLDSA keygen (expect ≥2) | ❌ Not implemented | Need iteration with slot 8 count=1 |

### C Tests — Enforcement Behavior

| Test | RFC Description | Status |
|------|----------------|--------|
| lock_wr prevents slot overwrite in FMC | Write to locked slot 0, verify no effect | ❌ Not implemented |
| lock_use prevents FMC key access in RT | Use slot 6 as HMAC key in RT, verify fail | ❌ Not implemented |
| Cleared slots inaccessible | Read slot 3 after ROM→FMC clear, verify zero | ❌ Not implemented |
| DOE lockdown | Write DOE command after FMC, verify rejected | ✅ Partial (checked in happy path, ready=1/valid=0) |

### C Tests — Transition Detection

| Test | RFC Description | Status |
|------|----------------|--------|
| ROM callback does not regress layer | FMC calls ROM-resident function, verify boot_flow_fmc stays True | ❌ Not implemented |
| Enforcement fires on first FMC fetch | Verify ROM ICCM fetches don't trigger enforcement | ❌ Not implemented |

### C Tests — ICCM Region Configuration

| Test | RFC Description | Status | Notes |
|------|----------------|--------|-------|
| Unprogrammed regions — fetch before lock | Jump to ICCM with lock=0 → fatal | ✅ Done | Iter 3 in iccm_region |
| Unprogrammed — lock without addresses | Lock set, addresses=0, FMC entry nonzero → error | ❌ Not implemented | |
| Lock prevents address modification | Program, lock, attempt overwrite | ✅ Done | Iter 0 in iccm_region |
| Lock persists across boot phases | Set lock in ROM, verify in FMC | ✅ Done | Iter 0/2 in iccm_region |
| Registers reset on all reset types | Warm and fw update reset clear regs | ✅ Done | Iter 1 (warm) and iter 2 (fw update persistence) |

### SVA Assertions — 0 of 18 implemented

All 18 SVA assertions from the RFC test plan remain unimplemented:
- Enforcement timing (6): lock_wr, lock_use, slot clear at transitions
- Error chain (2): cptra_error_fatal and KV zeroization timing
- Monotonicity (2): boot_flow_fmc/rt non-decreasing, layer ordering
- DOE lockdown (1): doe_cmd_lock asserted when boot_flow active
- Write counters (3): increment correctness, saturation, reset domain
- ICCM region (4): boot_flow_error on lock=0, W1S property, write blocking, reset behavior

### Other Outstanding Items

| Item | Status |
|------|--------|
| Fix K_SLOT_RT_MLDSA typo (kv_defines_pkg.sv line 71) | ❌ Not done |
| smoke_test_kv_iccm_region confirmed passing | ❌ Unverified |
| Register all 3 tests in master_test_list.csv | ❌ Not done |
| Run gen_caliptra_ss_regression_ymls.py | ❌ Not done |

## Todos — ALL COMPLETE

### Priority 1 — Bug fix + test confirmation
- [x] **typo-fix**: Already correct in codebase (KV_SLOT_RT_MLDSA)
- [x] **iccm-test-verify**: Confirmed passing by user

### Priority 2 — Enforcement behavior tests
- [x] **enforcement-test**: Created `smoke_test_kv_enforcement` (7 scenarios: lock_wr, lock_use, cleared slots, ROM callback, DOE lockdown)

### Priority 3 — Missing negative test iterations
- [x] **neg-write-counts**: Added iterations 6 (slot 7 count=1) and 7 (slot 8 count=1) to smoke_test_kv_monitor_neg

### Priority 4 — Missing ICCM region edge case
- [x] **iccm-lock-no-addrs**: Added iteration 4 (lock=1, addresses=0) to smoke_test_kv_iccm_region

### Priority 5 — SVA assertions (18 properties)
- [x] **sva-enforcement**: 12 assertions (lock_wr × 9 slots, lock_use × 3 slots)
- [x] **sva-error-chain**: kv_error → cptra_error_fatal propagation
- [x] **sva-monotonicity**: 3 assertions (FMC/RT non-regression, layer ordering)
- [x] **sva-doe-lock**: 2 assertions (doe_cmd_lock in FMC and RT)
- [x] **sva-write-counters**: 9 assertions (increment, saturation, hard-reset-only clear)
- [x] **sva-iccm-region**: 3 assertions (fetch-without-lock, W1S sticky, reset-to-0)

### Priority 6 — Test registration
- [x] **test-registration**: Added all 4 tests to L0_regression.yml and caliptra_top_nightly_directed_regression.yml

### Priority 7 — Shadow register hardening (prim_subreg_shadow migration)
- [x] **shadow-migration**: Replaced custom `caliptra_reg_shadow_checker` with `caliptra_prim_subreg_shadow`
  - Changed 4 ICCM address registers to `external` in RDL
  - Instantiated 4 `caliptra_prim_subreg_shadow` instances in `soc_ifc_top.sv`
  - Added sticky committed flags (flip-flop per register, set on `qe` pulse)
  - Manual lock gating (`we & ~lock_val`), read-enables for phase-clear
  - External reg ack wiring to PeakRDL hwif_in
  - Removed old `caliptra_reg_shadow_checker.sv` and compile.yml entries
  - All 4 regression tests pass
