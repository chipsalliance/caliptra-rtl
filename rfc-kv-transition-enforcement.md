# [RFC] Key Vault Boot Phase Transition Enforcement Block

A hardware block within the Caliptra Key Vault that monitors and enforces the expected KV state at firmware phase transitions (ROM-to-FMC and FMC-to-RT). The block detects anomalous KV state caused by firmware control-flow compromise and proactively applies locks and slot clears to contain the blast radius of any undetected fault.

This proposal also introduces **ICCM fetch monitoring** — hardware that observes the ICCM instruction-fetch address bus to detect firmware layer transitions autonomously. When the first instruction fetch targets the FMC or RT region, the enforcement block triggers immediately. ICCM region boundaries are **programmed by ROM** at runtime via dedicated registers in `soc_ifc`, which are locked before ROM transfers control to FMC. ROM is responsible for enforcing that the RT region is only updated during firmware update reset.

## Scope

### Affected Components

| Component | Change |
|-----------|--------|
| `caliptra-rtl` Key Vault (`kv.sv`, `kv_reg.sv`) | New enforcement logic, monitoring comparators, hwset/hwclr enforcement controls |
| `caliptra-rtl` ICCM fetch monitor | Comparator on ICCM instruction-fetch address bus to detect FMC/RT region entry |
| `caliptra-rtl` soc_ifc registers | New `CPTRA_ICCM_FMC_START_ADDR`, `CPTRA_ICCM_FMC_END_ADDR`, `CPTRA_ICCM_RT_START_ADDR`, `CPTRA_ICCM_RT_END_ADDR` registers and `CPTRA_ICCM_REGION_LOCK` for ROM-programmed ICCM region configuration |
| `caliptra-rtl` Key Vault register definitions | New `KV_TRANSITION_STATUS` read-only register for firmware observability; new hwset/hwclr bits on `lock_wr`, `lock_use`, and slot clear for enforcement |
| `caliptra-rtl` DOE FSM (`doe_fsm.sv`) | Remove `FIXME` on `dest_valid` hardcoding; document `'d3` as a security invariant |
| `caliptra-sw` ROM | ROM must program ICCM region registers (`CPTRA_ICCM_FMC_START_ADDR`, `CPTRA_ICCM_FMC_END_ADDR`, `CPTRA_ICCM_RT_START_ADDR`, `CPTRA_ICCM_RT_END_ADDR`) and set `CPTRA_ICCM_REGION_LOCK` before jumping to FMC; ROM enforces RT region update policy on firmware update reset |
| Caliptra Hardware Specification | New sections: enforcement block behavior, expected-state tables, fatal response, ICCM fetch monitor |
| Caliptra Integration Specification | Updated port list if external fatal/zeroize signal is exposed to SoC |

### Security Posture (FIPS 140-3)

This proposal **strengthens** the security posture. It adds a hardware-enforced redundancy layer that contains the impact of firmware control-flow attacks (instruction skips, glitch-induced branches) on DICE key derivation. No existing FIPS-validated behavior is modified; the block acts as a one-way ratchet that only restricts key access.

### Area and Memory Impact

Estimated additions:
- ~9 `dest_valid` comparators (9 bits each, hardwired expected values)
- ~16 slot occupancy checks (1 bit each)
- ~6 lock-state checks (existing register readback)
- Enforcement control: hwset/hwclr signals for `lock_wr`, `lock_use`, and slot clear — fires atomically in one clock cycle
- Hardwired expected-value constants (no RAM/ROM required)
- One 32-bit status register
- ICCM fetch monitor: 2 base/limit comparators on the instruction-fetch address bus + monotonic layer tracker
- 4 x 18-bit ROM-programmed ICCM region address registers + 1-bit lock register in `soc_ifc`

Estimated area: < 1K gates. No SRAM or ROM impact.

### Timing, CDC, RDC

The enforcement block operates synchronously within the `clk` domain of the Key Vault. No new clock domain crossings are introduced. The transition trigger originates from the ICCM fetch address monitor (same clock domain). No RDC concerns; the block uses `hard_reset_b` for expected-value registers and `core_only_rst_b` for the enforcement-complete flag.

## Rationale

### Threat Model

Caliptra's DICE key derivation in ROM spans multiple crypto operations across 5 phases (DOE decrypt, IDevID, LDevID, Stable Identity Key Ladder, FMC Alias). Each phase writes intermediate and final keys to specific Key Vault slots with specific `dest_valid` permissions. The security of the entire attestation chain depends on:

1. Each DICE phase executing to completion
2. Parent secrets being erased after use
3. Derived keys having the correct `dest_valid` restrictions
4. Retired keys being locked before the next firmware layer runs

Today, all of these properties are enforced **exclusively by firmware**. A successful fault injection attack (e.g., instruction skip via voltage glitch) can violate any of them. Analysis of the ROM DICE flow shows:

- **2 instruction skips** can expose UDS (the device root secret) to Runtime firmware by skipping both the `kv_clear` of the raw UDS and the overwrite with the Stable Identity Root key
- **1 instruction skip** can leave a parent CDI unlocked, allowing a compromised child firmware layer to re-derive keys it should not possess
- ROM's existing CFI countermeasures (`cfi_assert`, `cfi_launder`) raise the practical bar to ~3 glitches, but cannot provide a hardware-rooted guarantee

A hardware enforcement block at phase transitions provides a **defense-in-depth** layer that is independent of firmware correctness. Even if ROM's control flow is disrupted by glitch attacks (the primary threat model — ROM binary integrity is assumed), the enforcement block limits what a subsequent firmware layer can do with the Key Vault.

### Update Reset: RT-Overwrites-FMC Attack

During update reset, ICCM content (FMC + RT code) persists from cold boot. ROM validates the new firmware bundle, verifies the FMC section is unchanged, and copies only the new RT image to ICCM at the load address specified in the signed Table of Contents. ROM does NOT re-copy FMC.

The RT image's load address is a field in the signed TOC. If an attacker can get ROM to accept a bundle with a malicious RT load address — via compromised signing keys or glitched signature verification — the RT image copy overwrites FMC code in ICCM. The compromised "FMC" then executes with full access to FMC DICE keys (Slots 6, 7, 8).

This attack is outside the KV enforcement block's scope because the problem occurs before the ROM-to-FMC transition: by the time enforcement runs, FMC code is already corrupted. The mitigation is **ROM-enforced RT region update policy**: ROM must validate that ICCM writes during firmware update reset target only the RT region `[RT_START, RT_END]`. Since ROM binary integrity is assumed in the threat model (only glitch attacks, not ROM binary compromise), this policy is enforceable by ROM's existing validation logic plus CFI protections. The ICCM region boundaries are programmed by ROM from the signed TOC into the `CPTRA_ICCM_RT_START_ADDR` / `CPTRA_ICCM_RT_END_ADDR` registers and locked before FMC entry.

### Why Enforcement Over Audit-Only

Two approaches were considered:

1. **Audit/Assert (detect-only)**: Check KV state at transition; fire fatal on mismatch.
2. **Proactive Enforcement (correct + detect)**: Apply locks and clears unconditionally, AND monitor for anomalies.

Audit-only has a gap: it cannot act on detected violations in a way that prevents exploitation. By the time a fatal interrupt is serviced, a compromised firmware layer may have already read an exposed key. Proactive enforcement runs in hardware before the next firmware layer's first instruction, closing this window. The monitor component provides observability and triggers KV zeroization on anomalies that the enforcement cannot correct (e.g., wrong key value in correct slot).

### Design Enhancement: Write Counters for DICE Chain Integrity

#### Problem: Rolling CDI Blind Spot

ROM uses slot 6 (`KEY_ID_ROM_FMC_CDI`) as a **rolling CDI accumulator** across DICE layers:

| Write # | Layer | Operation | dest_valid |
|:-------:|-------|-----------|:----------:|
| 1 | IDevID | `HMAC-KDF(UDS, "idevid_cdi")` → IDevID CDI | `HMAC\|ECC_SEED\|MLDSA_SEED` |
| 2 | LDevID | `HMAC-MAC(slot6, "ldevid_cdi")` → intermediate | `HMAC` only |
| 3 | LDevID | `HMAC-MAC(slot6, FE)` → LDevID CDI | `HMAC\|ECC_SEED\|MLDSA_SEED` |
| 4 | FMC Alias | `HMAC-KDF(slot6, "alias_fmc_cdi")` → FMC Alias CDI | `HMAC\|ECC_SEED\|MLDSA_SEED` |

Writes 1, 3, and 4 produce **identical `dest_valid`**. If a glitch attack skips the FMC Alias derivation (write 4), slot 6 contains the LDevID CDI with the correct `dest_valid` — the dest_valid-only monitor cannot detect this. The DICE chain is truncated: FMC derives its keys from the wrong identity root, producing invalid attestation certificates.

Similarly, slots 7 and 8 are reused across DICE layers with the same `dest_valid`:

| Slot | Write 1 (IDevID) | Erase (LDevID) | Write 2 (FMC Alias) | dest_valid |
|:----:|:-:|:-:|:-:|:----------:|
| 7 | IDevID ECC keygen | Erased after LDEV cert signing | FMC Alias ECC keygen | `ECC_PKEY` |
| 8 | IDevID MLDSA keygen | Erased after LDEV cert signing | FMC Alias MLDSA keygen | `MLDSA_SEED` |

If both the erase and re-write are glitched away (or the entire LDEV+FMC Alias sequence is skipped), slots 7/8 retain IDevID keys with the correct `dest_valid`.

#### Solution: Per-Slot Crypto Write Counters

Add a **3-bit saturating counter** per monitored entry that increments on every crypto-engine write (`key_entry_we`). SW-initiated erases (`KEY_CTRL.clear`) use a separate `hwclr` path and do **not** increment the counter. This is critical: it means the counter tracks only actual crypto engine output writes, not housekeeping erases.

**Scope**: Counters are only needed on **slots 6, 7, and 8** — the three slots reused across DICE layers with identical `dest_valid`. All other slots are either:
- Written once (slots 0, 1 by DOE) — caught by existing `dest_valid` check
- Cleared at transition (slots 3, 4, 5, 9–15) — handled by enforcement
- Variable-iteration (slot 2, key ladder) — lower severity; CFI-protected in ROM

**Hardware cost**: 3 bits × 3 slots = **9 flip-flops**, plus increment and comparison logic.

**Counter properties**:
- Resets on `hard_reset_b` (same domain as key data and `dest_valid`)
- Saturates at 7 (3-bit max) — no overflow concern
- Increment: `write_count[slot] <= write_count[slot] + 1` when `key_entry_we[slot][any_dword]` fires and counter < 7
- Read-only from firmware (no SW write path)

**Expected minimum counts at ROM→FMC (cold boot)**:

| Slot | Expected crypto writes | Min count |
|:----:|:-----:|:---------:|
| 6 | IDevID CDI + LDEV intermediate + LDEV CDI + FMC Alias CDI | **4** |
| 7 | IDevID ECC keygen + FMC Alias ECC keygen | **2** |
| 8 | IDevID MLDSA keygen + FMC Alias MLDSA keygen | **2** |

On **update/warm reset**, key data and `dest_valid` persist but `hard_reset_b` is not asserted, so the counters also persist with their values from the original cold boot. The monitor checks the same minimum thresholds — they must still be met from the original derivation.

**What this catches**:
- Glitch skipping FMC Alias CDI derivation → slot 6 count = 3 instead of ≥ 4 → detected
- Glitch skipping both LDEV and FMC Alias → slot 6 count = 1 → detected
- Glitch skipping FMC Alias ECC keygen (and erase) → slot 7 count = 1 instead of ≥ 2 → detected
- Glitch skipping entire LDEV+FMC Alias sequence → all three counts too low → detected

**Coupling to firmware**: The minimum counts are derived from the ROM DICE derivation sequence. If ROM adds or removes a DICE layer, the hardware thresholds must be updated. This is an acceptable tradeoff: DICE layer changes are major architectural events that already require coordinated HW/FW updates.

## Implementation

### ICCM Fetch Monitor (Layer Transition Detection)

#### Region Parameters (ROM-Programmed)

The FMC and RT memory boundaries are **programmed by ROM** at runtime via dedicated registers in `soc_ifc`. This allows the firmware image builder to choose FMC/RT layout without requiring RTL rebuilds.

##### ICCM Region Registers

| Register | Width | Reset Value | Access | Description |
|----------|-------|-------------|--------|-------------|
| `CPTRA_ICCM_FMC_START_ADDR` | 18 bits | `0` | RW (locked by `CPTRA_ICCM_REGION_LOCK`) | FMC image start address within ICCM address space |
| `CPTRA_ICCM_FMC_END_ADDR` | 18 bits | `0` | RW (locked by `CPTRA_ICCM_REGION_LOCK`) | FMC image end address (base + size - 1) |
| `CPTRA_ICCM_RT_START_ADDR` | 18 bits | `0` | RW (locked by `CPTRA_ICCM_REGION_LOCK`) | RT image start address within ICCM address space |
| `CPTRA_ICCM_RT_END_ADDR` | 18 bits | `0` | RW (locked by `CPTRA_ICCM_REGION_LOCK`) | RT image end address (base + size - 1) |
| `CPTRA_ICCM_REGION_LOCK` | 1 bit | `0` | W1S (write-1-to-set, sticky until reset) | Locks all 4 address registers and arms the fetch monitor |

All registers reset on `cptra_uc_rst_b` (cleared on every reset type: cold, warm, firmware update). ROM must reprogram them on every boot.

##### ROM Programming Sequence

```
1. ROM derives addresses from signed firmware image Table of Contents (TOC)
2. ROM writes CPTRA_ICCM_FMC_START_ADDR, CPTRA_ICCM_FMC_END_ADDR
3. ROM writes CPTRA_ICCM_RT_START_ADDR, CPTRA_ICCM_RT_END_ADDR
4. ROM writes CPTRA_ICCM_REGION_LOCK = 1   (arms the monitor, locks addresses)
5. ROM jumps to FMC entry point
```

##### Unprogrammed Region Safety

If any ICCM fetch occurs while `CPTRA_ICCM_REGION_LOCK` is 0 (regions not yet configured), the boot flow monitor fires `boot_flow_error` immediately. This covers:
- **Glitch skipping ROM region programming**: Attacker glitches ROM past the register writes → first FMC fetch sees lock=0 → fatal error
- **Glitch causing premature jump to ICCM**: ROM glitched to jump to ICCM before programming addresses → fatal error
- **Normal operation**: ROM executes from ROM address space (not ICCM), so no ICCM fetches occur until ROM explicitly jumps to FMC after locking

The `boot_flow_error` propagates through `CPTRA_HW_ERROR_FATAL.kv_error` → `cptra_error_fatal` → `flush_keyvault`, which destroys all key material. This is the same fatal path used by monitor dest_valid mismatches.

#### Fetch-Based Layer Detection

Hardware monitors the **ICCM instruction-fetch address bus** to autonomously detect firmware layer transitions. The ICCM already exposes the fetch address for every instruction read — the monitor adds comparators against the ROM-programmed region registers without requiring any modification to the VeeR EL2 core or its wrapper.

```
                    ICCM Address Space
    ┌─────────────────────────────────────────────────┐
    │           ROM Region (outside ICCM)             │  No ICCM fetch → ROM executing
    ├─────────────────────────────────────────────────┤
    │   FMC Region [FMC_START..FMC_END]               │  ICCM fetch in FMC range → FMC executing
    ├─────────────────────────────────────────────────┤
    │   RT Region  [RT_START..RT_END]                 │  ICCM fetch in RT range  → RT executing
    └─────────────────────────────────────────────────┘

    Precondition: CPTRA_ICCM_REGION_LOCK must be set (else any ICCM fetch → fatal error)

    Transition events (directly trigger enforcement):
      First ICCM fetch in FMC region  →  ROM-to-FMC enforcement
      First ICCM fetch in RT region   →  FMC-to-RT enforcement
```

The layer detector monitors the ICCM read-enable and address signals:
- `current_layer = ROM` when `CPTRA_ICCM_REGION_LOCK` is set but no ICCM fetch has targeted the FMC or RT region since reset
- `current_layer = FMC` after the first fetch targeting `[FMC_START, FMC_END]`
- `current_layer = RT` after the first fetch targeting `[RT_START, RT_END]`

The layer state is **monotonically non-decreasing** (ROM → FMC → RT) within a single boot cycle. Once a higher-privilege-to-lower-privilege transition fires, it cannot regress. This handles edge cases like FMC calling ROM-resident crypto routines — returning to non-ICCM addresses does not reset the layer.

A transition event fires on the **first cycle** where a fetch enters a new (lower-privilege) region. Enforcement actions (locks and clears) execute atomically in that same cycle via hwset/hwclr controls (see below), so no CPU stall mechanism is required.

**Advantages over PC-based monitoring:**
- No VeeR EL2 wrapper modification needed — the ICCM fetch interface is already external to the core
- Triggers at fetch time, before the instruction reaches the execute stage
- Cannot be bypassed by firmware — the fetch address is a hardware signal
- Naturally handles all reset types (the fetch address always passes through the same layer sequence)

#### OPEN: Speculative Fetch Qualification

**Status: Requires resolution before implementation.**

VeeR EL2's branch predictor can speculatively redirect the fetch address to an ICCM target via the BTB (Branch Target Buffer) before the branch instruction commits. The ICCM read-enable (`iccm_rden`) is asserted at the BF (Before Fetch) stage based on a **purely combinatorial address comparison** — there is no commit gate:

```
ifc_iccm_access_bf = iccm_acc_in_range_bf;   // address range check, no commit qualification
iccm_rden = ifc_iccm_access_bf & ifc_fetch_req_bf;   // speculative fetch enable
```

If the BTB contains a stale entry pointing into ICCM (e.g., from a previous boot on warm/update reset), the enforcement block could fire while ROM is still mid-DICE-derivation, prematurely locking/clearing slots that ROM hasn't finished writing.

**Options under consideration:**

| Approach | Pro | Con |
|----------|-----|-----|
| Use commit-time trace port (`trace_rv_i_address_ip` + `trace_rv_i_valid_ip`) | Safe — only fires on retired instructions; already exposed at VeeR wrapper | 1+ cycle latency after first FMC instruction commits; must verify KV read response timing |
| Verify BTB is flushed on all reset types | Simplest if provable — no speculative ICCM fetch possible with cold BTB | Defense depends on VeeR microarchitectural guarantee about BTB clearing |
| Require N consecutive ICCM fetches before triggering | Filters out single-cycle speculative probes | Fragile; delays enforcement; hard to choose N |

The commit-time trace port approach is currently favored. VeeR exposes `trace_rv_i_address_ip` (32-bit committed PC) and `trace_rv_i_valid_ip` (commit valid) at the wrapper level. Monitoring these signals eliminates speculative false triggers. The latency concern (enforcement fires after the first FMC instruction commits rather than at fetch) is mitigated by VeeR's pipeline depth: a load instruction targeting KV issued by the first FMC instruction would still be in the memory pipeline when enforcement fires, so the KV read response has not yet been generated. **This timing argument must be formally verified during implementation.**

#### RT Region Update Policy (ROM-Enforced)

During firmware update reset, ROM is responsible for ensuring that ICCM writes target only the RT region. This is enforced by ROM's existing firmware image validation: the signed TOC specifies load addresses, and ROM validates them before copying. ROM's CFI protections guard against glitch-induced bypass of this validation. Since ROM binary integrity is assumed in the threat model, this policy does not require additional hardware write-protect logic on the ICCM. ROM derives the RT region boundaries from the signed TOC and programs them into `CPTRA_ICCM_RT_START_ADDR` / `CPTRA_ICCM_RT_END_ADDR` before setting `CPTRA_ICCM_REGION_LOCK`.

### KV Enforcement Architecture

The block consists of two functions that execute atomically in a single clock cycle on each transition trigger:

```
ICCM fetch monitor detects layer transition
        |
        v
  +-----------+
  |  MONITOR  |  Compare KV state against expected-state table (combinational)
  +-----------+  Inputs: dest_valid[slot], occupied[slot], lock_wr[slot], lock_use[slot],
                         write_count[6,7,8]
        |
        |-- violation? --> FATAL: assert cptra_error_fatal, trigger KV zeroize
        |
        v
  +-----------+
  |  ENFORCE  |  Assert hwset/hwclr on lock_wr, lock_use, and slot clear (unconditional, atomic)
  +-----------+
```

Monitor and enforcement execute in the **same clock cycle** as the transition trigger. Enforcement uses dedicated hwset/hwclr control bits on the KV registers — all locks are set and all clears fire in parallel in one cycle. No FSM sequencing or CPU stall is required. A monitor violation triggers fatal AND enforcement (belt and suspenders).

### Transition 1: ROM-to-FMC

#### Monitor Checks (reset-type-aware)

The block reads `CPTRA_RESET_REASON` to distinguish cold, update, and warm resets.

| Slot | Check | Cold Reset | Update/Warm Reset |
|:----:|-------|:----------:|:-----------------:|
| 0 | `dest_valid == AES_KEY` | Required | Required |
| 0 | occupied | Required | Required |
| 1 | `dest_valid == AES_KEY` | Required | Required |
| 1 | occupied | Required | Required |
| 2 | `dest_valid == HMAC_KEY` | Required | Required |
| 2 | occupied | Required | Required |
| 3 | unoccupied | Required | Relaxed (may have stale data) |
| 4,5 | unoccupied | Required | Relaxed (old RT keys may persist) |
| 6 | `dest_valid == {HMAC_KEY\|MLDSA_SEED\|ECC_SEED}` | Required | Required |
| 6 | occupied | Required | Required |
| 6 | `write_count >= 4` | Required | Required |
| 7 | `dest_valid == ECC_PKEY` | Required | Required |
| 7 | occupied | Required | Required |
| 7 | `write_count >= 2` | Required | Required |
| 8 | `dest_valid == MLDSA_SEED` | Required | Required |
| 8 | occupied | Required | Required |
| 8 | `write_count >= 2` | Required | Required |
| 9 | unoccupied | Required | Relaxed (old RT MLDSA seed may persist) |
| 10-14 | unoccupied | Required | Required |
| 15 | unoccupied (if `!stable_owner_key_en`) | Conditional | Conditional |

#### Enforcement Actions (identical for all reset types)

| Action | Slots | Mechanism | Purpose |
|--------|:-----:|-----------|---------|
| `lock_wr` | 0, 1, 2 | hwset | Prevent overwrite of stable identity roots and key ladder |
| `lock_wr` | 6, 7, 8 | hwset | FMC reads these but must not overwrite them |
| `clear` | 3, 4, 5, 9, 10-15 | hwclr | Remove scratch keys, old RT keys, and any unexpected occupants |
| `clear` (conditional) | 15 | hwclr (skip if `stable_owner_key_en`) | Preserve Stable Owner Key if feature is active |
| `clear` (conditional) | 16, 22 | hwclr (skip if `ocp_lock_mode_en`) | Preserve MDK and HEK if OCP Lock is active |

All actions fire atomically in one clock cycle via dedicated hardware set/clear control bits on the KV registers. No KV write-client arbitration is involved.

**Key property**: After enforcement, the KV state entering FMC is identical regardless of reset type.

#### Post-Enforcement KV State (FMC entry, all reset types)

| Slot | Contents | dest_valid | lock_wr | lock_use |
|:----:|----------|:----------:|:-------:|:--------:|
| 0 | Stable Identity Root IDevID | `AES_KEY` | Yes | -- |
| 1 | Stable Identity Root LDevID | `AES_KEY` | Yes | -- |
| 2 | Key Ladder | `HMAC_KEY` | Yes | -- |
| 3-5 | **empty** | -- | -- | -- |
| 6 | FMC CDI | `HMAC_KEY\|MLDSA_SEED\|ECC_SEED` | Yes | -- |
| 7 | FMC ECDSA Key | `ECC_PKEY` | Yes | -- |
| 8 | FMC MLDSA Seed | `MLDSA_SEED` | Yes | -- |
| 9-14 | **empty** | -- | -- | -- |
| 15 | Stable Owner Key (if `stable_owner_key_en`) or **empty** | `AES_KEY` or -- | ROM-locked | -- |
| 16 | MDK (if `ocp_lock_mode_en`) or **empty** | -- | ROM-locked | -- |
| 17-21 | **empty** | -- | -- | -- |
| 22 | HEK (if `ocp_lock_mode_en`) or **empty** | -- | ROM-locked | -- |
| 23 | **empty** | -- | -- | -- |

### Transition 2: FMC-to-RT

#### Monitor Checks

| Slot | Check | Purpose |
|:----:|-------|---------|
| 0 | `lock_wr == 1` | Verify ROM-to-FMC enforcement ran (cross-transition validation) |
| 1 | `lock_wr == 1` | Same |
| 2 | `lock_wr == 1` | Same |
| 4 | occupied, `dest_valid == {HMAC_KEY\|MLDSA_SEED\|ECC_SEED}` | RT CDI was derived |
| 5 | occupied, `dest_valid == ECC_PKEY` | RT ECDSA key was derived |
| 6 | occupied, `lock_wr == 1` | FMC CDI still protected |
| 7 | occupied, `lock_wr == 1` | FMC ECDSA key still protected |
| 8 | occupied, `lock_wr == 1` | FMC MLDSA seed still protected |
| 9 | occupied, `dest_valid == MLDSA_SEED` | RT MLDSA seed was derived |
| 10-14 | unoccupied | No unexpected keys |
| 15 | unoccupied (if `!stable_owner_key_en`) | No unexpected keys; skipped if Stable Owner Key is active |

#### Enforcement Actions

| Action | Slots | Mechanism | Purpose |
|--------|:-----:|-----------|---------|
| `lock_use` | 6, 7, 8 | hwset | Retire FMC keys -- RT cannot read them |
| `lock_wr` | 4, 5, 9 | hwset | Prevent RT from overwriting its own DICE identity |
| `clear` | 3, 10-14 | hwclr | Remove any scratch or unexpected keys |
| `clear` (conditional) | 15 | hwclr (skip if `stable_owner_key_en`) | Preserve Stable Owner Key if feature is active |
| `clear` (conditional) | 16, 22 | hwclr (skip if `ocp_lock_mode_en`) | Preserve MDK and HEK if OCP Lock is active |

All actions fire atomically in one clock cycle.

### Reset Behavior

KV locks (`lock_wr`, `lock_use`) use `core_only_rst_b` -- they are cleared on ALL reset types. Key data and `dest_valid` use `hard_reset_b` -- they persist through update and warm resets. This means:

| Property | Cold Reset | Update Reset | Warm Reset |
|----------|:----------:|:------------:|:----------:|
| Key data | Cleared | Persists | Persists |
| `dest_valid` | Cleared | Persists | Persists |
| `lock_wr` / `lock_use` | Cleared | Cleared | Cleared |
| Enforcement locks from previous boot | Gone | Gone | Gone |

The enforcement block re-applies all locks on every transition, making it **idempotent across reset types**. The only reset-type-awareness is in the ROM-to-FMC monitor's occupancy checks for Slots 3-5 and 9 (relaxed on update/warm because old RT keys may persist before enforcement clears them).

### Fatal Response

On any monitor violation:
1. Assert `cptra_error_fatal` via dedicated `kv_error` field in `CPTRA_HW_ERROR_FATAL` (bit 4)
2. Trigger full KV zeroization (all 16 standard slots cleared)
3. Latch violation details in `CPTRA_HW_ERROR_ENC` register (SoC/MCU-visible)
4. Enforcement still runs (in case fatal handling is delayed, enforcement limits exposure)

#### Violation Encoding in `CPTRA_HW_ERROR_ENC`

Since a fatal error locks up the Caliptra core, violation details are latched into the existing `CPTRA_HW_ERROR_ENC` register (at `0x30030010`), which is readable by the MCU and SoC even after Caliptra is locked. This replaces the previously proposed KV-internal `KV_TRANSITION_STATUS` register — an internal register would be unreachable after fatal lockup.

The encoding is latched by hardware on the cycle `kv_monitor_alert` fires. Only the first violation is captured (subsequent violations in the same cycle do not overwrite).

| Field | Bits | Reset | Description |
|-------|:----:|:-----:|-------------|
| `transition` | [0] | 0 | Which transition failed: 0 = ROM→FMC, 1 = FMC→RT |
| `violation_slot` | [4:1] | 0 | Slot index (0–15) of the first failing check |
| `violation_check` | [7:5] | 0 | Check type: 0 = dest_valid mismatch (expandable for future check types) |
| `actual_dest_valid` | [16:8] | 0 | Actual `dest_valid[8:0]` of the failing slot |
| Reserved | [31:17] | 0 | -- |

The expected `dest_valid` for any slot+transition combination is a hardwired constant in RTL and can be looked up from the slot index and transition field.

Reset: cleared on `cptra_pwrgood`. Persists through warm/update resets.

> **OPEN — Side-Channel Concern**: Encoding the actual `dest_valid` value leaks information about the internal KV state to an external observer (MCU/SoC) after a failed glitch attempt. An attacker performing iterative glitch attacks could use the violation encoding to refine their attack strategy (e.g., learning which DICE derivation step was skipped based on the `actual_dest_valid` pattern). Options under consideration:
>
> 1. **Full encoding** (current proposal): Maximum debug utility. Acceptable if the threat model assumes the attacker cannot read SoC registers after triggering fatal, or if the platform forces a full power-on reset after any fatal error (clearing `CPTRA_HW_ERROR_ENC`).
> 2. **Reduced encoding**: Omit `actual_dest_valid` — encode only transition + slot + check type (8 bits). Still identifies which slot failed but not *how* the KV state diverged. Limits attacker feedback to "which step was skipped" rather than "what the intermediate state looks like."
> 3. **No encoding**: Only the `kv_error` bit in `CPTRA_HW_ERROR_FATAL` is set. Zero information leakage, but significantly harder to debug in the lab.
>
> Recommendation pending security architecture review.

### Redundant Backstop Design Principle

All enforcement actions are **redundant backstops** — they duplicate protections that ROM and FMC are expected to apply correctly during normal operation. In the nominal flow:

- ROM already locks FMC keys (`lock_wr` on Slots 6, 7, 8) before jumping to FMC — enforcement's hwset is a no-op on already-set bits
- ROM already clears scratch slots (3, 4, 5) — enforcement's hwclr clears already-empty slots
- FMC already locks its own keys before transferring to RT — enforcement's hwset is redundant

The enforcement block adds value only when a glitch attack causes ROM or FMC to skip one of these operations. The hwset/hwclr mechanism is idempotent: applying it to a correctly-configured KV produces no state change. This means enforcement never interferes with a correct boot and adds zero-cost defense-in-depth against fault injection.

### Monitor Scope: DICE Keys Only

The KV boot flow monitor checks `dest_valid` values and write counters **only for DICE derivation key slots** (0–9). Optional feature keys — Stable Owner Key (slot 15) and OCP Lock keys (slots 16–23) — are deliberately excluded from monitoring for the following reasons:

1. **Conditional derivation**: These keys are only derived when their respective feature is enabled at boot time. The monitor's expected-state tables use hardwired constants; adding conditional expected values would significantly complicate the comparator logic for keys that are not part of the core DICE trust chain.

2. **No glitch-amplification risk**: DICE keys form a chain of trust where skipping one derivation step silently corrupts the entire attestation chain. Optional feature keys are standalone — if their derivation is skipped, the feature simply doesn't work. There is no cascading trust violation.

3. **Separate protection mechanisms**: OCP Lock slots (16–23) are already protected by `kv_write_rule_check.sv`, which enforces standard-to-OCP-Lock isolation during active OCP Lock flows. The Stable Owner Key is locked by ROM after derivation.

The enforcement block (slot clearing and locking) **does** handle these slots — it conditionally preserves or clears them based on runtime configuration signals. Only the monitor (dest_valid verification and write counting) is restricted to DICE keys.

### Conditional Slot Preservation (Non-DICE Keys)

Two optional Caliptra features populate KV slots that must survive boot transitions when the feature is active, but must be cleared when inactive:

#### Stable Owner Key (Slot 15)

The Stable Owner Root Key is derived by ROM via 2-step HKDF-SHA512 from `FUSE_HEK_SEED` during the IDevID DICE layer. Derivation is gated on three conditions:

```
stable_owner_key_en = SUBSYSTEM_MODE_en & ~OCP_LOCK_MODE_en & SS_STRAP_GENERIC[3][0]
```

- `SUBSYSTEM_MODE_en`: Caliptra is operating in subsystem mode (always true in caliptra-ss integration)
- `OCP_LOCK_MODE_en`: OCP Lock is NOT enabled (stable owner and OCP Lock are mutually exclusive)
- `SS_STRAP_GENERIC[3][0]`: SoC strap bit indicating stable owner key feature is enabled

The `stable_owner_key_en` signal is computed in `soc_ifc_top.sv` and routed through `caliptra_top.sv` to `kv.sv`. When active, slot 15 is excluded from `boot_flow_key_clear` at both ROM-to-FMC and FMC-to-RT transitions. When inactive, slot 15 is cleared normally along with other non-preserved slots.

**Security rationale**: Slot 15 is not monitored (no dest_valid check, no write counter) because it is not a DICE key. It does not participate in the attestation chain. ROM locks it via `lock_wr` after derivation, providing firmware-level protection.

#### OCP Lock Keys (Slots 16, 22)

When OCP Lock mode is enabled, DOE populates slot 16 (MDK — runtime obfuscation key) and slot 22 (HEK seed) before ROM runs. FMC and RT firmware require these keys to derive EPK, VEK, and MEK for key release flows.

The `ocp_lock_mode_en` signal (directly from `ss_ocp_lock_en` SoC strap) gates preservation:

- When `ocp_lock_mode_en = 1`: Slots 16 and 22 are excluded from clearing at both transitions
- When `ocp_lock_mode_en = 0`: Slots 16 and 22 are cleared normally

**Slot 23 (MEK) is always cleared** regardless of `ocp_lock_mode_en`. MEK is DMA-accessible (`dest_valid` includes `DMA_DATA`) and is only derived during RT firmware operation. Persisting it across transitions would allow a compromised firmware layer to exfiltrate key material via DMA. RT re-derives MEK when needed.

**Security rationale**: Only the specific slots that ROM or FMC actually derive (16, 22) are preserved — not the entire OCP Lock range (16–23). Slots 17–21 and 23 are always cleared. This minimizes the key material that survives transitions while maintaining functional correctness for the OCP Lock flow.

#### Mutual Exclusion

Stable Owner Key and OCP Lock are mutually exclusive by construction: `stable_owner_key_en` includes `~OCP_LOCK_MODE_en` in its definition. The four possible states are:

| `ocp_lock_mode_en` | `SS_STRAP_GENERIC[3][0]` | Slot 15 | Slots 16, 22 | Slot 23 |
|:---:|:---:|:---:|:---:|:---:|
| 0 | 0 | Cleared | Cleared | Cleared |
| 0 | 1 | **Preserved** | Cleared | Cleared |
| 1 | 0 | Cleared | **Preserved** | Cleared |
| 1 | 1 | Cleared | **Preserved** | Cleared |

Note: When both `ocp_lock_mode_en=1` and `strap[3][0]=1`, OCP Lock takes precedence — slot 15 is cleared because `stable_owner_key_en` evaluates to 0.

### Threat Coverage Summary

| Threat | Detection/Mitigation Layer |
|--------|---------------------------|
| UDS/FE not overwritten (instruction skip) | Monitor: `dest_valid` mismatch on Slot 0/1 (DOE writes `HMAC_KEY\|HMAC_BLOCK`; expected is `AES_KEY`) |
| Parent CDI not cleared after use | Enforce: clear Slots 3-5, 9-15 at ROM-to-FMC |
| FMC keys readable by RT | Enforce: `lock_use` on Slots 6,7,8 at FMC-to-RT |
| RT keys overwritten by RT | Enforce: `lock_wr` on Slots 4,5,9 at FMC-to-RT |
| ROM-to-FMC enforcement skipped (ROM glitch) | FMC-to-RT monitor: check `lock_wr` on Slots 0,1,2 (set by prior enforcement) |
| Old RT keys survive update reset | Enforce: clear Slots 4,5,9 at ROM-to-FMC (all reset types) |
| All enforcement locks lost on reset | Enforcement re-applies on every boot, triggered by ICCM fetch monitor |
| Malicious RT load address overwrites FMC in ICCM | ROM-enforced RT region update policy (ROM integrity assumed; CFI protects validation) |
| Firmware spoofs transition trigger | ICCM fetch address is a hardware signal; firmware cannot influence the comparator |
| ROM glitched past ICCM region programming | Any ICCM fetch while `CPTRA_ICCM_REGION_LOCK` = 0 fires `boot_flow_error` → fatal |
| ROM programs wrong region boundaries | ROM integrity assumed in threat model; addresses derived from signed TOC; CFI protects programming sequence |

#### OCP LOCK Slots (16-23): Conditional Preservation

See [Conditional Slot Preservation (Non-DICE Keys)](#conditional-slot-preservation-non-dice-keys) for full design details. In summary: slots 16 (MDK) and 22 (HEK) are conditionally preserved when `ocp_lock_mode_en` is active; slot 23 (MEK) is always cleared; no OCP Lock slots are monitored.

#### Stable Owner Key (Slot 15): Conditional Preservation

See [Conditional Slot Preservation (Non-DICE Keys)](#conditional-slot-preservation-non-dice-keys) for full design details. In summary: slot 15 is conditionally preserved when `stable_owner_key_en` is active; not monitored because it is not a DICE key.

#### DOE `dest_valid` Hardcoding (Prerequisite)

DOE's `dest_valid` for UDS/FE slots is currently hardwired to `HMAC_KEY|HMAC_BLOCK` (`'d3`) in `doe_fsm.sv`. This value must remain a non-configurable constant — it must never become FW-programmable. The enforcement block's monitor relies on the invariant that DOE-written `dest_valid` differs from the Stable Identity derivation output (`AES_KEY`), making `dest_valid` a reliable proxy for detecting skipped overwrites. A `FIXME` comment in `doe_fsm.sv:268` questioning whether to make this FW-programmable should be resolved by removing the FIXME and documenting the constant as a security invariant.

## Implementation Tradeoffs

### Trigger Mechanism

| Option | Pros | Cons |
|--------|------|------|
| ICCM fetch address monitor (recommended) | Hardware-only, cannot be glitched by firmware, triggers at fetch time (before execute), no VeeR wrapper modification needed, ICCM fetch interface already external | Requires region comparator logic; must handle monotonic layer tracking for ROM callbacks |
| VeeR PC export | Detects exact instruction boundary | Requires VeeR EL2 wrapper RTL modification to expose internal PC; only commit-time trace PC is currently available |
| Boot FSM signal | Simple integration, fires at known point | Requires Boot FSM modification; approximate timing; may not align with actual first-instruction boundary |
| Firmware-written trigger register | Simplest integration | Defeatable by same glitch that compromises ROM; reduces security value |

**Recommendation**: ICCM fetch address monitor as primary trigger. The region boundaries are programmed by ROM from the signed firmware TOC and locked before FMC entry. A firmware-written "enforcement-complete-ack" register can optionally serve as a cross-check (FW confirms it saw enforcement happen), but must not be the sole trigger.

### Enforcement Mechanism

| Option | Pros | Cons |
|--------|------|------|
| Atomic hwset/hwclr on KV registers (recommended) | Single-cycle enforcement, no FSM, no CPU stall, no arbitration contention | Requires new hwset/hwclr bits in KV register definitions |
| Enforcement block as KV write client | Uses existing KV write path | Requires FSM to serialize operations (one slot per cycle); adds arbitration contention; needs CPU stall mechanism |
| Mask registers at read time | No write needed | Adds gate delay to every KV read path; does not clear slot data |

**Recommendation**: Atomic hwset/hwclr. The enforcement block asserts dedicated hardware set bits on `lock_wr` and `lock_use`, and dedicated hardware clear bits on slot data and `dest_valid`, all in parallel in one clock cycle. This avoids the need for FSM sequencing, KV write-client arbitration, or CPU stall logic.

### Expected-State Configuration

| Option | Pros | Cons |
|--------|------|------|
| Hardwired constants (recommended for v1) | Smallest area, no configuration attack surface | Requires RTL change if DICE flow changes |
| Fuse-programmable expected values | Adapts to different firmware configurations | Adds fuse bits, configuration complexity, attack surface |
| ROM-written expected values | Most flexible | Completely defeatable by firmware compromise |

## Implementation Timeline

Target: Caliptra 2.x release cycle. The block is self-contained within the Key Vault module and has no dependencies on other in-flight features.

## Test Plan

### Design Invariants

The monitor and enforcement block behaviors are **identical across all reset types** (cold boot, warm reset, firmware update reset). The boot flow monitor in `caliptra_top.sv` resets on `cptra_uc_rst_b`, which is asserted by all reset types. After any reset, the layer state starts at ROM and progresses monotonically through FMC → RT as ICCM fetch addresses enter the respective regions.

**Monitor responsibility**: Verify that preserved DICE key slots contain the correct `dest_valid` at each transition. The monitor checks only the slots that will survive the transition (i.e., not cleared by enforcement).

**Enforcement responsibility**: Everything else — lock preserved slots (`lock_wr`), restrict FMC key usage in RT (`lock_use`), and clear all non-preserved slots. This ensures that even if the monitor doesn't check a slot, it cannot be accessed improperly after the transition.

Together: the monitor confirms the keys that remain are correct; enforcement destroys or locks everything else.

### Functional Verification — C Tests

#### Happy Path

- **`smoke_test_kv_boot_flow_monitor`** (implemented): Cold boot. ROM populates DICE slots with correct `dest_valid` via HMAC. Jump to FMC. Verify: `kv_error` not set, `lock_wr` on slots 0,1,2,6,7,8, non-preserved slots cleared, DOE locked (ready=1, valid=0), write counters meet thresholds (slot 6 ≥ 4, slots 7,8 ≥ 2). FMC populates RT slots. Jump to RT. Verify: `kv_error` not set, `lock_wr` on slots 4,5,9, `lock_use` on slots 6,7,8, non-preserved slots cleared, DOE still locked.

- **Warm reset happy path**: Perform cold boot through RT. Issue warm reset. Repeat ROM DICE derivation and transitions. Verify identical enforcement behavior — monitor passes, locks/clears applied identically.

- **Update reset happy path**: Perform cold boot through RT. Issue firmware update reset. ROM re-derives keys, copies new RT image. Verify monitor passes at both transitions. Verify old RT slot contents (4,5,9) are cleared at ROM→FMC before FMC re-populates them.

#### Monitor Violations (Negative Tests)

- **dest_valid mismatch — ROM→FMC**: Populate slot 0 (UDS) with wrong `dest_valid` (e.g., `HMAC_KEY` instead of `AES_KEY`). Jump to FMC. Verify: `CPTRA_HW_ERROR_FATAL.kv_error` is set, all KV slots zeroized, `CPTRA_HW_ERROR_ENC` contains correct violation encoding (transition=0, slot=0, check=dest_valid).

- **dest_valid mismatch — FMC→RT**: Populate slot 4 (RT_CDI) with wrong `dest_valid`. Jump to RT. Verify: `kv_error` set, KV zeroized, `CPTRA_HW_ERROR_ENC` encoding correct (transition=1, slot=4).

- **Missing key — ROM→FMC**: Skip populating slot 6 (FMC_CDI) entirely — `dest_valid` remains 0. Jump to FMC. Verify: `kv_error` set (expected CDI `dest_valid` vs actual 0).

- **Missing key — FMC→RT**: Skip populating slot 9 (RT_MLDSA). Jump to RT. Verify: `kv_error` set.

- **Glitch simulation — skipped DICE step**: Populate all ROM-phase slots correctly except slot 2 (Key Ladder) — simulate a glitch that skipped the key ladder derivation. Verify monitor catches `dest_valid` mismatch on slot 2 at ROM→FMC.

- **Write count too low — slot 6 (truncated DICE chain)**: Populate slot 6 with correct `dest_valid` (`HMAC_KEY|MLDSA_SEED|ECC_SEED`) but only perform 1 HMAC write (simulating IDevID CDI only, with LDevID and FMC Alias derivations glitched away). Jump to FMC. Verify: `kv_error` set due to `write_count[6] < 4`, even though `dest_valid` is correct.

- **Write count too low — slot 7 (skipped FMC Alias ECC keygen)**: Populate slot 7 with correct `dest_valid` (`ECC_PKEY`) but only perform 1 ECC keygen (simulating IDevID key only, with erase and FMC Alias keygen glitched away). Jump to FMC. Verify: `kv_error` set due to `write_count[7] < 2`.

- **Write count too low — slot 8 (skipped FMC Alias MLDSA keygen)**: Same as slot 7 but for MLDSA seed. Verify: `kv_error` set due to `write_count[8] < 2`.

#### Enforcement Behavior

- **lock_wr prevents slot overwrite in FMC**: After ROM→FMC transition, attempt to write to slot 0 (locked by enforcement). Verify write has no effect — `dest_valid` unchanged.

- **lock_use prevents FMC key access in RT**: After FMC→RT transition, attempt to use slot 6 (FMC_CDI) as HMAC key input. Verify operation fails (key read blocked).

- **Cleared slots inaccessible**: After ROM→FMC transition, attempt to read slot 3 (cleared). Verify key data is zero / read fails.

- **DOE lockdown**: After ROM→FMC transition, write a DOE command. Verify `DOE_STATUS.ready=1` (engine idle, command was rejected) and `DOE_STATUS.valid=0` (no result produced). Repeat check after FMC→RT.

#### Conditional Slot Preservation

- **Stable Owner Key preserved (slot 15)**: Configure `SS_STRAP_GENERIC[3][0]=1`, `ocp_lock_mode_en=0`. Populate slot 15 with HMAC result in ROM phase. After ROM→FMC and FMC→RT transitions, verify slot 15 `dest_valid != 0` (preserved). Verify canary slots (e.g., slot 10, 17) are cleared to confirm enforcement ran.

- **Stable Owner Key cleared when disabled**: Configure `SS_STRAP_GENERIC[3][0]=0`. Populate slot 15 in ROM phase. After ROM→FMC, verify slot 15 `dest_valid == 0` (cleared).

- **OCP Lock slots preserved (slots 16, 22)**: Configure `ocp_lock_mode_en=1`. Populate slots 16, 22, and 23 in ROM phase. After both transitions, verify slots 16 and 22 are preserved (`dest_valid != 0`), slot 23 is cleared (`dest_valid == 0`).

- **OCP Lock slots cleared when disabled**: Configure `ocp_lock_mode_en=0`. Populate slots 16, 22, 23 in ROM phase. After ROM→FMC, verify all three are cleared.

- **MEK (slot 23) always cleared**: With `ocp_lock_mode_en=1`, populate slot 23. After both transitions, verify slot 23 is cleared regardless of OCP Lock mode.

- **Mutual exclusion — OCP Lock overrides Stable Owner**: Configure `ocp_lock_mode_en=1` and `SS_STRAP_GENERIC[3][0]=1`. Populate slot 15. After ROM→FMC, verify slot 15 is cleared (because `stable_owner_key_en = subsystem_mode & ~ocp_lock & strap[3][0] = 0`).

- **`directed_kv_enforcement` test** (implemented): Uses randomized `SS_STRAP_GENERIC[3]` and `ocp_lock_mode_en` BFM strap values. C test reads back `CPTRA_HW_CONFIG` and `SS_STRAP_GENERIC_3` registers at runtime to compute expected preservation behavior, then verifies conditional slots at both FMC and RT entry. Canary slots (10, 17) verify enforcement always fires. Across regression seeds, all four mutual exclusion states are covered.

#### Transition Detection

- **ROM callback does not regress layer**: FMC calls a function at a ROM-resident address (outside ICCM). Verify `boot_flow_fmc` remains asserted. Verify enforcement does not re-fire on return to FMC ICCM region.

- **Enforcement fires on first FMC fetch**: Verify that ICCM fetches in the ROM region do not trigger enforcement. First fetch into FMC region triggers ROM→FMC enforcement.

#### ICCM Region Configuration

- **Unprogrammed regions — ICCM fetch before lock**: ROM does not program ICCM region registers or set `CPTRA_ICCM_REGION_LOCK`. Glitch ROM to jump directly to ICCM. Verify: `boot_flow_error` fires immediately on first ICCM fetch, `CPTRA_HW_ERROR_FATAL.kv_error` set, KV flushed.

- **Unprogrammed regions — lock without addresses**: ROM sets `CPTRA_ICCM_REGION_LOCK` without programming any address registers (all still 0). Jump to ICCM. Verify: FMC region comparator `[0,0]` matches address 0 only; if FMC entry point is nonzero, fetch lands outside both regions → `boot_flow_error` (ICCM fetch in neither configured region is an error). **Note**: This test validates that zero-valued region registers do not create a false match for the actual FMC entry point.

- **Lock prevents address modification**: Program all 4 address registers, set `CPTRA_ICCM_REGION_LOCK`. Attempt to overwrite `CPTRA_ICCM_FMC_START_ADDR`. Verify: register value unchanged (write blocked by lock).

- **Lock persists across boot phases**: Set `CPTRA_ICCM_REGION_LOCK` in ROM. In FMC, attempt to clear it. Verify: lock remains set (W1S, sticky until reset).

- **Registers reset on all reset types**: Program addresses and lock. Issue warm reset. Verify: all 4 address registers are 0, lock is 0. ROM must reprogram. Repeat for firmware update reset.

### SVA Assertions

- `lock_wr` on slots 0,1,2,6,7,8 asserted within 1 cycle of `enter_fmc`
- `lock_wr` on slots 4,5,9 asserted within 1 cycle of `enter_rt`
- `lock_use` on slots 6,7,8 asserted within 1 cycle of `enter_rt`
- Slots 3,4,5,9,10-14 cleared within 1 cycle of `enter_fmc`; slot 15 cleared only if `!stable_owner_key_en`; slots 16,22 cleared only if `!ocp_lock_mode_en`; slot 23 always cleared
- Slots 3,10-14 cleared within 1 cycle of `enter_rt`; slot 15 cleared only if `!stable_owner_key_en`; slots 16,22 cleared only if `!ocp_lock_mode_en`; slot 23 always cleared
- All enforcement actions (hwset/hwclr) complete in the same clock cycle as their trigger -- no multi-cycle sequencing
- `cptra_error_fatal` asserts within 1 cycle of `kv_monitor_alert`
- KV zeroization triggers within 2 cycles of `kv_monitor_alert`
- `boot_flow_fmc` and `boot_flow_rt` are monotonically non-decreasing (False -> True, never True -> False) within a single boot cycle
- `boot_flow_rt` cannot assert before `boot_flow_fmc` (layer ordering)
- `doe_cmd_lock` asserted whenever `boot_flow_fmc` or `boot_flow_rt` is true
- Write counter for slot 6 increments on each `key_entry_we[6]` and does not increment on `key_entry_clear[6]`
- Write counter for slots 7, 8 -- same property
- Write counters saturate at 7 (never wrap)
- Write counters reset on `hard_reset_b` only (persist across warm and fw update resets)
- `boot_flow_error` fires if any ICCM fetch occurs while `CPTRA_ICCM_REGION_LOCK` = 0
- `CPTRA_ICCM_REGION_LOCK` is W1S: once set, cannot be cleared by any write (only reset clears)
- Address register writes are ignored when `CPTRA_ICCM_REGION_LOCK` = 1
- All 4 address registers and `CPTRA_ICCM_REGION_LOCK` reset to 0 on `cptra_uc_rst_b`

### Coverage Targets

- All 9 monitored slots: pass and fail `dest_valid` check individually
- Both transitions (ROM→FMC, FMC→RT) with monitor pass and fail
- All three reset types through both transitions
- `kv_error` → `CPTRA_HW_ERROR_FATAL` → `cptra_error_fatal` signal chain exercised
- `CPTRA_HW_ERROR_ENC` latched on violation (all encoding fields nonzero)
- Each enforcement action type exercised: `lock_wr` hwset, `lock_use` hwset, slot clear
- ICCM fetch transitions: ROM→FMC, FMC→RT, with ROM callback in between
- DOE lockdown: `doe_cmd_lock` asserted in FMC and RT phases
- Write counter: slot 6 count reaches 4 on happy path (cold boot)
- Write counter: slots 7, 8 count reaches 2 on happy path (cold boot)
- Write counter: monitor fires when slot 6 count < 4 at ROM→FMC
- Write counter: monitor fires when slot 7 or 8 count < 2 at ROM→FMC
- Write counter: counters persist across warm/update reset (same values readable after reset)
- ICCM region registers: all 4 addresses programmed and locked on happy path
- ICCM region registers: `boot_flow_error` fires on ICCM fetch with lock=0
- ICCM region registers: address writes blocked after lock is set
- ICCM region registers: lock and addresses cleared on each reset type (cold, warm, fw update)
- Conditional preservation: slot 15 preserved when `stable_owner_key_en=1` at both transitions
- Conditional preservation: slot 15 cleared when `stable_owner_key_en=0` at both transitions
- Conditional preservation: slots 16,22 preserved when `ocp_lock_mode_en=1` at both transitions
- Conditional preservation: slots 16,22 cleared when `ocp_lock_mode_en=0` at both transitions
- Conditional preservation: slot 23 (MEK) always cleared regardless of `ocp_lock_mode_en`
- Conditional preservation: mutual exclusion — when `ocp_lock_mode_en=1`, slot 15 is always cleared even if `SS_STRAP_GENERIC[3][0]=1`

## Maintenance

[To be assigned] -- Feature proposer and Caliptra Key Vault module owner. The enforcement block's expected-state constants must be reviewed whenever the DICE derivation flow in `caliptra-sw` ROM or FMC changes (slot assignments, `KeyUsage` values, or derivation ordering). ROM must be updated to program the correct ICCM region addresses from the signed firmware TOC whenever the firmware memory layout changes.

## Appendix A: KV Slot Assignments (Reference)

Source: `caliptra-sw/common/src/keyids.rs`

### Standard Slots (0-15) — Covered by Enforcement Block

| Slot | ROM Usage | FMC Usage | RT Usage | Final Contents at RT Entry |
|:----:|-----------|-----------|----------|---------------------------|
| 0 | UDS (DOE) --> Stable Identity Root IDevID | -- | -- | Stable Identity Root IDevID |
| 1 | FE (DOE) --> Stable Identity Root LDevID | -- | -- | Stable Identity Root LDevID |
| 2 | Key Ladder (HMAC) | -- | -- | Key Ladder |
| 3 | ECC temp seed (scratch) | -- | -- | **empty** |
| 4 | LDevID MLDSA Seed --> cleared | RT CDI (HMAC) | -- | RT CDI |
| 5 | LDevID ECDSA Key --> cleared | RT ECDSA Key (ECC) | -- | RT ECDSA Key |
| 6 | CDI (HMAC, overwritten 3x) | -- | -- | FMC CDI (locked) |
| 7 | IDevID ECDSA --> FMC ECDSA Key | -- | -- | FMC ECDSA Key (locked) |
| 8 | IDevID MLDSA Seed --> FMC MLDSA Seed | -- | -- | FMC MLDSA Seed (locked) |
| 9 | -- | RT MLDSA Seed | -- | RT MLDSA Seed |
| 10 | -- | -- | DPE CDI | **empty** (cleared by FMC-to-RT enforcement; written by RT) |
| 11 | -- | -- | DPE Private Key | **empty** (cleared by FMC-to-RT enforcement; written by RT) |
| 12 | -- | -- | Exported DPE CDI | **empty** (cleared by FMC-to-RT enforcement; written by RT) |
| 13-14 | -- | -- | -- | **empty** |
| 15 | Stable Owner Root Key (if `stable_owner_key_en`) | -- | -- | Stable Owner Root Key (if `stable_owner_key_en`) or **empty** |

### OCP LOCK Slots (16-23) — Conditionally Preserved (Not Monitored)

OCP LOCK slots are **not monitored** by the transition enforcement block (no dest_valid checks, no write counters). However, slots 16 (MDK) and 22 (HEK) are **conditionally preserved** from clearing when `ocp_lock_mode_en` is active. Slot 23 (MEK) is always cleared at transitions. Separate protection via `kv_write_rule_check.sv` enforces standard-to-OCP-Lock isolation during active OCP Lock flows.

| Slot | Usage | Populated By |
|:----:|-------|-------------|
| 16 | MDK (runtime obfuscation key) | DOE (`DOE_HEK` command, before ROM runs) |
| 17 | EPK | OCP LOCK flow |
| 18 | VEK | OCP LOCK flow |
| 19 | Locked MPK Encryption Key | OCP LOCK flow |
| 21 | MEK Secrets | OCP LOCK flow |
| 22 | HEK / HEK Seed | DOE (`running_hek`, before ROM runs) |
| 23 | MEK (key release) | AES ECB decrypt during OCP LOCK flow |

## Appendix B: dest_valid Bit Encoding (Reference)

Source: `caliptra-rtl/src/keyvault/rtl/kv_defines_pkg.sv`

| Bit | Engine | Mnemonic |
|:---:|--------|----------|
| 0 | HMAC Key input | `HMAC_KEY` |
| 1 | HMAC Block input | `HMAC_BLOCK` |
| 2 | MLDSA Seed | `MLDSA_SEED` |
| 3 | ECC Private Key | `ECC_PKEY` |
| 4 | ECC Key Gen Seed | `ECC_SEED` |
| 5 | AES Key | `AES_KEY` |
| 6 | MLKEM Seed | `MLKEM_SEED` |
| 7 | MLKEM Message | `MLKEM_MSG` |
| 8 | DMA Data | `DMA_DATA` |

## Appendix C: Verified dest_valid per Slot

Source: `caliptra-sw` ROM and FMC Rust source (see Important Files below)

| Slot | Expected dest_valid | Bits Set | Source |
|:----:|:-------------------:|:--------:|--------|
| 0 | `AES_KEY` | `[5]` | `ldev_id.rs`: `KeyUsage::default().set_aes_key_en()` |
| 1 | `AES_KEY` | `[5]` | `ldev_id.rs`: `KeyUsage::default().set_aes_key_en()` |
| 2 | `HMAC_KEY` | `[0]` | `key_ladder.rs`: `KeyUsage::default().set_hmac_key_en()` |
| 4 | `HMAC_KEY\|MLDSA_SEED\|ECC_SEED` | `[0,2,4]` | `rt_alias.rs` / `dice.rs`: `set_hmac_key_en().set_mldsa_key_gen_seed_en().set_ecc_key_gen_seed_en()` |
| 5 | `ECC_PKEY` | `[3]` | `crypto.rs` `ecc384_key_gen`: `set_ecc_private_key_en()` |
| 6 | `HMAC_KEY\|MLDSA_SEED\|ECC_SEED` | `[0,2,4]` | `dice.rs`: `set_hmac_key_en().set_mldsa_key_gen_seed_en().set_ecc_key_gen_seed_en()` |
| 7 | `ECC_PKEY` | `[3]` | `crypto.rs` `ecc384_key_gen`: `set_ecc_private_key_en()` |
| 8 | `MLDSA_SEED` | `[2]` | `crypto.rs` `mldsa87_key_gen`: `set_mldsa_key_gen_seed_en()` |
| 9 | `MLDSA_SEED` | `[2]` | `crypto.rs` `mldsa87_key_gen`: `set_mldsa_key_gen_seed_en()` |
