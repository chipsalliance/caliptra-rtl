# Caliptra Malicious Firmware Threat Analysis

## Security Analysis: Attestation Integrity Under Firmware Substitution Attacks

**Scope:** This report analyzes what happens when an attacker uses fault injection
(glitch attacks) against ROM to load malicious firmware onto the Caliptra RISC-V
core. For each attack path, it catalogs what resources the malicious firmware has
access to, whether it could pass a BMC attestation check (SPDM GET_MEASUREMENTS),
and which Caliptra defense layer detects the compromise.

**Threat model:** Physical fault injection (laser, EM probe) targeting ROM
instruction execution. ROM binary integrity is assumed (immutable mask ROM), but
individual instructions may be skipped or corrupted via glitch. The attacker has
full knowledge of the open-source Caliptra design, including expected PCR values,
DICE derivation algorithms, and firmware image hashes.

**Out of scope:** Supply chain attacks (compromised vendor signing key), ROM binary
replacement, side-channel attacks on key material.

---

## 1. Background: The Boot Measurement Chain

During cold boot, ROM performs these steps in order:

```
Step 1: DOE decrypts UDS → KV slot (hardware, ROM triggers but can't read result)
Step 2: ROM reads FW image from locked mailbox
Step 3: ROM hashes image → FMC_TCI = SHA384(FW_image)
Step 4: ROM verifies dual signatures (ECC-P384 + MLDSA-87) against FUSE_VENDOR_PK_HASH
Step 5: ROM derives CDI = HMAC(parent_CDI, FMC_TCI ‖ SVN) → KV slot 6
Step 6: ROM extends PCR[0] and PCR[1] with FMC_TCI and security state metadata
Step 7: ROM calls pcr_lock_clear(PCR0, PCR1) — prevents clearing until reset
Step 8: ROM generates X.509 certificates with tcg-dice-fwid extension containing FMC_TCI
Step 9: ROM copies FW image from mailbox SRAM to ICCM
Step 10: ROM sets INTERNAL_ICCM_LOCK = 1 (sticky until reset)
Step 11: ROM programs ICCM region registers and sets ICCM_REGION_LOCK
Step 12: ROM jumps to FMC entry point
```

FMC then performs an analogous derivation for RT firmware (RT_TCI → RT CDI →
RT Alias keys → RT certificate).

### Key architectural constraints

- **ICCM isolation:** Only the Caliptra RISC-V CPU can write to ICCM. No external
  AXI master (SoC, MCU, BMC) has a bus path to ICCM. There is no DMA engine that
  can target ICCM.
- **Key Vault opacity:** Firmware cannot read raw key bytes from KV slots
  (`KEY_ENTRY` has permanent `swwel=1`). Firmware can only direct crypto engines
  to operate on specific slots, subject to `dest_valid` bitmasks and lock bits.
- **PCR write protection:** PCR entries are hardware write-only via hash-extend
  from the SHA engine. Software can trigger extensions but cannot write arbitrary
  values. `pcr_lock_clear()` prevents clearing until core reset.
- **UDS secrecy:** The Unique Device Secret is a per-device hardware secret,
  decrypted by the Deobfuscation Engine directly into the Key Vault. It never
  exists in software-readable form.

---

## 2. Attack Paths: How Malicious Firmware Gets Loaded

All paths require physical fault injection against ROM. The attacker cannot modify
ROM code (mask-programmed), but can glitch individual instructions to skip them.

### Attack Path A: Glitch Signature Verification (Skip Step 4)

**Attack:** ROM skips the dual-signature check. The malicious image (unsigned or
signed by a different key) passes validation. ROM proceeds to hash, derive keys,
extend PCRs, and load the image normally.

**What ROM still does:** Steps 1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12 all execute.
The entire DICE derivation and PCR extension chain runs — but on the malicious
firmware image.

**Prerequisites:** Single glitch to skip the signature verification branch or its
error handler. ROM's CFI (Control Flow Integrity) hardening must also be defeated
if present.

### Attack Path B: Glitch DICE Derivation (Skip Step 5)

**Attack:** ROM validates and loads firmware, but skips the CDI derivation step.
KV slot 6 either retains stale data or is never written.

**What ROM still does:** Steps 1-4, 6-12. Signature verification passes (so this
could be valid OR malicious firmware depending on whether step 4 was also glitched).
PCR extension still runs.

**Prerequisites:** Single glitch to skip the HMAC operation or its KV write.

### Attack Path C: Glitch PCR Extension (Skip Steps 6-7)

**Attack:** ROM skips PCR extension and/or the pcr_lock_clear() call. PCR entries
remain at their reset value (all zeros) and the clear lock is not set.

**Prerequisites:** Multiple glitches needed (PCR extend is multiple calls).

### Attack Path D: Glitch Everything — Skip Validation, DICE, and PCR (Skip Steps 3-8)

**Attack:** ROM reads the firmware image, copies it to ICCM, and jumps. No
measurement, no signature check, no key derivation, no PCR extension, no
certificate generation.

**Prerequisites:** Multiple glitches to bypass all security steps while preserving
the copy-and-jump logic. ROM CFI hardening makes this increasingly difficult.

### Attack Path E: TOCTOU — Correct Measurement, Different Execution

**Attack:** ROM measures and derives keys from the valid image (Steps 1-8 run
correctly), but the actual code in ICCM is different at execution time (Step 12).

**Why this is architecturally infeasible:**

1. Only the Caliptra CPU can write to ICCM — no external bus path exists.
2. The CPU is running immutable ROM during the copy step.
3. ROM reads from the locked mailbox (SoC cannot modify mailbox contents while
   Caliptra holds the lock).
4. ROM copies the same data it just measured — there is no second data source.

An attacker would need to simultaneously glitch ROM's copy loop to write
different data from a different source while the CPU is executing the copy
instructions. This requires controlling both the source address and the write
data across potentially thousands of loop iterations — far beyond the capability
of single or few-glitch fault injection.

**Assessment:** Not a practical attack vector.

---

## 3. What Malicious Firmware Has Access To

For each attack path, the following table summarizes what resources the malicious
firmware can use once it is running:

### Attack Path A (Signature Glitched, Full DICE on Malicious Image)

| Resource | Available? | Details |
|----------|-----------|---------|
| KV signing keys (RT Alias ECC/MLDSA) | **Yes** | Derived from CDI of malicious image. Valid keys, wrong identity. |
| Key Vault raw key bytes | **No** | `swwel=1` permanent — KV never exposes raw key data to software. |
| ECC/HMAC/MLDSA crypto operations | **Yes** | Can direct crypto engines to use KV slots per dest_valid policy. |
| DICE certificate chain | **Yes** | Generated by ROM/FMC using malicious image measurements. Contains wrong FWID. |
| PCR values | **Contains wrong measurements** | ROM extended PCRs with SHA384(malicious_image). Locked for clear. |
| PCR hash-extend | **Yes** | Can extend further (one-way), but cannot revert to different values. |
| ICCM (self-modification) | **No** | ICCM locked by ROM at Step 10. |
| Mailbox (SoC communication) | **Yes** | Full mailbox access for command processing. |
| `cptra_error_fatal` status | **Clean** | No HW errors — all derivation steps completed normally. |

### Attack Path B (DICE Derivation Skipped)

| Resource | Available? | Details |
|----------|-----------|---------|
| KV signing keys | **No / Wrong** | CDI slot not written or has stale data. Downstream keys invalid or missing. |
| DICE certificate chain | **Incomplete** | Missing or malformed Alias certificates. |
| PCR values | **May be correct** | If PCR extension still ran with correct measurements. |
| `cptra_error_fatal` | **Set by KV monitor** | Write counter for KV slot 6 below minimum (< 4). `kv_error` fires. Key vault flushed. |

### Attack Path C (PCR Extension Skipped)

| Resource | Available? | Details |
|----------|-----------|---------|
| KV signing keys | **Depends** | If DICE ran, keys exist (bound to whatever was measured). |
| PCR values | **All zeros** | Never extended. Clear lock not set. |
| PCR manipulation | **Yes** | pcr_lock_clear() was skipped, so malicious FW can clear and re-extend PCRs. |
| Certificate FWID | **Contains measurement** | If DICE ran, cert has the measured hash (correct or malicious). |

### Attack Path D (Everything Skipped)

| Resource | Available? | Details |
|----------|-----------|---------|
| KV signing keys | **None** | No DICE derivation occurred. All KV slots empty or hold only DOE output. |
| DICE certificate chain | **None** | No certificates generated. Data vault empty. |
| PCR values | **All zeros, unlocked** | Never extended, clear lock never set. |
| `cptra_error_fatal` | **Set by KV monitor** | Write counters all zero, dest_valid all wrong. Key vault flushed. |
| Crypto operations | **No useful keys** | Even if crypto engines are functional, no key material to operate on. |

---

## 4. Can Malicious Firmware Pass GET_MEASUREMENTS?

The SPDM GET_MEASUREMENTS flow:

```
BMC → GET_MEASUREMENTS(nonce = <random 32 bytes>)
Caliptra RT FW:
  1. Triggers GEN_PCR_HASH hardware FSM
     → HW reads all 32 PCR entries + nonce
     → HW computes: digest = SHA384(PCR[0] ‖ ... ‖ PCR[31] ‖ nonce)
  2. Signs digest: signature = ECC_SIGN(RT_Alias_key, digest)
  3. Returns {PCR values, signed digest} to BMC
BMC:
  4. Verifies signature against RT Alias public key from certificate chain
  5. Verifies cert chain back to vendor CA (anchored at IDevID)
  6. Compares FWID in certificates against known-good firmware hashes
  7. Compares PCR values against expected golden values
```

### Analysis by Attack Path

#### Path A: Can It Pass? **NO**

The malicious firmware has valid signing keys and can produce a properly signed
GET_MEASUREMENTS response. However:

- **FWID mismatch (Step 6):** The Alias FMC certificate's `tcg-dice-fwid`
  extension contains `SHA384(malicious_image)`, not the expected firmware hash.
  The BMC compares this against the known-good hash from the firmware release
  manifest. **Mismatch detected.**

- **PCR mismatch (Step 7):** PCR values reflect `SHA384(malicious_image)`.
  **Mismatch detected.**

- **Key mismatch (Step 4-5):** The RT Alias public key in the certificate is
  different from any previously seen key for this device (since CDI differs).
  If the BMC pins to a known public key from a previous good boot, **mismatch
  detected.**

- **Can the attacker forge PCR values?** No. ROM locked PCR clear
  (`pcr_lock_clear`). Hash-extend is one-way — the attacker cannot reverse the
  hash to reach the expected PCR value from the current (wrong) value.

- **Can the attacker forge certificates?** No. Certificates are stored in the
  DCCM Data Vault, which ROM write-locked. Even if the attacker could generate
  new certs, they would be signed by the wrong LDevID key (which chains to the
  wrong CDI, which chains to the wrong measurement).

**Verdict: Detected by BMC via FWID comparison, PCR comparison, or key pinning.**

#### Path B: Can It Pass? **NO**

- **KV monitor fires** before malicious FW reaches steady state. `kv_error` →
  `cptra_error_fatal` → key vault flushed.
- Even if the error signal is somehow glitched away, no valid signing key exists
  in KV. The firmware cannot produce a signed GET_MEASUREMENTS response.
- BMC sees: SPDM timeout (no response) or invalid signature.

**Verdict: Detected by KV monitor (HW) + BMC timeout/signature failure.**

#### Path C (PCR Skipped, DICE Ran on Malicious Image): Can It Pass? **NO**

This is the most interesting case because the attacker has:
- Valid signing keys (bound to malicious image)
- Unlocked, zero PCR values
- Open-source knowledge of expected PCR extension inputs

The attacker could attempt to replay ROM's PCR extension sequence:

```
pcr_extend(PCR0, [lifecycle_state, debug_locked, anti_rollback,
                   vendor_pk_index, fw_svn, fuse_svn, ...])
pcr_extend(PCR0, MANUFACTURER_PK)
pcr_extend(PCR0, OWNER_PK)
pcr_extend(PCR0, expected_FMC_TCI)    ← known from open-source firmware
```

**Can this produce correct PCR values?** Potentially yes — if all input values
(lifecycle state, debug flags, SVN, public keys) match the production
environment, and the attacker replays extensions in the correct order, the
resulting PCR values would match the expected golden values.

**But the signature still fails.** The signing key is the RT Alias private key,
which was derived from `HMAC(FMC_CDI, SHA384(malicious_image) ‖ SVN)`. This key
is **different** from the key the BMC expects (derived from the valid firmware
hash). The certificate chain contains the wrong public key and the wrong FWID.

- **Step 4 (signature verification):** BMC verifies the GET_MEASUREMENTS
  signature against the RT Alias public key from the **certificate chain**. The
  cert chain was generated with keys bound to the malicious image. The BMC must
  then verify the cert chain back to the vendor CA:
  - IDevID cert: valid (UDS-derived, firmware-independent)
  - LDevID cert: valid (Field Entropy-derived, firmware-independent)
  - **Alias FMC cert: contains wrong FWID** → Step 6 catches it

Even if the attacker forges perfect PCR values, the certificate chain reveals
the wrong firmware identity.

**Verdict: Detected by FWID comparison in certificate chain.**

#### Path D (Everything Skipped): Can It Pass? **NO**

- KV monitor fires immediately → key vault flushed
- No signing keys, no certificates
- Cannot produce any SPDM response

**Verdict: Detected by KV monitor (HW) + BMC timeout.**

#### Path E (TOCTOU): **NOT FEASIBLE**

As established in Section 2, architectural isolation prevents this attack.
Only the Caliptra CPU can write to ICCM, the CPU runs immutable ROM, and ROM
reads from the locked mailbox.

---

## 5. The Attacker's Fundamental Dilemma

The Caliptra attestation architecture creates an inescapable constraint:

```
To pass GET_MEASUREMENTS, the attacker needs:
  ✓ Correct PCR values          — requires running ROM's PCR extensions
                                   with valid inputs (or forging them)
  ✓ Correct signing key         — requires DICE derivation with valid
                                   firmware hash (SHA384 of legitimate image)
  ✓ Correct certificate chain   — requires DICE to produce certs with
                                   correct FWID and correct public keys

To have the correct signing key, DICE must derive CDI from the valid image hash.
To have DICE derive from the valid image hash, ROM must measure the valid image.
To have ROM measure the valid image, the valid image must be in the mailbox.
To have the valid image in ICCM, ROM copies from the mailbox (the only writer).

∴ Correct attestation ⟹ Valid firmware is running.
   Malicious firmware ⟹ Wrong attestation (detectable).
```

The attacker cannot decouple measurement from execution because:

1. **The measurement IS the execution input.** ROM hashes the same bytes it
   copies to ICCM. There is no separate "measurement path" and "execution path"
   that could be independently targeted.

2. **The signing key IS the measurement output.** The DICE CDI is derived from
   the firmware hash. Different firmware → different hash → different CDI →
   different key. You cannot have the "correct" key without the correct
   measurement.

3. **The UDS anchors everything.** All keys chain back to the per-device UDS
   hardware secret. Without the UDS, you cannot produce any key that verifies
   against the device's certificate chain. The UDS never leaves the Key Vault.

4. **The nonce prevents replay.** Each GET_MEASUREMENTS request includes a fresh
   random nonce in the signed digest. Previously captured valid responses cannot
   be replayed.

---

## 6. Defense Layer Summary

| Layer | What It Detects | Enforcement Type | BMC Visibility |
|-------|----------------|------------------|----------------|
| **Signature verification (ROM)** | Unsigned/mis-signed firmware | FW-enforced (ROM) | Indirect (boot failure → no SPDM) |
| **DICE key binding** | Any firmware whose hash differs from expected | Cryptographic (HMAC chain from UDS) | FWID in cert + key mismatch |
| **PCR measurements** | Any firmware whose hash differs from expected | HW hash-extend + ROM extension | Signed PCR quote via SPDM |
| **KV boot flow monitor** | Skipped DICE derivation (glitched steps) | HW-enforced (write counters, dest_valid) | `cptra_error_fatal` wire + kv_error register |
| **KV enforcement block** | N/A (proactive lock/clear at transitions) | HW-enforced (hwset/hwclr) | Indirect (contains blast radius) |
| **ICCM lock** | Post-load ICCM modification | HW-enforced (AHB gating) | Indirect (prevents tampering) |
| **ICCM region registers + lock** | ICCM fetch before regions are configured | HW-enforced (boot_flow_error → fatal) | `cptra_error_fatal` wire |
| **ICCM architectural isolation** | External write to ICCM | HW architecture (no bus path) | N/A (not observable, prevented) |
| **Vendor CA anchor** | Forged certificate chain | PKI trust model | Cert chain verification failure |
| **SPDM nonce** | Replay of old valid responses | Protocol-level (fresh randomness) | Signature verification failure |
| **WDT** | Boot stall / infinite loop from glitch | HW-enforced (independent timer) | `cptra_error_fatal` wire + nmi_pin |

---

## 7. Conclusions

1. **No achievable attack path allows malicious firmware to pass a BMC
   GET_MEASUREMENTS check.** The DICE key binding ensures that any firmware
   whose hash differs from the expected value produces a different signing key,
   different certificate FWID, and (if ROM's PCR path was not glitched)
   different PCR values. The BMC detects the discrepancy through any of these
   three independent channels.

2. **The KV boot flow monitor closes the "skip everything" gap.** Without the
   monitor, an attacker who glitches ROM to skip all DICE derivation could run
   malicious firmware with empty KV slots and hope the BMC doesn't check (or
   the SPDM timeout is ignored). The monitor fires `cptra_error_fatal` within
   one clock cycle of the first ICCM fetch, flushing all key material before
   the malicious code executes a single instruction.

3. **Open-source knowledge of PCR values does not help the attacker.** Even if
   the attacker can reconstruct the correct PCR extension sequence (possible in
   Attack Path C), the GET_MEASUREMENTS response must be signed by the RT Alias
   private key. This key is bound to the firmware measurement via the DICE chain.
   Correct PCR values + wrong signing key = BMC detects the mismatch.

4. **The TOCTOU attack (correct measurement, different execution) is
   architecturally infeasible.** ICCM has no external write path. The only
   writer is the Caliptra CPU running immutable ROM, reading from a locked
   mailbox. The attacker cannot inject different code into ICCM without
   controlling the CPU's execution across thousands of copy-loop iterations.

5. **The UDS hardware secret is the root of all attestation trust.** Every
   defense ultimately depends on the attacker's inability to extract or
   reproduce the UDS. The Key Vault's `swwel=1` permanent write-enable lock
   on key data, the DOE's direct-to-KV decryption path, and the crypto
   engines' KV-only operation model collectively ensure this property.
