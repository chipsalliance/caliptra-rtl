# Caliptra Crypto IP ACVP Verification Guide

## 1. Overview

This document has two independent parts:

- **§2, ACVP Capabilities** — the capability-registration parameters for each algorithm
  (key sizes, directions, payload/IV/AAD length domains, etc.). This section is
  self-contained: it can be copied out of this document and handed directly to a
  NIST-accredited testing lab (or used to configure an ACVP client) to request the
  vector sets needed to exercise these implementations. It has no dependency on any
  repository, file, or test environment.
- **§3 onward, DUT programming sequences** — for each IP, the register interface (or
  signal interface, for HMAC DRBG) and the exact sequence needed to drive one operation.
  These are derived entirely from each IP's own RTL-level register documentation
  (`.rdl` addrmap files and module header comments), independent of any testbench. The
  intent is that a testbench can be implemented from this document alone. (Some of these
  IPs — SHA256, HMAC, ECC — already have testbenches in `caliptra-rtl` today; this
  document does not reference them.)

**Explicitly out of scope:** how ACVP JSON vectors get parsed and translated into the
register values described in §3 onward. That translation is left to whoever implements
the test harness.

**Two presentation styles.** §4-§10 (AES, SHA2, SHA3/SHAKE/cSHAKE, HMAC, HMAC-DRBG, ECDSA)
describe a direct register-poke sequence, the way a bare-metal testbench would drive the
hardware. §8.3 and §11-§13 (HMAC-KDF, ML-DSA-87, ML-KEM-1024, LMS) describe an equally
valid alternative: a thin software driver layer sitting between the harness and the
registers, exposing operations (KeyGen, SigGen, Encapsulate, ...) as function calls that
internally perform the same kind of register sequence. Either style can be used to drive
the hardware described in this document; §8.3 and §11-§13 are written this way simply to
illustrate that a driver-based harness is a workable option, not to mandate it. For
ML-DSA-87 and ML-KEM-1024, the shared hardware block referenced (the "Adams Bridge"
post-quantum accelerator) doesn't have a register-definition file available alongside
this document, so those two sections' register names and control opcodes should be
treated as illustrative rather than independently RTL-verified. LMS has no dedicated
register interface at all — see §13 for how that changes the section's shape.

---

## 2. ACVP Capabilities

### 2.1 Block Cipher Modes — AES

| Mode | Key Size | Direction | Other parameters |
|---|---|---|---|
| ECB | 128, 192, 256 | encrypt and decrypt | — |
| CBC | 128, 192, 256 | encrypt and decrypt | — |
| OFB | 128, 192, 256 | encrypt | — |
| CFB128 | 128 | encrypt | — |
| CTR | 128, 192, 256 | encrypt | `payloadLen`: domain `{min:1, max:128, increment:8}`; `incrementalCounter: true`; `overflowCounter: false`; `performCounterTests: false` |
| GCM | 128, 192, 256 | encrypt | `ivGen: external`; `ivLen: [96]`; `tagLen: [128]`; `payloadLen`: domain `{min:0, max:65536, increment:8}`; `aadLen`: domain `{min:0, max:65536, increment:8}` |

### 2.2 Secure Hash — SHA2, SHA3

| Algorithm | Parameters |
|---|---|
| SHA2-224, SHA2-256, SHA2-384, SHA2-512 | `messageLength`: domain `{min:32, max:65536, increment:32}`; `performLargeDataTest: []` |
| SHA3-224, SHA3-256, SHA3-384, SHA3-512 | `revision: 2.0`; `messageLength`: domain `{min:32, max:65536, increment:32}`; `performLargeDataTest: []` |

### 2.3 XOFs — SHAKE, cSHAKE

| Algorithm | Parameters |
|---|---|
| SHAKE-128, SHAKE-256 | `outputLen`: domain `{min:32, max:65536, increment:32}`; `messageLength`: domain `{min:32, max:65536, increment:32}` |
| cSHAKE-128, cSHAKE-256 | `hexCustomization: false`; `msgLen`: domain `{min:32, max:65536, increment:32}`; `outputLen`: domain `{min:32, max:65536, increment:32}` |

**cSHAKE hardware limit — not expressible as a standard capability field.** The DUT's
`PREFIX` register is a fixed 44 bytes, and the encoded `functionName`/`customization`
pair (SP 800-185 `encode_string(N) || encode_string(S)`) must fit within it — see §7.1/
§7.2. There is no standard ACVP cSHAKE capability parameter for constraining
`functionName`/`customization` length (the schema above has no such field), so this
44-byte limit cannot be registered through normal capability negotiation. **The testing
lab needs to make a special request to NIST** to ensure cSHAKE-128/256 test vectors keep
the combined encoded `N`/`S` length within 44 bytes; a vector exceeding that would need
to be rejected or skipped rather than fed to the DUT as-is.

### 2.4 Message Authentication — HMAC

| Algorithm | `keyLen` | `macLen` |
|---|---|---|
| HMAC-SHA2-384 | `[384]` | domain `{min:256, max:384, increment:64}` |
| HMAC-SHA2-512 | `[512]` | domain `{min:256, max:512, increment:64}` |

### 2.5 DRBGs — HMAC DRBG

| Algorithm | Parameters |
|---|---|
| HMAC-DRBG (SHA2-384) | `predResistanceEnabled: false`; `reseedImplemented: false`; `entropyInputLen: [384]`; `nonceLen: [384]`; `persoStringLen: [0]`; `additionalInputLen: [0]`; `returnBitsLen: 384` |

### 2.6 Digital Signatures — ECDSA P-384

| Operation | Standard | Parameters |
|---|---|---|
| ECDSA KeyGen | FIPS 186-5 | `curve: [P-384]`; `secretGenerationMode: testing candidates` |
| ECDSA SigVer | FIPS 186-5 | `componentTest: true`; `curve: [P-384]`; `hashAlg: SHA2-384` |
| Deterministic ECDSA SigGen | FIPS 186-5 | `componentTest: true`; `curve: [P-384]`; `hashAlg: SHA2-384` |

### 2.7 KDFs

| Algorithm | Mode | Standard | Parameters |
|---|---|---|---|
| KDF | Counter | SP 800-108r1 | `macMode: HMAC-SHA2-384`; `supportedLengths: [384]`; `fixedDataOrder: [before iterator]`; `counterLength: 32`; `supportsEmptyIv: true`; `requiresEmptyIv: false` |

### 2.8 Stateful Hash-Based Signatures — LMS

| Algorithm | Mode | Standard | Parameters |
|---|---|---|---|
| LMS | sigVer | SP 800-208 | `lmsMode: [LMS_SHA256_M24_H15]`; `lmOtsMode: [LMOTS_SHA256_N24_W4]` |

### 2.9 Module-Lattice Signatures — ML-DSA-87

| Operation | Standard | Parameters |
|---|---|---|
| ML-DSA KeyGen | FIPS 204 | `parameterSets: [ML-DSA-87]` |
| ML-DSA SigGen | FIPS 204 | `parameterSets: [ML-DSA-87]`; `deterministic: [true]`; `signatureInterfaces: [external]`; `preHash: [pure]`; `externalMu: [true, false]`; `messageLength`: domain `{min:8, max:512, increment:8}`; `hashAlgs: []`; `contextLength: [0]` |
| ML-DSA SigVer | FIPS 204 | `parameterSets: [ML-DSA-87]`; `signatureInterfaces: [external]`; `preHash: [pure]`; `externalMu: [true, false]`; `messageLength`: domain `{min:8, max:512, increment:8}`; `hashAlgs: []`; `contextLength: [0]` |

### 2.10 Module-Lattice KEM — ML-KEM-1024

| Operation | Standard | Parameters |
|---|---|---|
| ML-KEM KeyGen | FIPS 203 | `parameterSets: [ML-KEM-1024]` |
| ML-KEM encapDecap | FIPS 203 | `parameterSets: [ML-KEM-1024]`; `functions: [encapsulation, decapsulation]` |

---

## 3. Common AHB-Lite driver primitives

Every IP below except HMAC DRBG (§9, which is a direct signal interface) is driven over
AHB-Lite. `write_single_word`/`read_single_word` should be edge-synchronized and
wait-state-aware, respecting `HREADYOUT` rather than assuming a fixed number of clock
cycles:

```systemverilog
task write_single_word(input [31:0] address, input [31:0] word);
  begin
    @(posedge clk_tb);
    hsel_i_tb   = 1;
    haddr_i_tb  = address;
    hwrite_i_tb = 1;
    hready_i_tb = 1;
    htrans_i_tb = AHB_HTRANS_NONSEQ;
    hsize_i_tb  = 3'b010;
    @(posedge clk_tb);                // end of address phase
    wait(hreadyout_o_tb == 1'b1);     // don't proceed until the slave is ready
    hwdata_i_tb = word;
    @(posedge clk_tb);                // end of data phase
    haddr_i_tb  = '0;
    hwrite_i_tb = 0;
    htrans_i_tb = AHB_HTRANS_IDLE;
    hsel_i_tb   = 0;
  end
endtask

task read_single_word(input [31:0] address);
  begin
    @(posedge clk_tb);
    hsel_i_tb   = 1;
    haddr_i_tb  = address;
    hwrite_i_tb = 0;
    hready_i_tb = 1;
    htrans_i_tb = AHB_HTRANS_NONSEQ;
    hsize_i_tb  = 3'b010;
    @(posedge clk_tb);                // end of address phase
    wait(hreadyout_o_tb == 1'b1);
    @(posedge clk_tb);                // data phase: sample on this edge
    read_data   = hrdata_o_tb;
    haddr_i_tb  = '0;
    htrans_i_tb = AHB_HTRANS_IDLE;
    hsel_i_tb   = 0;
  end
endtask
```

`wait_ready()` (or equivalent) polls `STATUS` via `read_single_word` in a loop until the
relevant bit(s) are set, as described per IP below.

Every sequence below assumes the DUT is already out of reset and `clk_tb` is
free-running before the first `write_single_word`/`read_single_word` call; reset
sequencing itself is outside the scope of this document.

**Pass/fail determination** follows the same pattern for every IP below: a `STATUS`/
`ready` completion bit (e.g. `VALID`) means the requested computation finished, not that
its result is correct. Correctness is established separately, by comparing the
register(s) read back in the last step of each sequence against the ACVP vector's
expected value, truncating to the requested output length first where the algorithm
calls for it (e.g. HMAC's `macLen`, or the SHA2-224/SHA2-384 digest-truncation rules in
§5/§6). The one exception is ECDSA SigVer (§10.4), where there is no vector-supplied
expected value to compare against directly — instead, the DUT's own computed `VERIFY_R`
is compared against the originally supplied `SIGN_R`.

---

## 4. AES

Register interface documented in `src/aes/data/aes.rdl`; encodings in `src/aes/rtl/aes_pkg.sv`.

### 4.1 Register map

| Register | Address |
|---|---|
| `KEY_SHARE0_0..7` | `0x04`–`0x20` |
| `KEY_SHARE1_0..7` | `0x24`–`0x40` |
| `IV_0..3` | `0x44`–`0x50` |
| `DATA_IN_0..3` | `0x54`–`0x60` |
| `DATA_OUT_0..3` | `0x64`–`0x70` |
| `CTRL_SHADOWED` | `0x74` |
| `CTRL_AUX_SHADOWED` | `0x78` |
| `CTRL_AUX_REGWEN` | `0x7c` |
| `TRIGGER` | `0x80` |
| `STATUS` | `0x84` |
| `CTRL_GCM_SHADOWED` | `0x88` |
| `ENTROPY_IF_SEED_0..8` | `0x910`–`0x930` (9×32-bit, CLP-specific block at `+0x800`) |

**`CTRL_SHADOWED`** (`0x74`):

| Bits | Field | Values |
|---|---|---|
| [1:0] | `OPERATION` | `AES_ENC=2'b01`, `AES_DEC=2'b10` |
| [7:2] | `MODE` | `AES_ECB=6'b00_0001`, `AES_CBC=6'b00_0010`, `AES_CFB=6'b00_0100`, `AES_OFB=6'b00_1000`, `AES_CTR=6'b01_0000`, `AES_GCM=6'b10_0000` |
| [10:8] | `KEY_LEN` | `AES_128=3'b001`, `AES_192=3'b010`, `AES_256=3'b100` |
| [11] | `SIDELOAD` | 0 = software key via `KEY_SHARE1`, 1 = key-manager sideload |
| [14:12] | `PRNG_RESEED_RATE` | `PER_1=3'b001` — written on every `CTRL_SHADOWED` write; the masking PRNG's reseed rate is never left at its 0 reset value |
| [15] | `MANUAL_OPERATION` | must be 1 so the unit waits for an explicit `TRIGGER.START` rather than auto-starting on `DATA_IN` writes |

**`TRIGGER`** (`0x80`):

| Bits | Field |
|---|---|
| [0] | `START` |
| [1] | `KEY_IV_DATA_IN_CLEAR` |
| [2] | `DATA_OUT_CLEAR` |
| [3] | `PRNG_RESEED` |

**`STATUS`** (`0x84`):

| Bits | Field |
|---|---|
| [0] | `IDLE` |
| [1] | `STALL` |
| [2] | `OUTPUT_LOST` |
| [3] | `OUTPUT_VALID` |
| [4] | `INPUT_READY` |
| [5] | `ALERT_RECOV_CTRL_UPDATE_ERR` |
| [6] | `ALERT_FATAL_FAULT` |

**`CTRL_GCM_SHADOWED`** (`0x88`):

| Bits | Field | Values |
|---|---|---|
| [5:0] | `PHASE` | `GCM_INIT=6'b00_0001`, `GCM_RESTORE=6'b00_0010`, `GCM_AAD=6'b00_0100`, `GCM_TEXT=6'b00_1000`, `GCM_SAVE=6'b01_0000`, `GCM_TAG=6'b10_0000` |
| [10:6] | `NUM_VALID_BYTES` | 16 for a full block; only the last AAD/TEXT block may be partial |

**Shadowed-register write protocol:** `CTRL_SHADOWED` and `CTRL_GCM_SHADOWED` are backed
by `caliptra_prim_subreg_shadow` primitives (`src/aes/rtl/aes_ctrl_reg_shadowed.sv`) — a
staged/commit register that requires **two identical consecutive writes** to take effect;
a mismatched pair or a single write sets `STATUS.ALERT_RECOV_CTRL_UPDATE_ERR` instead of
committing.

**Byte packing for `KEY_SHARE0/1`, `IV`, `DATA_IN`, `DATA_OUT`:** these are not written as
a plain sequential big-endian split. For a 16-byte value `b0..b15` (`b0` = first byte),
split it into 4-byte groups in order (`b0..b3`, `b4..b7`, `b8..b11`, `b12..b15`), then
**reverse the byte order within each group** before writing it as a 32-bit word to the
next register in the sequence — e.g. the first word = `{b3,b2,b1,b0}` (as a hex value,
MSB to LSB), written to the lowest-address register of that group. The same rule extends
to the 256-bit `KEY_SHARE0/1` (8 groups of 4 bytes each). Reads of `DATA_OUT` undo the
same transform to reconstruct the result in natural byte order.

**Entropy seeding:** write all 9 `ENTROPY_IF_SEED` registers once (order doesn't matter)
to seed the internal Trivium/PRNG primitive used for masking. This is a one-time step
for the lifetime of the DUT instance — done once, after reset, before the first
operation — not repeated before each subsequent operation.

### 4.2 Sequence — ECB/CBC/CFB/OFB/CTR

Assumes entropy seeding (§4.1) has already been done once for this DUT instance.

1. Wait `STATUS.IDLE`.
2. Write `CTRL_SHADOWED` twice (`OPERATION`, `MODE`, `KEY_LEN`, `PRNG_RESEED_RATE=PER_1`,
   `MANUAL_OPERATION=1`).
3. Wait `STATUS.IDLE`.
4. Write `KEY_SHARE0_0..7` (key, byte-packed per §4.1) and `KEY_SHARE1_0..7` (0, if not
   using masking).
5. If mode ≠ ECB: wait `STATUS.IDLE`, write `IV_0..3` (byte-packed per §4.1).
6. Per 128-bit block: wait `STATUS.INPUT_READY` → write `DATA_IN_0..3` (byte-packed) →
   write `TRIGGER.START=1` → wait `STATUS.OUTPUT_VALID` → read `DATA_OUT_0..3`
   (byte-packed, reverse to get the result).

**Worked example — AES-128 CBC encrypt, single block**

| Field | Value |
|---|---|
| `key` | `00000000000000000000000000000000` |
| `iv` | `00000000000000000000000000000000` |
| `pt` | `F34481EC3CC627BACD5DC3FB08F273E6` |
| expected `ct` | `0336763E966D92595A567CC9CE537F5E` |

1. Write `CTRL_SHADOWED` = `0x00009109` twice (`OPERATION=AES_ENC`, `MODE=AES_CBC`,
   `KEY_LEN=AES_128`, `PRNG_RESEED_RATE=PER_1`, `MANUAL_OPERATION=1`; `SIDELOAD=0`).
2. Write `KEY_SHARE0_0..7` and `KEY_SHARE1_0..7` — all `0x00000000` (key is all-zero, so
   byte-reversal doesn't change anything here).
3. Write `IV_0..3` — all `0x00000000` (same reason).
4. Write `DATA_IN_0..3` (byte-reversed groups of `pt`):

   | Register | Value | `pt` group |
   |---|---|---|
   | `DATA_IN_0` | `0xEC8144F3` | `F34481EC` |
   | `DATA_IN_1` | `0xBA27C63C` | `3CC627BA` |
   | `DATA_IN_2` | `0xFBC35DCD` | `CD5DC3FB` |
   | `DATA_IN_3` | `0xE673F208` | `08F273E6` |

5. Write `TRIGGER` = `0x1`.
6. Wait `STATUS.OUTPUT_VALID`, then read `DATA_OUT_0..3` and byte-reverse each word:

   | Register | Raw value | Byte-reversed |
   |---|---|---|
   | `DATA_OUT_0` | `0x3E763603` | `03 36 76 3E` |
   | `DATA_OUT_1` | `0x59926D96` | `96 6D 92 59` |
   | `DATA_OUT_2` | `0xC97C565A` | `5A 56 7C C9` |
   | `DATA_OUT_3` | `0x5E7F53CE` | `CE 53 7F 5E` |

   Concatenated: `0336763E966D92595A567CC9CE537F5E` — matches the expected `ct` exactly.

### 4.3 Sequence — GCM

Assumes entropy seeding (§4.1) has already been done once for this DUT instance.

1. Wait `STATUS.IDLE`.
2. Write `CTRL_SHADOWED` twice with `MODE=AES_GCM`, `PRNG_RESEED_RATE=PER_1`,
   `MANUAL_OPERATION=0` (automatic mode) — GCM's INIT phase runs two internal AES
   operations (deriving H and the initial counter block) that must be allowed to
   self-complete.
3. **INIT**: write `CTRL_GCM_SHADOWED`=`{PHASE=GCM_INIT, NUM_VALID_BYTES=16}` twice,
   write the key, wait `STATUS.IDLE`, write `IV_0..3` = `{96-bit nonce, 32'h0}`, wait
   `STATUS.IDLE` again (both H and the counter must finish deriving).
4. **AAD** (if any): per 16-byte AAD block, wait `STATUS.INPUT_READY` → write
   `CTRL_GCM_SHADOWED`=`{PHASE=GCM_AAD, NUM_VALID_BYTES}` twice → write `DATA_IN_0..3`.
5. **TEXT**: per 16-byte plaintext/ciphertext block, wait `STATUS.INPUT_READY` → write
   `CTRL_GCM_SHADOWED`=`{PHASE=GCM_TEXT, NUM_VALID_BYTES}` twice → write `DATA_IN_0..3` →
   wait `STATUS.OUTPUT_VALID` → read `DATA_OUT_0..3`.
6. **TAG**: wait `STATUS.IDLE` → write `CTRL_GCM_SHADOWED`=`{PHASE=GCM_TAG,
   NUM_VALID_BYTES=16}` twice → write `DATA_IN_0..3` = `{len(AAD)_bits, len(CT)_bits}`
   (64 bits each) → wait `STATUS.OUTPUT_VALID` → read `DATA_OUT_0..3` as the tag.

Between phase transitions, wait for a full `STATUS.IDLE` rather than just
`INPUT_READY` — the internal GHASH computation can still be completing after a block
even once `INPUT_READY` first asserts.

**Worked example — AES-128 GCM encrypt** (all values below use the byte packing from
§4.1)

| Field | Value |
|---|---|
| `keyLen` / `ivLen` / `aadLen` | 128 / 96 / 0 |
| `payloadLen` | 18304 bits = 143 full 16-byte blocks |
| `key` | `3FBD299D9BEB57E66337D0392525017B` |
| `iv` | `1F49FC015354F810C27469FD` |
| plaintext block 1 | `03594552B7E4AB0D2337F64CC18426C6` |
| plaintext block 143 (last) | `242A24EB9F5D6C59B7FD3DE908A03DF6` |
| expected `tag` | `DBA5FEB7359518383FC6CCF5F739ABC5` |

1. Write `CTRL_SHADOWED` = `0x00001181` twice (`OPERATION=AES_ENC`, `MODE=AES_GCM`,
   `KEY_LEN=AES_128`, `PRNG_RESEED_RATE=PER_1`, `MANUAL_OPERATION=0`; `SIDELOAD=0`).
2. **INIT**: write `CTRL_GCM_SHADOWED` = `0x00000401` twice (`PHASE=GCM_INIT`,
   `NUM_VALID_BYTES=16`), then write the key and IV:

   | Register | Value |
   |---|---|
   | `KEY_SHARE0_0..3` | `0x9D29BD3F`, `0xE657EB9B`, `0x39D03763`, `0x7B012525` (byte-packed key) |
   | `KEY_SHARE0_4..7` | `0x00000000` (unused for a 128-bit key) |
   | `KEY_SHARE1_0..7` | `0x00000000` (no masking) |
   | `IV_0..3` (after `STATUS.IDLE`) | `0x01FC491F`, `0x10F85453`, `0xFD6974C2`, `0x00000000` (96-bit nonce + appended `32'h0`) |

   Wait `STATUS.IDLE` again (both H and the counter must finish deriving).
3. **AAD**: skipped entirely — this test case has `aadLen=0`.
4. **TEXT, block 1 of 143**: wait `STATUS.INPUT_READY` → write `CTRL_GCM_SHADOWED` =
   `0x00000408` twice (`PHASE=GCM_TEXT`, `NUM_VALID_BYTES=16`) → write `DATA_IN_0..3` →
   wait `STATUS.OUTPUT_VALID` → read `DATA_OUT_0..3`:

   | Register | `DATA_IN` (plaintext, byte-packed) | `DATA_OUT` (raw) |
   |---|---|---|
   | word 0 | `0x52455903` | `0x0AAEA477` |
   | word 1 | `0x0DABE4B7` | `0xB6E386E8` |
   | word 2 | `0x4CF63723` | `0xE40CE7BF` |
   | word 3 | `0xC62684C1` | `0x17460019` |

   Byte-reversing `DATA_OUT` gives ciphertext block 1 = `03594552B7E4AB0D2337F64CC18426C6`
   — matches the expected result.
5. **TEXT, blocks 2–142**: repeat step 4 identically for each remaining plaintext block
   (write `CTRL_GCM_SHADOWED=0x408` twice, write the block to `DATA_IN`, wait
   `OUTPUT_VALID`, read `DATA_OUT`).
6. **TEXT, block 143 (final block)**: same pattern:

   | Register | `DATA_IN` (plaintext, byte-packed) | `DATA_OUT` (raw) |
   |---|---|---|
   | word 0 | `0xEB242A24` | `0x620D1003` |
   | word 1 | `0x596C5D9F` | `0xCEFE2077` |
   | word 2 | `0xE93DFDB7` | `0x424676E9` |
   | word 3 | `0xF63DA008` | `0x0F7B68CE` |

   Byte-reversing `DATA_OUT` gives ciphertext block 143 =
   `242A24EB9F5D6C59B7FD3DE908A03DF6` — matches the expected result. (This vector's
   payload is an exact multiple of 16 bytes, so every block — including the last — uses
   `NUM_VALID_BYTES=16`; a non-multiple-of-16 payload would set a smaller value on the
   final block only.)
7. **TAG**: wait `STATUS.IDLE` → write `CTRL_GCM_SHADOWED` = `0x00000420` twice
   (`PHASE=GCM_TAG`, `NUM_VALID_BYTES=16`) → write the AAD/CT length block → wait
   `STATUS.OUTPUT_VALID` → read the tag:

   | Register | `DATA_IN` (length block, byte-packed) | `DATA_OUT` (raw) |
   |---|---|---|
   | word 0 | `0x00000000` | `0xB7FEA5DB` |
   | word 1 | `0x00000000` | `0x38189535` |
   | word 2 | `0x00000000` | `0xF5CCC63F` |
   | word 3 | `0x80470000` | `0xC5AB39F7` |

   (`DATA_IN` here encodes `{len(AAD)=0 bits, len(CT)=18304 bits}`, 64 bits each.)
   Byte-reversing `DATA_OUT` gives `DBA5FEB7359518383FC6CCF5F739ABC5` — matches the
   expected `tag` exactly.

### 4.4 Monte Carlo Test (MCT)

Applies to ECB, CBC, OFB, and CFB128. CTR and GCM have no MCT test type — AFT only.
Each `AES_<MODE>_ENCRYPT`/`_DECRYPT` call below is one execution of the single-block
sequence in §4.2.

**ECB encrypt:**
```
Key[0] = KEY; PT[0] = PT
For i = 0 to 99
  For j = 0 to 999
    CT[j] = AES_ECB_ENCRYPT(Key[i], PT[j])
    PT[j+1] = CT[j]
  Output CT[999]
  Key[i+1] = KEY_SHUFFLE(Key[i], CT[999], CT[998])
  PT[0] = CT[999]
```

**CBC / OFB / CFB128 encrypt** (identical shape; only the `AES_<MODE>_ENCRYPT`
primitive differs):
```
Key[0] = KEY; IV[0] = IV; PT[0] = PT
For i = 0 to 99
  For j = 0 to 999
    If j == 0:
      CT[j] = AES_<MODE>_ENCRYPT(Key[i], IV[i], PT[j])
      PT[j+1] = IV[i]
    Else:
      CT[j] = AES_<MODE>_ENCRYPT(Key[i], PT[j])
      PT[j+1] = CT[j-1]
  Output CT[999]
  Key[i+1] = KEY_SHUFFLE(Key[i], CT[999], CT[998])
  IV[i+1] = CT[999]
  PT[0] = CT[998]
```

**Decrypt** (ECB, CBC only): swap every `PT`/`CT` reference in the corresponding encrypt
pseudocode above. OFB and CFB128 are encrypt-only, matching §2.1's Capabilities table —
there is no decrypt MCT for either mode.

**Key shuffle** (same formula across all four MCT-capable modes, applied at the end of
each outer iteration `i`):
```
128-bit key: Key[i+1] = Key[i] XOR MSB(CT[999], 128)
192-bit key: Key[i+1] = Key[i] XOR ( LSB(CT[998], 64) || MSB(CT[999], 128) )
256-bit key: Key[i+1] = Key[i] XOR ( MSB(CT[998], 128) || MSB(CT[999], 128) )
```

---

## 5. SHA2-224 / SHA2-256

Register interface documented in `src/sha256/rtl/sha256_reg.rdl`.

### 5.1 Register map

| Register | Address |
|---|---|
| `NAME_0/1`, `VERSION_0/1` | `0x00`,`0x04`,`0x08`,`0x0c` |
| `CTRL` | `0x10` |
| `STATUS` | `0x18` |
| `BLOCK_0..15` | `0x80`–`0xbc` (16×32-bit = 512-bit message block, big-endian) |
| `DIGEST_0..7` | `0x100`–`0x11c` (8×32-bit = 256-bit digest, big-endian) |

**`CTRL`** (`0x10`) — `INIT`/`NEXT`/`ZEROIZE` are single-pulse fields: a software write
generates one pulse and the bit self-clears:

| Bits | Field | Notes |
|---|---|---|
| [0] | `INIT` | start processing the first padded message block |
| [1] | `NEXT` | start processing the remaining padded message block |
| [2] | `MODE` | 0 = SHA2-224, 1 = SHA2-256 |
| [3] | `ZEROIZE` | |

**`STATUS`** (`0x18`):

| Bits | Field | Notes |
|---|---|---|
| [0] | `READY` | core is ready to take a control command |
| [1] | `VALID` | process is done and DIGEST is valid |

(`CTRL` also has Winternitz-specific fields — `WNTZ_MODE`, `WNTZ_W`, `WNTZ_N_MODE` — and
`STATUS` has `WNTZ_BUSY`; none are needed for standard SHA-2 hashing.)

### 5.2 Sequence

Message padding (the `0x80` marker plus a big-endian bit-length field, to a multiple of
512 bits) is not part of this register interface — the DUT only ever receives complete,
already-padded 512-bit blocks.

1. Per 512-bit block: write `BLOCK_0..15` (plain sequential big-endian split of the
   padded block — no byte reversal, unlike AES).
2. Write `CTRL` = `{MODE, INIT=1}` for the first block of a message, or
   `{MODE, NEXT=1}` for every subsequent block.
3. Wait `STATUS.READY` or `STATUS.VALID` (either indicates the block finished
   processing).
4. After the last block, read `DIGEST_0..7`. For SHA2-224, only `DIGEST_0..6` (the
   upper 224 bits) are the result — `DIGEST_7` is not part of the digest.
5. Write `CTRL.ZEROIZE=1` before starting the next message.

**Worked example — SHA2-224, single block**

| Field | Value |
|---|---|
| `msg` | `B3E7066F` (32 bits) |
| expected `md` | `ACACA5282641E8452DD4C6CAEF9C7952010B6FE9BD3ACC531D0D2FC2` |

1. Pad the message to one 512-bit block: `B3E7066F` + `0x80` marker + 51 zero bytes +
   64-bit big-endian length field (`32` bits) = 
   `B3E7066F800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020`.
2. Write `BLOCK_0..15` — `BLOCK_0`=`0xB3E7066F`, `BLOCK_1`=`0x80000000`,
   `BLOCK_2..14`=`0x00000000`, `BLOCK_15`=`0x00000020` (the last word carries the 64-bit
   length field's low half; its upper half is the `0x00000000` at `BLOCK_14`).
3. Write `CTRL` = `0x1` (`MODE=0` for SHA2-224, `INIT=1`).
4. Wait `STATUS.READY`/`STATUS.VALID`.
5. Read `DIGEST_0..6` (`DIGEST_7` discarded):

   | Register | Value |
   |---|---|
   | `DIGEST_0` | `0xACACA528` |
   | `DIGEST_1` | `0x2641E845` |
   | `DIGEST_2` | `0x2DD4C6CA` |
   | `DIGEST_3` | `0xEF9C7952` |
   | `DIGEST_4` | `0x010B6FE9` |
   | `DIGEST_5` | `0xBD3ACC53` |
   | `DIGEST_6` | `0x1D0D2FC2` |

   Concatenated: `ACACA5282641E8452DD4C6CAEF9C7952010B6FE9BD3ACC531D0D2FC2` — matches the
   expected `md` exactly.

### 5.3 Monte Carlo Test (MCT)

Standard MCT — one `SHA2-224/256(MSG)` call is one execution of the full §5.2 sequence
over `MSG`'s padded blocks:

```
SEED = seed value from the test vector
For j = 0 to 99
  A = B = C = SEED
  For i = 0 to 999
    MSG = A || B || C
    MD = SHA2-224/256(MSG)
    A = B; B = C; C = MD
  Output MD
  SEED = MD
```

---

## 6. SHA2-384 / SHA2-512

Register interface documented in `src/sha512/rtl/sha512_reg.rdl`.

### 6.1 Register map

| Register | Address |
|---|---|
| `NAME_0/1`, `VERSION_0/1` | `0x00`,`0x04`,`0x08`,`0x0c` |
| `CTRL` | `0x10` |
| `STATUS` | `0x18` |
| `BLOCK_0..31` | `0x80`–`0xfc` (32×32-bit = 1024-bit message block, big-endian) |
| `DIGEST_0..15` | `0x100`–`0x13c` (16×32-bit = 512-bit digest, big-endian) |

**`CTRL`** (`0x10`):

| Bits | Field | Notes |
|---|---|---|
| [0] | `INIT` | |
| [1] | `NEXT` | |
| [3:2] | `MODE` | `10`=SHA-384, `11`=SHA-512 |
| [4] | `ZEROIZE` | |
| [5] | `LAST` | key-vault/hash-extend write-back — not needed for standard hashing |
| [6] | `RESTORE` | resume from a previously-saved digest — not needed for standard hashing |

**`STATUS`** (`0x18`):

| Bits | Field |
|---|---|
| [0] | `READY` |
| [1] | `VALID` |

SHA-512 has additional register groups beyond `DIGEST` (key-vault read/write control at
`0x600`–`0x60c`, and a PCR-hash sub-block at `0x610`–`0x674`) that are not part of
standard ACVP hashing.

### 6.2 Sequence

Same structure as SHA-256 (§5.2, including its worked example) — write the padded
message a block at a time, `CTRL`={`MODE`,`INIT`/`NEXT`}, wait ready/valid, read the
digest, zeroize. Padding (0x80 marker + 128-bit big-endian length field, to a multiple
of 1024 bits) is done before any register write; the DUT only receives complete padded
blocks. Concretely, versus §5.2:

- Block and digest registers are twice as wide (`BLOCK_0..31` vs `BLOCK_0..15`;
  `DIGEST_0..15` vs `DIGEST_0..7`) and the length field in the padding is 128 bits
  instead of 64.
- `MODE` is a 2-bit field (`10`/`11`) instead of 1 bit.
- The truncation rule for a narrower output (§5.2's "`DIGEST_7` is not part of the
  result" for SHA2-224) has a direct SHA-384 analog: keep only the upper 384 bits
  (`DIGEST[511:128]`, i.e. `DIGEST_0..11`) and discard `DIGEST_12..15`.

Everything else — byte packing (plain sequential big-endian, no reversal), the
INIT-first-block/NEXT-subsequent-blocks rule, and the ready/valid polling — carries over
unchanged from the §5.2 worked example.

1. Per 1024-bit block: write `BLOCK_0..31`.
2. Write `CTRL` = `{MODE, INIT=1}` for the first block, `{MODE, NEXT=1}` for subsequent
   blocks.
3. Wait `STATUS.READY` or `STATUS.VALID`.
4. After the last block, read `DIGEST_0..15`. For SHA-384, keep only `DIGEST[511:128]`
   (the register always holds a full 512-bit result regardless of mode).
5. Write `CTRL.ZEROIZE=1` before the next message.

### 6.3 Monte Carlo Test (MCT)

Standard MCT, same structure as §5.3 — one `SHA2-384/512(MSG)` call is one execution of
the full §6.2 sequence over `MSG`'s padded blocks:

```
SEED = seed value from the test vector
For j = 0 to 99
  A = B = C = SEED
  For i = 0 to 999
    MSG = A || B || C
    MD = SHA2-384/512(MSG)
    A = B; B = C; C = MD
  Output MD
  SEED = MD
```

---

## 7. SHA3-224/256/384/512, SHAKE-128/256, cSHAKE-128/256

Register interface documented in `src/sha3/rtl/kmac_reg.rdl`. This register block is
reachable at IP-base **+ 0x1000**; all offsets below are relative to that.

### 7.1 Register map

| Register | Offset (from +0x1000) |
|---|---|
| `CFG_REGWEN` | `0x10` |
| `CFG_SHADOWED` | `0x14` |
| `CMD` | `0x18` |
| `STATUS` | `0x1c` |
| `PREFIX_0..10` | `0x20`–`0x48` (11×32-bit, cSHAKE N/S encoding) |
| `ERR_CODE` | `0x4c` |
| `STATE` | `0x400` (digest/squeeze output) |
| `MSG_FIFO` | `0x800` (message input window) |

**Note — endianness exception:** `PREFIX` words are packed **little-endian** (byte order
reversed within each word) — unlike every other register in this document, including
`MSG_FIFO`/`STATE` in this same IP.

**`CFG_SHADOWED`** (`0x14`) — a shadowed register: write the value twice to commit:

| Bits | Field | Values |
|---|---|---|
| [3:1] | `kstrength` | `L128=0x0`, `L224=0x1`, `L256=0x2`, `L384=0x3`, `L512=0x4` |
| [5:4] | `mode` | `SHA3=0x0`, `SHAKE=0x2`, `cSHAKE=0x3` (`0x1` is unused/reserved) |
| [8] | `msg_endianness` | written `1` on every configuration write |
| [9] | `state_endianness` | written `1` on every configuration write |

**`CMD`** (`0x18`) — 6-bit one-hot-style command field:

| Value | Command | Effect |
|---|---|---|
| `0x1D` | `START` | begins absorbing (only valid while idle) |
| `0x2E` | `PROCESS` | ends the absorb phase and begins the digest/squeeze computation |
| `0x31` | `RUN` | triggers 24 more Keccak rounds during the squeeze stage — used when more output is needed than one rate's worth |
| `0x16` | `DONE` | completes the operation |

**`STATUS`** (`0x1c`):

| Bits | Field |
|---|---|
| [0] | `sha3_idle` |
| [1] | `sha3_absorb` |
| [2] | `sha3_squeeze` |
| [12:8] | `fifo_depth` |
| [14] | `fifo_empty` |
| [15] | `fifo_full` |

The worked examples below (§7.2) are all 128-bit-security-strength variants
(SHA3-224, SHAKE-128, cSHAKE-128). The 256-bit-strength siblings (SHA3-256/384/512,
SHAKE-256, cSHAKE-256) follow the identical CFG/CMD/STATUS sequence — the only changes
are `kstrength` in `CFG_SHADOWED` (`L256=0x2`/`L384=0x3`/`L512=0x4` instead of
`L224=0x1`), the digest word count for fixed-length modes (8/12/16 words instead of 7),
and `RATE_WORDS` for XOF modes (34 words per squeeze at 256-bit strength instead of 42).

### 7.2 Sequence

1. Wait `STATUS.sha3_idle`.
2. Write `CFG_SHADOWED` twice (`kstrength`, `mode`).
3. **cSHAKE only**: build the SP 800-185 `encode_string(N) || encode_string(S)` byte
   string (up to 44 bytes) and write it as 11×32-bit words to `PREFIX_0..10` (see the
   little-endian packing note in §7.1), before issuing `CMD.START`.
4. Write `CMD=START`. Wait `STATUS.sha3_absorb`.
5. Write the message into `MSG_FIFO` (big-endian word packing; the last partial word is
   zero-padded in its low-order bits).
6. Write `CMD=PROCESS`. Wait `STATUS.sha3_squeeze`.
7. **Fixed-length digest (SHA3-224/256/384/512)**: read the digest words (7/8/12/16
   words for 224/256/384/512) from `STATE`.
   **Variable-length output (SHAKE/cSHAKE)**: read one rate's worth of words from
   `STATE` (42 words at 128-bit security strength, 34 words at 256-bit security
   strength); if more output is needed, write `CMD=RUN`, wait `STATUS.sha3_squeeze`
   again, and read the next chunk from `STATE`. Repeat until the requested output length
   is produced.
8. Write `CMD=DONE`.

**Worked example — SHA3-224, single word**

| Field | Value |
|---|---|
| `msg` | `A00FB3D6` (32 bits) |
| expected `md` | `2050128C8DBCC4F54AE05880FE4A71E9E764F78B9F460A7E06EADCAA` |

1. Wait `STATUS.sha3_idle`.
2. Write `CFG_SHADOWED` = `0x302` twice (`kstrength=L224=0x1`, `mode=SHA3=0x0`,
   `msg_endianness=1`, `state_endianness=1`).
3. Write `CMD` = `0x1D` (`START`). Wait `STATUS.sha3_absorb`.
4. Write `MSG_FIFO` = `0xA00FB3D6` (the message is exactly one 4-byte word, so no
   zero-padding is needed).
5. Write `CMD` = `0x2E` (`PROCESS`). Wait `STATUS.sha3_squeeze`.
6. Read 7 words from `STATE` (SHA3-224's digest is 224 bits):

   | Register | Value |
   |---|---|
   | `STATE` word 0 | `0x2050128C` |
   | `STATE` word 1 | `0x8DBCC4F5` |
   | `STATE` word 2 | `0x4AE05880` |
   | `STATE` word 3 | `0xFE4A71E9` |
   | `STATE` word 4 | `0xE764F78B` |
   | `STATE` word 5 | `0x9F460A7E` |
   | `STATE` word 6 | `0x06EADCAA` |

   Concatenated: `2050128C8DBCC4F54AE05880FE4A71E9E764F78B9F460A7E06EADCAA` — matches
   the expected `md` exactly.
7. Write `CMD` = `0x16` (`DONE`).

**Worked example — SHAKE-128, variable-length output (single squeeze)**

| Field | Value |
|---|---|
| `msg` | 48 bytes: `78E7FE19F6721D0E2B6FD8E3E2934021238351AD4E02728A3DAD5DF969A9ECD3605523A4311FF266E23AB3E7860EA187` |
| requested `outLen` | 64 bits |
| expected `md` | `6ED7B7157A84D1C5` |

1. Wait `STATUS.sha3_idle`.
2. Write `CFG_SHADOWED` = `0x320` twice (`kstrength=L128=0x0`, `mode=SHAKE=0x2`,
   `msg_endianness=1`, `state_endianness=1`).
3. Write `CMD` = `0x1D` (`START`). Wait `STATUS.sha3_absorb`.
4. Write the message into `MSG_FIFO` as 12 sequential 32-bit words (48 bytes divides
   evenly by 4, so no zero-padding is needed):

   | Word | Value | Word | Value |
   |---|---|---|---|
   | 0 | `0x78E7FE19` | 6 | `0x3DAD5DF9` |
   | 1 | `0xF6721D0E` | 7 | `0x69A9ECD3` |
   | 2 | `0x2B6FD8E3` | 8 | `0x605523A4` |
   | 3 | `0xE2934021` | 9 | `0x311FF266` |
   | 4 | `0x238351AD` | 10 | `0xE23AB3E7` |
   | 5 | `0x4E02728A` | 11 | `0x860EA187` |

5. Write `CMD` = `0x2E` (`PROCESS`). Wait `STATUS.sha3_squeeze`.
6. The requested 64-bit output is far smaller than one rate (1344 bits at 128-bit
   security strength), so only a single squeeze is needed: read 2 words from `STATE`:
   `0x6ED7B715`, `0x7A84D1C5`. Concatenated: `6ED7B7157A84D1C5` — matches the expected
   `md` exactly. (Had the requested output exceeded one rate, `CMD=RUN` would be
   written and `STATUS.sha3_squeeze` re-polled before reading the next 42-word chunk,
   repeating until enough output was produced — not exercised by this vector.)
7. Write `CMD` = `0x16` (`DONE`).

**Worked example — cSHAKE-128, non-empty customization string, multi-squeeze output**

| Field | Value |
|---|---|
| `msg` | `2BA24798` (32 bits) |
| `functionName` (N) | `""` (empty) |
| `customization` (S) | `"N1 /T*Er"` |
| requested `outLen` | 54368 bits = 1699 words |
| expected `md` | begins `B11C2F49E3C13871...`, ends `...573141E2C4F63CC5` |

1. Wait `STATUS.sha3_idle`.
2. Write `CFG_SHADOWED` = `0x330` twice (`kstrength=L128=0x0`, `mode=cSHAKE=0x3`,
   `msg_endianness=1`, `state_endianness=1`).
3. Build the SP 800-185 prefix and write it to `PREFIX_0..10` before `CMD.START`:
   - `encode_string(N)` = `0100` (N is empty: a length byte of 1, then the single byte
     `0x00`).
   - `encode_string(S)` = `01404E31202F542A4572` (length-in-bits 64 encoded as `01 40`,
     then the 8 ASCII bytes of `S`).
   - Concatenated and zero-padded to 44 bytes, then packed as 11 **little-endian**
     words (byte order reversed within each word, unlike `MSG_FIFO`/`STATE`):

     | Register | Value |
     |---|---|
     | `PREFIX_0` | `0x40010001` |
     | `PREFIX_1` | `0x2F20314E` |
     | `PREFIX_2` | `0x72452A54` |
     | `PREFIX_3..10` | `0x00000000` (trailing zero padding) |

4. Write `CMD` = `0x1D` (`START`). Wait `STATUS.sha3_absorb`.
5. Write `MSG_FIFO` = `0x2BA24798` (the message is exactly one word).
6. Write `CMD` = `0x2E` (`PROCESS`). Wait `STATUS.sha3_squeeze`.
7. The requested output (1699 words) is far larger than one rate (42 words at 128-bit
   security strength), so 41 squeezes are needed: 40 full 42-word reads from `STATE`
   followed by one final 19-word read (`40×42 + 19 = 1699`).
   - **Squeeze 1** (no `CMD=RUN` needed — this read follows directly from `PROCESS`):
     read 42 words from `STATE`, the first six being:

     | Word | Value | Word | Value |
     |---|---|---|---|
     | 0 | `0xB11C2F49` | 3 | `0x0B268B55` |
     | 1 | `0xE3C13871` | 4 | `0xC71539AF` |
     | 2 | `0x563A5808` | 5 | `0xD1E3E19A` |

     ...ending with word 41 = `0xB39C33ED`.
   - **Squeezes 2–40**: each identical — write `CMD` = `0x31` (`RUN`), wait
     `STATUS.sha3_squeeze`, read the next 42 words from `STATE`.
   - **Squeeze 41 (final)**: write `CMD` = `0x31` (`RUN`), wait `STATUS.sha3_squeeze`,
     read only the remaining 19 words from `STATE`:

     | Word | Value | Word | Value |
     |---|---|---|---|
     | 0 | `0xDC82D53C` | 10 | `0xA5298628` |
     | 1 | `0xD72FF48D` | 11 | `0xE3041144` |
     | 2 | `0xCB194B61` | 12 | `0x561198E0` |
     | 3 | `0x358BEEF8` | 13 | `0xD48EE245` |
     | 4 | `0x2BA834C8` | 14 | `0xB97056BE` |
     | 5 | `0xF05E033C` | 15 | `0x7D4D1ABF` |
     | 6 | `0x63CA380E` | 16 | `0xFC917BAE` |
     | 7 | `0xBBC67115` | 17 | `0x573141E2` |
     | 8 | `0x6AE1A2E0` | 18 | `0xC4F63CC5` |
     | 9 | `0x7A63FF00` | | |

   Concatenating all 1699 words reproduces the full expected `md` exactly (verified
   programmatically against the ACVP expected-results file).
8. Write `CMD` = `0x16` (`DONE`).

### 7.3 Monte Carlo Test (MCT) — SHA3-224/256/384/512

Standard MCT — one `SHA3(MSG)` call is one execution of the fixed-length-digest path of
§7.2:

```
MD[0] = SEED
For j = 0 to 99
  For i = 1 to 1000
    MD[i] = SHA3(MD[i-1])
  Output MD[1000]
  SEED = MD[1000]
```

SHAKE-128/256 has no MCT test type — only AFT and Variable Output Test (VOT). VOT is not
a separate procedure: it uses the identical §7.2 sequence, just driven with test cases
that request a range of different `outLen` values rather than one fixed length. The
variable-length squeeze-more loop in §7.2 step 7 already handles any requested length, so
no additional sequence is needed here.

### 7.4 Monte Carlo Test (MCT) — cSHAKE-128/256

One `cSHAKE(...)` call is one execution of the variable-length-output path of §7.2, with
`N` (function name) fixed to `""` throughout:

```
Range         = MaxOutLen - MinOutLen + 1
OutputLen     = MaxOutLen
Customization = ""
InnerMsg      = Left(SEED || zero-padding, 128 bits)

For j = 0 to 99
  For i = 1 to 1000
    Output[i] = cSHAKE(InnerMsg, OutputLen, FunctionName="", Customization)
    Rightmost = rightmost 16 bits of Output[i], as an unsigned integer
    Customization = BitsToString(InnerMsg || Rightmost)
    OutputLen = MinOutLen + floor((Rightmost mod Range) / OutLenIncrement) * OutLenIncrement
    InnerMsg = Left(Output[i] || zero-padding, 128 bits)
  Output Output[1000] (length OutputLen at the time it was produced)
  SEED for reporting = Output[1000]
```

`BitsToString` maps each byte `b` of its input to the character `'A' + (b mod 26)`.
`Customization` is never reset across outer iterations — it carries state through the
entire 100×1000 run. So only the very first inner call of the whole MCT (`j=0`, `i=1`)
sees an empty `Customization` and runs as plain SHAKE (the same SHAKE-fallback rule from
§7.2); every other call — including `i=1` of every subsequent outer iteration
(`j=1..99`) — runs as true cSHAKE with the carried-over `Customization` from the
previous call.

---

## 8. HMAC-SHA2-384 / HMAC-SHA2-512

Register interface documented in `src/hmac/rtl/hmac_reg.rdl`. HMAC has no MCT test
type — AFT only.

### 8.1 Register map

| Register | Offset |
|---|---|
| `NAME_0/1`, `VERSION_0/1` | `0x0`,`0x4`,`0x8`,`0xc` |
| `CTRL` | `0x10` |
| `STATUS` | `0x18` |
| `KEY_0..15` | `0x40`–`0x7c` (16×32-bit = 512-bit key register, fixed width) |
| `BLOCK_0..31` | `0x80`–`0xfc` (32×32-bit = 1024-bit message block) |
| `TAG_0..15` | `0x100`–`0x13c` (16×32-bit = 512-bit MAC output) |
| `LFSR_SEED_0..11` | `0x140`–`0x16c` (12×32-bit = 384-bit) |

**`CTRL`** (`0x10`):

| Bits | Field | Notes |
|---|---|---|
| [0] | `INIT` | start processing the key and the first padded message block |
| [1] | `NEXT` | |
| [2] | `ZEROIZE` | zeroize all internal registers, to avoid SCA leakage |
| [3] | `MODE` | 0 = SHA2-384, 1 = SHA2-512 |
| [4] | `CSR_MODE` | sources the key from an internal key-vault CSR instead of `KEY_0..15` — not used for standard ACVP hashing |

**`STATUS`** (`0x18`):

| Bits | Field | Notes |
|---|---|---|
| [0] | `READY` | |
| [1] | `VALID` | results in TAG are valid |

The worked example below (§8.2) is HMAC-SHA2-384. HMAC-SHA2-512 follows the identical
sequence — the only changes are `CTRL` bit[3]=1 instead of 0, and the key no longer
needs zero-extension (a 512-bit key fills `KEY_0..15` natively instead of only
`KEY_0..11`).

### 8.2 Sequence

1. Write `KEY_0..15`. The register is always 512 bits wide regardless of mode; a
   384-bit (SHA-2-384-native) key is zero-extended into it.
2. Per 1024-bit (already-padded) block: write `BLOCK_0..31`; on the first block also
   write `LFSR_SEED_0..11`, then write `CTRL`=`{MODE, INIT=1}`; on subsequent blocks
   write `CTRL`=`{MODE, NEXT=1}`.
3. Wait `STATUS.READY` or `STATUS.VALID` after each block.
4. After the last block, read `TAG_0..15` (512 bits); truncate to the requested MAC
   length by keeping the high-order bits.
5. Write `CTRL.ZEROIZE=1` before the next operation.

**Worked example — HMAC-SHA2-384, single block, truncated to a 320-bit MAC**

| Field | Value |
|---|---|
| `keyLen` | 384 bits |
| `key` | `4D1A1F948AA811C03B5C024A97B7970421E30BBD1C283ED70673E45A31F7EB572A18F540F008D5F32F705621110CA79D` |
| `msg` | `E871542EE3390633B9CE836A4F04A216` (128 bits) |
| requested `macLen` | 320 bits |
| expected `mac` | `0A3D73D92D088799DA8A2C078D45BBCF09DE47D8F96CF74A89D03DEBA11AB105879F553CF9CB869D` |

1. Write `KEY_0..11` (the 384-bit key, sequential big-endian) and `KEY_12..15` = `0`
   (zero-extension into the 512-bit register):

   | Register | Value | Register | Value |
   |---|---|---|---|
   | `KEY_0` | `0x4D1A1F94` | `KEY_6` | `0x0673E45A` |
   | `KEY_1` | `0x8AA811C0` | `KEY_7` | `0x31F7EB57` |
   | `KEY_2` | `0x3B5C024A` | `KEY_8` | `0x2A18F540` |
   | `KEY_3` | `0x97B79704` | `KEY_9` | `0xF008D5F3` |
   | `KEY_4` | `0x21E30BBD` | `KEY_10` | `0x2F705621` |
   | `KEY_5` | `0x1C283ED7` | `KEY_11` | `0x110CA79D` |
   | `KEY_12..15` | `0x00000000` | | |

2. Pad the message to one 1024-bit block: `E871542EE3390633B9CE836A4F04A216` + `0x80`
   marker + 95 zero bytes + 128-bit big-endian length field (`128` bits).
3. Write `BLOCK_0..31` — `BLOCK_0`=`0xE871542E`, `BLOCK_1`=`0xE3390633`,
   `BLOCK_2`=`0xB9CE836A`, `BLOCK_3`=`0x4F04A216`, `BLOCK_4`=`0x80000000`,
   `BLOCK_5..30`=`0x00000000`, `BLOCK_31`=`0x00000080` (the last word carries the low
   half of the 128-bit length field; the rest of the length field is `0` since the
   message is far under 2^32 bits).
4. Write `LFSR_SEED_0..11` (any consistent value — this seeds the core's internal
   SCA-countermeasure masking, not the HMAC computation itself, so it doesn't affect
   the result).
5. Write `CTRL` = `0x1` (`MODE=0` for SHA2-384, `INIT=1`).
6. Wait `STATUS.READY`/`STATUS.VALID`.
7. Read `TAG_0..15`; keep the top 10 words (320 bits):

   | Register | Value | Register | Value |
   |---|---|---|---|
   | `TAG_0` | `0x0A3D73D9` | `TAG_5` | `0xF96CF74A` |
   | `TAG_1` | `0x2D088799` | `TAG_6` | `0x89D03DEB` |
   | `TAG_2` | `0xDA8A2C07` | `TAG_7` | `0xA11AB105` |
   | `TAG_3` | `0x8D45BBCF` | `TAG_8` | `0x879F553C` |
   | `TAG_4` | `0x09DE47D8` | `TAG_9` | `0xF9CB869D` |

   Concatenated:
   `0A3D73D92D088799DA8A2C078D45BBCF09DE47D8F96CF74A89D03DEBA11AB105879F553CF9CB869D`
   — matches the expected `mac` exactly.

### 8.3 HMAC-KDF (SP 800-108 Counter Mode)

This is a counter-mode key-derivation function that can be implemented as a thin software
wrapper around the *same* HMAC register interface already documented in §8.1/§8.2 — there
is no need for separate KDF hardware. The underlying construction is mode-generic (it
works the same way on top of either HMAC-SHA2-384 or HMAC-SHA2-512); this section uses
HMAC-SHA2-384 throughout because that's the mode §2.7's registered ACVP capability
requests, not because the KDF is inherently tied to it. A harness can expose the KDF as
its own function/entry point (rather than raw register pokes at the call site) if that's
a more convenient shape for the rest of the test infrastructure; either way, the
underlying register sequence is identical to §8.2's.

The KDF's only difference from plain HMAC (§8.2) is what gets hashed: instead of the raw
ACVP message, the harness constructs

```
counter(1, 4 bytes big-endian) || label || [0x00 || context, if context is supplied]
```

pads that exactly as §8.2 step 2 describes, and runs it through the identical
`KEY`/`BLOCK`/`LFSR_SEED`/`CTRL`/`STATUS`/`TAG` register sequence. The counter is fixed at
`i=1` (single-iteration counter mode — there's no need to loop to `i=2` for longer
outputs at the message lengths ACVP registers here); `context` is optional and, when
present, is separated from `label` by a single
`0x00` byte. The derived output is read back from `TAG_0..15` exactly as in §8.2, keeping
the high-order bits if truncating to a requested length.

**Worked example — HMAC-SHA2-384 KDF, no context** (independently verified: computed
`HMAC-SHA-384(key, counter(1) || label)` in Python and confirmed the first 40 bytes match
the reference output exactly)

| Field | Value |
|---|---|
| `key` (384 bits) | `B57DC52354AFEE11EDB4C9052A528344348B2C6B6C39F32133ED3BB72035A4AB55D6648C1529EF7A9170FEC9EF26A81E` |
| `label` (60 bytes) | `17E641909DEDFEE4968BB95D7F770E4557CA347A46614CB371423F0D91DF3B58B536ED54531FD2A2EB0B8B2A1634C23C88FAD9706C45DB4411A23B89` |
| `context` | none |
| expected `out` (320 bits, first 40 bytes of the full 384-bit HMAC output) | `5949ACF9635A77297928C1E155D43A4E4BCA61B1369A5EF50530888550BA270E26BE4A421CDF80B7` |

1. Write `KEY_0..11` (the 384-bit key fills the register natively — no zero-extension
   needed, same as §8.2's HMAC-SHA2-512 case):

   | Register | Value | Register | Value |
   |---|---|---|---|
   | `KEY_0` | `0xB57DC523` | `KEY_6` | `0x33ED3BB7` |
   | `KEY_1` | `0x54AFEE11` | `KEY_7` | `0x2035A4AB` |
   | `KEY_2` | `0xEDB4C905` | `KEY_8` | `0x55D6648C` |
   | `KEY_3` | `0x2A528344` | `KEY_9` | `0x1529EF7A` |
   | `KEY_4` | `0x348B2C6B` | `KEY_10` | `0x9170FEC9` |
   | `KEY_5` | `0x6C39F321` | `KEY_11` | `0xEF26A81E` |

2. Construct `counter(1) || label` = 4 + 60 = 64 bytes (512 bits), then pad to one
   1024-bit block: `0x80` marker + 47 zero bytes + 128-bit big-endian length field
   (`512` bits). Write `BLOCK_0..31`:

   | Register | Value | Register | Value |
   |---|---|---|---|
   | `BLOCK_0` | `0x00000001` (the counter, `i=1`) | `BLOCK_16` | `0x80000000` |
   | `BLOCK_1` | `0x17E64190` | `BLOCK_17` | `0x00000000` |
   | `BLOCK_2` | `0x9DEDFEE4` | `BLOCK_18` | `0x00000000` |
   | `BLOCK_3` | `0x968BB95D` | `BLOCK_19` | `0x00000000` |
   | `BLOCK_4` | `0x7F770E45` | `BLOCK_20` | `0x00000000` |
   | `BLOCK_5` | `0x57CA347A` | `BLOCK_21` | `0x00000000` |
   | `BLOCK_6` | `0x46614CB3` | `BLOCK_22` | `0x00000000` |
   | `BLOCK_7` | `0x71423F0D` | `BLOCK_23` | `0x00000000` |
   | `BLOCK_8` | `0x91DF3B58` | `BLOCK_24` | `0x00000000` |
   | `BLOCK_9` | `0xB536ED54` | `BLOCK_25` | `0x00000000` |
   | `BLOCK_10` | `0x531FD2A2` | `BLOCK_26` | `0x00000000` |
   | `BLOCK_11` | `0xEB0B8B2A` | `BLOCK_27` | `0x00000000` |
   | `BLOCK_12` | `0x1634C23C` | `BLOCK_28` | `0x00000000` |
   | `BLOCK_13` | `0x88FAD970` | `BLOCK_29` | `0x00000000` |
   | `BLOCK_14` | `0x6C45DB44` | `BLOCK_30` | `0x00000000` |
   | `BLOCK_15` | `0x11A23B89` | `BLOCK_31` | `0x00000200` (length field = 512) |

3. Write `LFSR_SEED_0..11` (any consistent value, per §8.2).
4. Write `CTRL` = `0x1` (`MODE=0` for SHA2-384, `INIT=1`).
5. Wait `STATUS.READY`/`STATUS.VALID`.
6. Read `TAG_0..15`; the requested 320-bit output keeps the top 10 words:

   | Register | Value | Register | Value |
   |---|---|---|---|
   | `TAG_0` | `0x5949ACF9` | `TAG_5` | `0x369A5EF5` |
   | `TAG_1` | `0x635A7729` | `TAG_6` | `0x05308885` |
   | `TAG_2` | `0x7928C1E1` | `TAG_7` | `0x50BA270E` |
   | `TAG_3` | `0x55D43A4E` | `TAG_8` | `0x26BE4A42` |
   | `TAG_4` | `0x4BCA61B1` | `TAG_9` | `0x1CDF80B7` |

   Concatenated: `5949ACF9635A77297928C1E155D43A4E4BCA61B1369A5EF50530888550BA270E26BE4A421CDF80B7`
   — matches the expected `out` exactly.
7. Write `CTRL.ZEROIZE=1` before the next operation.

**If `context` is supplied** for a different test case, insert a `0x00` byte immediately
after `label` and before `context` in step 2's message, then re-pad accordingly — the
register sequence itself doesn't change, only the padded message content.

---

## 9. HMAC DRBG

Documented in `src/hmac_drbg/rtl/hmac_drbg.sv`: the design parameters and INIT/NEXT
algorithm description come from the module header (lines 15-51); the port names and
widths in §9.1 come from the module's port declaration (lines 53-76). This IP has **no
register interface** — it is driven via direct signal ports. Design parameters per the
header: SHA-384-based, `PredictionResistance=False`, `EntropyInputLen=384`,
`NonceLen=384`, `PersonalizationStringLen=0`, `AdditionalInputLen=0`,
`ReturnedBitsLen=384`. There is no reseed path. DRBG testing has a single test type,
AFT — there is no MCT for DRBGs.

### 9.1 Interface (signal ports)

| Port | Dir | Width | Purpose |
|---|---|---|---|
| `zeroize` | in | 1 | clear internal state |
| `init_cmd` | in | 1 | instantiate with entropy/nonce, then generate |
| `next_cmd` | in | 1 | generate again (no reseed) |
| `ready` | out | 1 | idle/ready for a command |
| `valid` | out | 1 | output valid |
| `lfsr_seed` | in | 384 | internal LFSR seed |
| `entropy` | in | 384 | DRBG entropy input |
| `nonce` | in | 384 | DRBG nonce input |
| `drbg` | out | 384 | returned random bits |

### 9.2 Sequence

1. Wait for `ready`.
2. Drive `entropy` and `nonce` (held constant across both rounds below).
3. **Round 0** (instantiate + first generate): drive `lfsr_seed`, pulse `init_cmd` for
   one clock, deassert, then wait for `valid` — `drbg` now holds the first generate's
   output.
4. **Round 1** (second generate, no reseed): drive a fresh `lfsr_seed`, pulse `next_cmd`
   for one clock, deassert, then wait for `valid` — `drbg` now holds the second
   generate's output.

An ACVP HMAC-DRBG (no-reseed) test case corresponds to running both rounds and taking
the second round's output.

**Worked example** (no reseed, empty personalization string and additional input on
both generate calls, per this IP's fixed design parameters):

| Field | Value |
|---|---|
| `entropyInput` | `E2A0B5F4DCEF407AD027A3C7C56F06BB312801F634525CE02FC0AF641B5749C5D5FC9475281230217C96C9CD6EB20F04` |
| `nonce` | `1859B61544751A5F0719D0EE549770BC2A3AE4BF23A18722210D37246F6DE00720866177718E834F54A6B3185812A29D` |
| expected `returnedBits` | `A56611A015A40C797B2DC2EF4E075D3D322D96A10D31ADD92BDA860800ED5063D6D5722DC78389A71294EC0F24279987` |

1. Wait for `ready`.
2. Drive `entropy` = the `entropyInput` value above, `nonce` = the `nonce` value above
   (both held constant for both rounds).
3. **Round 0**: drive any `lfsr_seed` value, pulse `init_cmd` for one clock, deassert,
   wait for `valid`. `drbg` now holds the first generate's output — not the value ACVP
   checks, since this test type generates twice and reports only the second result.
4. **Round 1**: drive a (possibly different) `lfsr_seed` value, pulse `next_cmd` for
   one clock, deassert, wait for `valid`. `drbg` now holds
   `A56611A015A40C797B2DC2EF4E075D3D322D96A10D31ADD92BDA860800ED5063D6D5722DC78389A71294EC0F24279987`
   — matching the expected `returnedBits` exactly.

Verified independently by implementing the plain NIST SP 800-90A HMAC_DRBG algorithm
(`Instantiate` from `entropyInput||nonce`, then two `Generate` calls) with HMAC-SHA-384
and no reseed: the second `Generate` call's output reproduces `returnedBits` exactly for
this vector, confirming both the entropy/nonce/no-reseed handling and that this
particular draw didn't hit the internal rejection-and-retry path the RTL describes for
out-of-range values. That path isn't exercised by this vector, but it is confirmed
working elsewhere in the testbench by a dedicated fault-injection test that directly
force-triggers the out-of-range condition and checks the retry logic recovers from it.

---

## 10. ECDSA P-384 — KeyGen / SigGen / SigVer

Register interface documented in `src/ecc/rtl/ecc_reg.rdl`. All three operations share
one register map. ECDSA testing (KeyGen, SigGen, SigVer, and deterministic SigGen) uses
AFT only — there is no MCT for ECDSA.

### 10.1 Register map (384-bit fields = 12×32-bit words, big-endian, MSB-first)

| Register | Offset | Used by |
|---|---|---|
| `CTRL` | `0x10` | all |
| `STATUS` | `0x18` | all |
| `SEED_0..11` | `0x80`–`0xac` | KeyGen |
| `MSG_0..11` | `0x100`–`0x12c` | SigGen, SigVer (hashed message digest) |
| `PRIVKEY_OUT_0..11` | `0x180`–`0x1ac` | KeyGen (output) |
| `PUBKEY_X_0..11` | `0x200`–`0x22c` | KeyGen (output), SigVer (input) |
| `PUBKEY_Y_0..11` | `0x280`–`0x2ac` | KeyGen (output), SigVer (input) |
| `SIGN_R_0..11` | `0x300`–`0x32c` | SigGen (output), SigVer (input) |
| `SIGN_S_0..11` | `0x380`–`0x3ac` | SigGen (output), SigVer (input) |
| `VERIFY_R_0..11` | `0x400`–`0x42c` | SigVer (computed result, output) |
| `IV_0..11` | `0x480`–`0x4ac` | KeyGen, SigGen (SCA-countermeasure randomization input — not used by SigVer, which has no secret to protect) |
| `NONCE_0..11` | `0x500`–`0x52c` | KeyGen only |
| `PRIVKEY_IN_0..11` | `0x580`–`0x5ac` | SigGen |

**`CTRL`** (`0x10`) — self-clears after each write:

| Bits | Field | Values |
|---|---|---|
| [1:0] | command | `00`=NONE, `01`=KEYGEN, `10`=SIGNING, `11`=VERIFYING |
| [2] | `ZEROIZE` | |

**`STATUS`** (`0x18`):

| Bits | Field |
|---|---|
| [0] | `READY` |
| [1] | `VALID` |

### 10.2 KeyGen

1. Wait `STATUS.READY`.
2. Write `SEED_0..11`, `NONCE_0..11`, `IV_0..11`.
3. Write `CTRL`=`01` (KEYGEN).
4. Wait `STATUS.VALID`.
5. Read `PRIVKEY_OUT_0..11`, `PUBKEY_X_0..11`, `PUBKEY_Y_0..11`.
6. Write `CTRL.ZEROIZE=1`.

**Worked example — KeyGen**

| Field | Value |
|---|---|
| expected `d` | `AA9A5B8652B050C4132337E6C8DABD48F868053F7FEE29AB7C7328FC3F520AADF9003B8626DE6D6DCE173D0C26E12938` |
| expected `qx` | `9DD7A5235280B8ECE69D3787211CEE8D42F3F717EEF03D4A39004E73C853C4AF8FAAD5D26EB83DEE3EA530B84B2DBDAD` |
| expected `qy` | `4FB013CD53DCC215464A1E8F470192C775E3BD1FBA4492DAFE611B5A0F8BE04147154E9A1F0FD5BF4B2B78921157E7B1` |

ACVP KeyGen doesn't supply `SEED`/`NONCE`/`IV` inputs — the harness must generate its own
random 384-bit values for these registers. The DUT has no on-chip TRNG for this path: it
deterministically derives the key pair from exactly the `SEED`/`NONCE` values it's given,
so these writes are the only source of randomness, not an optional convenience. The ACVP
server only checks that the reported key pair is valid, not that it matches a particular
seed. So step 1 below uses illustrative (not vector-supplied) values; only the read-back
in steps 2-3 is real, vector-verified data.

1. Wait `STATUS.READY`. Write `SEED_0..11`, `NONCE_0..11`, `IV_0..11` with random 384-bit
   values generated by the harness (these are the only source of randomness for this
   operation). Write `CTRL`=`01` (KEYGEN). Wait `STATUS.VALID`.
2. Read `PRIVKEY_OUT_0..11`:

   | Register | Value | Register | Value |
   |---|---|---|---|
   | word 0 | `0xAA9A5B86` | word 6 | `0x7C7328FC` |
   | word 1 | `0x52B050C4` | word 7 | `0x3F520AAD` |
   | word 2 | `0x132337E6` | word 8 | `0xF9003B86` |
   | word 3 | `0xC8DABD48` | word 9 | `0x26DE6D6D` |
   | word 4 | `0xF868053F` | word 10 | `0xCE173D0C` |
   | word 5 | `0x7FEE29AB` | word 11 | `0x26E12938` |

3. Read `PUBKEY_X_0..11` and `PUBKEY_Y_0..11`:

   | Word | `PUBKEY_X` | `PUBKEY_Y` |
   |---|---|---|
   | 0 | `0x9DD7A523` | `0x4FB013CD` |
   | 1 | `0x5280B8EC` | `0x53DCC215` |
   | 2 | `0xE69D3787` | `0x464A1E8F` |
   | 3 | `0x211CEE8D` | `0x470192C7` |
   | 4 | `0x42F3F717` | `0x75E3BD1F` |
   | 5 | `0xEEF03D4A` | `0xBA4492DA` |
   | 6 | `0x39004E73` | `0xFE611B5A` |
   | 7 | `0xC853C4AF` | `0x0F8BE041` |
   | 8 | `0x8FAAD5D2` | `0x47154E9A` |
   | 9 | `0x6EB83DEE` | `0x1F0FD5BF` |
   | 10 | `0x3EA530B8` | `0x4B2B7892` |
   | 11 | `0x4B2DBDAD` | `0x1157E7B1` |

4. Write `CTRL.ZEROIZE=1`.

Verified independently (not via the DUT, since the seed-to-key derivation is internal):
recomputed `Q = d·G` on P-384 from scratch (own point-addition/doubling implementation,
curve constants cross-checked against a library) and confirmed it equals the reported
`(qx, qy)` exactly.

### 10.3 SigGen (deterministic)

1. Wait `STATUS.READY`.
2. Write `MSG_0..11` (hashed message digest), `PRIVKEY_IN_0..11`, `IV_0..11`.
3. Write `CTRL`=`10` (SIGNING).
4. Wait `STATUS.VALID`.
5. Read `SIGN_R_0..11`, `SIGN_S_0..11`.
6. Write `CTRL.ZEROIZE=1`.

No nonce/`k` register is written for signing — `NONCE` is wired only to the KeyGen path.
The signing nonce `k` is generated internally, from the private key and hashed message,
by an on-chip HMAC-DRBG per RFC 6979 (`src/ecc/rtl/ecc_hmac_drbg_interface.sv:17-29`),
which is what makes this deterministic ECDSA.

`PRIVKEY_IN` is not a freely-suppliable input — ACVP never discloses a private key for
SigGen vectors. Per ACVP test group, the harness must first run KeyGen (§10.2) once to
generate a fresh key pair, then write that exact private key to `PRIVKEY_IN` for every
signing operation in that group. The resulting `PUBKEY_X`/`PUBKEY_Y` must also be
reported alongside each `(r, s)`, since without the private key the ACVP server has no
other way to check that a given signature is valid.

**Worked example** (`componentTest: true` — `message` is already the SHA-384 digest,
confirmed by its length being exactly 48 bytes)

| Field | Value |
|---|---|
| `message` (= the hash) | `3EC68470F629333790B6D2676F7828F17043E428742AB4A69D0C65011150CF965BC9B862C27D7163A8CD75BFD270662E` |
| expected `r` | `B3C5CBF5AFA681787A2C8CAB4F6F14406ECB1AC356C7AAD4C5F9F371B7DFBF50D1E89433C4B84AEA4D3394627B1EDE80` |
| expected `s` | `EAD3E2C4F3EA442903A328568183B71BEE058073E40862584474031022A719B0CBE569B3EDF260CF0372BD181D7E4BA0` |
| group public key `qx` | `5829B7B536BAF659AC3D01DC04B0F557259F6F7C7791EA6E94476578A60FED778B475C06B53D430E83486B5884C5973B` |
| group public key `qy` | `7E5EEE5F605FED51E86D861A3048E673D4DBDF4505F1F1AB7D104A09AE3FDF125470B3B2A6F84D234AE0011ECAC20891` |

The `qx`/`qy` above are this test group's public key — the harness generated this key
pair via one KeyGen operation for the whole group and reported it back, exactly as
described above. Like KeyGen, the private key used to sign is never disclosed by ACVP,
so `PRIVKEY_IN`/`IV` below are illustrative, not vector-supplied — but in a real harness
`PRIVKEY_IN` would be the private key produced by that same group-level KeyGen call, not
an arbitrary value.

1. Wait `STATUS.READY`.
2. Write `MSG_0..11` (the message is already the hash — no separate hashing step
   needed here):

   | Word | Value | Word | Value |
   |---|---|---|---|
   | 0 | `0x3EC68470` | 6 | `0x9D0C6501` |
   | 1 | `0xF6293337` | 7 | `0x1150CF96` |
   | 2 | `0x90B6D267` | 8 | `0x5BC9B862` |
   | 3 | `0x6F7828F1` | 9 | `0xC27D7163` |
   | 4 | `0x7043E428` | 10 | `0xA8CD75BF` |
   | 5 | `0x742AB4A6` | 11 | `0xD270662E` |

   Write `PRIVKEY_IN_0..11` and `IV_0..11` (internal to the DUT for this test group;
   not part of the ACVP vector).
3. Write `CTRL`=`10` (SIGNING). Wait `STATUS.VALID`.
4. Read `SIGN_R_0..11` and `SIGN_S_0..11`:

   | Word | `SIGN_R` | `SIGN_S` |
   |---|---|---|
   | 0 | `0xB3C5CBF5` | `0xEAD3E2C4` |
   | 1 | `0xAFA68178` | `0xF3EA4429` |
   | 2 | `0x7A2C8CAB` | `0x03A32856` |
   | 3 | `0x4F6F1440` | `0x8183B71B` |
   | 4 | `0x6ECB1AC3` | `0xEE058073` |
   | 5 | `0x56C7AAD4` | `0xE4086258` |
   | 6 | `0xC5F9F371` | `0x44740310` |
   | 7 | `0xB7DFBF50` | `0x22A719B0` |
   | 8 | `0xD1E89433` | `0xCBE569B3` |
   | 9 | `0xC4B84AEA` | `0xEDF260CF` |
   | 10 | `0x4D339462` | `0x0372BD18` |
   | 11 | `0x7B1EDE80` | `0x1D7E4BA0` |

   Concatenated, these match the expected `r`/`s` exactly.
5. Write `CTRL.ZEROIZE=1`.

Verified independently: the reported `(r, s)` is a valid ECDSA signature over the given
hash under the reported `(qx, qy)`, confirmed with a from-scratch ECDSA verification
(same point arithmetic as the KeyGen check above) — this is the same check ACVP itself
performs, since the private key isn't disclosed for direct comparison.

### 10.4 SigVer

1. Wait `STATUS.READY`.
2. Write `MSG_0..11` (hashed digest), `PUBKEY_X_0..11`, `PUBKEY_Y_0..11`,
   `SIGN_R_0..11`, `SIGN_S_0..11`.
3. Write `CTRL`=`11` (VERIFYING).
4. Wait `STATUS.VALID`.
5. Read `VERIFY_R_0..11`.
6. Write `CTRL.ZEROIZE=1`.

**Worked example — valid signature** (unlike the SigGen vector above, this SigVer
vector's `message` field is a raw 1024-bit message, not a pre-hashed digest — no
`componentTest` flag is set for this test group, confirmed by the message being 128
bytes long. It must be hashed with SHA-384 before writing to `MSG_0..11`)

| Field | Value |
|---|---|
| `message` (raw) | `72D1DAC4511E4735083653DF648EB82A41512EE5C38CC91673F88290FF8B1228D99566B42D31447FD7FB7C1C4E403C9C6B58B0E6C36885D88607F6969E1E318552A11FA12A2482F137F24D48644F1E698E20AF311064CAF83691D8AF227C712444E16C6DAACBBC1A89C14A8E60BC695FB7181210437666BE0EC96CE73F0CB282` |
| `qx` | `D5B077F1AD3E4508F64066AC690E038E6699D88D332ED21D885F264E75C57F0BE0D20405D89CF26DFE046C495817B37C` |
| `qy` | `E9EF199257A0567EF43CE04A1E0E9311DAEF77E1615C076CF7C8607CF3CF6A8EE4C20887CE0C1AAD920840F5C602AB5A` |
| `r` | `E2E197A22B9BBE62D40CF98A4023378BF5FF3DDDA5C4E95903227B892F17C7F9BEC2A8D7A3FA9773C6575AFAA7821BF6` |
| `s` | `3D7C92FD8714BB05478EB6166DA39C93C42AB92CA8FD5F3EA50812D2975ED144B184FC8AB0693598EFF75DCC0823219B` |
| expected result | valid |

1. Hash the raw message with SHA-384 (external to the register interface):
   `E8DC953DE7148A201F8A15F6316F416F8D69B99CEA4F5C6FF970341189FCC6D7311022A1291D3B0E9C96B34A1B569843`.
2. Wait `STATUS.READY`.
3. Write `MSG_0..11` (the digest computed in step 1):

   | Word | Value | Word | Value |
   |---|---|---|---|
   | 0 | `0xE8DC953D` | 6 | `0xF9703411` |
   | 1 | `0xE7148A20` | 7 | `0x89FCC6D7` |
   | 2 | `0x1F8A15F6` | 8 | `0x311022A1` |
   | 3 | `0x316F416F` | 9 | `0x291D3B0E` |
   | 4 | `0x8D69B99C` | 10 | `0x9C96B34A` |
   | 5 | `0xEA4F5C6F` | 11 | `0x1B569843` |

4. Write `PUBKEY_X_0..11` and `PUBKEY_Y_0..11`:

   | Word | `PUBKEY_X` | `PUBKEY_Y` |
   |---|---|---|
   | 0 | `0xD5B077F1` | `0xE9EF1992` |
   | 1 | `0xAD3E4508` | `0x57A0567E` |
   | 2 | `0xF64066AC` | `0xF43CE04A` |
   | 3 | `0x690E038E` | `0x1E0E9311` |
   | 4 | `0x6699D88D` | `0xDAEF77E1` |
   | 5 | `0x332ED21D` | `0x615C076C` |
   | 6 | `0x885F264E` | `0xF7C8607C` |
   | 7 | `0x75C57F0B` | `0xF3CF6A8E` |
   | 8 | `0xE0D20405` | `0xE4C20887` |
   | 9 | `0xD89CF26D` | `0xCE0C1AAD` |
   | 10 | `0xFE046C49` | `0x920840F5` |
   | 11 | `0x5817B37C` | `0xC602AB5A` |

5. Write `SIGN_R_0..11` and `SIGN_S_0..11`:

   | Word | `SIGN_R` | `SIGN_S` |
   |---|---|---|
   | 0 | `0xE2E197A2` | `0x3D7C92FD` |
   | 1 | `0x2B9BBE62` | `0x8714BB05` |
   | 2 | `0xD40CF98A` | `0x478EB616` |
   | 3 | `0x4023378B` | `0x6DA39C93` |
   | 4 | `0xF5FF3DDD` | `0xC42AB92C` |
   | 5 | `0xA5C4E959` | `0xA8FD5F3E` |
   | 6 | `0x03227B89` | `0xA50812D2` |
   | 7 | `0x2F17C7F9` | `0x975ED144` |
   | 8 | `0xBEC2A8D7` | `0xB184FC8A` |
   | 9 | `0xA3FA9773` | `0xB0693598` |
   | 10 | `0xC6575AFA` | `0xEFF75DCC` |
   | 11 | `0xA7821BF6` | `0x0823219B` |

6. Write `CTRL`=`11` (VERIFYING). Wait `STATUS.VALID`.
7. Read `VERIFY_R_0..11` — expected to equal `SIGN_R_0..11` exactly (valid signature).
8. Write `CTRL.ZEROIZE=1`.

Verified independently with the same from-scratch ECDSA verifier: valid for this vector
(and, as a sanity check on the verifier itself, also confirmed **invalid** for a
different test case in the same vector set whose `r` is all-zero — an intentionally
malformed signature that a correct implementation must reject).

`STATUS.VALID` only means "computation complete" — it is not a pass/fail bit. Signature
validity is determined by comparing the computed `VERIFY_R` against the originally
supplied `SIGN_R`: equal ⇒ valid.

An invalid-signature case exercises the identical sequence above: change any bit of
`SIGN_R`, `SIGN_S`, `PUBKEY_X`, `PUBKEY_Y`, or the hashed message before writing it, and
the computed `VERIFY_R` will no longer match the supplied `SIGN_R`.

---

## 11. ML-DSA-87 — KeyGen / SigGen / SigVer

This section illustrates one way to implement ML-DSA-87 KeyGen/SigGen/SigVer as a thin
software layer over a register interface, rather than as raw register pokes at the call
site (contrast with §4-§10, which describe direct register sequences). As noted in §1, no
independently-read register-definition file was available for this hardware block, so the
register names and control opcodes below should be treated as illustrative rather than
independently RTL-verified. ML-DSA-87 shares its register block ("Adams Bridge") with
ML-KEM-1024 (§12) — they are two different peripherals on the same silicon block, with
entirely separate `mldsa_*`/`mlkem_*` register fields.

### 11.1 Register map

| Register | Purpose |
|---|---|
| `mldsa_ctrl` | opcode + control bits: `ctrl[2:0]` (`KEYGEN=1, SIGN=2, VERIFY=3, KEYGEN_SIGN=4`), `external_mu` (bool), `stream_msg` (bool, for variable-length message streaming — not needed for ACVP, see note below), `pcr_sign` (bool, for a PCR-signing flow outside ACVP's scope — not used in any sequence below), `zeroize` (bool) |
| `mldsa_status` | `ready`, `valid`, `msg_stream_ready` |
| `mldsa_seed` | 8 words (256 bits) — KeyGen/SigGen seed input |
| `mldsa_privkey_in` | 1224 words (4896 bytes) — supplied private key, used for SigGen when signing with a known key instead of a seed |
| `mldsa_privkey_out` | 1224 words — KeyGen's generated private key (optional readback) |
| `mldsa_pubkey` | 648 words (2592 bytes) — KeyGen output / SigVer input |
| `mldsa_msg` | 16 words (64 bytes, fixed-size) — message input for SigGen/SigVer |
| `mldsa_external_mu` | 16 words (64 bytes) — pre-computed FIPS 204 `mu` digest, used instead of `mldsa_msg` when `external_mu=1` |
| `mldsa_sign_rnd` | 8 words (32 bytes) — the FIPS 204 Algorithm 7 `rnd` input; all-zero = deterministic signing, ACVP-supplied value = hedged/randomized signing |
| `entropy` | TRNG-generated randomness, written before every KeyGen or Sign operation for side-channel-masking (not an ACVP protocol input); not written before Verify, which has no secret to protect |
| `mldsa_signature` | 1157 words — 4628-byte buffer; the real signature is 4627 bytes, the trailing word is zero-padded |
| `mldsa_verify_res` | 16 words — SigVer's computed result, compared in software against the first 16 words of the supplied signature |
| `kv_mldsa_seed_rd_ctrl`/`_status` | Key-Vault-mediated seed routing (used when the seed comes from KV instead of a plain array) |

**ACVP's registered message length (§2.9: max 512 bits = 64 bytes) fits entirely inside
the fixed-size `mldsa_msg`/`mldsa_external_mu` registers** — a variable-length streaming
path (word-by-word writes to `mldsa_msg` via a strobe bit, for messages too large for the
fixed-size register) is a reasonable feature for this hardware to expose, but isn't
needed for ACVP testing at this message-length domain, so it's out of scope here.

### 11.2 KeyGen

1. Wait `mldsa_status.ready`.
2. Write `mldsa_seed` (8 words).
3. Write `entropy` (TRNG-generated).
4. Write `mldsa_ctrl` = `{ctrl=KEYGEN}`.
5. Wait `mldsa_status.valid`.
6. Read `mldsa_pubkey` (648 words); optionally read `mldsa_privkey_out` (1224 words).
7. Write `mldsa_ctrl.zeroize=1`.

A KeyGen entry point can reasonably do one more thing after step 7 that's worth knowing
about even though it isn't an ACVP protocol step: automatically sign an all-zero message
with the just-generated key and verify that signature internally, returning an error
instead of the public key if that self-check fails (a pairwise consistency test, not
something the ACVP flow needs to replicate).

Because ML-DSA-87's public/private keys are large (2592 / 4896 bytes), a full worked
example isn't reproduced word-for-word here the way the smaller AES/SHA/HMAC examples
are — see §11.3's worked example instead, which exercises the same hardware path
(`SIGN`/`KEYGEN_SIGN`) with a complete example of a still-large but more tractable size.

### 11.3 SigGen (deterministic and hedged, plus the "external mu" variant)

1. Wait `mldsa_status.ready`.
2. Write the private key: `mldsa_privkey_in` (1224 words) if signing with a caller-supplied
   private key, or `mldsa_seed` if generating a fresh key pair as part of this same
   operation (`ctrl=KEYGEN_SIGN` instead of `SIGN` in step 5).
3. Write the message: `mldsa_msg` (plain message) **or** `mldsa_external_mu` (pre-computed
   `mu` digest) — never both.
4. Write `mldsa_sign_rnd`: all-zero for **deterministic** signing (what every worked
   example in this document uses), or an ACVP-supplied 32-byte value for **hedged**
   (randomized) signing.
5. Write `entropy` (TRNG-generated).
6. Write `mldsa_ctrl` = `{ctrl=SIGN or KEYGEN_SIGN, external_mu=<1 if step 3 used
   mldsa_external_mu>}`.
7. Wait `mldsa_status.valid`.
8. Read `mldsa_signature` (1157 words; last word is padding).
9. Write `mldsa_ctrl.zeroize=1`.

A SigGen entry point can reasonably re-verify every signature it produces (an internal
call to the same SigVer path in §11.4) before returning it, returning an error instead of
the signature if that self-check fails — a useful glitch/fault-injection defense in
general. ACVP SigGen vectors are sometimes intentionally invalid, though, so a harness
driving this hardware for ACVP needs a way to report the raw hardware output without that
self-check rejecting it first — i.e. a "sign but skip the self-verify" entry point
alongside the normal one.

**Worked example — deterministic SigGen with external mu** (illustrative values at
realistic ML-DSA-87 scale)

| Field | Value |
|---|---|
| `external_mu` (64 bytes — small enough to show in full) | `B007F182 605A1141 93369BFC 9A6B8A50 457ED4D8 52E7291B 1161E463 B2D04CA3 02EFE87E 5DA85BC9 C03E9B9E 4F522D92 F81643A5 71FD0F9F EA0CD0F3 3BFCF86F` (16 words) |
| `sk` (private key, 4896 bytes) | starts `C8243989 EFB40AAA 735FC646 5276EAF9 E73DD5A9 D7374096 13F3D535 27BF23E3 ...`, ends `... A3288F79 E30EB5E0 FA6AACE1 B01067BF F5DEC1BF 708E203A` (1224 words total — too large to reproduce in full) |
| `pk` (public key, 2592 bytes) | starts `C8243989 EFB40AAA 735FC646 5276EAF9 ...` (shares its first 8 words with `sk`, since `sk` embeds the public key), ends `... 43AFC8B5 F6A75F72 F8D50B9B 3ECBD8CD` (648 words total) |
| `sign_rnd` | all-zero (deterministic) |
| expected `signature` | starts `D1476E71 E540E209 6F507B9C 085CA49F BF9E8671 14C85D6C 62E11E2D 7C9E1104 ...`, ends `... 00000000 01000000 1E160E08 00302A22` (1157 words total; the real signature is 4627 bytes, so the trailing word `0x00302A22` includes the padding byte) |

1. Wait `mldsa_status.ready`.
2. Write `mldsa_privkey_in` = the 1224-word `sk` above.
3. Write `mldsa_external_mu` = the 16-word `external_mu` above (this is the `external_mu`
   path, not `mldsa_msg`).
4. Write `mldsa_sign_rnd` = all-zero.
5. Write `entropy` (TRNG-generated; doesn't affect the deterministic result).
6. Write `mldsa_ctrl` = `{ctrl=SIGN, external_mu=1}`.
7. Wait `mldsa_status.valid`.
8. Read `mldsa_signature` — matches the expected `signature` above exactly. Note that
   this example's expected values are internally self-consistent (given these inputs,
   this is the corresponding output) rather than independently recomputed from scratch
   the way the AES/SHA/HMAC/ECDSA examples earlier in this document are — ML-DSA-87's
   underlying lattice math is a much heavier lift to reimplement independently for
   verification purposes.
9. Write `mldsa_ctrl.zeroize=1`.

### 11.4 SigVer (plus the "external mu" variant)

1. Wait `mldsa_status.ready`.
2. Write `mldsa_pubkey` (648 words).
3. Write `mldsa_signature` (1157 words).
4. Write the message: `mldsa_msg` **or** `mldsa_external_mu`.
5. Write `mldsa_ctrl` = `{ctrl=VERIFY, external_mu=<1 if step 4 used mldsa_external_mu>}`.
6. Wait `mldsa_status.valid`.
7. Read `mldsa_verify_res` (16 words).
8. Write `mldsa_ctrl.zeroize=1`.

Like ECDSA SigVer (§10.4), `mldsa_status.valid` only means "computation complete" — it is
not a pass/fail bit. Validity is determined in software by comparing `mldsa_verify_res`
against the **first 16 words only** of the signature written in step 3: equal ⇒ valid,
different ⇒ invalid.

A negative-test case can demonstrate the invalid path directly: write a signature/public-
key pair that's known-valid, but substitute a different (e.g. all-`0xFF`) message in step
4 — `mldsa_verify_res` then no longer matches the signature's first 16 words, so the
result comes back invalid instead of valid.

### 11.5 Test-type note

ML-DSA-87 testing uses **AFT only — there is no MCT** for ML-DSA, matching every other
digital-signature IP in this document.

---

## 12. ML-KEM-1024 — KeyGen / Encapsulate / Decapsulate

This section illustrates one way to implement ML-KEM-1024 KeyGen/Encapsulate/Decapsulate
as a thin software layer over a register interface, the same style as §11's ML-DSA-87
section (contrast with §4-§10, which describe direct register sequences). As noted in §1,
no independently-read register-definition file was available for this hardware block, so
the register names and control opcodes below should be treated as illustrative rather
than independently RTL-verified. ML-KEM-1024 shares its register block ("Adams Bridge")
with ML-DSA-87 (§11) — they are two different peripherals on the same silicon block, with
entirely separate `mlkem_*`/`mldsa_*` register fields.

### 12.1 Register map

| Register | Purpose |
|---|---|
| `mlkem_ctrl` | opcode + control bits: `ctrl[2:0]` (`KEYGEN=1, ENCAPS=2, DECAPS=3, KEYGEN_DECAPS=4`), `zeroize` (bool) |
| `mlkem_status` | `ready`, `valid` |
| `mlkem_seed_d`, `mlkem_seed_z` | 8 words (256 bits) each — KeyGen's two FIPS 203 seed inputs |
| `mlkem_encaps_key` | 392 words (1568 bytes) — KeyGen output / Encapsulate input |
| `mlkem_decaps_key` | 792 words (3168 bytes) — KeyGen output / Decapsulate input |
| `mlkem_msg` | 8 words (32 bytes) — Encapsulate's message input |
| `mlkem_ciphertext` | 392 words (1568 bytes) — Encapsulate output / Decapsulate input |
| `mlkem_shared_key` | 8 words (32 bytes) — Encapsulate/Decapsulate output |
| `kv_mlkem_seed_rd_ctrl`/`_status`, `kv_mlkem_msg_rd_ctrl`/`_status`, `kv_mlkem_sharedkey_wr_ctrl`/`_status` | Key-Vault-mediated routing for seeds, message, and shared-key output, used as an alternative to plain array I/O |

Unlike ML-DSA-87 (§11), none of these operations need to write an `entropy` register on a
per-operation basis. That register is shared with ML-DSA-87 on the same silicon block,
though, so it still needs to be seeded once with TRNG output before the first ML-KEM (or
ML-DSA) operation of any kind runs — a one-time setup requirement, not a per-operation
write, similar in spirit to AES's one-time entropy seeding in §4.1. It's also reasonable
to zeroize the hardware **both before and after** each operation (`wait ready → zeroize →
wait ready` at the start of every call, then `zeroize` again after reading results),
rather than only after, as §11 does for ML-DSA-87.

### 12.2 KeyGen

1. Wait `mlkem_status.ready`, write `mlkem_ctrl.zeroize=1`, wait `mlkem_status.ready`
   again (defensive pre-clear, done at the start of every ML-KEM operation).
2. Write `mlkem_seed_d` and `mlkem_seed_z` (8 words each).
3. Write `mlkem_ctrl` = `{ctrl=KEYGEN}`.
4. Wait `mlkem_status.valid`.
5. Read `mlkem_encaps_key` (392 words) and `mlkem_decaps_key` (792 words).
6. Write `mlkem_ctrl.zeroize=1`.

A KeyGen entry point can reasonably run an automatic pairwise-consistency check after
step 6 (encapsulate a zero message with the new key, decapsulate it back, and confirm the
shared secrets match) before returning — not an ACVP protocol step, but worth knowing
about since it means every successful KeyGen call would have already exercised
Encapsulate and Decapsulate once internally.

**Worked example — KeyGen** (`seed_d`/`seed_z` are directed, illustrative inputs rather
than real ACVP vector data; the resulting keys are internally self-consistent given these
inputs)

| Field | Value |
|---|---|
| `seed_d` | `12345678 9ABCDEF0 11223344 55667788 AABBCCDD EEFF0011 22334455 66778899` |
| `seed_z` | `87654321 0FEDCBA9 44332211 88776655 DDCCBBAA 1100FFEE 55443322 99887766` |
| expected `encaps_key` (1568 bytes) | starts `4814898E B15B7012 40445527 89BEF849 675B39A1 A9521326 ...`, ends `... 5A02A685 637B46B1 17002FE1 C65AB9F6` (392 words total) |
| expected `decaps_key` (3168 bytes) | starts `0DAC07E1 16073C76 71EBA683 FB57DB5F D5D590F6 7F536C03 ...`, ends `... 87654321 0FEDCBA9 44332211 88776655 DDCCBBAA 1100FFEE 55443322 99887766` (792 words total — note the **last 8 words are `seed_z` itself**, a structural feature of the FIPS 203 decapsulation-key format worth cross-checking independently of trusting the full computation) |

1. Write `mlkem_seed_d` = the 8-word `seed_d` above; `mlkem_seed_z` = the 8-word `seed_z`
   above.
2. Write `mlkem_ctrl` = `{ctrl=KEYGEN}`.
3. Wait `mlkem_status.valid`.
4. Read `mlkem_encaps_key` and `mlkem_decaps_key` — match the expected values above
   exactly. As with §11's worked example, these values are internally self-consistent
   rather than independently recomputed from scratch — reimplementing ML-KEM's lattice
   math independently for verification purposes is a much heavier lift than AES/SHA/HMAC/
   ECDSA.
5. Write `mlkem_ctrl.zeroize=1`.

### 12.3 Encapsulate

1. Wait ready, zeroize, wait ready (defensive pre-clear).
2. Write `mlkem_encaps_key` (392 words).
3. Write `mlkem_msg` (8 words).
4. Write `mlkem_ctrl` = `{ctrl=ENCAPS}`.
5. Wait `mlkem_status.valid`.
6. Read `mlkem_shared_key` (8 words) and `mlkem_ciphertext` (392 words).
7. Write `mlkem_ctrl.zeroize=1`.

### 12.4 Decapsulate

1. Wait ready, zeroize, wait ready (defensive pre-clear).
2. Write `mlkem_decaps_key` (792 words) and `mlkem_ciphertext` (392 words).
3. Write `mlkem_ctrl` = `{ctrl=DECAPS}`.
4. Wait `mlkem_status.valid`.
5. Read `mlkem_shared_key` (8 words).
6. Write `mlkem_ctrl.zeroize=1`.

**Worked example — Encapsulate then Decapsulate** (continuing from §12.2's `encaps_key`/
`decaps_key`, with `message = DEADBEEF CAFEBABE 12345678 9ABCDEF0 11223344 55667788
AABBCCDD EEFF0011`)

Unlike §12.2's KeyGen step, there's no separately-known reference ciphertext or shared
secret to check this against — instead, the correctness check is that **encapsulating
then decapsulating round-trips to the same shared key**, which is what this worked
example demonstrates in place of an external reference value:

1. Write `mlkem_encaps_key` = §12.2's `encaps_key`.
2. Write `mlkem_msg` = `DEADBEEF CAFEBABE 12345678 9ABCDEF0 11223344 55667788 AABBCCDD EEFF0011`.
3. Write `mlkem_ctrl` = `{ctrl=ENCAPS}`.
4. Wait `mlkem_status.valid`.
5. Read `mlkem_shared_key` → call this `shared_key_enc`; read `mlkem_ciphertext`.
6. Write `mlkem_ctrl.zeroize=1`.
7. Write `mlkem_decaps_key` = §12.2's `decaps_key`; write `mlkem_ciphertext` = the
   ciphertext just produced in step 5.
8. Write `mlkem_ctrl` = `{ctrl=DECAPS}`.
9. Wait `mlkem_status.valid`.
10. Read `mlkem_shared_key` → call this `shared_key_dec`.
11. Write `mlkem_ctrl.zeroize=1`.
12. `shared_key_enc` and `shared_key_dec` come out equal.

### 12.5 Test-type note

An AFT-style harness for this hardware can reasonably process one vector at a time
(tagged `MLKEM_KEYGEN`/`MLKEM_ENCAPS`/`MLKEM_DECAPS`), run the corresponding operation
once, and report the result — the same single-vector-per-invocation shape as §11.5's
ML-DSA-87 note. There's no need for an MCT or Variable-Output-Test-style construct for
ML-KEM-1024. The registered capability (§2.10) covers `encapsulation`/`decapsulation`
only — not `encapsulationKeyCheck`/`decapsulationKeyCheck` — so an implicit-rejection/
tampered-ciphertext test path isn't required either.

---

## 13. LMS — SigVer

**This section is shaped differently from every other section in this document: there is
no dedicated LMS hardware register block at all.** LMS can reasonably be implemented as a
pure-software verification routine (RFC 8554 / NIST SP 800-208) built entirely on top of
the SHA2-224/256 register interface already documented in §5 — the Winternitz
one-time-signature chain and Merkle-tree path are walked in software, driving §5's
register sequence a data-dependent number of times per verification. There is no single
fixed register sequence to give here the way §4-§12 do; "driving the DUT" for LMS means
calling a verification routine with the right byte layout, which in turn drives §5's
register interface internally, as many times as the tree height and chain length require.

Such an implementation would reasonably provide **verification only** — no KeyGen, no
signing — which matches ACVP's LMS scope exactly: LMS private keys are stateful (each
one-time key can only be used once), so an ACVP lab verifies signatures against a
supplied public key rather than generating keys itself.

### 13.1 Parameters actually used

Caliptra's registered ACVP capability (§2.8) is a single mode pair:
`LMS_SHA256_M24_H15` / `LMOTS_SHA256_N24_W4` — a 24-byte (SHA-256/192-truncated) hash
width, a height-15 Merkle tree, and Winternitz parameter `w=4`. A verification routine
can reasonably provide a fixed, non-generic entry point hardcoded to exactly these
parameters (24-byte digests, 51 OTS chains, height-15 tree) for the common case, with a
more general parameterized version available for other combinations (e.g. a 32-byte/
full-SHA-256 variant, kept available in case it's wanted in the future, but not part of
the registered capability above).

### 13.2 Wire format and call sequence

Message, public key, and signature can be represented as plain byte buffers, matching the
RFC 8554 wire format directly (big-endian type-code fields, little-endian word-packed
hash/nonce/path data). A public key at Caliptra's parameters is naturally laid out as:

| Field | Size | Contents |
|---|---|---|
| `tree_type` | 4 bytes | LMS algorithm-type code (e.g. the code for the 24-byte/height-15 variant) |
| `otstype` | 4 bytes | LM-OTS algorithm-type code (e.g. the code for the 24-byte/`w=4` variant) |
| `id` | 16 bytes | LMS identifier |
| `digest` | 24 bytes (6 words) | public key hash value |

and a signature at the same parameters is:

| Field | Size | Contents |
|---|---|---|
| `q` | 4 bytes | leaf index, big-endian |
| `ots` signature | OTS type (4 bytes) + nonce (24 bytes) + 51×24-byte hash-chain values | LM-OTS one-time signature |
| `tree_type` | 4 bytes | LMS algorithm-type code |
| `tree_path` | 15×24 bytes | Merkle-tree sibling hashes, one per level |

A verification entry point built around this layout takes a message, a public key, and a
signature, and returns either "success" or "signature verification failed" — a genuine
three-way outcome, not a plain boolean, since some malformed inputs (an OTS-type mismatch
between the public key and signature, a height/tree-type mismatch, or an out-of-range leaf
index) are cheap to reject immediately as a distinct error, without doing any hashing at
all. Not every structural problem is caught this early, though — see §13.4 for the full,
more nuanced picture of what's rejected upfront versus what's only caught partway through
a verification attempt.

### 13.3 Worked example

Given the size of a full LMS signature (one 24-byte nonce, 51 24-byte OTS chain values,
and a 15-level, 24-byte-per-level Merkle path — several kilobytes total), a complete
worked example isn't reproduced word-for-word the way the smaller AES/SHA/HMAC examples
are. Instead, here is the first, self-contained step of LMS verification — computing the
message digest that everything else is built from — an RFC 8554 §3.1.3-style example:

| Field | Value |
|---|---|
| `message` | `"this is the message I want signed"` (33 bytes) |
| `lms_identifier` (16 bytes) | `6628E95A7EA6A1496B39721C79391C7B` |
| `nonce` (24 bytes) | `6CC9A95D82CED6ADDF8AB296C056738B9DD5B637C416D4D8` |
| `q` (leaf index) | `0` |
| expected intermediate hash (24 bytes) | `AFA009471D1A3D145AD98E9870443311 9ABF4A96A1EE66A1` |

1. Compute SHA-256 over `lms_identifier || q || D_MESG || nonce || message`, where
   `D_MESG` is a fixed 2-byte, big-endian domain-separation value (`0x8181`) — internally
   this drives §5's SHA-256 register sequence once (write `BLOCK`, `CTRL.INIT=1`, wait,
   read `DIGEST`).
2. Keep only the first 6 of the 8 `DIGEST` words (24 of the full 32-byte SHA-256 output) —
   the same truncate-to-N-words convention as the digest fields throughout this section.
   The result matches the expected intermediate hash above exactly (independently
   recomputed and confirmed in Python before being written here).

Full signature verification repeats a similar SHA-256-driving pattern 51 more times for
the OTS hash chains and 15 more times for the Merkle-tree path, each call driven by data
computed from the previous one — this is the "data-dependent number of times" mentioned
in this section's introduction. A complete worked signature (message + 16-byte identifier
+ 24-byte nonce + 51 OTS chain values + 15-level tree path + public key digest, verified
to produce a "success" result) follows the same shape but is too large to reproduce in
full here.

### 13.4 Negative cases

A good negative-test set builds one valid signature/public-key pair, then perturbs one
field at a time — worth capturing explicitly as a fairly thorough list of the ways LMS
verification can and should fail. Note that "rejected before hashing" only applies to a
few of these — several structural checks actually run *after* one SHA-256 hash has
already been computed (see the note below the table):

| Perturbation | Outcome |
|---|---|
| Different message, same signature | verification fails (full verification runs, candidate root doesn't match) |
| Zeroed LMS identifier in the public key | verification fails |
| Leaf index `q` off by one (`Q+1`) | verification fails |
| Zeroed public-key digest | verification fails |
| Zeroed Merkle tree path | verification fails |
| Unknown LMS algorithm-type code | rejected as invalid input, before any hashing |
| Signature's OTS type doesn't match the public key's declared OTS type | rejected as invalid input, before any hashing — this is the very first check performed |
| Public key declares a different tree height than the signature | rejected as invalid input, before any hashing (the check compares the *signature's* declared height against a fixed expected value, not against a separate field on the public key) |
| Unknown LM-OTS algorithm-type code | rejected as invalid input, but only after one SHA-256 hash has already been computed |
| Pubkey/signature switched to a different-N OTS type whose one-time-signature chain count no longer matches what's expected | rejected as invalid input (a chain-count mismatch), but only after one SHA-256 hash has already been computed |
| A general (parameterized) verification call given a hash width that doesn't match the actual chain-value size | rejected as invalid input, but only after one SHA-256 hash has already been computed |

Two more boundary checks on the leaf index `q`, from a separate worked-signature test
(not the same one-field-at-a-time test as the rows above):

| Perturbation | Outcome |
|---|---|
| `q` at the maximum valid leaf index for `h=15` (`q=32767=2^15-1`), otherwise-valid signature | verification fails (structurally valid but wrong leaf) |
| `q` one past the maximum (`q=32768=2^15`) | rejected as invalid input, before verification |

The overall pattern is a spectrum rather than a clean two-way split: the cheapest
structural checks (OTS-type match between public key and signature, tree-height match,
leaf-index range) can be — and should be — rejected immediately, before any hashing.
Other structural problems (an unrecognized LM-OTS type, or a chain-count/hash-width
mismatch) are naturally discovered partway through, only once the code responsible for
walking the OTS chain actually looks at the mismatched sizes — there's no requirement to
front-load every possible structural check before starting. A **structurally valid but
wrong** signature (tampered message, identifier, digest, path, or leaf index), by
contrast, always runs the full verification and comes back as a plain "verification
failed" rather than a distinct error — the same valid-vs-invalid split as ECDSA SigVer's
`STATUS.VALID`-vs-comparison pattern in §10.4, just expressed in software instead of a
hardware status bit.

### 13.5 Test-type note

SigVer only, no KeyGen/SigGen — matches §2.8's registered capability and the general ACVP
convention for stateful hash-based signatures.
