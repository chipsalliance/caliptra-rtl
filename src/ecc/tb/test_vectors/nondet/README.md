# Non-Deterministic ECDSA Test Vectors

This directory holds KAT vectors for the non-deterministic ECDSA SIGN
path (`ECC_CTRL.NONDETERMINISTIC=1`). See
`plans/non-deterministic-ecdsa.md` for the full spec.

## Files

- `secp256_nondet_testvector.hex`    – raw output from mbedtls `-DNON_DET` P-256 tool (latest single TC)
- `secp256_nondet_testvector_all.hex` – raw accumulated P-256 TCs from repeated tool runs
- `secp256_nondet_kat.hex`           – 50-TC P-256 KAT, TB-consumable (produced by `gen_nondet_kat.py` from the raw `_all.hex` file, with `privkeyB` slot overwritten by the DRBG-derived `k`)
- `secp384_nondet_testvector.hex`    – raw output from mbedtls `-DNON_DET` P-384 tool (latest single TC)
- `secp384_nondet_testvector_all.hex` – raw accumulated P-384 TCs
- `secp384_nondet_kat.hex`           – 50-TC P-384 KAT, TB-consumable (pass-through from raw, with TC-counter separator)
- `gen_nondet_kat.py`                – helper script: converts raw `_testvector*.hex` files into TB-consumable `_kat.hex`

The raw `_testvector*.hex` files are **helper-script inputs only** — they use a
blank-line TC separator that hard-fails `ecc_top_tb::read_test_vectors` (12-field
`$fscanf`). Only the `_kat.hex` files are safe to hand to the TB directly.

Each **`_kat.hex`** TC is the 12-line format consumed by
`ecc_top_tb::read_test_vectors`:

| line | field         | role in non-det SIGN                                 |
|-----:|---------------|------------------------------------------------------|
|   0  | hashed_msg    | write to `ECC_MSG_*`                                 |
|   1  | privkey       | write to `ECC_PRIVKEY_IN_*`                          |
|   2  | pubkey.x      | (verify only)                                        |
|   3  | pubkey.y      | (verify only)                                        |
|   4  | seed          | **write to `ECC_SEED_*`**  (DRBG entropy)            |
|   5  | nonce         | **write to `ECC_NONCE_*`** (DRBG nonce)              |
|   6  | R             | expected sign output                                 |
|   7  | S             | expected sign output                                 |
|   8  | IV            | unused for non-det SIGN                              |
|   9  | privkeyB      | **P-256: k = HMAC-DRBG-SHA256(seed,nonce)** (injected by `gen_nondet_kat.py`, consumed by `ecc_nondet_sign_p256_bypass_test` via SV-force on `hmac_drbg_result_p256` until the P-256 DRBG block is instantiated); **P-384: unused** |
|  10  | DH_sharedkey  | unused                                               |
|  11  | (pad)         | blank slot                                           |

DRBG seeding (Option B): `entropy = seed_buf, nonce = nonce_buf`.
`hashed_msg` is **not** mixed into the DRBG — FW must therefore
write a fresh `(seed, nonce)` pair for every signature, else `k`
will repeat and leak the private key.

Unused slots (`IV`, `DH_sharedkey`, `(pad)`) are emitted as all-zeros
by `gen_nondet_kat.py`; the TB reader still consumes them so the
12-line stride stays intact.

## Known limitation — P-256 bypass corpus degeneracy (`d == k`)

The current `secp256_nondet_kat.hex` corpus was generated without
rejecting TCs where the injected `k` equals the private key `d`.
When `d == k`, `s = k^-1 * (h + r*d) mod n` collapses to
`s = 1 + h*d^-1`, which happens to satisfy the SIGN check for the
bypass path independently of the DRBG. The current bypass test
(`ecc_nondet_sign_p256_bypass_test`) does not catch this degeneracy.

Corpus regeneration with `d != k` filtering is the correct long-term
fix but is out of scope for this PR (requires re-running the mbedtls
tool with a rejection loop and rebuilding the KAT). This section is
the disclosure fix; a follow-up PR is tracked to regenerate the
vectors.

## Regenerating the vectors

The vectors are produced by the patched mbedtls tools at
`src/ecc/tb/ecc_secp256r1.c` and `src/ecc/tb/ecc_secp384r1.c`.
Build them with `-DNON_DET` against a mbedtls 3.x tree:

```
# from a mbedtls source checkout
cp <caliptra-rtl>/src/ecc/tb/ecc_secp256r1.c programs/pkey/
cp <caliptra-rtl>/src/ecc/tb/ecc_secp384r1.c programs/pkey/
make CFLAGS='-DNON_DET -I include -I library' programs/pkey/ecc_secp256r1
make CFLAGS='-DNON_DET -I include -I library' programs/pkey/ecc_secp384r1

# each invocation appends one TC to *_all.hex and overwrites
# the single-TC *.hex; loop N times to grow the KAT:
for i in $(seq 1 50); do ./programs/pkey/ecc_secp256r1; done
for i in $(seq 1 50); do ./programs/pkey/ecc_secp384r1; done

# move outputs into the repo:
mv secp256_nondet_testvector*.hex \
   <caliptra-rtl>/src/ecc/tb/test_vectors/nondet/
mv secp384_nondet_testvector*.hex \
   <caliptra-rtl>/src/ecc/tb/test_vectors/nondet/
```

Without `-DNON_DET` the tools fall back to the original deterministic
(RFC-6979) flow and emit the existing `secp256_testvector*.hex` /
`secp384_testvector*.hex` files unchanged.

### Converting raw vectors into TB-consumable `_kat.hex`

After the raw `_testvector*.hex` files are regenerated above, run
`gen_nondet_kat.py` to produce the 12-line KATs the TB reads:

```
# from this directory
./gen_nondet_kat.py secp256_nondet_testvector_all.hex secp256_nondet_kat.hex
./gen_nondet_kat.py secp384_nondet_testvector_all.hex secp384_nondet_kat.hex
```

The script:
- Replaces the mbedtls blank-line TC separator with an explicit
  TC-counter line (so the TB's 12-field `$fscanf` doesn't hard-fail).
- For P-256: overwrites the `privkeyB` slot with `k =
  HMAC-DRBG-SHA256(entropy=seed, nonce=nonce)`, matching the
  bit-exact reference in `hmac_drbg.sv`.
- For P-384: passes `privkeyB` through unchanged.

**Do not** hand-edit `_kat.hex` files — regenerate from the raw
`_testvector*.hex` inputs.
