# Non-Deterministic ECDSA Test Vectors

This directory holds KAT vectors for the non-deterministic ECDSA SIGN
path (`ECC_CTRL.RAND_K_EN=1`). See
`plans/non-deterministic-ecdsa.md` for the full spec.

## Files

- `secp256_nondet_testvector.hex`    – 1 P-256 TC (latest run)
- `secp256_nondet_testvector_all.hex` – accumulated P-256 TCs
- `secp384_nondet_testvector.hex`    – 1 P-384 TC (latest run)
- `secp384_nondet_testvector_all.hex` – accumulated P-384 TCs

Each TC is the standard 12-line format consumed by
`ecc_top_tb.read_test_vectors`:

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
