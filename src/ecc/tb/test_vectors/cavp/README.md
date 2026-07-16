# NIST CAVP Vectors (vendored subset)

This directory holds filtered subsets of NIST Cryptographic Algorithm
Validation Program (CAVP) test vectors. Files are public domain (US-Gov)
and pinned by SHA-256 of the upstream archives in `cavp_filter.py`.

## Layout

```
cavp/
├── README.md                                # this file
├── cavp_filter.py                           # downloader/filter (re-run to refresh)
├── cavp_ecdsa_to_kat.py                     # ECDSA SigGen .rsp -> 12-line .hex
├── ecdsa/
│   ├── SigGen_P256_SHA256.rsp               # 15 TCs from SigGen.txt
│   ├── SigGen_P384_SHA384.rsp               # 15 TCs from SigGen.txt
│   ├── cavp_p256_sha256.hex                 # 12-line KAT for ECC_cavp_sign_p256_test
│   └── cavp_p384_sha384.hex                 # 12-line KAT for ECC_cavp_sign_p384_test
└── drbg/
    ├── HMAC_DRBG_SHA256_no_reseed.rsp       # 60 TCs (no PR/perso/addin)
    └── HMAC_DRBG_SHA384_no_reseed.rsp       # 60 TCs (no PR/perso/addin)
```

## Upstream sources

| Archive | URL | SHA-256 |
|---------|-----|---------|
| 186-4ecdsatestvectors.zip | https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/dss/186-4ecdsatestvectors.zip | `fe47cc92...72824752` |
| drbgtestvectors.zip | https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/drbg/drbgtestvectors.zip | `5f7e5658...699377769` |

## Usage

**Refresh the vendored subsets** (after a NIST update):
```
cd src/ecc/tb/test_vectors/cavp
curl -O <ecdsa_url> -O <drbg_url>
python3 cavp_filter.py 186-4ecdsatestvectors.zip drbgtestvectors.zip
python3 cavp_ecdsa_to_kat.py ecdsa/SigGen_P256_SHA256.rsp ecdsa/cavp_p256_sha256.hex
python3 cavp_ecdsa_to_kat.py ecdsa/SigGen_P384_SHA384.rsp ecdsa/cavp_p384_sha384.hex
```

**Cross-check the DRBG model against CAVP** (todo #16):
```
python3 src/ecc/tb/k_drbg_match_nondet.py --cavp-drbg \
    src/ecc/tb/test_vectors/cavp/drbg/HMAC_DRBG_SHA256_no_reseed.rsp
python3 src/ecc/tb/k_drbg_match_nondet.py --cavp-drbg \
    src/ecc/tb/test_vectors/cavp/drbg/HMAC_DRBG_SHA384_no_reseed.rsp
```

**Run the CAVP ECDSA RTL KATs** (todo #18):
```
pb fe sim ecc ecc_cavp_sign_p384_test
pb fe sim ecc ecc_cavp_sign_p256_test
```

## How the ECDSA RTL KAT works

CAVP SigGen records carry the test `k` and the expected `(R, S)`.
The TB tasks `ecc_cavp_sign_p{256,384}_test` run the *deterministic*
ECDSA SIGN micro-program (NONDETERMINISTIC=0) but force-inject the CAVP `k`
on the HMAC-DRBG output net (`hmac_drbg_result_p{256,384}`) and zero
the blinding entropy (lambda=1, scalar_rnd=masking_rnd=0). With those
nets pinned, `(R, S)` becomes a deterministic function of
`(k, d, SHA(Msg))` and must bit-exactly match the CAVP-published
`(R, S)`. This is the closest end-to-end RTL-level evidence of NIST
ECDSA SigGen compliance achievable without instantiating a NIST-AVP
harness around the engine.
