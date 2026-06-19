// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
// Description:
//   Shared library for ICCM hash measurement tests. Provides helpers for
//   acquiring the SHA accelerator, driving the ICCM hash flow, running the
//   regular sha512_ctrl pcr_hash_extend, and checking PCR contents.

#ifndef ICCM_HASH_H
#define ICCM_HASH_H

#include "caliptra_defines.h"
#include "caliptra_reg.h"
#include "riscv_hw_if.h"
#include <stdint.h>

// ICCM_MODE field (bit 2 of MODE register) -- fallback if caliptra_reg.h
// pre-dates the ICCM hash feature
#ifndef SHA512_ACC_CSR_MODE_ICCM_MODE_MASK
#define SHA512_ACC_CSR_MODE_ICCM_MODE_MASK (0x4)
#endif

// Number of dwords in a single PCR entry (384-bit / 32-bit)
#define ICCM_HASH_PCR_DWORDS 12

// Default ICCM data pattern used by run_default_iccm_hash:
// 64 words {0x10..0x4F} -- matches directed_test_iccm_hash sequence 1
#define ICCM_HASH_DEFAULT_NUM_WORDS 64
#define ICCM_HASH_DEFAULT_WORD(i)   (0x10 + (i))

// Expected PCR4/PCR5 value after run_default_iccm_hash extends from zero:
//   PCR_n = SHA-384(48_zeros || SHA-384(LE bytes of {0x10..0x4F}))
extern const uint32_t expected_default_iccm_hash_pcr[ICCM_HASH_PCR_DWORDS];

// ---- SHA accelerator + ICCM hash flow ----

// Acquire SHA acc lock: release reset-default lock, then read-to-acquire.
// Returns 1 on success, 0 on timeout.
uint8_t acquire_sha_lock(void);

// Wait for PCR4 to be written by the extend FSM (poll dword[0] non-zero).
// Returns 1 on success, 0 on timeout.
uint8_t wait_pcr4_ready(void);

// Run an ICCM hash with the default 64-word pattern. Acquires lock, sets
// ICCM_MODE, writes data to ICCM, asserts iccm_lock, waits for PCR4.
// Returns 1 on success, 0 on timeout.
uint8_t run_default_iccm_hash(void);

// ---- Regular sha512_ctrl pcr_hash_extend driver ----

// Drive the regular SHA512 controller to extend the given PCR with the
// supplied 12-dword digest. Reads PCR_n into BLOCK[0:11], writes digest
// into BLOCK[12:23], pads to a 128-byte block, and pulses init+last.
// Returns 1 on success, 0 on timeout.
uint8_t sha_ctrl_extend(uint32_t pcr_entry, const uint32_t *digest);

// ---- FW attack helpers ----

// Attempt 12 FW AHB writes of 0xDEADBEEF into the given PCR entry's dwords
void fw_write_attack(uint32_t pcr_base);

// ---- PCR readers / checkers ----

// Snapshot all 12 dwords of a PCR into out[12]
void snapshot_pcr(uint32_t pcr_base, uint32_t *out);

// Verify all 12 dwords of a PCR are zero. Returns 1 on pass, 0 on fail.
uint8_t check_pcr_zero(uint32_t pcr_base, uint32_t pcr_idx);

// Verify any dword of a PCR is non-zero. Returns 1 on pass, 0 on fail.
uint8_t check_pcr_nonzero(uint32_t pcr_base, uint32_t pcr_idx);

// Verify all 12 dwords of a PCR equal the expected array. Returns 1 on
// pass, 0 on fail. iter and pcr_idx are used in error prints.
uint8_t check_pcr_match(uint32_t pcr_base, const uint32_t *expected,
                             uint32_t pcr_idx, uint32_t iter);

#endif // ICCM_HASH_H
