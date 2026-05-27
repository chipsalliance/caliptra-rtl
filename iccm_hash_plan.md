# ICCM Write Hash -> PCR Feature Plan

## Problem Statement
Add hardware-only measurement of all data written to ICCM by computing a SHA-384
hash of the write stream and storing the result in PCR4. This PCR must be exclusively
updated by the HW hash logic -- ROM/FMC/Runtime firmware must not be able to extend,
clear, or overwrite it.

## Security Goal
ROM's existing PCR0/PCR1 measurements prove the mailbox image was authentic.
The new HW ICCM hash (PCR4) proves what actually landed in ICCM -- closing the gap
between "image was verified" and "image was correctly copied." This is defense-in-depth
against copy corruption, glitch/fault injection, or ROM memcpy bugs.

## Design Decisions (Resolved)

| Decision | Choice | Rationale |
|----------|--------|-----------|
| Hash input | Raw write data only (no addresses) | Simpler, user preference |
| PCR count | One cumulative hash | User preference |
| Target PCR | PCR4 | First free index after FW-reserved PCR0-3 |
| Interception point | ICCM bank write exports (el2_mem_export) | Ground truth of what lands in ICCM |
| Start trigger | First ICCM write after reset | Fully autonomous, no FW involvement |
| End trigger | iccm_lock assertion | Natural end-of-copy signal from ROM |
| SHA engine | Reuse sha512_acc_top (add iccm_mode) | Saves ~30k gates vs dedicated sha512_core instance; sha512_acc already has streaming data path, block accumulation, padding, and finalization FSM |
| FW update handling | Reset hash on cptra_uc_rst_b / fw_update_rst_window, re-capture on next copy | Same reset model as boot_flow_monitor |

## ROM FW Loading Flow (context)

```
Mailbox SRAM (0x30040000)
  |
  +-> ROM: load_manifest()  -- parse ImageManifest from mailbox
  +-> ROM: verify_image()   -- SHA-384 via HW SHA accelerator (reads mailbox SRAM)
  |     verify_fmc():    sha384_acc_digest(fmc.offset, fmc.size) vs manifest digest
  |     verify_runtime(): sha384_acc_digest(rt.offset, rt.size) vs manifest digest
  +-> ROM: extend_pcrs()    -- extend PCR0/PCR1 with FMC TCI
  +-> ROM: load_image()     -- CPU memcpy from mailbox SRAM to ICCM  <-- HW hash captures here
  +-> ROM: lock_registers() -- writes CPTRA_INTERNAL_ICCM_LOCK       <-- HW hash finalizes here
  +-> ROM: launch_fmc()     -- jumps to FMC entry point
```

**Temporal analysis**: verify_image() completes and releases the SHA accelerator lock
BEFORE load_image() begins. The SHA accelerator is idle during ICCM copy. No contention.

## Architecture

### SHA Accelerator Reuse Approach
Instead of instantiating a new sha512_core (~30k gates), we add an "iccm_mode" to the
existing sha512_acc_top module. This module already has:
- A streaming data input path (datain_write -> block_reg accumulation)
- Block boundary tracking (block_wptr, block_full)
- SHA-384 mode support (mode register)
- Automatic padding and finalization FSM (SHA_PAD0/PAD1/DONE)
- An instantiated sha512_core that we reuse at zero additional gate cost

We add:
- A third input mode (iccm_mode) alongside mailbox_mode and streaming_mode
- New ports for ICCM write data and iccm_lock
- HW auto-lock logic (ICCM mode takes priority, FW sees lock held)
- A pv_write output port + PCR write FSM for writing digest to PCR4
- ICCM write serializer (bank 0->1->2->3 when multiple banks write)

### Data Flow
```
ICCM bank writes (el2_mem_export)
  iccm_wren_bank[3:0]          -- per-bank write enable
  iccm_bank_wr_data[3:0][31:0] -- per-bank write data (32b)
       |
       v
  +---------------------------------------------+
  | iccm_write_serializer (new, in caliptra_top |
  | or thin wrapper module)                      |
  |  - serializes multi-bank writes to single    |
  |    32-bit stream, bank 0 first               |
  |  - outputs: iccm_hash_dv, iccm_hash_data    |
  +---------------------------------------------+
       |
       v
  +---------------------------------------------+
  | sha512_acc_top (MODIFIED)                    |
  |  - existing module in src/soc_ifc/rtl/      |
  |  - new iccm_mode alongside streaming/mbox   |
  |  - iccm_hash_data feeds input_data mux      |
  |  - iccm_lock triggers finalization           |
  |  - new pv_write output for PCR4             |
  |  - reuses existing sha512_core instance     |
  +---------------------------------------------+
       |
       v
  PCR Vault (pv_write port)
  PCR4 [384 bits]
```

### Trigger Model
```
cptra_uc_rst_b deassert (or fw_update_rst_window clear)
  -> sha512_acc iccm_mode IDLE (waiting for ROM to trigger)

ROM: write MODE register with ICCM_MODE=1
  -> sha512_acc auto-acquires lock in iccm_mode
  -> SHA-384 mode set, ready to accept ICCM write stream
  -> FW sees lock held, cannot use sha512_acc until ICCM hash completes

ICCM writes arrive (ROM memcpy from mailbox to ICCM)
  -> sha512_acc accumulates data into SHA blocks

iccm_lock asserted (ROM locks ICCM regions)
  -> equivalent to execute_set in streaming mode
  -> SHA padding and finalization via existing FSM
  -> PCR write FSM writes 12 dwords to PCR4
  -> sha512_acc lock released, FW can use it again
```

### Security Argument for ROM-Triggered Mode
The only path to a valid attestation quote requires ALL of:
1. ROM triggers iccm_mode (writes MODE.ICCM_MODE=1)
2. ROM copies correct FW image to ICCM (hash captures every write)
3. ROM locks ICCM (triggers finalization, digest written to PCR4)

If any step is skipped:
- No iccm_mode trigger: PCR4 stays at reset value (all zeros) -> quote fails
- Wrong data written: PCR4 digest mismatches expected -> verifier rejects
- No iccm_lock: hash never finalizes, PCR4 never written -> quote fails

This makes boot_flow_monitor_en gating unnecessary for the hash engine --
even if the monitor is disabled (debug mode), skipping iccm_mode just means
PCR4 is empty and attestation fails. No security bypass.

### Lock Priority / FW Interaction
- On reset, sha512_acc is idle (lock=0), iccm_mode=0
- ROM writes MODE.ICCM_MODE=1 to trigger iccm_mode (acquires lock)
- While iccm_mode is active, FW lock requests are blocked (FW sees LOCK=1)
- After iccm_lock finalizes the hash and PCR4 is written, lock is released
- FW can then use sha512_acc normally for its own hashing needs
- ROM must trigger iccm_mode BEFORE load_image() begins the ICCM copy
- Since ROM verify_image() runs BEFORE load_image(), the sequence is:
  1. verify_image() uses sha512_acc (streaming/mailbox mode) -> releases lock
  2. ROM writes MODE.ICCM_MODE=1 -> acquires lock
  3. load_image() memcpys to ICCM -> sha512_acc captures writes
  4. lock_registers() sets iccm_lock -> sha512_acc finalizes, writes PCR4, releases lock
  5. FW can use sha512_acc again

## Implementation Blocks

### Block 1: sha512_acc_top.sv Modifications
File: src/soc_ifc/rtl/sha512_acc_top.sv

New ports:
```
input  logic        iccm_hash_dv_i,      // serialized ICCM write data valid
input  logic [31:0] iccm_hash_data_i,    // serialized ICCM write data
input  logic        iccm_lock_i,         // ICCM lock (finalize trigger)
output pv_write_t   iccm_pv_write_o      // PCR vault write port
```

Modifications:
- Add `iccm_mode` signal (set when ROM writes MODE.ICCM_MODE=1 and lock is free)
- Extend `input_data` mux: add `iccm_hash_data_i` as third source
- Extend `block_we`: add `iccm_mode_block_we = (iccm_mode & iccm_hash_dv_i)`
- Lock acquisition: when ROM sets ICCM_MODE, acquire lock (same as streaming mode)
- Map `iccm_lock_i` to `execute_set` equivalent in iccm_mode (triggers padding)
- Force SHA-384 mode when iccm_mode active (ignore MODE register SHA_MODE field)
- Force ENDIAN_TOGGLE=0 behavior when iccm_mode active (LE->BE byte swap)
- Add PCR write FSM: after SHA_DONE in iccm_mode, write 12 dwords of digest to
  pv_write_o with write_entry=4 (PCR4), then release lock
- DLEN tracking: internal counter increments by 4 on each iccm_hash_dv_i
- MODE.ICCM_MODE field: write-once per boot (cleared on reset, cannot be re-set after
  iccm_mode completes -- prevents FW from re-triggering to overwrite PCR4)

### Block 2: ICCM Write Serializer
Small module or logic block (can be in caliptra_top.sv or a thin wrapper):
- Inputs: iccm_wren_bank[NUM_BANKS-1:0], iccm_bank_wr_data[NUM_BANKS-1:0][31:0]
- Outputs: iccm_hash_dv, iccm_hash_data[31:0]
- When multiple banks write simultaneously (DMA 64-bit write -> 2 banks),
  serialize in deterministic order: bank 0 first, then bank 1, etc.
- Single-bank write: pass through in same cycle
- Multi-bank write: takes N cycles for N active banks (uses small shift register)
- Must handle backpressure from sha512_acc (stall_write / req_hold)

### Block 3: PCR Vault Modifications
- Bump PV_NUM_WRITE from 1 to 2 in pv_defines_pkg.sv
- Connect second pv_write port from sha512_acc_top's iccm_pv_write_o
- PCR4 write protection:
  - Block AHB/FW data writes to PCR_ENTRY[4] (swwe=0 for entry 4) -- FW cannot
    write arbitrary values
  - **Block the existing SHA pv_write client from targeting PCR4**: add a guard in pv.sv
    that masks pv_write[0] (the SHA/crypto client) when write_entry == 4. This ensures
    PCR4 can ONLY be written by pv_write[1] (the iccm hash path). The existing PCR
    extend flow (sha512_ctrl -> pv_write[0]) must never reach PCR4.
- PCR4 clear mechanism (field escape hatch):
  - FW CAN clear PCR4 to zero via PCR_CTRL[4].clear (hwclr on PCR_ENTRY[4])
  - FW CANNOT write nonzero values to PCR4 (swwe=0 blocks data writes)
  - This allows Runtime FW to zero PCR4 if the feature is buggy, so attestation
    can succeed with a verifier policy that accepts PCR4=0 as "feature disabled"
  - An attacker who controls FW can only zero PCR4 (detectable), never forge a hash
- PCR4 lock behavior:
  - HW sets PCR_CTRL[4].lock after hash engine writes PCR4
  - FW CAN clear lock via PCR_CTRL[4].clear (which also zeros the entry)
  - This differs from PCR0-3 where lock is more restrictive
- RDL changes: pv_reg.rdl needs PCR4 write protection (swwe=0 on data, swwel on lock)

### Block 4: soc_ifc_top.sv Integration
- Route new sha512_acc_top ports through soc_ifc_top.sv:
  - iccm_hash_dv_i, iccm_hash_data_i, iccm_lock_i (inputs from caliptra_top)
  - iccm_pv_write_o (output to caliptra_top for PCR vault connection)

### Block 5: caliptra_top.sv Integration
- Tap iccm_bank_wr_data from el2_mem_export (alongside existing wren/addr taps)
- Instantiate ICCM write serializer logic
- Route serialized data + iccm_lock into soc_ifc_top
- Connect iccm_pv_write_o to PCR vault's second pv_write port

### Block 6: Build Integration
- No new .sv files for SHA (reusing sha512_acc_top)
- If serializer is a separate module, add to appropriate compile.yml
- Do NOT modify .vf files (auto-generated from compile.yml)

### Block 7: caliptra-sw Updates (separate repo: chipsalliance/caliptra-sw)
- ROM: add MODE.ICCM_MODE=1 write between verify_image() and load_image()
- runtime/src/pcr.rs: add PcrId4 to EXTEND_PCR reserved/rejected list
- runtime: add PCR4 clear logic gated by a feature-disable flag or FW policy
  (e.g., clear PCR4 on startup if ICCM hash feature is known buggy for this FW version)
- drivers/src/pcr_log.rs: add PCR_ID_ICCM_MEASUREMENT constant
- Documentation updates

### Block 8: Tests
- C test: write known data to ICCM, verify PCR4 matches expected SHA-384
- C test: verify FW cannot write/extend/clear PCR4 (AHB write rejected)
- C test: verify sha512_ctrl PCR extend cannot target PCR4
- C test: verify hash resets correctly on fw_update_rst_window
- C test: verify FW can still use sha512_acc normally after ICCM hash completes
- C test: verify FW can clear PCR4 to zero via PCR_CTRL[4].clear
- C test: verify FW clear results in all-zero PCR4 (not stale data)
- C test: verify FW cannot write nonzero values to PCR4 after clearing
- SVA assertions for iccm_mode FSM states, lock priority, and PCR4 protection

## Timing Impact
**Zero boot time impact.** The sha512_acc captures ICCM writes as they happen --
it piggybacks on the existing write data bus with no backpressure. The SHA-384
computation runs in parallel with the memcpy using the existing sha512_core instance.
By the time ROM sets iccm_lock, the SHA state is already up-to-date; only finalization
(padding + last compression) remains, which takes ~80 cycles. This is invisible to
boot latency.

**Minimal ROM code change.** ROM needs one additional register write (MODE.ICCM_MODE=1)
between verify_image() and load_image(). This is a single 32-bit store instruction.

## FIPS Compliance Considerations
The sha512_acc's sha512_core is already FIPS-validated. The iccm_mode reuses this
exact same core with no datapath modifications -- only the input data source and
trigger mechanism change. Therefore:
- The sha512_core validation is NOT affected (same gates, same crypto math)
- The existing KAT for sha512_acc still exercises the core at boot
- The iccm_mode is just a new "user" of the same validated SHA engine
- If FIPS auditors question it: the mode adds a data input path and a PCR write
  output, but the cryptographic computation is identical to existing validated usage
- The PCR4 output is read-only attestation data with no key material involvement

## Gate Cost Analysis
- sha512_core reuse: 0 additional gates (already instantiated)
- iccm_mode FSM additions to sha512_acc_top: ~200-400 gates (mux, auto-lock, mode tracking)
- PCR write FSM: ~200-300 gates (12-dword write sequencer)
- ICCM write serializer: ~200-300 gates (bank priority encoder + shift register)
- PCR vault guard logic: ~50 gates
- **Total: ~700-1000 gates** (vs ~30,000 for a dedicated sha512_core instance)

## Security Properties (must hold)
1. PCR4 nonzero data is ONLY writable by sha512_acc iccm_mode (pv_write[1]) -- never
   by FW via AHB, never by sha512_ctrl via pv_write[0]
2. FW can clear PCR4 to zero (field escape hatch) but cannot write arbitrary values
3. iccm_mode lock prevents FW from using sha512_acc during ICCM hashing
4. Hash captures ALL ICCM writes between iccm_mode trigger and iccm_lock -- no gaps
5. Bank serialization order is deterministic (bank 0 first)
6. Hash engine resets cleanly on cptra_uc_rst_b and fw_update_rst_window
7. After ICCM hash completes, sha512_acc lock is released for normal FW use
8. FW cannot re-trigger iccm_mode after it completes (write-once per boot)
9. ICCM writes before iccm_mode trigger are NOT captured (ROM controls the window)
10. Skipping any step (trigger, copy, lock) results in empty PCR4 -> attestation failure
11. Verifier policy determines whether PCR4=0 is acceptable (feature disabled/buggy)
    or a failure (feature expected to be working)

## Open Items
- Coordinate with caliptra-sw team on PCR4 reservation and ROM iccm_mode trigger placement
- Review sha512_acc_top stall_write / req_hold interaction with iccm_mode
  (iccm writes arrive from HW bus, not CSR -- backpressure mechanism differs)

## Resolved: boot_flow_monitor_en Gating

**Decision: Do NOT gate the hash engine with boot_flow_monitor_en.**

ROM-triggered iccm_mode is self-securing: the only path to a valid attestation
quote is trigger -> correct copy -> lock. If debug-unlocked tests skip iccm_mode,
PCR4 stays empty and attestation fails -- no security bypass possible. Gating
would add complexity with no security benefit.

## Resolved: Endianness for ICCM Hash Mode

**Decision: Use the default byte-swap (ENDIAN_TOGGLE=0) -- same as mailbox mode.**

Analysis:
- SHA-384 (FIPS 180-4) expects big-endian input
- RISC-V VeeR EL2 is little-endian; ICCM writes arrive as little-endian 32-bit words
- ROM's verify_image() uses sha512_acc in mailbox mode with ENDIAN_TOGGLE=0 (default),
  which byte-swaps the 4-byte input word from LE to BE before feeding sha512_core:
  `swizzled_data[b] = input_data[(DATA_NUM_BYTES-1-b)]` (byte reversal within each dword)
- The mailbox SRAM data that ROM hashes during verify_image() is the same raw LE bytes
  that ROM later memcpys to ICCM during load_image()
- Therefore the ICCM write data (LE) needs the same byte-swap that mailbox mode applies

Implementation: in iccm_mode, hardwire the swizzle to the default (ENDIAN_TOGGLE=0)
behavior. Do NOT let FW control endianness for iccm_mode -- it must be fixed to match
the convention ROM uses for verification. This means:
- iccm_hash_data feeds into input_data[] alongside mbox_rdata/streaming_wdata
- The existing swizzle logic (line 230-231) applies the LE->BE conversion
- The resulting SHA-384 digest over the ICCM write stream will match what ROM computed
  over the same bytes in the mailbox (modulo any address/offset differences in the image
  layout, which we avoid by hashing raw data only, no addresses)
