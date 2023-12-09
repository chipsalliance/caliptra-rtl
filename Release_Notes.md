_*SPDX-License-Identifier: Apache-2.0<BR>
<BR>
<BR>
Licensed under the Apache License, Version 2.0 (the "License");<BR>
you may not use this file except in compliance with the License.<BR>
You may obtain a copy of the License at<BR>
<BR>
http://www.apache.org/licenses/LICENSE-2.0 <BR>
<BR>
Unless required by applicable law or agreed to in writing, software<BR>
distributed under the License is distributed on an "AS IS" BASIS,<BR>
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.<BR>
See the License for the specific language governing permissions and<BR>
limitations under the License.*_<BR>

# **Release Notes** #
_*Last Update: 2023/12/08*_

## Rev 1p0-rc2 ##

### Rev 1p0-rc2 release date: 2023/12/13 (1p0 version pending ROM release for official declaration) ###
- Caliptra Hardware Specification: Markdown conversion
- Caliptra Integration specification update with synthesis warnings and jtag tck requirement
- Caliptra README updates to clarify test cases and running with VCS
- Makefile updates to support DPI compilation in VCS
- Verification
  - Adding ECC, DOE, HMAC_DRBG and SHA512_masked formal Assertion IP
  - JTAG with clock gating test cases
  - Fixes for UVM caliptra_top test scenarios
  - Fixes for UVM KeyVault test scenarios
- Updated synthesis tool from Design Compiler to Fusion Compiler (sanity checks only)
- RTL
  - Remove TODO comments on caliptra_top ports
  - Remove JTAG IDCODE command from RISC-V processor

### Bug Fixes ###
[MBOX] Fix ICCM Uncorrectable ECC error driving hw_error_non_fatal bit for LSU reads

## Previous Releases ##

### Rev 1p0-rc1 ###

#### Rev 1p0-rc1 release date: 2023/11/03 (1p0 version pending ROM release for official declaration) ###
- Caliptra IP Specification: see docs/ folder
- Caliptra Integration Specification: see docs/ folder
- Caliptra testplan: see docs/ folder
- Data Vault
- RISC-V Timers
  - mtime + mtimecmp implementation
  - Watchdog timer configuration by SOC; escalate interrupts to error
- Reliability, Availability, Serviceability Features
  - Connectivity for cptra_error_fatal/cptra_error_non_fatal interrupts
  - Mailbox protocol violation detection and Error state
  - SRAM ECC error detection and reporting for ICCM, DCCM, Mailbox
  - Key clearing and system reset on fatal errors
- SOC Interface
  - QSPI inout changed to input+output+enable
  - FUSE PAUSER config registers and enforcement
- Reset Domain Crossing (RDC) fixes
  - Reset-triggered clock gating on cross-domain registers
  - Reset timing changes for noncore reset assertion
  - Migrate most internal logic to the noncore reset domain
  - Migrate APB interface to noncore reset domain
- FIPS compliance updates
  - SHA Accelerator LOCK default to Caliptra-owned
  - LMS Fuse
  - SOC Stepping ID field in HW Revision
  - Extended pcr_nonce from 32-bit to 256-bit
  - TRNG Data Clear
- RISC-V Core
  - Increase ROM size to 48KiB
  - Added 2:1 AHB lite mux on LSU and SB buses to allow debug access to
    peripherals
- Timing Optimizations
  - Remove PSEL loopback path in APB slave
  - Remove unnecessary Mailbox SRAM ECC writeback path
- Validation enhancements
  - SOC_IFC/Mailbox randomized regressions via UVM testbench
  - SOC Interface Register validation via directed + random tests
  - Coverage reporting and analysis for all interfaces, registers, FSM
  - Automated GitHub action using OpenOCD for interactive JTAG debugging
  - SHA Formal Verification

#### Bug Fixes ####
[CLK GATING] Fatal error should wake up clks<br>
[CLK GATING] JTAG accesses need to wake up clocks<br>
[DOE] add zeroize to clear all internal regs<br>
[DOE] DOE IV reg needs hwclr input<br>
[DOE] doe_fsm incr_dest_sel logic can be removed since FE now only takes up 12 dwords<br>
[DOE] doe_fsm write_offset increments to 0xC<br>
[DOE] Simplify kv_write dest_valid hardcoded value in doe_fsm<br>
[ECC] ECC input register bound check<br>
[ECC] ECC output register bound check<br>
[ECC] ECC Public key validation check<br>
[ECC] mismatch of final reduction in Mont. mult in the case of prime<= p_internal<br>
[ECC] mismatch of modular addition result in the case of p<= a+b < 2^384<br>
[ECC] remove FW read access to kv/privkey reg<br>
[ECC} error trigger when pcr_sign ctrl input is set in keygen/verifying mode<br>
[KV] Debug Mode and Scan Mode switch doesn't flush locked registers<br>
[KV] Debug mode should flush KV even if core is asleep<br>
[KV] Dest_valid and last_dword should check lock_use to clear along with lock_wr<br>
[KV] KV may still contain secrets during scan mode<br>
[KV] kv_reg.rdl still has 6 bits for dest_valid while we have 5 valid clients<br>
[KV] KV->SHA ->FW read path and KV->HMAC->FW read path should NOT exist in the design<br>
[KV] last dword of secret values stays in KV/crypto interface<br>
[KV] Suppress writes to an entry altogether when it's being cleared<br>
[MBOX] ECC error decode may detect error on mbox_sram when a write is in progress<br>
[MBOX] First resp read data is zero after handling a command with DLEN > MBOX SIZE<br>
[MBOX] HWCLR triggered by force-unlock has lower precedence than SW writes<br>
[MBOX] Mailbox data length limiting reads is calculated incorrectly<br>
[MBOX] Mailbox does not flag protocol error for attempted writes to DLEN<br>
[MBOX] mailbox returns non-zero data in an overread case<br>
[MBOX] New RAS feature to detect protocol violation incorrectly decodes certain reg accesses as errors<br>
[MBOX] SOC can read mbox_dataout with stale data<br>
[MBOX] Writes beyond the mailbox size overwrite the last data dword in mailbox memory<br>
[MBOX] Writes to (a) unaligned addresses (b) size < AHB_DATA_WIDTH may corrupt memory<br>
[MBOX] error_cmd_fail_sts.hwset is continuously set when mailbox protocol error occurs<br>
[PCR] Extend PCR Nonce from 32-bit to 256-bit to protect replay attack<br>
[PCR] PCR dword mismatch<br>
[PCR] Update the reset of the 'lock' PCR control to the core reset domain (so that a FW update reset or warm reset can also unlock the PCR)<br>
[PCR] zeroize doesn't take effect if is set with pcr at the same cycle<br>
[SHA ACCEL] SoC requester can use mailbox mode<br>
[SOC_IFC] Arbiter lets direct request dv through at the same time as soc ifc mailbox request causing deadlock<br>
[SOC_IFC] Breakpoint is unreachable<br>
[SOC_IFC] Fuse Registers can never be written using non-default values programmed in FUSE_VALID_PAUSER<br>
[SOC_IFC] Generic Input Wires toggle (any bit) should trigger notification interrupt to uC<br>
[SOC_IFC] INTERNAL_HW_ERROR_FATAL_MASK and INTERNAL_HW_ERROR_NON_FATAL_MASK allow writes to (and non-zero reads from) reserved fields.<br>
[SOC_IFC] Mailbox ECC errors detected during SHA Accel direct accesses are not detected/corrected<br>
[SOC_IFC] mbox_execute can be cleared by SOC at any point after acquiring lock<br>
[SOC_IFC] uC can't write to CPTRA_FW_ERROR regs (Github issue #64)<br>
[SOC_IFC] WDT may not correctly detect when uC services the timer expiration interrupt<br>
[WDT] CPTRA_WDT_STATUS reg should be FW writeable so it can clear the flags<br>
[WDT] First stage interrupt output should be "error_intr" instead of "notif_intr"<br>
[WDT] WDT registers need to be on ungated clk<br>
[AHB] AHB 2:1 Mux hangs with back to back transactions after a stall<br>
[RST] scan_mode should not corrupt resets<br>
[TOP] EL2 Mem interface is not instantiated with a modport at all levels

### Rev 0p8 ###

#### DISCALIMER: This is NOT A BUG-FREE MODEL YET. This is a 0p8 release model. Please see testplan document in docs folder to know the status of validation. ####
##### This model is released mainly for interface, floorplan planning purposes for consumers. #####
##### Rev 0p8 release date: 03-31-2023 #####

- Caliptra IP Specification: see docs/ folder
- Caliptra Integration Specification: see docs/ folder
- Caliptra testplan: see docs/ folder
- CHIPALLIANCE RISC-V Core - https://github.com/chipsalliance/Cores-VeeR-EL2/
  - ICCM, DCCM enabled w/ 128KB each; Instruction Cache disabled; fast interrupt redirect enabled
- Cryptos (please see the spec for NIST compliance algorithms followed)
    - HMAC384 – Caliptra consortium provided (built based on SHA384 block below)
    - ECC384 – Based on secp384, Caliptra consortium provided
    - HMAC-DRBG – Caliptra consortium provided (but built using HMAC384 above)
    - Key Vault & PCR Vault – Caliptra consortium provided
    - SHA384/SHA512 – https://github.com/secworks/sha512
    - Deobfuscation block – Built on https://github.com/secworks/aes but NOT ROM/FW accessible
    - SHA256 – https://github.com/secworks/sha256
    - Side channel attack analysis and solutions where applicable  (Plz see Caliptra IP specification for details)
    - AHB-lite internal fabric
    - Please see spec for decoding details of various blocks
- Key Vault, PCR Vault w/ HW PCR extension & Data Vault
- Interrupts from all peripherals (Cryptos, SOC mailbox, IOs, timers etc.)
- ICCM write locking
- TAP interface
- Idle Clock Gating
- Impactless update reset
- Mailbox SRAM ECC
- Security Assert Flushing in debug unlocked & scan modes
- SOC interface (APB, mailbox, architectural registers, fuse registers, external TRNG REQ, SHA384 acceleration) – Caliptra Consortium provided
- Lint clean to the rules published in the integration spec
- HTML (generated from RDLs) for all registers (internal registers, external facing architectural registers, fuse registers)
- RTL “Frozen” IP interface;  Frozen SOC facing registers.
    - All changes from hereon forth will require CHIPSALLIACE CALIPTRA WG approval
- WDT, Integrated TRNG, SPI (unused in BMD/passive mode)
- Validation Notes:
    - DUT per crypto block and associated checkers
    - Nightly regression on crypto blocks on-going
    - Smoke tests for all of the above passing including bring up/boot of the caliptra IP (KV testing for ECC & SHA)
    - UVMF for multiple DUT blocks and SOC interface
    - DV complete for first cut of the boot & reset flows, Fuses, SOC registers, Crypto blocks, Key vault, PCR Vault, PCR extend, PCR signing, Mailbox

### Rev Pre0p8: ###
#### DISCLAIMER: This is NOT A BUG-FREE MODEL. This is a pre-0p8 development model that will be sync’d every week. ####
#### This model is released mainly for interface, floorplan planning purposes for consumers. ####
#### 0p8 release date = 03-31-2023 ####
- Caliptra Hardware Specification: see docs/ folder
- Caliptra Integration Specification: see docs/ folder
- Caliptra testplan: see docs/ folder
- CHIPALLIANCE RISC-V Core - https://github.com/chipsalliance/Cores-VeeR-EL2/
  - ICCM, DCCM enabled w/ 128KB each; Instruction Cache disabled; fast interrupt redirect enabled
-	Cryptos (please see the spec for NIST compliance algorithms followed)
    -   HMAC384 – Caliptra consortium provided (built based on SHA384 block below)
    -   ECC384 – Based on secp384, Caliptra consortium provided
    -   HMAC-DRBG – Caliptra consortium provided (but built using HMAC384 above)
    -   Key Vault & PCR Vault – Caliptra consortium provided
    -   SHA384/SHA512 – https://github.com/secworks/sha512
    -   Deobfuscation block – Built on https://github.com/secworks/aes but NOT ROM/FW accessible
    -   SHA256 – https://github.com/secworks/sha256
    -   Side channel attack analysis and solutions where applicable  (Plz see Caliptra IP specification for details)
-	AHB-lite internal fabric
    -   Please see spec for decoding details of various blocks
-	Key Vault, PCR Vault w/ HW PCR extension & Data Vault
-	Interrupts from all peripherals (Cryptos, SOC mailbox, IOs, timers etc.)
-	ICCM write locking
-	TAP interface
-	Idle Clock Gating
-	Impactless update reset
-	Mailbox SRAM ECC
-	Security Assert Flushing in debug unlocked & scan modes
-	SOC interface (APB, mailbox, architectural registers, fuse registers, external TRNG REQ, SHA384 acceleration) – Caliptra Consortium provided
-	Lint clean to the rules published in the integration spec
-	HTML (generated from RDLs) for all registers (internal registers, external facing architectural registers, fuse registers)
-	RTL “Frozen” IP interface;  Frozen SOC facing registers.
    -   All changes from hereon forth will require CHIPSALLIACE CALIPTRA WG approval
-	Validation Notes:
    -   DUT per crypto block and associated checkers
    -   Nightly regression on crypto blocks on-going
    -   Smoke tests for all of the above passing including bring up/boot of the caliptra IP (KV testing for ECC & SHA)
    -   UVMF for multiple DUT blocks and SOC interface

### Rev rtl-caliptra_rtl_0.5.1 ###
-   Add missing printf/ and includes/ directories to src/integration/test_suites which are required to run the tests
-   Updated Version.txt and tar.gz

### Rev rtl-caliptra_rtl_0.5rtl ###
-	CHIPALLIANCE RISC-V Core - https://github.com/chipsalliance/Cores-VeeR-EL2
    - ICCM, DCCM enabled w/ 128KB each; Instruction Cache disabled; fast interrupt redirect enabled
-	Cryptos (please see the spec for NIST compliance algorithms followed)
    - HMAC384 – Caliptra consortium provided (built based on SHA384 block below)
    - ECC384 – Based on secp384, Caliptra consortium provided
    - HMAC-DRBG – Caliptra consortium provided (but built using HMAC384 above)
    - Key Vault & PCR Vault – Caliptra consortium provided
    - SHA384/SHA512 – https://github.com/secworks/sha512
    - Deobfuscation block – Built on https://github.com/secworks/aes but NOT ROM/FW accessible
    - SHA256 – https://github.com/secworks/sha256
    - Side channel attack analysis and solutions where applicable  (Plz see Caliptra IP specification for details)
-	AHB-lite internal fabric
    - Please see spec for decoding details of various blocks
-   Interrupts from all peripherals (Cryptos, SOC mailbox, IOs, timers etc.)
-	ICCM locking
-	SOC interface (APB, mailbox, architectural registers, fuse registers, TRNG REQ protocol) – Caliptra Consortium provided
-	Lint clean up is partially done
-	HTML (generated from RDLs) for all registers (internal registers, external facing architectural registers, fuse registers)
-	Stable IP interface (pending TRNG interface wires that is a new feature)
-	Validation Notes:
    - DUT per crypto block and associated checkers
    - Nightly regression on crypto blocks on-going
    - Smoke tests for all of the above passing including bring up/boot of the caliptra IP (KV testing for ECC & SHA are pending)
    - UVMF for multiple DUT blocks and SOC interface
    - NOTE: 0p8 release will have stress validation on SOC interface with random resets, clock gating, impactless update crossed with mailbox protocol etc.




