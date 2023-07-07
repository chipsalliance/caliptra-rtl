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
_*Last Update: 2023/06/08*_

## Rev 0p8 ##

### DISCALIMER: This is NOT A BUG-FREE MODEL YET. This is a 0p8 release model. Please see testplan document in docs folder to know the status of validation. ###
#### This model is released mainly for interface, floorplan planning purposes for consumers. ####
#### Rev 0p8 release date: 03-31-2023 ####

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

## Pending for RTL 1p0: ##
- Timers, integrated-TRNG integration w/ Caliptra, Error domain logic
- Lots of bug fixes :-)
- Data Vault, TRNG REQ protocol, SHA384 acceleration, More mailbox val, PCR val, cross product flows

## Previous Releases ##

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




