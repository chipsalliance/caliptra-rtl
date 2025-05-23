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

# **Caliptra Hands-On Guide** #
_*Last Update: 2025/04/29*_

## **Release Consumption and Integration** ##
Prior official releases are available at: https://github.com/chipsalliance/caliptra-rtl/releases<br>
Releases are published as a tag, and also contain downloadable assets (which should not be used).
Instead of downloading the assets attached to the published release, integrators should consume Caliptra releases by pulling code from the repository at the associated tag, due to https://github.com/chipsalliance/caliptra-rtl/issues/471.

## **Tools Used** ##

OS:
 - Build instructions assume a Linux environment

Lint:
 - Synopsys Spyglass
   - `Version S-2021.09-1`
 - Real Intent AscentLint
   - `Version 2019.A.p15 for RHEL 6.0-64, Rev 116515, Built On 12/18/2020`

Simulation:
 - Synopsys VCS with Verdi
   - `Version R-2020.12-SP2-7_Full64`
 - Verilator
   - `Version 5.012`
 - Mentor Graphics QVIP
   - `Version 2021.2.1` of AHB models
 - Avery AXI VIP
   - `Version 2025.1` of axixactor
 - UVM installation
   - `Version 1.1d`
 - Mentor Graphics UVM-Frameworks
   - `2022.3`

Synthesis:
 - Synopsys Fusion Compiler
   - `Version 2022.12-SP3`

GCC:
 - RISCV Toolchain for generating memory initialization files
   - `Version 2023.04.29`
   - `riscv64-unknown-elf-gcc (g) 12.2.0`
 - G++ Used to compile Verilator objects and test firmware
   - `g++ (GCC) 11.2.0`

CDC:
 - Questa CDC
   - `2023.4_3 5762808 linux_x86_64 29-Feb-2024`
  
RDC:
 - Real Intent Meridian
   - `2022.A.P18.3`

RDL Compiler:
 - systemrdl-compiler==1.27.3
 - peakrdl-systemrdl==0.3.0
 - peakrdl-regblock==0.21.0
 - peakrdl-uvm==2.3.0
 - peakrdl-ipxact==3.4.3
 - peakrdl-html==2.10.1
 - peakrdl-cheader==1.0.0
 - peakrdl==1.1.0

Other:
 - Playbook (Microsoft Internal workflow management tool)

### **RISCV Toolchain installation** ###
There is significant configurability when installing the RISCV toolchain.
These instructions may be used to create a RISCV installation that will be compatible
with the provided Makefile for compiling test C programs.

1. Install from this repository:
    - https://github.com/riscv-collab/riscv-gnu-toolchain
    - Follow the included README in that repository for installation instructions
2. The most recently tested toolchain build that was confirmed to work was 2023-04-29
    - https://github.com/riscv-collab/riscv-gnu-toolchain/releases/tag/2023.04.29
3. A compatible tool installation requires newlib cross-compiler, multilib support, and the zicsr/zifencei extensions. Use this configure command:
    - `./configure --enable-multilib --prefix=/path/to/tools/riscv-gnu/2023.04.29 --with-multilib-generator="rv32imc-ilp32--a*zicsr*zifencei"`
4. Use `make` instead of `make linux` to install the tool (using newlib option)

## **ENVIRONMENT VARIABLES** ##
Required for simulation:<BR>
`CALIPTRA_WORKSPACE`: Defines the absolute path to the directory where the Verilator "scratch" output directory will be created. Recommended to define as the absolute path to the directory that contains a subdirectory "chipsalliance" which, in turn, contains the Project repository root (called "Caliptra" or "caliptra-rtl")<BR>
`CALIPTRA_ROOT`: Defines the absolute path to the Project repository root (called "Caliptra" or "caliptra-rtl"). Recommended to define as `${CALIPTRA_WORKSPACE}/chipsalliance/caliptra-rtl`.<BR>

Required for Firmware (i.e. Test suites) makefile:<BR>
  `TESTNAME`: Contains the name of one of the tests listed inside the `src/integration/test_suites` folder; only used for `caliptra_top_tb` tests<BR>

## **Repository Overview** ##
```
caliptra-rtl
|-- LICENSE
|-- README.md
|-- Release_Notes.md
|-- SECURITY.md
|-- docs
|   |-- CaliptraHardwareSpecification.md
|   |-- CaliptraIntegrationSpecification.md
|   |-- CaliptraReleaseChecklist.md
|   |-- Caliptra_TestPlan.xlsx
|   `-- images
|-- src
|   |-- aes
|   |-- ahb_lite_bus
|   |-- axi
|   |-- caliptra_prim
|   |-- caliptra_prim_generic
|   |-- caliptra_tlul
|   |-- csrng
|   |-- datavault
|   |-- doe
|   |-- ecc
|   |-- edn
|   |-- entropy_src
|   |-- hmac
|   |-- hmac_drbg
|   |-- integration
|   |-- keyvault
|   |-- kmac
|   |-- lc_ctrl
|   |-- libs
|   |-- mldsa
|   |-- pcrvault
|   |-- riscv_core
|   |-- sha256
|   |-- sha512
|   |-- sha512_masked
|   `-- soc_ifc
|-- submodules
    `-- adams-bridge
`-- tools
    |-- README
    |-- scripts
    `-- templates
```
The root of the repository is structured as shown above, to a depth of 2 layers.<BR>
Each sub-component is accompanied by a file list summary (located in src/<component>/config/<name>.vf) that comprises all the filenames required to compile the component, and an optional testbench filelist for unit-level simulation. <BR>
VF files provide absolute filepaths (prefixed by the `CALIPTRA_ROOT` environment variable) to each compile target for the associated component.<BR>
The "Integration" sub-component contains the top-level fileset for Caliptra. `src/integration/config/compile.yml` defines the required filesets and sub-component dependencies for this build target. All of the files/dependencies are explicitly listed in `src/integration/config/caliptra_top_tb.vf`. Users may compile the entire design using only this VF filelist.<BR>


## **Verilog File Lists** ##
Verilog file lists are generated via VCS and included in the config directory for each unit. New files added to the design must be included in the vf list. They can be included manually or by using VCS to regenerate the vf file. File lists define the compilation sources (including all dependencies) required to build and simulate a given module or testbench, and should be used by integrators for simulation, lint, and synthesis.

## **Scripts Description** ##

`demo.rdl`:Sample RDL file<BR>
`Makefile`: Makefile to generate SRAM initialization files from test firmware and to run Verilator simulation<BR>
`gen_soc_ifc_covergroups.py`: Python script to generate a template of covergroups for all registers in soc_ifc<BR>
`reg_gen.py`: Used to compile/export RDL files to register source code<BR>
`reg_gen.sh`: Wrapper used to call `reg_gen.py` for all IP cores in Caliptra<BR>
`reg_doc_gen.py`: Used to compile/export top-level RDL address map to register source code, defining complete Caliptra address space, and produces HTML documentation<BR>
`reg_doc_gen.sh`: Wrapper to invoke `reg_doc_gen.py`<BR>
`reg_json.py`:Used to import JSON register definition from OpenTitan and generate SystemRDL model<BR>
`rdl_post_process.py`: Post-processing functionality to make RDL generated SystemVerilog files compatible with lint/Verilator requirements<BR>
`run_verilator_l0_regression.py`: Wrapper to run the L0 smoke test regression suite using the Makefile flow in Verilator<BR>
`integration_vector_gen.py`: Generates test vectors for crypto core tests<BR>
`veer_build_command.sh`: Shell script used to generate the VeeR-EL2 repository present in `src/riscv_core/veer_el2`<BR>
`openocd`: Open-Source FW debug utility used for JTAG testing in automated workflows

## **Simulation Flow** ##

### Caliptra Top VCS Steps: ###
1. Setup tools, add to PATH (ensure RISC-V toolchain is also available)
1. Define all environment variables above
    - For the initial test run after downloading repository, `iccm_lock` is recommended for TESTNAME
    - See [Regression Tests](#Regression-Tests) for information about available tests
1. Create a run folder for build outputs (and cd to it)
1. Either use the provided Makefile or execute each of the following steps manually to run VCS simulations
1. Makefile usage:
    - Example command:
        `make -C <path/to/run/folder> -f ${CALIPTRA_ROOT}/tools/scripts/Makefile TESTNAME=${TESTNAME} vcs`
    - NOTE: `TESTNAME=${TESTNAME}` is optional; if not provided, test defaults to value of TESTNAME environment variable, then to `iccm_lock`
    - NOTE: Users may wish to produce a run log by piping the make command to a tee command, e.g.:
        `make ... <args> ... | tee <path/to/run/folder>/vcs.log`
    - NOTE: The following macro values may be overridden to define the hardware configuration that is built. Default values in the Makefile are shown with each macro:
      - CALIPTRA_INTERNAL_TRNG=1
      - E.g. `make -f ${CALIPTRA_ROOT}/tools/scripts/Makefile CALIPTRA_INTERNAL_TRNG=1 vcs`
1. Remaining steps describe how to manually run the individual steps for a VCS simulation
1. [OPTIONAL] By default, this run flow will use the RISC-V toolchain to compile test firmware (according to TESTNAME) into program.hex, iccm.hex, dccm.hex, and mailbox.hex. As a first pass, integrators may alternatively use the pre-built hexfiles for convenience (available for [iccm_lock](src/integration/test_suites/iccm_lock) test). To do this, copy [iccm_lock.hex](src/integration/test_suites/iccm_lock/iccm_lock.hex) to the run directory and rename to `program.hex`. [dccm.hex](src/integration/test_suites/iccm_lock/iccm_lock.hex) should also be copied to the run directory, as-is. Use `touch iccm.hex mailbox.hex` to create empty hex files, as these are unnecessary for `iccm_lock` test.
1. Invoke `${CALIPTRA_ROOT}/tools/scripts/Makefile` with target 'program.hex' to produce SRAM initialization files from the firmware found in `src/integration/test_suites/${TESTNAME}`
    - E.g.: `make -f ${CALIPTRA_ROOT}/tools/scripts/Makefile program.hex`
    - NOTE: TESTNAME may also be overridden in the makefile command line invocation, e.g. `make -f ${CALIPTRA_ROOT}/tools/scripts/Makefile TESTNAME=iccm_lock program.hex`
    - NOTE: The following macro values must be overridden to match the value provided (later) during hardware compilation. The full L0 regression suite includes tests that will fail if the firmware and hardware configuration has a discrepancy. Default values in the Makefile are shown with each macro:
      - CALIPTRA_INTERNAL_TRNG=1
      - E.g. `make -f ${CALIPTRA_ROOT}/tools/scripts/Makefile CALIPTRA_INTERNAL_TRNG=1 program.hex`
1. Compile complete project using `src/integration/config/caliptra_top_tb.vf` as a compilation target in VCS. When running the `vcs` command to generate simv, users should ensure that `caliptra_top_tb` is explicitly specified as the top-level component in their command to ensure this is the sole "top" that gets simulated.
    - NOTE: The following macro values must be defined (or omitted) to match the value provided during firmware compilation. The full L0 regression suite includes tests that will fail if the firmware and hardware configuration has a discrepancy.
      - CALIPTRA_INTERNAL_TRNG
1. Copy the test generator scripts to the run output directory:
    - [src/ecc/tb/ecc_secp384r1.exe](src/ecc/tb/ecc_secp384r1.exe)
        * Necessary for [randomized_pcr_signing](src/integration/test_suites/randomized_pcr_signing)
        * OPTIONAL otherwise
    - [src/doe/tb/doe_test_gen.py](src/doe/tb/doe_test_gen.py)
        * Allows use of randomized secret field inputs during testing.
        * Required when using the `+RAND_DOE_VALUES` plusarg during simulation
        * Also required for several smoke tests that require randomized DOE IV, such as smoke_test_doe_scan, smoke_test_doe_rand, smoke_test_doe_cg
1. Simulate project with `caliptra_top_tb` as the top target

### Caliptra Top Verilator Steps: ###
1. Setup tools, add to PATH (ensure Verilator, GCC, and RISC-V toolchain are available)
2. Define all environment variables above
    - For the initial test run after downloading repository, `iccm_lock` is recommended for TESTNAME
    - See [Regression Tests](#Regression-Tests) for information about available tests.
3. Create a run folder for build outputs
    - Recommended to place run folder under `${CALIPTRA_WORKSPACE}/scratch/$USER/verilator/<date>`
4. [OPTIONAL] By default, this run flow will use the RISC-V toolchain to compile test firmware (according to TESTNAME) into program.hex, iccm.hex, dccm.hex, and mailbox.hex. As a first pass, integrators may alternatively use the pre-built hexfiles for convenience (available for `iccm_lock` test). To do this, copy `iccm_lock.hex` to the run directory and rename to `program.hex`. `dccm.hex` should also be copied to the run directory, as-is. Use `touch iccm.hex mailbox.hex` to create empty hex files, as these are unnecessary for `iccm_lock` test.
5. Run Caliptra/tools/scripts/Makefile, which provides steps to run a top-level simulation in Verilator
    - Example command:
        `make -C <path/to/run/folder> -f ${CALIPTRA_ROOT}/tools/scripts/Makefile TESTNAME=${TESTNAME} debug=1 verilator`
    - NOTE: `debug=1` is optional; if provided, the verilator run will produce a .vcd file with waveform information
    - NOTE: `TESTNAME=${TESTNAME}` is optional; if not provided, test defaults to value of TESTNAME environment variable, then to `iccm_lock`
    - NOTE: Users may wish to produce a run log by piping the make command to a tee command, e.g.:
        `make ... <args> ... | tee <path/to/run/folder>/verilate.log`
6. Users have the option to run the entire suite of smoke tests using the provided python script `run_verilator_l0_regression.py`
    1. Ensure Python 3.9.2 is available by adding to the $PATH variable
    2. Run the script with:
        `python3 run_verilator_l0_regression.py`
    3. NOTE: The script automatically creates run output folders at `${CALIPTRA_WORKSPACE}/scratch/$USER/verilator/<timestamp>/<testname>` for each test run
    4. NOTE: The output folder is populated with a run log that reports the run results and pass/fail status

### Unit Test VCS Steps: ###
1. Setup tools, add to PATH
1. Define all environment variables above
1. Create a run folder for build outputs (and cd to it)
1. Compile complete project using `src/<block>/config/<name>_tb.vf` as a compilation target in VCS. When running the `vcs` command to generate simv, users should ensure that `<name>_tb` is explicitly specified as the top-level component in their command to ensure this is the sole "top" that gets simulated.
1. Copy the test generator scripts or test vectors to the run output directory:
    - [src/ecc/tb/test_vectors/mm_test_vectors\*.hex](src/ecc/tb/test_vectors)
        * Necessary for [ecc_montgomerymultiplier_tb](src/ecc/tb/ecc_montgomerymultiplier_tb.sv)
    - [src/sha256/tb/sha256_test_gen.py](src/sha256/tb/sha256_test_gen.py)
        * Necessary for [sha256_random_test](src/sha256/tb/sha256_random_test.sv)
1. Simulate project with `<name>_tb` as the top target

### UVM Testbench Steps for `caliptra_top`: <BR>

**Description**:<BR>
The UVM Framework generation tool was used to create the baseline UVM testbench for verification of the top-level Caliptra image. The top-level bench leverages the `soc_ifc_top` testbench as a subenvironment, to reuse environment level sequences, agents, register models, and predictors.

**Prerequisites**:<BR>
- QVIP 2021.2.1 for Mentor Graphics (provides the AHB VIP)
- AXI VIP 2025.1 for Avery
- UVM 1.1d installation
- Mentor Graphics UVM-Framework installation

**Environment Variables**:<BR>
Required for UVM simulation:<BR>
`UVM_HOME`: Filesystem path to the parent directory containing SystemVerilog source code for the UVM library of the desired version. <BR>
`UVMF_HOME`: Filesystem path to the parent directory containing source code (uvmf_base_pkg) for the UVM Frameworks library, a tool available from Mentor Graphics for generating baseline UVM projects. <BR>
`QUESTA_MVC_HOME`: Filesystem path to the parent directory containing source code for Mentor Graphics QVIP, the verification library from which AHB UVM agents are pulled in the Caliptra UVM environment. <BR>
`AVERY_SIM`: Filesystem path to the parent directory containing source code for Avery UVM VIP, the verification library from which AXI UVM agents are pulled in the Caliptra UVM environment. <BR>
`AVERY_PLI`: Filesystem path to the parent directory containing source code for Avery UVM PLI, the verification library from which AXI UVM agents are pulled in the Caliptra UVM environment. <BR>
`AVERY_AXI`: Filesystem path to the parent directory containing source code for Avery AXI VIP, the verification library from which AXI UVM agents are pulled in the Caliptra UVM environment. <BR>

**Steps:**<BR>
1. Compile UVM 1.1d library
1. Compile the AHB/AXI VIP source
1. Compile the Mentor Graphics UVM-Frameworks base library
1. Compile the UVMF wrapper for AHB in Caliptra/src/libs/uvmf
1. Compile the custom Caliptra extended library components from Avery AXI VIP
1. Compile the `verification_ip` provided for `soc_ifc` found in `Caliptra/src/soc_ifc/uvmf_soc_ifc`
1. Compile the `caliptra_top` testbench found in `Caliptra/src/integration/uvmf_caliptra_top`
1. ALL compilation steps may be completed by using the file-list found at `src/integration/uvmf_caliptra_top/config/uvmf_caliptra_top.vf`
1. NOTE: `Caliptra/src/integration/uvmf_caliptra_top/uvmf_template_output/project_benches/caliptra_top/tb/testbench/hdl_top.sv` is the top-level TB wrapper for the system
1. Compile the validation firmware (as described in [Regression Tests](#Regression-Tests)) that will run on Caliptra's embedded RISC-V core
    - The expected output products are `program.hex`, `caliptra_fmc.hex`, `caliptra_rt.hex` and must be placed in the simulation run directory
    - `make -f ${CALIPTRA_ROOT}/tools/scripts/Makefile TESTNAME=caliptra_top program.hex`
    - `make -f ${CALIPTRA_ROOT}/tools/scripts/Makefile TESTNAME=caliptra_fmc caliptra_fmc.hex`
    - `make -f ${CALIPTRA_ROOT}/tools/scripts/Makefile TESTNAME=caliptra_rt  caliptra_rt.hex`
1. Copy the test vectors to the run output directory:
    - [src/sha512/tb/vectors/SHA\*.rsp](src/sha512/tb/vectors/)
        * Required for SHA512 UVM unittest
1. Select a test to run from the set of tests in `Caliptra/src/integration/uvmf_caliptra_top/uvmf_template_output/project_benches/caliptra_top/tb/tests/src`
1. Provide `+UVM_TESTNAME=<test>` argument to simulation

### UVM Unit Test Steps: <BR>

**Description**:<BR>
The UVM Framework generation tool was used to create the baseline UVM testbench for verification of each IP component inside Caliptra. The following IP blocks have supported UVM testbenches:
- [ECC](src/ecc/uvmf_ecc)
- [HMAC](src/hmac/uvmf_2022)
- [SHA512](src/sha512/uvmf_sha512)
- [KeyVault](src/keyvault/uvmf_kv)
- [PCRVault](src/pcrvault/uvmf_pv)
- [SOC_IFC](src/soc_ifc/uvmf_soc_ifc)

**Prerequisites**:<BR>
- QVIP 2021.2.1 for Mentor Graphics (provides the AHB VIP)
- AXI VIP 2025.1 for Avery
- UVM 1.1d installation
- Mentor Graphics UVM-Framework installation

**Steps:**<BR>
1. Compile UVM 1.1d library
1. Compile the AHB/AXI VIP source
1. Compile the Mentor Graphics UVM-Frameworks base library
1. Compile the UVMF wrapper for AHB in Caliptra/src/libs/uvmf
1. Compile the custom Caliptra extended library components from Avery AXI VIP
1. Compile the `verification_ip` provided for the target testbench
1. ALL compilation steps may be completed by using the file-list found at `src/<block>/uvmf_<name>/config/<name>.vf`
1. NOTE: `Caliptra/src/<block>/uvmf_<name>/uvmf_template_output/project_benches/<block>/tb/testbench/hdl_top.sv` is the top-level TB wrapper for the system
1. Copy the test generator scripts to the run output directory:
    - [src/ecc/tb/ecc_secp384r1.exe](src/ecc/tb/ecc_secp384r1.exe)
        * Necessary for ECC unittest
    - [src/hmac/tb/test_gen.py](src/hmac/tb/test_gen.py)
        * Required for uvmf_hmac unittest
    - [src/sha512/tb/vectors/SHA\*.rsp](src/sha512/tb/vectors/)
        * Required for SHA512 UVM unittest
1. Select a test to run from the set of tests in `Caliptra/src/<block>/uvmf_<name>/uvmf_template_output/project_benches/<block>/tb/tests/src`
1. Provide `+UVM_TESTNAME=<test>` argument to simulation


## **Regression Tests** ##

### Standalone SystemVerilog Testbench Regression ###
Only tests from the L0 Regression List should be run.
The list is defined in the file [L0_regression.yml](https://github.com/chipsalliance/caliptra-rtl/blob/main/src/integration/stimulus/L0_regression.yml)

### UVM Regression ###
The UVM simulation environment for `caliptra_top` uses a special set of validation firmware to generate stimulus as required for the test plan. This firmware suite is found in `src/integration/test_suites` and includes:
 - `caliptra_top`: A C-based program that emulates a minimal set of bringup functions similar to the function of the ROM. This C file transitions very early to either a the FMC image or Runtime image based on bringup (reset reason) conditions.
 - `caliptra_fmc`: A C-based program that emulates the functionality of the First Mutable Code. In this reduced-functionality validation implementation, the FMC code is a simple intermediary that runs from ICCM and serves to boot the Runtime Firmware.
 - `caliptra_rt`: A C-based program that emulates the functionality of the production Runtime code. This program receives and services interrupts, defines a minimal Non-Maskable Interrupt handler, generates FW resets as needed, processes mailbox commands (generated through the UVM validation test plan), and runs some baseline Watchdog Timer testing.

These three programs are designed to be run within the context of a UVM simulation, and will fail to generate meaningful stimulus in the standalone `caliptra_top_tb` test.

## **NOTES** ##

* Register documentation is auto-rendered at the GitHub page
  * [v2.1 internal registers](https://chipsalliance.github.io/caliptra-rtl/main/internal-regs)
  * [v2.1 external registers](https://chipsalliance.github.io/caliptra-rtl/main/external-regs)
  * [v2.0 internal registers](https://chipsalliance.github.io/caliptra-rtl/v2_0/internal-regs)
  * [v2.0 external registers](https://chipsalliance.github.io/caliptra-rtl/v2_0/external-regs)
  * [v1.1 internal registers](https://chipsalliance.github.io/caliptra-rtl/v1_1/internal-regs)
  * [v1.1 external registers](https://chipsalliance.github.io/caliptra-rtl/v1_1/external-regs)
