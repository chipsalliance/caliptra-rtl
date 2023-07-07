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
_*Last Update: 2023/06/08*_

[[_TOC_]]

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
   - `Version 2021.2.1` of AHB/APB models
 - UVM installation
   - `Version 1.1d`

Synthesis:
 - Synopsys DC
   - `Version 2020.09-SP1`

GCC:
 - RISCV Toolchain for generating memory initialization files
   - `riscv64-unknown-elf-gcc-8.2.0-2019.02.0-x86_64-linux-centos6`
 - G++ Used to compile Verilator objects
   - `g++ (GCC) 8.2.0`

Other:
 - Playbook (Microsoft Internal workflow management tool)

## **ENVIRONMENT VARIABLES** ##
Required for simulation:<BR>
`CALIPTRA_WORKSPACE`: Defines the absolute path to the directory where the Verilator "scratch" output directory will be created. Recommended to define as the absolute path to the directory that contains the Project repository root (called "Caliptra" or "caliptra-rtl")<BR>
`CALIPTRA_ROOT`: Defines the absolute path to the Project repository root (called "Caliptra" or "caliptra-rtl"). Recommended to define as `${CALIPTRA_WORKSPACE}/Caliptra`.<BR>

Required for Firmware (i.e. Test suites) makefile:<BR>
  `TESTNAME`: Contains the name of one of the tests listed inside the `src/integration/test_suites` folder<BR>

## **Repository Overview** ##
```
Caliptra
|-- LICENSE
|-- README.md
|-- Release_notes.txt
|-- docs
|   |-- Caliptra_Integration_Specification.pdf
|   |-- Caliptra_Hardware_Spec.pdf
|   |-- Caliptra_TestPlan_L1.pdf
|-- src
|   |-- aes
|   |-- ahb_lite_bus
|   |-- caliptra_prim
|   |-- caliptra_prim_generic
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
|   |-- pcrvault
|   |-- riscv_core
|   |-- sha256
|   |-- sha512
|   |-- sha512_masked
|   |-- soc_ifc
|   |-- spi_host
|   |-- uart
`-- tools
    |-- config
    |-- README
    `-- scripts
```
The root of the repository is structured as shown above, to a depth of 2 layers.<BR>
Each sub-component is accompanied by a file list summary (located in src/<component>/config/<name>.vf) that comprises all the filenames required to compile the component, and an optional testbench filelist for unit-level simulation. <BR>
VF files provide absolute filepaths (prefixed by the `CALIPTRA_ROOT` environment variable) to each compile target for the associated component.<BR>
The "Integration" sub-component contains the top-level fileset for Caliptra. `src/integration/config/compile.yml` defines the required filesets and sub-component dependencies for this build target. All of the files/dependencies are explicitly listed in `src/integration/config/caliptra_top_tb.vf`. Users may compile the entire design using only this VF filelist.<BR>


## **Scripts Description** ##

`demo.rdl`:Sample RDL file<BR>
`Makefile`: Makefile to generate SRAM initialization files from test firmware and to run Verilator simulation<BR>
`reg_gen.py`: Used to compile/export RDL files to register source code<BR>
`reg_gen.sh`: Wrapper used to call `reg_gen.py` for all IP cores in Caliptra<BR>
`reg_doc_gen.py`: Used to compile/export top-level RDL address map to register source code, defining complete Caliptra address space, and produces HTML documentation<BR>
`reg_doc_gen.sh`: Wrapper to invoke `reg_doc_gen.py`<BR>
`reg_json.py`:Used to import JSON register definition from OpenTitan and generate SystemRDL model<BR>
`rdl_post_process.py`: Post-processing functionality to make RDL generated SystemVerilog files compatible with lint/Verilator requirements<BR>
`run_verilator_l0_regression.py`: Wrapper to run the L0 smoke test regression suite using the Makefile flow in Verilator<BR>
`integration_vector_gen.py`: Generates test vectors for crypto core tests<BR>
`veer_build_command.sh`: Shell script used to generate the VeeR-EL2 repository present in `src/riscv_core/veer_el2`<BR>

## **Simulation Flow** ##

### VCS Steps: ###
1. Setup tools, add to PATH (ensure riscv64-unknown-elf-gcc is also available)
1. Define all environment variables above
    - For the initial test run after downloading repository, `iccm_lock` is recommended for TESTNAME
1. Create a run folder for build outputs (and cd to it)
1. Invoke `${CALIPTRA_ROOT}/tools/scripts/Makefile` with target 'program.hex' to produce SRAM initialization files from the firmware found in `src/integration/test_suites/${TESTNAME}`
    - E.g.: `make -f ${CALIPTRA_ROOT}/tools/scripts/Makefile program.hex`
1. Compile complete project using `src/integration/config/caliptra_top_tb.vf` as a compilation target in VCS. When running the `vcs` command to generate simv, users should ensure that `caliptra_top_tb` is explicitly specified as the top-level component in their command to ensure this is the sole "top" that gets simulated.
1. Simulate project with `caliptra_top_tb` as the top target

### Verilator Steps: ###
1. Setup tools, add to PATH (ensure Verilator, GCC, and riscv64-unknown-elf-gcc are available)
1. Define all environment variables above
    - For the initial test run after downloading repository, `iccm_lock` is recommended for TESTNAME
1. Create a run folder for build outputs
    - Recommended to place run folder under `${CALIPTRA_WORKSPACE}/scratch/$USER/verilator/<date>`
1. Run Caliptra/tools/scripts/Makefile, which provides steps to run a top-level simulation in Verilator
    - Example command:
        `make -C <path/to/run/folder> -f ${CALIPTRA_ROOT}/tools/scripts/Makefile TESTNAME=${TESTNAME} debug=1 verilator`
    - NOTE: `debug=1` is optional; if provided, the verilator run will produce a .vcd file with waveform information
    - NOTE: `TESTNAME=${TESTNAME}` is optional; if not provided, test defaults to value of TESTNAME environment variable, then to `iccm_lock`
    - NOTE: Users may wish to produce a run log by piping the make command to a tee command, e.g.:
        `make ... <args> ... | tee <path/to/run/folder>/verilate.log`
1. Users have the option to run the entire suite of smoke tests using the provided python script `run_verilator_l0_regression.py`
    1. Ensure Python 3.9.2 is available by adding to the $PATH variable
    1. Run the script with:
        `python3 run_verilator_l0_regression.py`
    1. NOTE: The script automatically creates run output folders at `${CALIPTRA_WORKSPACE}/scratch/$USER/verilator/<timestamp>/<testname>` for each test run
    1. NOTE: The output folder is populated with a run log that reports the run results and pass/fail status

### UVM Testbench Steps for `caliptra_top`: <BR>

**Description**:<BR>
The UVM Framework generation tool was used to create the baseline UVM testbench for verification of the top-level Caliptra image. The top-level bench leverages the `soc_ifc_top` testbench as a subenvironment, to reuse environment level sequences, agents, register models, and predictors.

**Prerequisites**:<BR>
- QVIP 2021.2.1 for Mentor Graphics (provides the AHB/APB VIP)
- UVM 1.1d installation

Steps:<BR>
1. Compile UVM 1.1d library
1. Compile the AHB/APB QVIP source
1. Compile the UVMF wrapper for APB/AHB in Caliptra/src/libs/uvmf
1. Compile the `verification_ip` provided for `soc_ifc` found in `Caliptra/src/soc_ifc/uvmf_soc_ifc`
1. Compile the `caliptra_top` testbench found in `Caliptra/src/integration/uvmf_caliptra_top`
1. `Caliptra/src/integration/uvmf_caliptra_top/uvmf_template_output/project_benches/caliptra_top/tb/testbench/hdl_top.sv` is the top-level TB wrapper for the system
1. Select a test to run from the set of tests in `Caliptra/src/integration/uvmf_caliptra_top/uvmf_template_output/project_benches/caliptra_top/tb/tests/src`
1. Provide `+UVM_TESTNAME=<test>` argument to simulation

## **NOTES** ##

* The internal registers are auto rendered at the [GitHub
  page](https://chipsalliance.github.io/caliptra-rtl/main/internal-regs)
* So are the [external registers](https://chipsalliance.github.io/caliptra-rtl/main/external-regs)
