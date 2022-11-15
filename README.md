
# **Caliptra Hands-On Guide** #
_*Last Update: 2022/11/14*_

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

Synthesis:
 - Synopsys DC
   - `Version 2020.09-SP1`

GCC:
 - `riscv64-unknown-elf-gcc-8.2.0-2019.02.0-x86_64-linux-centos6`

Other:
 - Playbook (Microsoft Internal workflow management tool)

## **ENVIRONMENT VARIABLES** ##
`WORKSPACE`: Defines the absolute path to the directory that contains the Project repository root (called "Caliptra")

Required for Firmware (i.e. Test suites) makefile:<BR>
  `SIM_TOOLS_TOP_COMPILE_ROOT`: Absolute path pointing to the folder `src/integration` inside the repository<BR>
  `TESTNAME`: Contains the name of one of the tests listed inside the `src/integration/test_suites` folder<BR>

## **Repository Overview** ##
```
Caliptra
|-- LICENSE
|-- README.md
|-- VERSION.txt
|-- Release_notes.txt
|-- Coming_soon.txt
|-- src
|   |-- ahb_lite_bus
|   |-- doe
|   |-- ecc
|   |-- hmac
|   |-- hmac_drbg
|   |-- integration
|   |-- keyvault
|   |-- libs
|   |-- riscv_core
|   |-- sha256
|   |-- sha512
|   |-- soc_ifc
`-- tools
    |-- config
    |-- README
    `-- scripts
```
The root of the repository is structured as shown above, to a depth of 2 layers.<BR>
Each sub-component is accompanied by a file list summary (located in src/<component>/config/<name>.vf) that comprises all the filenames required to compile the component, and an optional testbench filelist for unit-level simulation. <BR>
VF files provide absolute filepaths (prefixed by the WORKSPACE environment variable) to each compile target for the associated component.<BR>
The "Integration" sub-component contains the top-level fileset for Caliptra. `src/integration/config/compile.yml` defines the required filesets and sub-component dependencies for this build target. All of the files/dependencies are explicitly listed in `src/integration/config/caliptra_top_tb.vf`. Users may compile the entire design using only this VF filelist.<BR>


## **Scripts Description** ##

`Makefile`: Makefile to generate SRAM initialization files from test firmware<BR>
`run_test_makefile`: Wrapper used in Microsoft internal build flow to invoke Makefile<BR>
`reg_gen.py`: Used to compile/export RDL files to register source code<BR>
`reg_gen.sh`: Wrapper used to call `reg_gen.py` for all IP cores in Caliptra<BR>
`reg_doc_gen.py`: Used to compile/export top-level RDL address map to register source code, defining complete Caliptra address space, and produces HTML documentation<BR>
`reg_doc_gen.sh`: Wrapper to invoke `reg_doc_gen.py`<BR>
`integration_vector_gen.py`: Generates test vectors for crypto core tests<BR>
`swerv_build_command.sh`: Shell script used to generate the SweRV-EL2 repository present in `src/riscv_core/swerv_el2`<BR>

## **Simulation Flow** ##
Steps:
1. Setup tools, add to PATH (ensure riscv64-unknown-elf-gcc is also available)
1. Define all environment variables above
1. Create a run folder for build outputs (and cd to it)
1. Invoke `${WORKSPACE}/Caliptra/tools/scripts/Makefile` with target 'program.hex' to produce SRAM initialization files from the firmware found in `src/integration/test_suites/${TESTNAME}`
     - E.g.: `make -f ${WORKSPACE}/Caliptra/tools/scripts/Makefile program.hex`
1. Compile complete project using `src/integration/config/caliptra_top_tb.vf` as a compilation target in VCS. When running the `vcs` command to generate simv, users should ensure that `caliptra_top_tb` is explicitly specified as the top-level component in their command to ensure this is the sole "top" that gets simulated.
1. Simulate project with `caliptra_top_tb` as the top target

## **NOTES** ##
