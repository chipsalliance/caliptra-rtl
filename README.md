
# **Caliptra Hands-On Guide** #

[[_TOC_]]

## **Tools Used** ##

OS:
 - Build instructions assume a Linux environment

Lint:
 - Synopsys Spyglass
   - Version S-2021.09-1
 - Real Intent AscentLint
   - Version 2019.A.p15 for RHEL 6.0-64, Rev 116515, Built On 12/18/2020

Simulation:
 - Synopsys VCS with Verdi
   - Version R-2020.12-SP2-7_Full64

Synthesis:
 - Synopsys DC
   - Version 2020.09-SP1

GCC:
 - riscv64-unknown-elf-gcc-8.2.0-2019.02.0-x86_64-linux-centos6

Other:
 - Playbook (Microsoft Internal workflow management tool)

## **ENVIRONMENT VARIABLES** ##
`WORKSPACE`: Defines the absolute path to the directory that contains the Project repository root (called "Caliptra")

Required for Firmware (i.e. Test suites) makefile:<BR>
  `COMPILE_ROOT`: Absolute path pointing to the folder "src/integration" inside the repository<BR>
  `TESTNAME`: Contains the name of one of the tests listed inside the `src/integration/test_suites` folder<BR>

## **Repository Overview** ##
```
Caliptra
|-- config
|   |-- compilespecs.yml
|   |-- pb_cmd_config_local
|   `-- repo_config.json
|-- etc
|   |-- eda.bashrc
|   |-- pipelines
|   `-- setup.bashrc
|-- LICENSE
|-- README.md
|-- SCA
|   |-- Caliptra_ECDSA_project
|   |-- Caliptra_ECDSA_project_sign
|   |-- Caliptra_masked_arith
|   `-- common_python_scripts
|-- src
|   |-- aes
|   |-- ahb_lite_bus
|   |-- ecc
|   |-- hmac
|   |-- hmac_drbg
|   |-- integration
|   |-- keyvault
|   |-- libs
|   |-- mbox
|   |-- riscv_core
|   |-- sha256
|   |-- sha512
|   |-- sim_irq_gen
|   `-- syn
`-- tools
    |-- config
    |-- README
    `-- scripts
```
The root of the repository is structured as shown above, to a depth of 2 layers.<BR>
config/compilespecs.yml contains a tree of named sub-components in the system that will be built using the Playbook workflow.<BR>
Each sub-component is associated with its own yaml file (located in src/<component>/config/compile.yml. Each of the compile.yml files defines a file list required to compile the component, and an optional testbench filelist for standalone simulation. <BR>
Alongside each of the compile.yml files is a set of raw filelist files (.vf extension). VF files provide absolute filepaths (prefixed by the WORKSPACE environment variable) to each compile target for the associated component.<BR>
The "Integration" sub-component contains the top-level fileset for Caliptra. `src/integration/config/compile.yml` defines the required filesets and sub-component dependencies for this build target. All of the files/dependencies are explicitly listed in `src/integration/config/caliptra_top_tb.vf`. Users may compile the entire design using only this filelist.<BR>
`etc/` provides a set of configuration files that are used to initialize a terminal session for project build commands.<BR>


## **Scripts Description** ##

`Makefile`: Makefile to generate SRAM initialization files from test firmware<BR>
`gen_pb_file_lists.sh`: Internally used by Microsoft to generate project filelists (.vf)<BR>
`reg_gen.py`: Used to compile/export RDL files to register source code<BR>
`run_test_makefile`: Wrapper used in Microsoft Playbook to invoke Makefile<BR>
`sim_config_parse.py`: Internal tool to extract generated yaml configuration file for simulation<BR>
`swerv_build_command.sh`: Shell script used to generate the SweRV-EL2 repository present in `src/riscv_core/swerv_el2`<BR>
`syn/dc.tcl`: Synopsys DC compile script<BR>
`syn/run_syn.py`: Wrapper to invoke dc.tcl<BR>

## **Simulation Flow** ##
Steps:
1. Setup tools, add to PATH (ensure riscv64-unknown-elf-gcc is also available)
1. Define all environment variables above
1. Create a scratch folder for build outputs (and cd to it)
1. Compile complete project using `src/integration/config/caliptra_top_tb.vf` as a compilation target in VCS.
1. Invoke `${WORKSPACE}/Caliptra/tools/scripts/Makefile` with target 'program.hex' to produce SRAM initialization files from the firmware found in `src/integration/test_suites/${TESTNAME}`
1. Simulate project with caliptra_top_tb as the top target

## **NOTES** ##
