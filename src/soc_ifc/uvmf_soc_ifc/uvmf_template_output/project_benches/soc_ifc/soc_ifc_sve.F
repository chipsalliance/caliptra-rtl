
// UVM
+incdir+${UVM_HOME}/src
${UVM_HOME}/src/uvm_pkg.sv

// Common UVMF files
${UVMF_HOME}/uvmf_base_pkg/uvmf_base_pkg_hdl.sv
-f ${UVMF_HOME}/common/common_sve.f

// BFM Files
-F ${UVMF_VIP_LIBRARY_HOME}/interface_packages/soc_ifc_ctrl_pkg/soc_ifc_ctrl_pkg_sve.F
-F ${UVMF_VIP_LIBRARY_HOME}/interface_packages/cptra_ctrl_pkg/cptra_ctrl_pkg_sve.F
-F ${UVMF_VIP_LIBRARY_HOME}/interface_packages/soc_ifc_status_pkg/soc_ifc_status_pkg_sve.F
-F ${UVMF_VIP_LIBRARY_HOME}/interface_packages/cptra_status_pkg/cptra_status_pkg_sve.F
-F ${UVMF_VIP_LIBRARY_HOME}/interface_packages/mbox_sram_pkg/mbox_sram_pkg_sve.F

// Environment Files
-F ${UVMF_VIP_LIBRARY_HOME}/environment_packages/soc_ifc_env_pkg/soc_ifc_env_pkg_sve.F

// Bench Files
+incdir+./tb/tests
./tb/tests/soc_ifc_tests_pkg.sv

+incdir+./tb/sequences
./tb/sequences/soc_ifc_sequences_pkg.sv

+incdir+./tb/parameters
./tb/parameters/soc_ifc_parameters_pkg.sv

./tb/testbench/hdl_top.sv
./tb/testbench/hvl_top.sv

