
// UVM
+incdir+${UVM_HOME}/src
${UVM_HOME}/src/uvm_pkg.sv

// Common UVMF files
-f ${UVMF_HOME}/common/common_sve.f

// BFM Files
-F ${UVMF_VIP_LIBRARY_HOME}/interface_packages/soc_ifc_ctrl_pkg/soc_ifc_ctrl_pkg_sve.F
-F ${UVMF_VIP_LIBRARY_HOME}/interface_packages/cptra_ctrl_pkg/cptra_ctrl_pkg_sve.F
-F ${UVMF_VIP_LIBRARY_HOME}/interface_packages/soc_ifc_status_pkg/soc_ifc_status_pkg_sve.F
-F ${UVMF_VIP_LIBRARY_HOME}/interface_packages/cptra_status_pkg/cptra_status_pkg_sve.F

// Environment Files
-F ${UVMF_VIP_LIBRARY_HOME}/environment_packages/caliptra_top_env_pkg/caliptra_top_env_pkg_sve.F

// Bench Files
+incdir+./tb/tests
./tb/tests/caliptra_top_tests_pkg.sv

+incdir+./tb/sequences
./tb/sequences/caliptra_top_sequences_pkg.sv

+incdir+./tb/parameters
./tb/parameters/caliptra_top_parameters_pkg.sv

./tb/testbench/hdl_top.sv
./tb/testbench/hvl_top.sv

