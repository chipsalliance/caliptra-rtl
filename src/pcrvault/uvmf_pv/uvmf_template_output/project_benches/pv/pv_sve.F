
// UVM
+incdir+${UVM_HOME}/src
${UVM_HOME}/src/uvm_pkg.sv

// Common UVMF files
-f ${UVMF_HOME}/common/common_sve.f

// BFM Files
-F ${UVMF_VIP_LIBRARY_HOME}/interface_packages/pv_rst_pkg/pv_rst_pkg_sve.F
-F ${UVMF_VIP_LIBRARY_HOME}/interface_packages/pv_write_pkg/pv_write_pkg_sve.F
-F ${UVMF_VIP_LIBRARY_HOME}/interface_packages/pv_read_pkg/pv_read_pkg_sve.F

// Environment Files
-F ${UVMF_VIP_LIBRARY_HOME}/environment_packages/pv_env_pkg/pv_env_pkg_sve.F

// Bench Files
+incdir+./tb/tests
./tb/tests/pv_tests_pkg.sv

+incdir+./tb/sequences
./tb/sequences/pv_sequences_pkg.sv

+incdir+./tb/parameters
./tb/parameters/pv_parameters_pkg.sv

./tb/testbench/hdl_top.sv
./tb/testbench/hvl_top.sv

