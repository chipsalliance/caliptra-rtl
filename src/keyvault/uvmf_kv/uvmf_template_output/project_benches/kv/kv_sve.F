
// UVM
+incdir+${UVM_HOME}/src
${UVM_HOME}/src/uvm_pkg.sv

// Common UVMF files
-f ${UVMF_HOME}/common/common_sve.f

// BFM Files
-F ${UVMF_VIP_LIBRARY_HOME}/interface_packages/kv_rst_pkg/kv_rst_pkg_sve.F
-F ${UVMF_VIP_LIBRARY_HOME}/interface_packages/kv_write_pkg/kv_write_pkg_sve.F
-F ${UVMF_VIP_LIBRARY_HOME}/interface_packages/kv_read_pkg/kv_read_pkg_sve.F

// Environment Files
-F ${UVMF_VIP_LIBRARY_HOME}/environment_packages/kv_env_pkg/kv_env_pkg_sve.F

// Bench Files
+incdir+./tb/tests
./tb/tests/kv_tests_pkg.sv

+incdir+./tb/sequences
./tb/sequences/kv_sequences_pkg.sv

+incdir+./tb/parameters
./tb/parameters/kv_parameters_pkg.sv

./tb/testbench/hdl_top.sv
./tb/testbench/hvl_top.sv

