
// UVM
+incdir+${UVM_HOME}/src
${UVM_HOME}/src/uvm_pkg.sv

// Common UVMF files
-f ${UVMF_HOME}/common/common_sve.f

// BFM Files
-F ${UVMF_VIP_LIBRARY_HOME}/interface_packages/HMAC256_rst_pkg/HMAC256_rst_pkg_sve.F

// Environment Files
-F ${UVMF_VIP_LIBRARY_HOME}/environment_packages/HMAC256_env_pkg/HMAC256_env_pkg_sve.F

// Bench Files
+incdir+./tb/tests
./tb/tests/HMAC256_tests_pkg.sv

+incdir+./tb/sequences
./tb/sequences/HMAC256_sequences_pkg.sv

+incdir+./tb/parameters
./tb/parameters/HMAC256_parameters_pkg.sv

./tb/testbench/hdl_top.sv
./tb/testbench/hvl_top.sv

