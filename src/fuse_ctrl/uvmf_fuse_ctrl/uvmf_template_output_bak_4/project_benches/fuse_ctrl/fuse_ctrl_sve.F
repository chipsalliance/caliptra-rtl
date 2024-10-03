
// UVM
+incdir+${UVM_HOME}/src
${UVM_HOME}/src/uvm_pkg.sv

// Common UVMF files
-f ${UVMF_HOME}/common/common_sve.f

// BFM Files
-F ${UVMF_VIP_LIBRARY_HOME}/interface_packages/fuse_ctrl_rst_in_pkg/fuse_ctrl_rst_in_pkg_sve.F
-F ${UVMF_VIP_LIBRARY_HOME}/interface_packages/fuse_ctrl_rst_out_pkg/fuse_ctrl_rst_out_pkg_sve.F
-F ${UVMF_VIP_LIBRARY_HOME}/interface_packages/fuse_ctrl_core_axi_write_in_pkg/fuse_ctrl_core_axi_write_in_pkg_sve.F
-F ${UVMF_VIP_LIBRARY_HOME}/interface_packages/fuse_ctrl_core_axi_write_out_pkg/fuse_ctrl_core_axi_write_out_pkg_sve.F
-F ${UVMF_VIP_LIBRARY_HOME}/interface_packages/fuse_ctrl_prim_axi_write_in_pkg/fuse_ctrl_prim_axi_write_in_pkg_sve.F
-F ${UVMF_VIP_LIBRARY_HOME}/interface_packages/fuse_ctrl_prim_axi_write_out_pkg/fuse_ctrl_prim_axi_write_out_pkg_sve.F
-F ${UVMF_VIP_LIBRARY_HOME}/interface_packages/fuse_ctrl_core_axi_read_in_pkg/fuse_ctrl_core_axi_read_in_pkg_sve.F
-F ${UVMF_VIP_LIBRARY_HOME}/interface_packages/fuse_ctrl_core_axi_read_out_pkg/fuse_ctrl_core_axi_read_out_pkg_sve.F
-F ${UVMF_VIP_LIBRARY_HOME}/interface_packages/fuse_ctrl_prim_axi_read_in_pkg/fuse_ctrl_prim_axi_read_in_pkg_sve.F
-F ${UVMF_VIP_LIBRARY_HOME}/interface_packages/fuse_ctrl_prim_axi_read_out_pkg/fuse_ctrl_prim_axi_read_out_pkg_sve.F
-F ${UVMF_VIP_LIBRARY_HOME}/interface_packages/fuse_ctrl_secreg_axi_read_in_pkg/fuse_ctrl_secreg_axi_read_in_pkg_sve.F
-F ${UVMF_VIP_LIBRARY_HOME}/interface_packages/fuse_ctrl_secreg_axi_read_out_pkg/fuse_ctrl_secreg_axi_read_out_pkg_sve.F
-F ${UVMF_VIP_LIBRARY_HOME}/interface_packages/fuse_ctrl_lc_otp_in_pkg/fuse_ctrl_lc_otp_in_pkg_sve.F
-F ${UVMF_VIP_LIBRARY_HOME}/interface_packages/fuse_ctrl_lc_otp_out_pkg/fuse_ctrl_lc_otp_out_pkg_sve.F
-F ${UVMF_VIP_LIBRARY_HOME}/interface_packages/fuse_ctrl_in_pkg/fuse_ctrl_in_pkg_sve.F
-F ${UVMF_VIP_LIBRARY_HOME}/interface_packages/fuse_ctrl_out_pkg/fuse_ctrl_out_pkg_sve.F

// Environment Files
-F ${UVMF_VIP_LIBRARY_HOME}/environment_packages/fuse_ctrl_env_pkg/fuse_ctrl_env_pkg_sve.F

// Bench Files
+incdir+./tb/tests
./tb/tests/fuse_ctrl_tests_pkg.sv

+incdir+./tb/sequences
./tb/sequences/fuse_ctrl_sequences_pkg.sv

+incdir+./tb/parameters
./tb/parameters/fuse_ctrl_parameters_pkg.sv

./tb/testbench/hdl_top.sv
./tb/testbench/hvl_top.sv

