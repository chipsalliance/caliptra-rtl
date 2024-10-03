// UVM
+incdir+${UVM_HOME}/src
${UVM_HOME}/src/uvm_pkg.sv

// Common UVMF files
-f ${UVMF_HOME}/common/common_sve.f

+incdir+.
-f ${UVMF_VIP_LIBRARY_HOME}/interface_packages/fuse_ctrl_core_axi_write_out_pkg/fuse_ctrl_core_axi_write_out_filelist_hdl.f
-f ${UVMF_VIP_LIBRARY_HOME}/interface_packages/fuse_ctrl_core_axi_write_out_pkg/fuse_ctrl_core_axi_write_out_filelist_hvl.f
