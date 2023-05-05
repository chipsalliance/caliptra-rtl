// UVM
+incdir+${UVM_HOME}/src
${UVM_HOME}/src/uvm_pkg.sv

// Common UVMF files
-f ${UVMF_HOME}/common/common_sve.f

+incdir+.
-f ${UVMF_VIP_LIBRARY_HOME}/interface_packages/kv_rst_pkg/kv_rst_filelist_hdl.f
-f ${UVMF_VIP_LIBRARY_HOME}/interface_packages/kv_rst_pkg/kv_rst_filelist_hvl.f
