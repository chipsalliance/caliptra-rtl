
// UVM
+incdir+${UVM_HOME}/src
${UVM_HOME}/src/uvm_pkg.sv

// Common UVMF files
-f ${UVMF_HOME}/common/common_sve.f

// Sub-Environments
-F ${UVMF_VIP_LIBRARY_HOME}/environment_packages/soc_ifc_env_pkg/soc_ifc_env_pkg_sve.F

+incdir+.
./caliptra_top_env_pkg.sv
