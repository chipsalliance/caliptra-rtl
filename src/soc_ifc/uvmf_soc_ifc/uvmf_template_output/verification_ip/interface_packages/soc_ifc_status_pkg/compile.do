# Tcl do file for compile of soc_ifc_status interface

# pragma uvmf custom additional begin
# pragma uvmf custom additional end


vlog -sv -timescale 1ps/1ps -suppress 2223,2286 +incdir+$env(UVMF_VIP_LIBRARY_HOME)/interface_packages/soc_ifc_status_pkg \
  -F $env(UVMF_VIP_LIBRARY_HOME)/interface_packages/soc_ifc_status_pkg/soc_ifc_status_filelist_hdl.f

vlog -sv -timescale 1ps/1ps -suppress 2223,2286 +incdir+$env(UVMF_VIP_LIBRARY_HOME)/interface_packages/soc_ifc_status_pkg \
  -F $env(UVMF_VIP_LIBRARY_HOME)/interface_packages/soc_ifc_status_pkg/soc_ifc_status_filelist_hvl.f

vlog -sv -timescale 1ps/1ps -suppress 2223,2286 +incdir+$env(UVMF_VIP_LIBRARY_HOME)/interface_packages/soc_ifc_status_pkg \
  -F $env(UVMF_VIP_LIBRARY_HOME)/interface_packages/soc_ifc_status_pkg/soc_ifc_status_filelist_xrtl.f