# Tcl do file for compile of core_axi_write_out_if interface

# pragma uvmf custom additional begin
# pragma uvmf custom additional end


vlog -sv -timescale 1ps/1ps -suppress 2223,2286 +incdir+$env(UVMF_VIP_LIBRARY_HOME)/interface_packages/core_axi_write_out_if_pkg \
  -F $env(UVMF_VIP_LIBRARY_HOME)/interface_packages/core_axi_write_out_if_pkg/core_axi_write_out_if_filelist_hdl.f

vlog -sv -timescale 1ps/1ps -suppress 2223,2286 +incdir+$env(UVMF_VIP_LIBRARY_HOME)/interface_packages/core_axi_write_out_if_pkg \
  -F $env(UVMF_VIP_LIBRARY_HOME)/interface_packages/core_axi_write_out_if_pkg/core_axi_write_out_if_filelist_hvl.f

vlog -sv -timescale 1ps/1ps -suppress 2223,2286 +incdir+$env(UVMF_VIP_LIBRARY_HOME)/interface_packages/core_axi_write_out_if_pkg \
  -F $env(UVMF_VIP_LIBRARY_HOME)/interface_packages/core_axi_write_out_if_pkg/core_axi_write_out_if_filelist_xrtl.f