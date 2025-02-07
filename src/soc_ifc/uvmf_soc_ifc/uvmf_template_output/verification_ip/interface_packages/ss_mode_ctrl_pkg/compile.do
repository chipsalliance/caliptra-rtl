# Tcl do file for compile of ss_mode_ctrl interface

# pragma uvmf custom additional begin
# pragma uvmf custom additional end


vlog -sv -timescale 1ps/1ps -suppress 2223,2286 +incdir+$env(UVMF_VIP_LIBRARY_HOME)/interface_packages/ss_mode_ctrl_pkg \
  -F $env(UVMF_VIP_LIBRARY_HOME)/interface_packages/ss_mode_ctrl_pkg/ss_mode_ctrl_filelist_hdl.f

vlog -sv -timescale 1ps/1ps -suppress 2223,2286 +incdir+$env(UVMF_VIP_LIBRARY_HOME)/interface_packages/ss_mode_ctrl_pkg \
  -F $env(UVMF_VIP_LIBRARY_HOME)/interface_packages/ss_mode_ctrl_pkg/ss_mode_ctrl_filelist_hvl.f

vlog -sv -timescale 1ps/1ps -suppress 2223,2286 +incdir+$env(UVMF_VIP_LIBRARY_HOME)/interface_packages/ss_mode_ctrl_pkg \
  -F $env(UVMF_VIP_LIBRARY_HOME)/interface_packages/ss_mode_ctrl_pkg/ss_mode_ctrl_filelist_xrtl.f