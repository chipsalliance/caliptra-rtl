# Tcl do file for compile of mbox_sram interface

# pragma uvmf custom additional begin
# pragma uvmf custom additional end


vlog -sv -timescale 1ps/1ps -suppress 2223,2286 +incdir+$env(UVMF_VIP_LIBRARY_HOME)/interface_packages/mbox_sram_pkg \
  -F $env(UVMF_VIP_LIBRARY_HOME)/interface_packages/mbox_sram_pkg/mbox_sram_filelist_hdl.f

vlog -sv -timescale 1ps/1ps -suppress 2223,2286 +incdir+$env(UVMF_VIP_LIBRARY_HOME)/interface_packages/mbox_sram_pkg \
  -F $env(UVMF_VIP_LIBRARY_HOME)/interface_packages/mbox_sram_pkg/mbox_sram_filelist_hvl.f

vlog -sv -timescale 1ps/1ps -suppress 2223,2286 +incdir+$env(UVMF_VIP_LIBRARY_HOME)/interface_packages/mbox_sram_pkg \
  -F $env(UVMF_VIP_LIBRARY_HOME)/interface_packages/mbox_sram_pkg/mbox_sram_filelist_xrtl.f