# Tcl do file for compile of caliptra_top interface

# pragma uvmf custom additional begin
# pragma uvmf custom additional end


# Include build for sub-environment soc_ifc_env_pkg
quietly set cmd [format "source %s/environment_packages/soc_ifc_env_pkg/compile.do" $env(UVMF_VIP_LIBRARY_HOME)]
eval $cmd

quietly set cmd [format "vlog -timescale 1ps/1ps +incdir+%s/environment_packages/caliptra_top_env_pkg" $env(UVMF_VIP_LIBRARY_HOME)]
quietly set cmd [format "%s %s/environment_packages/caliptra_top_env_pkg/caliptra_top_env_pkg.sv" $cmd $env(UVMF_VIP_LIBRARY_HOME)]
eval $cmd


