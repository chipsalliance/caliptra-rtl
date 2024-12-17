root="$( readlink -m $( dirname $( dirname "${BASH_SOURCE[0]}" ) ) )"
export DEFAULT_REGISTRY=cpscontainers.azurecr.io
export ADO_URL=$(cd ${root}; git remote get-url origin | sed 's#git@ssh.#https://#' | sed 's#:v3##' | xargs -Ivvv dirname vvv | sed 's#/_git$##')
export LM_PROJECT=tsd.blueridge.frontend
export INTEGRATION_LIB="${root}"			#Can rename it to "integration". Please update the var, based on location of this repo in the WS.
export MSFT_TOOLS="${root}/tools"
export MSFT_SCRIPTS_DIR=${MSFT_TOOLS}/scripts
export RISC64_GCC_HOME=/home/noncad/riscv-gnu/2023.04.29
export PATH=${RISC64_GCC_HOME}/bin:${PATH}
export MSFT_REPO_ROOT=${root}
export TOOLS=${MSFT_TOOLS}

export CHIPS=${WORKSPACE}/chipsalliance

export CALIPTRA_WORKSPACE=${CHIPS}
export CALIPTRA_ROOT=${CALIPTRA_WORKSPACE}/caliptra-rtl
export CALIPTRA_TOOLS="${CALIPTRA_ROOT}/tools"
export CALIPTRA_SCRIPTS_DIR=${CALIPTRA_TOOLS}/scripts

# Points to submodule - but build flows should use relative file paths in a caliptra-rtl context.
export ADAMSBRIDGE_SUBMODULE=${CALIPTRA_ROOT}/submodules/adams-bridge
# Env variable that points to adams-bridge repo comodule, for standalone tests and regressions
# variable is publicly visible, but should not be used in a caliptra-rtl context (use submodules/local
# relative file paths instead)
export ADAMSBRIDGE_ROOT=${CHIPS}/adams-bridge


export CALIPTRA_SS=${CHIPS}/caliptra-ss
export CALIPTRA_SS_TOOLS=${CALIPTRA_SS}/tools
export CALIPTRA_SS_SCRIPTS_DIR=${CALIPTRA_SS_TOOLS}/scripts

export I3C_ROOT=${CALIPTRA_SS}/third_party/i3c-core

export UVM_HOME=/home/cad/tools/mentor/questa/2022.2_1/questasim/verilog_src/uvm-1.1d
export UVMF_HOME=/home/cad/tools/mentor/uvmf/UVMF_2022.3
export AVERY_HOME=/cad/tools/mentor/avery/2023.2
export AVERY_AXI=${AVERY_HOME}/axixactor-2.1e.230314
export AVERY_PLI=/cad/tools/mentor/avery/2.5c/avery_pli-2023_0609
