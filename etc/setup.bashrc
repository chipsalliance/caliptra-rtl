root="$( readlink -m $( dirname $( dirname "${BASH_SOURCE[0]}" ) ) )"
export DEFAULT_REGISTRY=cpscontainers.azurecr.io
export ADO_URL=$(cd ${root}; git remote get-url origin | sed 's#git@ssh.#https://#' | sed 's#:v3##' | xargs -Ivvv dirname vvv | sed 's#/_git$##')
export LM_PROJECT=tsd.blueridge.frontend
export INTEGRATION_LIB="${root}"			#Can rename it to "integration". Please update the var, based on location of this repo in the WS.
export TOOLS="${root}/tools"
export RISC64_GCC_HOME=/home/fortressver/hardware/cores/antifortress/sifive/riscv64-unknown-elf-gcc-8.2.0-2019.02.0-x86_64-linux-centos6
export PATH=${RISC64_GCC_HOME}/bin:${PATH}
export AHA_POC_REPO=${root}
export SCRIPTS_DIR=${TOOLS}/scripts


