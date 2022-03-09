root="$( readlink -m $( dirname $( dirname "${BASH_SOURCE[0]}" ) ) )"
export DEFAULT_REGISTRY=cpscontainers.azurecr.io
export ADO_URL=$(cd ${root}; git remote get-url origin | sed 's#git@ssh.#https://#' | sed 's#:v3##' | xargs -Ivvv dirname vvv | sed 's#/_git$##')
export LM_PROJECT=tsd.blueridge.frontend
export INTEGRATION_LIB="${root}"			#Can rename it to "integration". Please update the var, based on location of this repo in the WS.
