#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# 
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
# http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#

function show_usage() {
    printf "Usage: $0 [optional [parameters]]\n"
    printf "\n"
    printf "Options:\n"
    printf " -i|--insertHeader\tInsert license header in files missing it (Currently unavailable) \n"
    printf " -h|--help\tShow usage information\n"

    return 0
}

set -euo pipefail

apacheLicenseHeader="# SPDX-License-Identifier: Apache-2.0
# 
#
# Licensed under the Apache License, Version 2.0 (the \"License\");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
# http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an \"AS IS\" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License."

apacheLicenseHeader_v_c="//********************************************************************************
// SPDX-License-Identifier: Apache-2.0
// Copyright 2020 Western Digital Corporation or its affiliates.
//
// Licensed under the Apache License, Version 2.0 (the \"License\");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an \"AS IS\" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//********************************************************************************"

while [[ ! -z "${1:+empty}" ]]; do
    if [[ "$1" == "--help" ]] || [[ "$1" == "-h" ]]; then
        show_usage 
    #elif [[ "$1" == "-i" ]] || [[ "$1" == "--insertHeader"]]; then
    #    insHeader=1
    #    shift
    fi
    shift
done

if [[ -z ${CALIPTRA_ROOT:+"empty"} ]]; then
    echo "Must set CALIPTRA_ROOT prior to running script"
    exit 1
fi

exclude_dir='{uvmf*,.git,cmark,caliptra_reg_html,caliptra_top_reg_html,sha256,sha512,sha512_masked,doe,fw_test_*,__pycache__,templates,docs}'
exclude_suffix='*.{tcl,txt,js,htm,html,json,vf,yml,woff,rsp,rdl,bashrc,waiver,cfg,hex,rc,exe,pdf,png,hvp,svg,log}'
exclude_regs='*_reg*.{sv,rdl}'
exclude_csr='*_csr*.*'
exclude_file='{sglint_waivers,pr_hash,pr_timestamp,.git-comodules,.gitignore,spyglass_lint.policy,ascent.ctl,clp_mapfile,readme.md,README.md,SECURITY.md,c_sample.c}'
apache_patn='Licensed under the Apache License'

# Recursive find through repository with some major exclusions
# 'eval' is used to expand exclude vars into a usable glob pattern
files_missing_header=$(eval grep -r -L -i  --exclude-dir=${exclude_dir} --exclude=${exclude_suffix} --exclude=${exclude_regs} --exclude=${exclude_csr} --exclude=${exclude_file} \"${apache_patn}\" "${CALIPTRA_ROOT}")

# After excluding some crypto directories, re-scan specific directories therein
# (can't specificy exclude-dir using '<patn>/<patn>' to catch nested directories)
files_missing_header="${files_missing_header:+$files_missing_header }$(eval grep -r -L -i  --exclude-dir={rtl,uvmf_*} --exclude={aes_tb.v,doe_tb.v,sha256_tb.v} --exclude=${exclude_suffix} --exclude=${exclude_regs} --exclude=${exclude_csr} --exclude=${exclude_file} \"${apache_patn}\" \"${CALIPTRA_ROOT}/src/sha256\" \"${CALIPTRA_ROOT}/src/sha512\" \"${CALIPTRA_ROOT}/src/sha512_masked\" \"${CALIPTRA_ROOT}/src/doe\")"

if [[ $files_missing_header != "" ]]; then
    echo -e "\n\n\tPlease add Apache license header to the following files and try again. \n"
    for file in $files_missing_header; do
        echo -e "\t\e[1;31m $file \e[0m\n"
    done
    exit 1
fi
echo "Apache license header check completed successfully"
