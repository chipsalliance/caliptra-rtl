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

while [ ! -z "$1" ]; do
    if [[ "$1" == "--help" ]] || [[ "$1" == "-h" ]]; then
        show_usage 
    #elif [[ "$1" == "-i" ]] || [[ "$1" == "--insertHeader"]]; then
    #    insHeader=1
    #    shift
    fi
    shift
done

if [[ $(command -v pb) = "" ]]; then
    echo "Enter Caliptra workspace (to make Playbook available) and try again"
    exit 1
fi
if [[ $(basename ${PWD}) != "Caliptra" ]]; then
    echo "Must run script from root of Caliptra repository (i.e. <workspace_name>/Caliptra)"
    exit 1
fi

files_missing_header=$(grep -r -L -i  --exclude-dir={uvmf*,.git,cmark,caliptra_reg_html,caliptra_top_reg_html,sha256,sha512,sha512_masked,doe,aes_secworks,fw_test_*,__pycache__,templates} --exclude=*.{tcl,txt,js,htm,html,json,vf,yml,woff,rsp,rdl,bashrc,waiver,cfg,hex,rc,exe,pdf,hvp,log} --exclude=*_reg*.{sv,rdl} --exclude=*_csr*.* --exclude={sglint_waivers,.git-comodules,.gitignore,spyglass_lint.policy,ascent.ctl} --exclude=c_sample.c Apache)

if [[ $files_missing_header != "" ]]; then
    echo -e "\n\n\tPlease add Apache license header to the following files and try again. \n"
    for file in $files_missing_header; do
        echo -e "\t\e[1;31m $file \e[0m\n"
    done
    exit 1
fi


