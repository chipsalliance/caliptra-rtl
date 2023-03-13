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
if [[ $(command -v pb) = "" ]]; then
    echo "Enter Caliptra workspace (to make Playbook available) and try again"
    exit 1
fi
if [[ $(basename ${PWD}) != "Caliptra" ]]; then
    echo "Must run script from root of Caliptra repository (i.e. <workspace_name>/Caliptra)"
    exit 1
fi
cpt_ymls=$(grep '^\s*\- src' ./config/compilespecs.yml | sed 's/^\s*- \(src.*\)/\1/')
for i in ${cpt_ymls}; do
    cpt_dir=$(sed 's/src\/\(.\+\)\/config\/.*/\1/' <<< ${i})
    if [[ $i = *"uvmf"* ]]; then continue; fi
    cpt_libs=$(grep '^\s*provides' ${i} | sed 's/.*\[\(\w\+\)\].*/\1/')
    for j in ${cpt_libs}; do
        cpt_vf_file=src/${cpt_dir}/config/${j}.vf
        # Skip UVM file lists, which reference installed libraries external to Caliptra repo
        if [[ $j == "uvmf_lib" || $j == "uvm_lib" || $j == "mvc_lib" ]]; then continue; fi
        echo "Generating File List for lib [${j}] in [${cpt_vf_file}]";
        pb fe file_list --tb integration_lib::${j} +def-target 'tb' --flat --dir-fmt=+incdir+{directory} --file ${cpt_vf_file};
        # Replace leading portion of path with ${CALIPTRA_ROOT}
        sed 's/\/home.*Caliptra\/src/\${CALIPTRA_ROOT}\/src/' -i ${cpt_vf_file}
        # Remove duplicate entries from the file
        perl -i -ne 'print if ! $a{$_}++' ${cpt_vf_file}
    done
done
