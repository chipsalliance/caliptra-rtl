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
function gen_pb_file_list {
    local cpt_vf_file;
    local cpt_dir;
    local cpt_lib;

    cpt_dir=$1;
    cpt_lib=$2;
    cpt_vf_file=src/${cpt_dir}/config/${cpt_lib}.vf

    # Skip UVM file lists, which reference installed libraries external to Caliptra repo
    if [[ $cpt_lib = *"coverage" ]]; then return; fi
    echo "Generating File List for lib [${cpt_lib}] in [${cpt_vf_file}]";
    pb fe file_list --tb integration_lib::${cpt_lib} +def-target 'tb' --flat --dir-fmt=+incdir+{directory} --file ${cpt_vf_file};
    # Replace leading portion of Caliptra source paths with ${CALIPTRA_ROOT}
    sed 's,/home.*Caliptra/src,\${CALIPTRA_ROOT}/src,' -i ${cpt_vf_file}
    # Replace leading portion of UVM/installed library paths with appropriate ENV VAR
    sed 's,/home/cad/tools/mentor/questa/[0-9\._]*/questasim/verilog_src/uvm-[^/]\+,\${UVM_HOME},' -i ${cpt_vf_file}
    sed 's,/home/cad/tools/mentor/uvmf/UVMF_[0-9\.]*,\${UVMF_HOME},' -i ${cpt_vf_file}
    sed 's,/home/cad/tools/mentor/questa_vip/[0-9\.]*,\${QUESTA_MVC_HOME},' -i ${cpt_vf_file}
    # Remove duplicate entries and empty lines from the file
    perl -i -ne 'print if ! $a{$_}++ and /\S/' ${cpt_vf_file}
}

if [[ $(command -v pb) = "" ]]; then
    echo "Enter Caliptra workspace (to make Playbook available) and try again"
    exit 1
fi
if [[ ${PWD} != ${CALIPTRA_ROOT} ]]; then
    echo "Must run script from root of Caliptra repository (i.e. ${CALIPTRA_ROOT})"
    exit 1
fi
cpt_ymls=$(grep '^\s*\- src' ./config/compilespecs.yml | sed 's/^\s*- \(src.*\)/\1/')
declare -A procs;
for i in ${cpt_ymls}; do
    cpt_dir=$(sed 's,src/\(.\+\)/config/.*,\1,' <<< ${i})
    cpt_libs=$(grep '^\s*provides' ${i} | sed 's/.*\[\(\w\+\)\].*/\1/')
    for j in ${cpt_libs}; do
        gen_pb_file_list ${cpt_dir} ${j} &
        procs["$i_$j"]=$!
    done
done
echo "waiting for ${procs[@]}"
wait ${procs[@]}
