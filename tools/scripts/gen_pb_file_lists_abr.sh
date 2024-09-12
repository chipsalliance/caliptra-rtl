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
    local abr_vf_file;
    local abr_dir;
    local abr_lib;

    abr_dir=$1;
    abr_lib=$2;
    abr_vf_file=${abr_dir}/${abr_lib}.vf

    # Skip UVM file lists, which reference installed libraries external to Caliptra repo
    # UPDATE: UVM file lists are now generated, but skip coverage files since these file
    # lists aren't useful to external integrators
    if [[ $abr_lib = *"coverage" ]]; then return; fi
    echo "Generating File List for lib [${abr_lib}] in [${abr_vf_file}]";
    pb fe file_list --tb integration_lib::${abr_lib} +def-target 'tb' --flat --dir-fmt=+incdir+{directory} --file ${abr_vf_file};
    # Replace leading portion of Adamsbridge source paths with ${ADAMSBRIDGE_ROOT}
    sed 's,/home.*adams-bridge/src,\${ADAMSBRIDGE_ROOT}/src,' -i ${abr_vf_file}
    # Replace leading portion of UVM/installed library paths with appropriate ENV VAR
    sed 's,/home/cad/tools/mentor/questa/[0-9\._]*/questasim/verilog_src/uvm-[^/]\+,\${UVM_HOME},' -i ${abr_vf_file}
    sed 's,/home/cad/tools/mentor/uvmf/UVMF_[0-9\.]*,\${UVMF_HOME},' -i ${abr_vf_file}
    sed 's,/home/cad/tools/mentor/questa_vip/[0-9\.]*,\${QUESTA_MVC_HOME},' -i ${abr_vf_file}
    # Remove duplicate entries and empty lines from the file
    perl -i -ne 'print if ! $a{$_}++ and /\S/' ${abr_vf_file}
}

if [[ $(command -v pb) = "" ]]; then
    echo "Enter Adamsbridge workspace (to make Playbook available) and try again"
    exit 1
fi
if [[ -z ${ADAMSBRIDGE_ROOT:+"empty"} ]]; then
    echo "Must run script from within Adamsbridge Playbook context"
    exit 1
fi
abr_ymls=$(grep '^\s*\- ../chipsalliance/adams-bridge/src' ${MSFT_REPO_ROOT}/config/compilespecs.yml | sed 's/^\s*- \(..\/chipsalliance\/adams-bridge\/src.*\)/\1/')
declare -A procs;
for i in ${abr_ymls}; do
    abr_dir=$(realpath $(sed 's,\(..\/chipsalliance\/adams-bridge\/src/.\+/config\)/.*,\1,' <<< ${i}))
    abr_libs=$(grep '^\s*provides' ${i} | sed 's/.*\[\(\w\+\)\].*/\1/')
    for j in ${abr_libs}; do
        gen_pb_file_list ${abr_dir} ${j} &
        procs["$i_$j"]=$!
    done
done
echo "waiting for ${procs[@]}"
wait ${procs[@]}
