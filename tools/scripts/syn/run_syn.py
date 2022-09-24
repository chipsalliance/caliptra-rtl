# SPDX-License-Identifier: Apache-2.0
# Copyright 2022 Microsoft Corporation or its affiliates.
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
import sys
import os
import subprocess
import time

def exec_print(cmd):
    popen = subprocess.Popen([cmd],stdout=subprocess.PIPE, shell=True, universal_newlines=True)
    while True:
        nextline = popen.stdout.readline()
        if nextline == '' and popen.poll() is not None:
            break
        sys.stdout.write(nextline)
        sys.stdout.flush()

    popen.stdout.close()
    return_code = popen.wait()
    if return_code:
        raise subprocess.CalledProcessError(return_code, cmd)

timestr = time.strftime("%Y%m%d.%H%M%S")

unit = sys.argv[1];
workspace = os.environ.get('WORKSPACE')
user = os.environ.get('USER')
output_dir = f"{workspace}/scratch/{user}/syn/{unit}/{timestr}"
dc_cmds = f"-x 'set design {unit}; set workspace {workspace}; set user {user};'"

# checking if the out directory exists or not.
if not os.path.exists(output_dir):  
    # if the out directory is not present then create it.
    os.makedirs(output_dir)

os.chdir(output_dir)
os.system(f"ln -snf {output_dir} ../latest")
os.system(f"cp {workspace}/Caliptra/tools/scripts/syn/dc.tcl .")
gen_file_list_cmd = f"pb fe file_list --tb integration_lib::{unit} --flat --dir-fmt=+incdir+{{directory}} --file {unit}.vf"
exec_print(gen_file_list_cmd)
run_syn_cmd = f"dc_shell -output_log_file {unit}.cmd -f dc.tcl {dc_cmds}"
exec_print(run_syn_cmd)


