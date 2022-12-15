# SPDX-License-Identifier: Apache-2.0
# Copyright 2022 Microsoft Corporation or its affiliates.
# # Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
# # http://www.apache.org/licenses/LICENSE-2.0 
# # Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
1.
To run UVMF, please set $UVMF_HOME use the following command:
"export UVMF_HOME=<path to UVMF home directory>"

The one on our server is located at:
"/home/cad/tools/mentor/questa/2022.2_1/questasim/examples/UVM_Framework/UVMF_2021.3"

Or, you can download the lastest release version online at: https://verificationacademy.com/courses/UVM-Framework-One-Bite-at-a-Time

2.
Please use the following commands to loading python and questa modules:
module load tools/python/python3/3.6.8
module load tools/mentor/license/2020.12
module load tools/mentor/questa/2022.2_1

3.
To run testbenches, go to "Caliptra/src/aes/uvmf/uvmf_template_output/project_benches/AES/sim"
and run "make debug" for random sequences, or "make debug TEST_NAME=AES_random_test" for preset sequences

4.
After Questa(ModelSim) opens, enter the run time (50000ns recommended) and hit run. It will run 25 random tests by default
