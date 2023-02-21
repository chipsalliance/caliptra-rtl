# SPDX-License-Identifier: Apache-2.0
# 
# # Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
# # http://www.apache.org/licenses/LICENSE-2.0 
# # Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
# **aha_poc** #

## **Overview** ##

Internal hands-on README describing use of Microsoft Playbook to build Caliptra project.
External integrators: review README.md at Repository root.

## **Workspace Setup** ##

### 1. Create a workspace as shown [here](https://dev.azure.com/ms-tsd/Documents/_wiki/wikis/Documents.wiki/114/Workspace-Commands).

Preferred command for making a workspace with this repo,

`make-workspace --project AHA_POC --top <Please_Add_TOP_NAME_Here> --directory integration_lib`


or,


`make-workspace --url git@ssh.dev.azure.com:v3/ms-tsd/AHA_POC/Caliptra --directory integration_lib`

### 2. Add comodules and then, recursively pull all comodules into the workspace (as per the tags specified in .git-comodules).

`pb workspace update`

<br>

# **Build Command:** #

`pb fe build --tb <top_from_compilespecs>::<compile_unit_name>_tb`


or,


`pb fe build --tb integration_lib::integration_tb`


or,


`pb fe build --tb integration_lib::integration_top`


or with IUS,


`pb fe build --tb integration_lib::integration_top --tool ius --targets packages rtl elab --options rtl="+define+TSD_DISABLE_ASSERTIONS"`


<br>

# **Lint Command:** #


`pb fe lint rtl --tb <top_from_compilespecs>::<compile_unit_name>_tb`


or,


`pb fe lint rtl --tb integration_lib::integration_top`


<br>


