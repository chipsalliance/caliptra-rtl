# SPDX-License-Identifier: Apache-2.0
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
##### Add Waivers here
##### Example below: Can dump these commands from GUI as well.

#*****************no_sync violations*****************

cdc report item -scheme no_sync -from "type in src path, careful with wildcards*" -to "*type in dest path, careful with wildcards" -module integration_top -status waived -message {<user_id>  <date>:  <Detailed reason for this waiver>}


#*****************multi_bits violations*****************
cdc report item -scheme multi_bits -from " type in src path, careful with wildcards*" -to "*type in dest path, careful with wildcards" -module integration_top -status waived -message {<user_id>  <date>:  <Detailed reason for this waiver>}
