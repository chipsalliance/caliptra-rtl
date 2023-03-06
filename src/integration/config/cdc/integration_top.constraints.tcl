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
#### Add directives/block specific constraints here

#***************************************************************************************************
# Section 1: Clock Constraints
#***************************************************************************************************

netlist clock    { clk1 } -module { integration_top }  -group { Group_AXI_CLK}

#***************************************************************************************************
# Section 2: Reset Constraints
#***************************************************************************************************

netlist reset    { reset1 } -active_high -async -module { integration_top }

#***************************************************************************************************
# Section 3: Port Constraints
#***************************************************************************************************

# INPUT PORTS

netlist port domain { input_port1 }    -clock { clk1 }    -combo_logic   -module { integration_top}


# OUTPUT PORTS

netlist port domain { output_port1 }         -clock { clk2 }              -module { integration_top }

#***************************************************************************************************
# Section 4: Local constraints i.e. Constants, Blackboxes (blackboxing discouraged...last resort) etc
#***************************************************************************************************

#Constants
netlist constant SIGNALX 0

#Blackbox
netlist blackbox module_name
