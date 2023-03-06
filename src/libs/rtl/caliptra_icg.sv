// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
`include "config_defines.svh"

`ifndef TECH_SPECIFIC_ICG
    module `CALIPTRA_ICG (
        input logic clk,
        input logic en,
        output clk_cg
    );
        logic en_lat;
    
        //Latch disable for both clk and soc_ifc clk
        always_latch begin
            if(!clk) begin
                en_lat = en;
            end
        end
         
        //Gate clk
        assign clk_cg = clk && en_lat;
    
    endmodule
`endif