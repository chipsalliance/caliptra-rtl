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
//
//======================================================================
//
// ecc_ram_tdp_file.sv
// --------
// ECC Data Memory.
//
//
//======================================================================

module ecc_ram_tdp_file #(
    parameter ADDR_WIDTH = 10,
    parameter DATA_WIDTH = 32
    )
    (      
    input  wire                      clk,
    
    input  wire                      ena,
    input  wire                      wea,
    input  wire  [ADDR_WIDTH-1 : 0]  addra,
    input  wire  [DATA_WIDTH-1 : 0]  dina,
    output logic [DATA_WIDTH-1 : 0]  douta,

    input  wire                      enb,
    input  wire                      web,
    input  wire  [ADDR_WIDTH-1 : 0]  addrb,
    input  wire  [DATA_WIDTH-1 : 0]  dinb,
    output logic [DATA_WIDTH-1 : 0]  doutb
    );
 
    // Declare the RAM variable
	reg [DATA_WIDTH-1:0] mem[2**ADDR_WIDTH-1:0];

    always_ff @ (posedge clk) 
    begin : reading_memory
        if (ena)
            douta <= mem[addra];

        if (enb)
            doutb <= mem[addrb];
    end // reading_memory

    always_ff @ (posedge clk) 
    begin : writing_memory
        if (ena & wea)
            mem[addra] <= dina;

        if (enb & web)
            mem[addrb] <= dinb;
    end // writing_memory

endmodule
