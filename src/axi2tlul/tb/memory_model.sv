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

// -------------------------------------------------------------
// AXI TLUL Write Shim
// -------------------------------------------------------------
// Description:
//   Shim to convert AXI protocol writes into TLUL
//
// Limitations:
//   - When multiple ID tracking is enabled, write responses are returned in the
//     same order they are received, regardless of ID.
//
// -------------------------------------------------------------
module memory_model 
    import tlul_pkg::*;
#(
    parameter TL_AW   = 32,
    parameter TL_DW   = 32,    // = TL_DBW * 8, TL_DBW must be a power-of-two
    parameter TL_AIW  = 8,    // a_source, d_source
    parameter TL_DIW  = 1,    // d_sink
    parameter TL_AUW  = 21,   // a_user
    parameter TL_DUW  = 14,   // d_user
              TL_DBW  = (TL_DW>>3),
              TL_SZW  = $clog2($clog2(TL_DBW)+1),
    parameter NUM_WORDS = 64
) (
        input logic     clk,
        input logic     rst_n,

        // TLUL INF
        input   tlul_pkg::tl_h2d_t tl_i,
        output  tlul_pkg::tl_d2h_t tl_o
        /* 
        input logic     [ADDR_WIDTH-1:0] addr,
        input logic     wr_en,
        input logic     [DATA_WIDTH-1:0] wdata,
        output logic    [DATA_WIDTH-1:0] rdata
        */
);

    // Parameterized memory array
    logic [TL_DW-1:0] mem [0:NUM_WORDS-1]; // Parameterized memory array
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            // Initialize memory to 0
            foreach (mem[i]) mem[i] <= i;
            tl_o.d_opcode   <= AccessAck;
            tl_o.d_valid    <= 0;
            tl_o.d_data     <= '0;
            tl_o.d_error    <= 0;
            tl_o.d_source   <= '0;
            tl_o.a_ready    <= 1;
        end 
        
        else if (tl_i.a_valid) begin
            // Write Transaction
            if (tl_i.a_opcode == PutFullData) begin
                tl_o.a_ready    <= 1;
                tl_o.d_opcode   <= AccessAck;
                tl_o.d_valid    <= 1;
                mem[tl_i.a_address]       <= tl_i.a_data;
            end
            // Read Transaction
            else if (tl_i.a_opcode == Get) begin
                tl_o.a_ready    <= 1;
                tl_o.d_opcode   <= AccessAckData;
                tl_o.d_valid    <= 1;
                tl_o.d_data     <= mem[tl_i.a_address];
                tl_o.d_source   <= tl_i.a_source;
            end
        end
        else if (tl_i.d_ready) begin
                tl_o.d_valid    <= 0;
        end
    end

endmodule