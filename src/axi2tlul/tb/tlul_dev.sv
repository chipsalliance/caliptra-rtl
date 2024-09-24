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


module tlul_dev
    import tlul_pkg::*;
    #(
        parameter TL_AW   = 32,
        parameter TL_DW   = 32,    // = TL_DBW * 8, TL_DBW must be a power-of-two
        parameter TL_AIW  = 8,    // a_source, d_source
        parameter TL_DIW  = 1,    // d_sink
        parameter TL_AUW  = 21,   // a_user
        parameter TL_DUW  = 14,   // d_user
                  TL_DBW  = (TL_DW>>3),
                  TL_SZW  = $clog2($clog2(TL_DBW)+1)
    ) (
        input logic         clk,
        input logic         rst_n,

        // TLUL INF
        input   tlul_pkg::tl_h2d_t tl_i,
        output  tlul_pkg::tl_d2h_t tl_o,

        // Memory model interface
        output logic [TL_AW-1:0]    address,
        output logic [TL_DW-1:0]    wdata,
        input logic  [TL_DW-1:0]    rdata,
        output logic                write
    );

    // Address Phase
    always_comb begin
        if (tl_i.a_valid) begin
            address = tl_i.a_address;
            tl_o.a_ready    = 1;
            tl_o.d_opcode   = AccessAck;
            if (tl_i.a_opcode == Get) begin
                write           = 0;
            end
            else if (tl_i.a_opcode == PutFullData) begin // TODO: Need to support PulPartialData
                write           = 1;
                wdata           = tl_i.a_data;
                tl_o.d_valid    = 1;
            end
        end
    end

    // Read Data Phase
    always_comb begin
        if (tl_i.a_valid && (tl_i.a_opcode == Get)) begin
            tl_o.d_data     = rdata;
            tl_o.d_valid    = 1;
            tl_o.d_opcode   = AccessAckData;
            if (tl_i.d_ready) tl_o.d_valid = 0;
        end
    end

/* 
    task readSingle();
        if (tl_i.a_valid && (tl_i.a_opcode == Get)) begin
            // Address Phase
            write           = 0;
            address         = tl_i.a_address;
            tl_o.a_ready    = 1;
            tl_o.d_opcode   = AccessAck;
            @(posedge clk);

            // Data Phase
            tl_o.d_data     = rdata;
            tl_o.d_valid    = 1;
            tl_o.d_opcode   = AccessAckData;

            // Wait for host to assert D_READY
            while (!tl_i.d_ready) begin
                @(posedge clk);
            end

            // Deassert D_VALID once D_READY has been asserted
            tl_o.d_valid    = 0;
        end
    endtask

    task writeSingle();
        if (tl_i.a_valid && (tl_i.a_opcode == PutFullData)) begin
            // Address Phase
            write           = 1;
            address         = tl_i.a_address;
            wdata           = tl_i.a_data;
            tl_o.a_ready    = 1;
            tl_o.d_opcode   = AccessAck;
            @(posedge clk);

            // Data Phase
            tl_o.d_valid    = 1;

            // Wait for host to assert D_READY
            while (!tl_i.d_ready) begin
                @(posedge clk);
            end

            // Deassert D_VALID once D_READY has been asserted
            tl_o.d_valid = 0;
        end
    endtask: writeSingle

    */

endmodule: tlul_dev
