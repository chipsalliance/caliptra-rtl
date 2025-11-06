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


module cptra_pm_reg_top 
    import cptra_pm_reg_pkg::*;
    #(
    )
    (
    input logic clk,
    input logic rst_b,

    // REG HWIF signals
    output cptra_pm_reg__out_t cptra_pm_reg_hwif_out,

    // Caliptra internal fabric response interface
    cptra_cif_if.response  cif_resp_if

    );

// REG HWIF signals
cptra_pm_reg__in_t   cptra_pm_reg_hwif_in;

// Byte Enable mapping
logic [CPTRA_PM_REG_DATA_WIDTH-1:0] c_cpuif_wr_biten;

// Error signals
logic cptra_pm_reg_read_error;
logic cptra_pm_reg_write_error;


///////////////////////////////////////////////
// Map CIF WSTRB to BITEN of REG block
///////////////////////////////////////////////
genvar i;
generate 
    for (i = 0; i < CPTRA_PM_REG_DATA_WIDTH; i = i + 1) begin : map_wstrb_to_biten
        assign c_cpuif_wr_biten[i] = cif_resp_if.req_data.wstrb[i/8];
    end
endgenerate


///////////////////////////////////////////////
// Error handling logic
///////////////////////////////////////////////

assign cif_resp_if.error = cptra_pm_reg_read_error | cptra_pm_reg_write_error;

///////////////////////////////////////////////
// Hold response logic
///////////////////////////////////////////////

// Reads and writes occur in 1 clock cycles
assign cif_resp_if.hold = '0;
    


///////////////////////////////////////////////
// REG Module      
///////////////////////////////////////////////
cptra_pm_reg i_cptra_pm_reg (

        .clk  (clk),
        .rst  ('0), 

        .s_cpuif_req            (cif_resp_if.dv),
        .s_cpuif_req_is_wr      (cif_resp_if.req_data.write),
        .s_cpuif_addr           (cif_resp_if.req_data.addr[AHB_ADDR_WIDTH-1:0]),
        .s_cpuif_wr_data        (cif_resp_if.req_data.wdata),
        .s_cpuif_wr_biten       (c_cpuif_wr_biten),
        .s_cpuif_req_stall_wr   (),  
        .s_cpuif_req_stall_rd   (),  
        .s_cpuif_rd_ack         (),  
        .s_cpuif_rd_err         (cptra_pm_reg_read_error),
        .s_cpuif_rd_data        (cif_resp_if.rdata),   
        .s_cpuif_wr_ack         (),    
        .s_cpuif_wr_err         (cptra_pm_reg_write_error),

        .hwif_in                (cptra_pm_reg_hwif_in),
        .hwif_out               (cptra_pm_reg_hwif_out)

);


endmodule
