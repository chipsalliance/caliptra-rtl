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


module cptra_pm_top 
import cptra_pm_reg_pkg::*;
#(
)
(
    input logic clk,
    input logic rst_b,
    
    // REG HWIF signals
    output cptra_pm_reg__out_t cptra_pm_reg_hwif_out,
    
    // AHB IF
    CALIPTRA_AHB_LITE_BUS_INF.Responder_Interface_Ports ahb_resp_if



);

localparam AHB_ADDR_WIDTH = $bits(ahb_resp_if.haddr);
localparam AHB_DATA_WIDTH = $bits(ahb_resp_if.hwdata);

cptra_cif_if #(
    .ADDR_WIDTH(AHB_ADDR_WIDTH)
    ,.DATA_WIDTH(CPTRA_PM_REG_DATA_WIDTH)
) cptra_pm_req_if(
    .clk(cptra_ss_rdc_clk_cg), 
    .rst_b(cptra_ss_rst_b_o));




//////////////////////
// AHB to CIF
//////////////////////
assign cptra_pm_req_if.req_data.id = '0; // Unused since only 1 master
assign cptra_pm_req_if.req_data.user = '0; // Unused since only 1 master
assign cptra_pm_req_if.req_data.last = '0; // Unused
assign cptra_pm_req_if.req_data.size = '0; // Unused
assign cptra_pm_req_if.req_data.wstrb = '1; // ahb_slv_sif only supports DWORD writes 

ahb_slv_sif #(
    .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
    .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
    .CLIENT_DATA_WIDTH(CPTRA_PM_REG_DATA_WIDTH)
) ahb_slv_sif_inst
(
    //AMBA AHB Lite INF
    .hclk(clk),
    .hreset_n(reset_n),
    .haddr_i(haddr_i),
    .hwdata_i(hwdata_i),
    .hsel_i(hsel_i),
    .hwrite_i(hwrite_i),
    .hready_i(hready_i),
    .htrans_i(htrans_i),
    .hsize_i(hsize_i),

    .hresp_o(hresp_o),
    .hreadyout_o(hreadyout_o),
    .hrdata_o(hrdata_o),


    //COMPONENT INF
    .dv(cptra_pm_req_if.dv),
    .hld(cptra_pm_req_if.hold),
    .err(cptra_pm_req_if.error),
    .write(cptra_pm_req_if.req_data.write),
    .wdata(cptra_pm_req_if.req_data.wdata),
    .addr(cptra_pm_req_if.req_data.addr),

    .rdata(cptra_pm_req_if.rdata)
);

//////////////////////
// PM REGISTERS  
//////////////////////

cptra_pm_reg_top #(
) cptra_pm_reg_top_inst
(
    .clk
    ,.rst_b

    ,.cptra_pm_reg_hwif_out

    ,.cif_resp_if(cptra_pm_req_if.response)
);



endmodule
