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


`include "caliptra_macros.svh"

module pv 
    import pv_defines_pkg::*;
    import pv_reg_pkg::*;

    #(
     parameter AHB_ADDR_WIDTH = PV_ADDR_W
    ,parameter AHB_DATA_WIDTH = 32
    )
    (
    input logic clk,
    input logic rst_b,
    input logic core_only_rst_b,
    input logic cptra_pwrgood,
    input logic fw_update_rst_window, 
    
    //uC AHB Lite Interface
    //from SLAVES PORT
    input logic [AHB_ADDR_WIDTH-1:0]      haddr_i,
    input logic [AHB_DATA_WIDTH-1:0]      hwdata_i,
    input logic                           hsel_i,
    input logic                           hwrite_i,
    input logic                           hready_i,
    input logic [1:0]                     htrans_i,
    input logic [2:0]                     hsize_i,

    output logic                          hresp_o,
    output logic                          hreadyout_o,
    output logic [AHB_DATA_WIDTH-1:0]     hrdata_o,

    input pv_read_t [PV_NUM_READ-1:0]     pv_read,
    input pv_write_t [PV_NUM_WRITE-1:0]   pv_write,
    output pv_rd_resp_t [PV_NUM_READ-1:0] pv_rd_resp,
    output pv_wr_resp_t [PV_NUM_WRITE-1:0] pv_wr_resp

);

logic uc_req_dv, uc_req_hold;
logic uc_req_error;
logic [31:0] uc_req_rdata;
logic pv_reg_read_error, pv_reg_write_error;
logic [AHB_ADDR_WIDTH-1:0] uc_req_addr;
pv_uc_req_t uc_req;

//intermediate signals to make verilator happy
logic [PV_NUM_PCR-1:0][PV_NUM_DWORDS-1:0] pv_entry_we;
logic [PV_NUM_PCR-1:0][PV_NUM_DWORDS-1:0][31:0] pv_entry_next;

pv_reg__in_t pv_reg_hwif_in;
pv_reg__out_t pv_reg_hwif_out;

ahb_slv_sif #(
    .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
    .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
    .CLIENT_DATA_WIDTH(32)
)
pv_ahb_slv1 (
    //AMBA AHB Lite INF
    .hclk(clk),
    .hreset_n(rst_b),
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
    .dv(uc_req_dv),
    .hld(uc_req_hold),
    .err(uc_req_error),
    .write(uc_req.write),
    .wdata(uc_req.wdata),
    .addr(uc_req_addr),

    .rdata(uc_req_rdata)
);

always_comb uc_req.addr = uc_req_addr[PV_ADDR_W-1:0];
always_comb uc_req_error = pv_reg_read_error | pv_reg_write_error;
always_comb uc_req_hold = '0;

always_comb begin : keyvault_ctrl
    for (int entry = 0; entry < PV_NUM_PCR; entry++) begin
        //once lock is set, any reset can unset it
        //During a fw update reset we'll be de-asserting locks - avoid RDC violation by synchronously de-asserting
        pv_reg_hwif_in.PCR_CTRL[entry].lock.swwel = pv_reg_hwif_out.PCR_CTRL[entry].lock.value & ~fw_update_rst_window;
        pv_reg_hwif_in.PCR_CTRL[entry].clear.swwel = pv_reg_hwif_out.PCR_CTRL[entry].lock.value & ~fw_update_rst_window;
    end

    //pcrvault storage
    //AND-OR mux writes to each entry from crypto blocks
    //write to the appropriate dest entry and offset when write_en is set
    for (int entry = 0; entry < PV_NUM_PCR; entry++) begin
        for (int dword = 0; dword < PV_NUM_DWORDS; dword++) begin
            //initialize to 0 for AND-OR mux
            pv_entry_we[entry][dword] = '0;
            pv_entry_next[entry][dword] = '0;
            
            for (int client = 0; client < PV_NUM_WRITE; client++) begin
                pv_entry_we[entry][dword] |= pv_write[client].write_en &(pv_write[client].write_entry == entry) & 
                                             (pv_write[client].write_offset == dword);
                pv_entry_next[entry][dword] |= pv_write[client].write_en & (pv_write[client].write_entry == entry) ? pv_write[client].write_data : '0;
            end 
            pv_reg_hwif_in.PCR_ENTRY[entry][dword].data.we = pv_entry_we[entry][dword];
            pv_reg_hwif_in.PCR_ENTRY[entry][dword].data.next =  pv_entry_next[entry][dword];
            pv_reg_hwif_in.PCR_ENTRY[entry][dword].data.hwclr = pv_reg_hwif_out.PCR_CTRL[entry].clear.value;
        end
    end
end

//read mux for pcrvault
//qualify with selected entry, offset
always_comb begin : keyvault_readmux
    for (int client = 0; client < PV_NUM_READ; client++) begin  
        pv_rd_resp[client].read_data = '0;
        pv_rd_resp[client].last = '0;
        pv_rd_resp[client].error = '0;
        for (int entry = 0; entry < PV_NUM_PCR; entry++) begin
            for (int dword = 0; dword < PV_NUM_DWORDS; dword++) begin
                pv_rd_resp[client].read_data |= (pv_read[client].read_entry == entry) & (pv_read[client].read_offset == dword) ? 
                                                 pv_reg_hwif_out.PCR_ENTRY[entry][dword].data.value : '0;
            end
        pv_rd_resp[client].last |= (pv_read[client].read_entry == entry) & (pv_read[client].read_offset == PV_NUM_DWORDS-1);
        pv_rd_resp[client].error |= '0; //currently no read errors for PCR
        end
    end
end

//Write error when attempting to write to entry that is locked for writes
always_comb begin : keyvault_write_resp
    for (int client = 0 ; client < PV_NUM_WRITE; client++) begin
        pv_wr_resp[client].error = '0;
        for (int entry = 0; entry < PV_NUM_PCR; entry++) begin
            pv_wr_resp[client].error |= '0; //currently no write errors for PCR
        end
    end
end

//tie-offs
always_comb begin
    for (int entry = 0; entry < PV_NUM_PCR; entry++) begin
        pv_reg_hwif_in.PCR_CTRL[entry].rsvd0.hwclr = '0;
    end
end


always_comb pv_reg_hwif_in.hard_reset_b = cptra_pwrgood;
always_comb pv_reg_hwif_in.reset_b = rst_b;
always_comb pv_reg_hwif_in.core_only_rst_b = core_only_rst_b; //Note that this signal will also reset when rst_b is asserted

pv_reg pv_reg1 (
    .clk(clk),
    .rst('0),
    //qualify request so no addresses alias
    .s_cpuif_req(uc_req_dv & (uc_req.addr[PV_ADDR_W-1:PV_REG_ADDR_WIDTH] == '0)),
    .s_cpuif_req_is_wr(uc_req.write),
    .s_cpuif_addr(uc_req.addr[PV_REG_ADDR_WIDTH-1:0]),
    .s_cpuif_wr_data(uc_req.wdata),
    .s_cpuif_wr_biten('1),
    .s_cpuif_req_stall_wr(),
    .s_cpuif_req_stall_rd(),
    .s_cpuif_rd_ack(),
    .s_cpuif_rd_err(pv_reg_read_error),
    .s_cpuif_rd_data(uc_req_rdata),
    .s_cpuif_wr_ack(),
    .s_cpuif_wr_err(pv_reg_write_error),
    
    .hwif_in(pv_reg_hwif_in),
    .hwif_out(pv_reg_hwif_out)
);

endmodule
