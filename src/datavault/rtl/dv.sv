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

module dv 
    import dv_defines_pkg::*;
    import dv_reg_pkg::*;

    #(
     parameter AHB_ADDR_WIDTH = DV_ADDR_W
    ,parameter AHB_DATA_WIDTH = 32
    )
    (
    input logic clk,
    input logic rst_b,
    input logic core_only_rst_b,
    input logic cptra_pwrgood,

    
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
    output logic [AHB_DATA_WIDTH-1:0]     hrdata_o

);

logic uc_req_dv, uc_req_hold;
logic uc_req_error;
logic [31:0] uc_req_rdata;
logic dv_reg_read_error, dv_reg_write_error;
dv_uc_req_t uc_req;

dv_reg__in_t dv_reg_hwif_in;
dv_reg__out_t dv_reg_hwif_out;

ahb_slv_sif #(
    .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
    .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
    .CLIENT_DATA_WIDTH(32)
)
dv_ahb_slv1 (
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
    .addr(uc_req.addr),

    .rdata(uc_req_rdata)
);

always_comb uc_req_error = dv_reg_read_error | dv_reg_write_error;
always_comb uc_req_hold = '0;

// Sticky (when lock is set, locked until cold reset) & Non-sticky (when lock is set, locked until warm reset) Generic DataVault registers.
always_comb begin: datavault

    //Sticky Data Vault Regs & Controls
    for (int entry = 0; entry < STICKY_DV_NUM_ENTRIES; entry++) begin
       dv_reg_hwif_in.StickyDataVaultCtrl[entry].lock_entry.swwel = dv_reg_hwif_out.StickyDataVaultCtrl[entry].lock_entry.value;
       for (int dword = 0; dword < DV_NUM_DWORDS; dword++) begin
           dv_reg_hwif_in.STICKY_DATA_VAULT_ENTRY[entry][dword].data.swwel = dv_reg_hwif_out.StickyDataVaultCtrl[entry].lock_entry.value;
       end
    end
 
    //Non-Sticky Data Vault Regs & Controls
    for (int entry = 0; entry < DV_NUM_ENTRIES; entry++) begin
       dv_reg_hwif_in.DataVaultCtrl[entry].lock_entry.swwel = dv_reg_hwif_out.DataVaultCtrl[entry].lock_entry.value;
       for (int dword = 0; dword < DV_NUM_DWORDS; dword++) begin
           dv_reg_hwif_in.DATA_VAULT_ENTRY[entry][dword].data.swwel = dv_reg_hwif_out.DataVaultCtrl[entry].lock_entry.value;
       end
    end
 
    //Non-Sticky Generic Lockable Registers in the Data Vault
    for (int entry = 0; entry < LOCK_SCRATCH_NUM_ENTRIES; entry++) begin
       dv_reg_hwif_in.LockableScratchRegCtrl[entry].lock_entry.swwel = dv_reg_hwif_out.LockableScratchRegCtrl[entry].lock_entry.value;
       dv_reg_hwif_in.LockableScratchReg[entry].data.swwel  = dv_reg_hwif_out.LockableScratchRegCtrl[entry].lock_entry.value;
    end
 
    //Sticky Generic Lockable Registers in the Data Vault
    for (int entry = 0; entry < STICKY_LOCK_SCRATCH_NUM_ENTRIES; entry++) begin
       dv_reg_hwif_in.StickyLockableScratchRegCtrl[entry].lock_entry.swwel = dv_reg_hwif_out.StickyLockableScratchRegCtrl[entry].lock_entry.value;
       dv_reg_hwif_in.StickyLockableScratchReg[entry].data.swwel  = dv_reg_hwif_out.StickyLockableScratchRegCtrl[entry].lock_entry.value;
    end
    
end

always_comb dv_reg_hwif_in.hard_reset_b = cptra_pwrgood;
always_comb dv_reg_hwif_in.reset_b = rst_b;
always_comb dv_reg_hwif_in.core_only_rst_b = core_only_rst_b; //Note that this signal will also reset when rst_b is asserted

dv_reg dv_reg1 (
    .clk(clk),
    .rst('0),
    //qualify request so no addresses alias
    .s_cpuif_req(uc_req_dv & (uc_req.addr[DV_ADDR_W-1:DV_REG_ADDR_WIDTH] == '0)),
    .s_cpuif_req_is_wr(uc_req.write),
    .s_cpuif_addr(uc_req.addr[DV_REG_ADDR_WIDTH-1:0]),
    .s_cpuif_wr_data(uc_req.wdata),
    .s_cpuif_wr_biten('1),
    .s_cpuif_req_stall_wr(),
    .s_cpuif_req_stall_rd(),
    .s_cpuif_rd_ack(),
    .s_cpuif_rd_err(dv_reg_read_error),
    .s_cpuif_rd_data(uc_req_rdata),
    .s_cpuif_wr_ack(),
    .s_cpuif_wr_err(dv_reg_write_error),
    
    .hwif_in(dv_reg_hwif_in),
    .hwif_out(dv_reg_hwif_out)
);

endmodule
