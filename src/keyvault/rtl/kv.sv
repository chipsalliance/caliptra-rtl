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

module kv 
    import kv_defines_pkg::*;
    import kv_reg_pkg::*;

    #(
     parameter AHB_ADDR_WIDTH = KV_ADDR_W
    ,parameter AHB_DATA_WIDTH = 32
    )
    (
    input logic clk,
    input logic rst_b,
    input logic cptra_pwrgood,

    input logic debug_locked,
    
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

    input kv_read_t [KV_NUM_READ-1:0]     kv_read,
    input kv_write_t [KV_NUM_WRITE-1:0]   kv_write,
    output kv_rd_resp_t [KV_NUM_READ-1:0] kv_rd_resp,
    output kv_wr_resp_t [KV_NUM_READ-1:0] kv_wr_resp

);

logic uc_req_dv, uc_req_hold;
logic uc_req_error;
logic [31:0] uc_req_rdata;
logic kv_reg_read_error, kv_reg_write_error;
kv_uc_req_t uc_req;

logic debug_locked_f;
logic debug_unlocked;
logic flush_keyvault;
logic [31:0] debug_value;

kv_reg__in_t kv_reg_hwif_in;
kv_reg__out_t kv_reg_hwif_out;

ahb_slv_sif #(
    .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
    .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
    .CLIENT_DATA_WIDTH(32)
)
kv_ahb_slv1 (
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

always_comb uc_req_error = kv_reg_read_error | kv_reg_write_error;
always_comb uc_req_hold = '0;

always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b) begin
        debug_locked_f <= '1;
    end
    else begin
        debug_locked_f <= debug_locked;
    end
end


//Edge detect - debug was locked and now it's not
always_comb debug_unlocked = debug_locked_f & ~debug_locked;
//Flush the keyvault with the debug value when FW pokes the register or we detect debug mode unlocking
always_comb flush_keyvault = debug_unlocked | kv_reg_hwif_out.CLEAR_SECRETS.wr_debug_values.value;
//Pick between keyvault debug mode 0 or 1
always_comb debug_value = kv_reg_hwif_out.CLEAR_SECRETS.sel_debug_value.value ? CLP_DEBUG_MODE_KV_1 : CLP_DEBUG_MODE_KV_0;

// Sticky (when lock is set, locked until cold reset) & Non-sticky (when lock is set, locked until warm reset) Generic DataVault registers.
always_comb begin: datavault

   //Sticky Data Vault Regs & Controls
   for (int entry = 0; entry < STICKY_DV_NUM_ENTRIES; entry++) begin
      kv_reg_hwif_in.StickyDataVaultCtrl[entry].lock_entry.swwel = kv_reg_hwif_out.StickyDataVaultCtrl[entry].lock_entry.value;
      for (int dword = 0; dword < DV_NUM_DWORDS; dword++) begin
          kv_reg_hwif_in.STICKY_DATA_VAULT_ENTRY[entry][dword].data.swwel = kv_reg_hwif_out.StickyDataVaultCtrl[entry].lock_entry.value;
      end
   end

   //Non-Sticky Data Vault Regs & Controls
   for (int entry = 0; entry < NONSTICKY_DV_NUM_ENTRIES; entry++) begin
      kv_reg_hwif_in.NonStickyDataVaultCtrl[entry].lock_entry.swwel = kv_reg_hwif_out.NonStickyDataVaultCtrl[entry].lock_entry.value;
      for (int dword = 0; dword < DV_NUM_DWORDS; dword++) begin
          kv_reg_hwif_in.NONSTICKY_DATA_VAULT_ENTRY[entry][dword].data.swwel = kv_reg_hwif_out.NonStickyDataVaultCtrl[entry].lock_entry.value;
      end
   end

   //Non-Sticky Generic Lockable Registers in the Data Vault
   for (int entry = 0; entry < NONSTICKY_LOCKQ_SCRATCH_NUM_ENTRIES; entry++) begin
      kv_reg_hwif_in.NonStickyLockableScratchRegCtrl[entry].lock_entry.swwel = kv_reg_hwif_out.NonStickyLockableScratchRegCtrl[entry].lock_entry.value;
      kv_reg_hwif_in.NonStickyLockableScratchReg[entry].data.swwel  = kv_reg_hwif_out.NonStickyDataVaultCtrl[entry].lock_entry.value;
   end

   //Sticky Generic Lockable Registers in the Data Vault
   for (int entry = 0; entry < STICKY_LOCKQ_SCRATCH_NUM_ENTRIES; entry++) begin
      kv_reg_hwif_in.StickyLockableScratchRegCtrl[entry].lock_entry.swwel = kv_reg_hwif_out.StickyLockableScratchRegCtrl[entry].lock_entry.value;
      kv_reg_hwif_in.StickyLockableScratchReg[entry].data.swwel  = kv_reg_hwif_out.StickyDataVaultCtrl[entry].lock_entry.value;
   end


end

always_comb begin : keyvault_ctrl
    //keyvault control registers
    for (int entry = 0; entry < KV_NUM_KEYS; entry++) begin
        //once lock is set, only reset can unset it
        kv_reg_hwif_in.KEY_CTRL[entry].lock_wr.swwel = kv_reg_hwif_out.KEY_CTRL[entry].lock_wr.value;
        kv_reg_hwif_in.KEY_CTRL[entry].lock_use.swwel = kv_reg_hwif_out.KEY_CTRL[entry].lock_use.value;
        //clear control clears the locks
        kv_reg_hwif_in.KEY_CTRL[entry].lock_wr.hwclr = kv_reg_hwif_out.KEY_CTRL[entry].clear.value;
        kv_reg_hwif_in.KEY_CTRL[entry].lock_use.hwclr = kv_reg_hwif_out.KEY_CTRL[entry].clear.value;
        kv_reg_hwif_in.KEY_CTRL[entry].dest_valid.hwclr = kv_reg_hwif_out.KEY_CTRL[entry].clear.value;
        //init for AND-OR
        kv_reg_hwif_in.KEY_CTRL[entry].dest_valid.next = '0; 
        kv_reg_hwif_in.KEY_CTRL[entry].dest_valid.we = '0;
        for (int client = 0; client < KV_NUM_WRITE; client++) begin
            kv_reg_hwif_in.KEY_CTRL[entry].dest_valid.we |= (kv_write[client].write_entry == entry) & ~kv_write[client].entry_is_pcr & kv_write[client].write_en; 
            kv_reg_hwif_in.KEY_CTRL[entry].dest_valid.next |= kv_write[client].write_en ? kv_write[client].write_dest_valid : '0; 
        end 
    end

    for (int entry = 0; entry < KV_NUM_PCR; entry++) begin
        //once lock is set, only reset can unset it
        kv_reg_hwif_in.PCR_CTRL[entry].lock_wr.swwel = kv_reg_hwif_out.PCR_CTRL[entry].lock_wr.value;
        kv_reg_hwif_in.PCR_CTRL[entry].lock_use.swwel = kv_reg_hwif_out.PCR_CTRL[entry].lock_use.value;
        //clear control clears the locks
        kv_reg_hwif_in.PCR_CTRL[entry].lock_wr.hwclr = kv_reg_hwif_out.PCR_CTRL[entry].clear.value;
        kv_reg_hwif_in.PCR_CTRL[entry].lock_use.hwclr = kv_reg_hwif_out.PCR_CTRL[entry].clear.value;
        kv_reg_hwif_in.PCR_CTRL[entry].dest_valid.hwclr = kv_reg_hwif_out.PCR_CTRL[entry].clear.value;
        //init for AND-OR
        kv_reg_hwif_in.PCR_CTRL[entry].dest_valid.next = '0; 
        kv_reg_hwif_in.PCR_CTRL[entry].dest_valid.we = '0; 
        for (int client = 0; client < KV_NUM_WRITE; client++) begin
            kv_reg_hwif_in.PCR_CTRL[entry].dest_valid.we |= (kv_write[client].write_entry == entry) & kv_write[client].entry_is_pcr & kv_write[client].write_en; 
            kv_reg_hwif_in.PCR_CTRL[entry].dest_valid.next |= kv_write[client].write_en? kv_write[client].write_dest_valid : '0; 
        end 
    end

    //keyvault storage
    //AND-OR mux writes to each entry from crypto blocks
    //write to the appropriate dest entry and offset when write_en is set
    for (int entry = 0; entry < KV_NUM_KEYS; entry++) begin
        for (int dword = 0; dword < KV_NUM_DWORDS; dword++) begin
            kv_reg_hwif_in.KEY_ENTRY[entry][dword].data.swwel = '1; //never allow sw writes
            //initialize to 0 for AND-OR mux
            kv_reg_hwif_in.KEY_ENTRY[entry][dword].data.next = '0;
            kv_reg_hwif_in.KEY_ENTRY[entry][dword].data.we = '0;
            for (int client = 0; client < KV_NUM_WRITE; client++) begin
                kv_reg_hwif_in.KEY_ENTRY[entry][dword].data.hwclr = kv_reg_hwif_out.KEY_CTRL[entry].clear.value;
                kv_reg_hwif_in.KEY_ENTRY[entry][dword].data.we |= (((kv_write[client].write_entry == entry) & (kv_write[client].write_offset == dword) & 
                                                                   ~kv_write[client].entry_is_pcr & kv_write[client].write_en) | flush_keyvault) & 
                                                                   ~kv_reg_hwif_out.KEY_CTRL[entry].lock_wr.value;
                kv_reg_hwif_in.KEY_ENTRY[entry][dword].data.next |= flush_keyvault ? debug_value :
                                                                    kv_write[client].write_en ? kv_write[client].write_data : '0;
            end
        end
    end
    for (int entry = 0; entry < KV_NUM_PCR; entry++) begin
        for (int dword = 0; dword < KV_NUM_DWORDS; dword++) begin
            kv_reg_hwif_in.PCR_ENTRY[entry][dword].data.swwel = kv_reg_hwif_out.PCR_CTRL[entry].lock_wr.value; //disable sw writes if locked
            //initialize to 0 for AND-OR mux
            kv_reg_hwif_in.PCR_ENTRY[entry][dword].data.next = '0; //hook up the next data to write from crypto writing to this key
            kv_reg_hwif_in.PCR_ENTRY[entry][dword].data.we = '0; //hook up the write enable from crypto writing to this key
            for (int client = 0; client < KV_NUM_WRITE; client++) begin
                kv_reg_hwif_in.PCR_ENTRY[entry][dword].data.hwclr = kv_reg_hwif_out.PCR_CTRL[entry].clear.value;
                kv_reg_hwif_in.PCR_ENTRY[entry][dword].data.we |= (kv_write[client].write_entry == entry) & (kv_write[client].write_offset == dword) & 
                                                                   kv_write[client].entry_is_pcr & kv_write[client].write_en &
                                                                   ~kv_reg_hwif_out.PCR_CTRL[entry].lock_wr.value;
                kv_reg_hwif_in.PCR_ENTRY[entry][dword].data.next |= kv_write[client].write_en ? kv_write[client].write_data : '0;
            end 
        end
    end
end

//read mux for keyvault
//qualify with selected entry, offset, and pcr flag
//qualify with lock use bit to ensure that locked values aren't read
//qualify with dest valid to ensure requesting client has permission to read this entry
always_comb begin : keyvault_readmux
    for (int client = 0; client < KV_NUM_READ; client++) begin  
        kv_rd_resp[client].read_data = '0;
        kv_rd_resp[client].error = '0;
        for (int entry = 0; entry < KV_NUM_KEYS; entry++) begin
            for (int dword = 0; dword < KV_NUM_DWORDS; dword++) begin
                kv_rd_resp[client].read_data |= ~kv_read[client].entry_is_pcr & (kv_read[client].read_entry == entry) & (kv_read[client].read_offset == dword) &
                                                ~kv_reg_hwif_out.KEY_CTRL[entry].lock_use.value & kv_reg_hwif_out.KEY_CTRL[entry].dest_valid.value[client] ? 
                                                 kv_reg_hwif_out.KEY_ENTRY[entry][dword].data.value : '0;
            end
        kv_rd_resp[client].error |= ~kv_read[client].entry_is_pcr & (kv_read[client].read_entry == entry) & 
                                    (kv_reg_hwif_out.KEY_CTRL[entry].lock_use.value | ~kv_reg_hwif_out.KEY_CTRL[entry].dest_valid.value[client]);
        end
        for (int entry = 0; entry < KV_NUM_PCR; entry++) begin
            for (int dword = 0; dword < KV_NUM_DWORDS; dword++) begin
                kv_rd_resp[client].read_data |= kv_read[client].entry_is_pcr & (kv_read[client].read_entry == entry) & (kv_read[client].read_offset == dword) &
                                                ~kv_reg_hwif_out.PCR_CTRL[entry].lock_use.value & kv_reg_hwif_out.PCR_CTRL[entry].dest_valid.value[client] ? 
                                                 kv_reg_hwif_out.PCR_ENTRY[entry][dword].data.value : '0;
            end
        kv_rd_resp[client].error |= kv_read[client].entry_is_pcr & (kv_read[client].read_entry == entry) & 
                                    (kv_reg_hwif_out.KEY_CTRL[entry].lock_use.value | ~kv_reg_hwif_out.KEY_CTRL[entry].dest_valid.value[client]);
        end
    end
end

//Write error when attempting to write to entry that is locked for writes
always_comb begin : keyvault_write_resp
    for (int client = 0 ; client < KV_NUM_WRITE; client++) begin
        kv_wr_resp[client].error = '0;
        for (int entry = 0; entry < KV_NUM_PCR; entry++) begin
            kv_wr_resp[client].error |= (kv_write[client].write_entry == entry) & 
                                        kv_write[client].entry_is_pcr & kv_write[client].write_en &
                                        kv_reg_hwif_out.PCR_CTRL[entry].lock_wr.value;
        end
        for (int entry = 0; entry < KV_NUM_KEYS; entry++) begin
            kv_wr_resp[client].error |= (kv_write[client].write_entry == entry) & 
                                        ~kv_write[client].entry_is_pcr & kv_write[client].write_en &
                                        kv_reg_hwif_out.PCR_CTRL[entry].lock_wr.value;
        end
    end
end

//tie-offs
always_comb begin
    for (int entry = 0; entry < KV_NUM_KEYS; entry++) begin
        kv_reg_hwif_in.KEY_CTRL[entry].rsvd0.hwclr = '0;
    end
    for (int entry = 0; entry < KV_NUM_PCR; entry++) begin
        kv_reg_hwif_in.PCR_CTRL[entry].rsvd0.hwclr = '0;
    end
end


always_comb kv_reg_hwif_in.hard_reset_b = cptra_pwrgood;
always_comb kv_reg_hwif_in.reset_b = rst_b;

kv_reg kv_reg1 (
    .clk(clk),
    .rst('0),
    //qualify request so no addresses alias
    .s_cpuif_req(uc_req_dv & (uc_req.addr[KV_ADDR_W-1:KV_REG_ADDR_WIDTH] == '0)),
    .s_cpuif_req_is_wr(uc_req.write),
    .s_cpuif_addr(uc_req.addr[KV_REG_ADDR_WIDTH-1:0]),
    .s_cpuif_wr_data(uc_req.wdata),
    .s_cpuif_req_stall_wr(),
    .s_cpuif_req_stall_rd(),
    .s_cpuif_rd_ack(),
    .s_cpuif_rd_err(kv_reg_read_error),
    .s_cpuif_rd_data(uc_req_rdata),
    .s_cpuif_wr_ack(),
    .s_cpuif_wr_err(kv_reg_write_error),
    
    .hwif_in(kv_reg_hwif_in),
    .hwif_out(kv_reg_hwif_out)
);

endmodule
