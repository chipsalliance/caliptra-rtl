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
    input logic core_only_rst_b,
    input logic cptra_pwrgood,
    input logic fw_update_rst_window,
    input logic cptra_in_debug_scan_mode,
    input logic debugUnlock_or_scan_mode_switch,
    
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
    output kv_wr_resp_t [KV_NUM_WRITE-1:0] kv_wr_resp,
    output logic [ECC_NUM_DWORDS-1:0][31:0]     pcr_ecc_signing_key,
    output logic [MLDSA_NUM_DWORDS-1:0][31:0]   pcr_mldsa_signing_key
);

logic uc_req_dv, uc_req_hold;
logic uc_req_error;
logic [31:0] uc_req_rdata;
logic kv_reg_read_error, kv_reg_write_error;
logic [AHB_ADDR_WIDTH-1:0] uc_req_addr;
kv_uc_req_t uc_req;

logic flush_keyvault;
logic [31:0] debug_value;

//intermediate signals to make verilator happy
logic [KV_NUM_KEYS-1:0][KV_NUM_DWORDS-1:0] key_entry_we;
logic [KV_NUM_KEYS-1:0] key_entry_ctrl_we;
logic [KV_NUM_KEYS-1:0][KV_NUM_DWORDS-1:0][31:0] key_entry_next;
logic [KV_NUM_KEYS-1:0][KV_NUM_READ-1:0] key_entry_dest_valid_next;
logic [KV_NUM_KEYS-1:0][KV_ENTRY_SIZE_W-1:0] key_entry_last_dword_next;
logic [KV_NUM_KEYS-1:0] lock_wr_q;
logic [KV_NUM_KEYS-1:0] lock_use_q;
kv_reg__in_t kv_reg_hwif_in;
kv_reg__out_t kv_reg_hwif_out;

logic [KV_NUM_KEYS-1:0] key_entry_clear;

logic [$clog2(KV_NUM_WRITE)-1:0] kv_write_cnt;
logic kv_multi_write_err;

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
    .addr(uc_req_addr),

    .rdata(uc_req_rdata)
);

always_comb uc_req.addr = uc_req_addr[KV_ADDR_W-1:0];
always_comb uc_req_error = kv_reg_read_error | kv_reg_write_error;
always_comb uc_req_hold = '0;

//Flush the keyvault with the debug value when FW pokes the register or we detect debug mode unlocking
always_comb flush_keyvault = debugUnlock_or_scan_mode_switch | 
                             (cptra_in_debug_scan_mode & kv_reg_hwif_out.CLEAR_SECRETS.wr_debug_values.value);
//Pick between keyvault debug mode 0 or 1
always_comb debug_value = kv_reg_hwif_out.CLEAR_SECRETS.sel_debug_value.value ? CLP_DEBUG_MODE_KV_1 : CLP_DEBUG_MODE_KV_0;

always_comb begin : keyvault_pcr_ecc_signing
    for (int dword = 0; dword < ECC_NUM_DWORDS; dword++) begin
        pcr_ecc_signing_key[dword] = kv_reg_hwif_out.KEY_ENTRY[KV_ENTRY_FOR_ECC_SIGNING][dword].data.value;
    end 
end

always_comb begin : keyvault_pcr_mldsa_signing
    for (int dword = 0; dword < MLDSA_NUM_DWORDS; dword++) begin
        pcr_mldsa_signing_key[dword] = kv_reg_hwif_out.KEY_ENTRY[KV_ENTRY_FOR_MLDSA_SIGNING][dword].data.value;
    end 
end

always_comb begin
    kv_write_cnt = 0;
    for (int client = 0; client < KV_NUM_WRITE; client++)begin
        if (kv_write[client].write_en)
            kv_write_cnt = kv_write_cnt + 'd1;
    end
end

always_comb kv_multi_write_err = kv_write_cnt > 1;

//Generate clear signal for each key entry 
//don't clear when writes are locked
//hold the clear when writes are in progress
generate
    for (genvar g_entry = 0; g_entry < KV_NUM_KEYS; g_entry++) begin
        always_ff@(posedge clk or negedge rst_b) begin
            if(~rst_b) begin
                key_entry_clear[g_entry] <= '0;
            end
            else begin
                key_entry_clear[g_entry] <= kv_multi_write_err |
                                            (kv_reg_hwif_out.KEY_CTRL[g_entry].clear.value & ~lock_wr_q[g_entry] & ~lock_use_q[g_entry]) |
                                            (key_entry_clear[g_entry] & key_entry_ctrl_we[g_entry]);
            end
        end
    end
endgenerate

always_comb begin : keyvault_ctrl
    //keyvault control registers
    for (int entry = 0; entry < KV_NUM_KEYS; entry++) begin
        //init for AND-OR
        key_entry_ctrl_we[entry] = '0;
        key_entry_dest_valid_next[entry] = '0; 
        key_entry_last_dword_next[entry] = '0;

        //Qualify lock signals as they are on fw upd reset and create RDC violations if allowed to reset asynchronously
        lock_wr_q[entry] = kv_reg_hwif_out.KEY_CTRL[entry].lock_wr.value & ~fw_update_rst_window;
        lock_use_q[entry] = kv_reg_hwif_out.KEY_CTRL[entry].lock_use.value & ~fw_update_rst_window;
        
        for (int client = 0; client < KV_NUM_WRITE; client++) begin
            key_entry_ctrl_we[entry] |= (kv_write[client].write_entry == entry) & kv_write[client].write_en & 
                                        ~lock_wr_q[entry] & ~lock_use_q[entry]; 
            key_entry_dest_valid_next[entry] |= (kv_write[client].write_entry == entry) & kv_write[client].write_en ? kv_write[client].write_dest_valid : '0;
            //store the final offset on the last write cycle, we'll use that to signal last dword on reads
            key_entry_last_dword_next[entry] |= (kv_write[client].write_entry == entry) & kv_write[client].write_en ? kv_write[client].write_offset : '0;
        end 
        //once lock is set, only reset can unset it
        kv_reg_hwif_in.KEY_CTRL[entry].lock_wr.swwel = lock_wr_q[entry];
        kv_reg_hwif_in.KEY_CTRL[entry].lock_use.swwel = lock_use_q[entry];
        //clear dest valid and last dword
        kv_reg_hwif_in.KEY_CTRL[entry].dest_valid.hwclr = key_entry_clear[entry];
        kv_reg_hwif_in.KEY_CTRL[entry].last_dword.hwclr = key_entry_clear[entry];

        kv_reg_hwif_in.KEY_CTRL[entry].dest_valid.we = key_entry_ctrl_we[entry] & ~key_entry_clear[entry];
        kv_reg_hwif_in.KEY_CTRL[entry].dest_valid.next = {3'd0,key_entry_dest_valid_next[entry]};
        kv_reg_hwif_in.KEY_CTRL[entry].last_dword.we = key_entry_ctrl_we[entry] & ~key_entry_clear[entry];
        kv_reg_hwif_in.KEY_CTRL[entry].last_dword.next = key_entry_last_dword_next[entry];
    end

    //keyvault storage
    //AND-OR mux writes to each entry from crypto blocks
    //write to the appropriate dest entry and offset when write_en is set
    for (int entry = 0; entry < KV_NUM_KEYS; entry++) begin
        for (int dword = 0; dword < KV_NUM_DWORDS; dword++) begin
            kv_reg_hwif_in.KEY_ENTRY[entry][dword].data.swwel = '1; //never allow sw writes
            //initialize to 0 for AND-OR mux
            key_entry_we[entry][dword] = '0;
            key_entry_next[entry][dword] = '0;
            for (int client = 0; client < KV_NUM_WRITE; client++) begin
                key_entry_we[entry][dword] |= ((((kv_write[client].write_entry == entry) & (kv_write[client].write_offset == dword) & 
                                                kv_write[client].write_en) | flush_keyvault) & 
                                              ((~lock_wr_q[entry] & ~lock_use_q[entry]) | debugUnlock_or_scan_mode_switch));
                key_entry_next[entry][dword] |= flush_keyvault ? debug_value :
                                                kv_write[client].write_en & (kv_write[client].write_entry == entry) ? kv_write[client].write_data : '0;
            end
            kv_reg_hwif_in.KEY_ENTRY[entry][dword].data.we = key_entry_we[entry][dword] & ~key_entry_clear[entry];
            kv_reg_hwif_in.KEY_ENTRY[entry][dword].data.next = key_entry_next[entry][dword];
            kv_reg_hwif_in.KEY_ENTRY[entry][dword].data.hwclr = key_entry_clear[entry];
        end
    end
end

//read mux for keyvault
//qualify with selected entry, offset
//qualify with lock use bit to ensure that locked values aren't read
//qualify with dest valid to ensure requesting client has permission to read this entry
always_comb begin : keyvault_readmux
    for (int client = 0; client < KV_NUM_READ; client++) begin  
        kv_rd_resp[client].read_data = '0;
        kv_rd_resp[client].error = '0;
        kv_rd_resp[client].last = '0;
        for (int entry = 0; entry < KV_NUM_KEYS; entry++) begin
            for (int dword = 0; dword < KV_NUM_DWORDS; dword++) begin
                kv_rd_resp[client].read_data |= (kv_read[client].read_entry == entry) & (kv_read[client].read_offset == dword) &
                                                ~lock_use_q[entry] & kv_reg_hwif_out.KEY_CTRL[entry].dest_valid.value[client] ? 
                                                 kv_reg_hwif_out.KEY_ENTRY[entry][dword].data.value : '0;
            end
        //signal last when reading the last dword
        kv_rd_resp[client].last |= (kv_read[client].read_entry == entry) & (kv_read[client].read_offset == kv_reg_hwif_out.KEY_CTRL[entry].last_dword.value);
        kv_rd_resp[client].error |= (kv_read[client].read_entry == entry) & 
                                    (lock_use_q[entry] | ~kv_reg_hwif_out.KEY_CTRL[entry].dest_valid.value[client]);
        end
    end
end

//Write error when attempting to write to entry that is locked for writes, use, or is being cleared
always_comb begin : keyvault_write_resp
    for (int client = 0 ; client < KV_NUM_WRITE; client++) begin
        kv_wr_resp[client].error = '0;
        for (int entry = 0; entry < KV_NUM_KEYS; entry++) begin
            kv_wr_resp[client].error |= (kv_write[client].write_entry == entry) & kv_write[client].write_en &
                                        (key_entry_clear[entry] | lock_wr_q[entry] | lock_use_q[entry]);
        end
    end
end

//tie-offs
always_comb begin
    for (int entry = 0; entry < KV_NUM_KEYS; entry++) begin
        kv_reg_hwif_in.KEY_CTRL[entry].rsvd0.hwclr = '0;
    end
end


always_comb kv_reg_hwif_in.hard_reset_b = cptra_pwrgood;
always_comb kv_reg_hwif_in.reset_b = rst_b;
always_comb kv_reg_hwif_in.core_only_rst_b = core_only_rst_b; //Note that this signal will also reset when rst_b is asserted

kv_reg kv_reg1 (
    .clk(clk),
    .rst('0),
    //qualify request so no addresses alias
    .s_cpuif_req(uc_req_dv),
    .s_cpuif_req_is_wr(uc_req.write),
    .s_cpuif_addr(uc_req.addr[KV_REG_ADDR_WIDTH-1:0]),
    .s_cpuif_wr_data(uc_req.wdata),
    .s_cpuif_wr_biten('1),
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
