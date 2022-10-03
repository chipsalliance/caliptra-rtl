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


`include "kv_defines.svh"

module kv #(
     parameter KV_NUM_READ = 1
    ,parameter KV_NUM_WRITE = 1
    ,parameter AHB_ADDR_WIDTH = 32
    ,parameter AHB_DATA_WIDTH = 32
    )
    (
    input logic clk,
    input logic rst_b,
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
    output logic [AHB_DATA_WIDTH-1:0]     hrdata_o,

    input kv_read_t [KV_NUM_READ-1:0]     kv_read,
    input kv_write_t [KV_NUM_WRITE-1:0]   kv_write,
    output kv_resp_t [KV_NUM_READ-1:0]    kv_resp

);

logic uc_req_dv, uc_req_hold;
logic uc_req_error;
logic [31:0] uc_req_rdata;
logic kv_reg_read_error, kv_reg_write_error;
kv_uc_req_t uc_req;

kv_reg_pkg::kv_reg__in_t kv_reg_hwif_in;
kv_reg_pkg::kv_reg__out_t kv_reg_hwif_out;

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
    .hold(uc_req_hold),
    .error(uc_req_error),
    .write(uc_req.write),
    .wdata(uc_req.wdata),
    .addr(uc_req.addr),

    .rdata(uc_req_rdata)
);

always_comb uc_req_error = kv_reg_read_error | kv_reg_write_error;
always_comb uc_req_hold = '0;
always_comb kv_reg_hwif_in.reset_b = rst_b;

always_comb begin : keyvault_ctrl
    //keyvault control registers
    for (int entry = 0; entry < KV_NUM_KEYS; entry++) begin
        //once lock is set, only reset can unset it
        kv_reg_hwif_in.key_ctrl[entry].lock_rd.swwel = kv_reg_hwif_out.key_ctrl[entry].lock_rd.value;
        kv_reg_hwif_in.key_ctrl[entry].lock_wr.swwel = kv_reg_hwif_out.key_ctrl[entry].lock_wr.value;
        kv_reg_hwif_in.key_ctrl[entry].lock_use.swwel = kv_reg_hwif_out.key_ctrl[entry].lock_use.value;
        //init for AND-OR
        kv_reg_hwif_in.key_ctrl[entry].dest_valid.next = '0; 
        kv_reg_hwif_in.key_ctrl[entry].dest_valid.we = '0;
        for (int client = 0; client < KV_NUM_WRITE; client++) begin
            kv_reg_hwif_in.key_ctrl[entry].dest_valid.we |= (kv_write[client].dest_addr == entry) & ~kv_write[client].dest_is_pcr & kv_write[client].dest_wr_vld; 
            kv_reg_hwif_in.key_ctrl[entry].dest_valid.next |= kv_write[client].dest_wr_vld ? kv_write[client].dest_valid : '0; 
        end 
    end

    for (int entry = 0; entry < KV_NUM_PCR; entry++) begin
        kv_reg_hwif_in.pcr_ctrl[entry].lock_rd.swwel = kv_reg_hwif_out.pcr_ctrl[entry].lock_rd.value;
        kv_reg_hwif_in.pcr_ctrl[entry].lock_wr.swwel = kv_reg_hwif_out.pcr_ctrl[entry].lock_wr.value;
        kv_reg_hwif_in.pcr_ctrl[entry].lock_use.swwel = kv_reg_hwif_out.pcr_ctrl[entry].lock_use.value;
        //init for AND-OR
        kv_reg_hwif_in.pcr_ctrl[entry].dest_valid.next = '0; 
        kv_reg_hwif_in.pcr_ctrl[entry].dest_valid.we = '0; 
        for (int client = 0; client < KV_NUM_WRITE; client++) begin
            kv_reg_hwif_in.pcr_ctrl[entry].dest_valid.we |= (kv_write[client].dest_addr == entry) & kv_write[client].dest_is_pcr & kv_write[client].dest_wr_vld; 
            kv_reg_hwif_in.pcr_ctrl[entry].dest_valid.next |= kv_write[client].dest_wr_vld? kv_write[client].dest_valid : '0; 
        end 
    end

    //keyvault storage
    //AND-OR mux writes to each entry from crypto blocks
    //write to the appropriate dest entry and offset when dest_wr_vld is set
    for (int entry = 0; entry < KV_NUM_KEYS; entry++) begin
        for (int dword = 0; dword < KV_NUM_DWORDS; dword++) begin
            kv_reg_hwif_in.key_entry[entry][dword].data.swwel = '1; //never allow sw writes
            //initialize to 0 for AND-OR mux
            kv_reg_hwif_in.key_entry[entry][dword].data.next = '0;
            kv_reg_hwif_in.key_entry[entry][dword].data.we = '0;
            for (int client = 0; client < KV_NUM_WRITE; client++) begin
                kv_reg_hwif_in.key_entry[entry][dword].data.hwclr = kv_reg_hwif_out.key_ctrl[entry].clear.value;
                kv_reg_hwif_in.key_entry[entry][dword].data.we |= (kv_write[client].dest_addr == entry) & (kv_write[client].dest_offset == dword) & 
                                                                  ~kv_write[client].dest_is_pcr & kv_write[client].dest_wr_vld;
                kv_reg_hwif_in.key_entry[entry][dword].data.next |= kv_write[client].dest_wr_vld ? kv_write[client].dest_data : '0;
            end
        end
    end
    for (int entry = 0; entry < KV_NUM_PCR; entry++) begin
        for (int dword = 0; dword < KV_NUM_DWORDS; dword++) begin
            kv_reg_hwif_in.pcr_entry[entry][dword].data.swwel = kv_reg_hwif_out.pcr_ctrl[entry].lock_wr.value; //disable sw writes if locked
            //initialize to 0 for AND-OR mux
            kv_reg_hwif_in.pcr_entry[entry][dword].data.next = '0; //hook up the next data to write from crypto writing to this key
            kv_reg_hwif_in.pcr_entry[entry][dword].data.we = '0; //hook up the write enable from crypto writing to this key
            for (int client = 0; client < KV_NUM_WRITE; client++) begin
                kv_reg_hwif_in.pcr_entry[entry][dword].data.hwclr = kv_reg_hwif_out.pcr_ctrl[entry].clear.value;
                kv_reg_hwif_in.pcr_entry[entry][dword].data.we |= (kv_write[client].dest_addr == entry) & (kv_write[client].dest_offset == dword) & 
                                                                   kv_write[client].dest_is_pcr & kv_write[client].dest_wr_vld;
                kv_reg_hwif_in.pcr_entry[entry][dword].data.next |= kv_write[client].dest_wr_vld ? kv_write[client].dest_data : '0;
            end 
        end
    end
end

//read mux for keyvault
//qualify with selected entry, offset, and pcr or not for key and src
//qualify with lock use bit to ensure that locked values aren't read
//qualify with dest valid to ensure requesting client has permission to read this entry
always_comb begin : keyvault_readmux
    for (int client = 0; client < KV_NUM_READ; client++) begin  
        kv_resp[client].key_data = '0;
        kv_resp[client].src_data = '0;  
        for (int entry = 0; entry < KV_NUM_KEYS; entry++) begin
            for (int dword = 0; dword < KV_NUM_DWORDS; dword++) begin
                kv_resp[client].key_data |= ~kv_read[client].key_is_pcr & (kv_read[client].key_entry == entry) & (kv_read[client].key_offset == dword) &
                                            ~kv_reg_hwif_out.key_ctrl[entry].lock_use.value & kv_reg_hwif_out.key_ctrl[entry].dest_valid.value[client] ? 
                                            kv_reg_hwif_out.key_entry[entry][dword].data.value : '0;
                kv_resp[client].src_data |= ~kv_read[client].src_is_pcr & (kv_read[client].src_entry == entry) & (kv_read[client].src_offset == dword) &
                                            ~kv_reg_hwif_out.key_ctrl[entry].lock_use.value & kv_reg_hwif_out.key_ctrl[entry].dest_valid.value[client] ? 
                                            kv_reg_hwif_out.key_entry[entry][dword].data.value : '0;
            end
        end
        for (int entry = 0; entry < KV_NUM_PCR; entry++) begin
            for (int dword = 0; dword < KV_NUM_DWORDS; dword++) begin
                kv_resp[client].key_data |= kv_read[client].key_is_pcr & (kv_read[client].key_entry == entry) & (kv_read[client].key_offset == dword) &
                                            ~kv_reg_hwif_out.pcr_ctrl[entry].lock_use.value & kv_reg_hwif_out.pcr_ctrl[entry].dest_valid.value[client] ? 
                                            kv_reg_hwif_out.pcr_entry[entry][dword].data.value : '0;
                kv_resp[client].src_data |= kv_read[client].src_is_pcr & (kv_read[client].src_entry == entry) & (kv_read[client].src_offset == dword) &
                                           ~kv_reg_hwif_out.pcr_ctrl[entry].lock_use.value & kv_reg_hwif_out.pcr_ctrl[entry].dest_valid.value[client] ? 
                                           kv_reg_hwif_out.pcr_entry[entry][dword].data.value : '0;
            end
        end
    end
end

always_comb kv_reg_hwif_in.hard_reset_b = cptra_pwrgood;

kv_reg kv_reg1 (
    .clk(clk),
    .rst('0),
    //qualify request so no addresses alias
    .s_cpuif_req(uc_req_dv & (uc_req.addr[KV_ADDR_W-1:11] == '0)),
    .s_cpuif_req_is_wr(uc_req.write),
    .s_cpuif_addr(uc_req.addr[10:0]),
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
