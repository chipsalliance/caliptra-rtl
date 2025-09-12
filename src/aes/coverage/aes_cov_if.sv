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



`ifndef VERILATOR

interface aes_cov_if
    import aes_pkg::*;
    import kv_defines_pkg::*;
    import aes_clp_reg_pkg::*;
    #(
        parameter AHB_DATA_WIDTH = 32,
        parameter AHB_ADDR_WIDTH = 32,
        parameter CIF_DATA_WIDTH = 32,
        localparam CIF_DATA_NUM_BYTES = CIF_DATA_WIDTH / 8
    )
    (
        // Clock and reset.
        input wire           clk,
        input wire           reset_n,
        input wire           cptra_pwrgood,

        input logic [AHB_ADDR_WIDTH-1:0] haddr_i,
        input logic [AHB_DATA_WIDTH-1:0] hwdata_i,
        input logic hsel_i,
        input logic hwrite_i,
        input logic hready_i,
        input logic [1:0] htrans_i,
        input logic [2:0] hsize_i,

        input logic hresp_o,
        input logic hreadyout_o,
        input logic [AHB_DATA_WIDTH-1:0] hrdata_o,
      
        // OCP LOCK
        input logic ocp_lock_in_progress,
        input logic [15:0] key_release_key_size,

        // status signals
        input logic input_ready_o,
        input logic output_valid_o,
        input logic status_idle_o,
        
        // DMA CIF
        input logic dma_req_dv,
        input logic dma_req_write,
        input logic   [AHB_ADDR_WIDTH-1 : 0] dma_req_addr,
        input logic   [CIF_DATA_WIDTH-1 : 0] dma_req_wdata,
        input logic dma_req_hold,
        input logic dma_req_error,
        input logic   [CIF_DATA_WIDTH-1 : 0] dma_req_rdata,
      
        // kv interface
        input kv_read_t kv_read,
        input kv_rd_resp_t kv_rd_resp,
        input kv_write_t kv_write,
        input kv_wr_resp_t kv_wr_resp,

        input logic busy_o,

        // Interrupt
        input logic error_intr,
        input logic notif_intr,
        input logic debugUnlock_or_scan_mode_switch,

        // Internal signals in aes_clp_wrapper
        input kv_write_ctrl_reg_t kv_write_ctrl_reg,
        input logic [KV_ENTRY_ADDR_W-1:0] kv_key_present_slot,
        input kv_write_filter_metrics_t kv_write_metrics,
        input caliptra2aes_t caliptra2aes,
        input aes2caliptra_t aes2caliptra
    );

    covergroup aes_clp_wrapper_cov_grp @(posedge clk);
        reset_n_cp: coverpoint reset_n;
        cptra_pwrgood_cp: coverpoint cptra_pwrgood;

        haddr_i_cp: coverpoint haddr_i;
        hwdata_i_cp: coverpoint hwdata_i;
        hsel_i_cp: coverpoint hsel_i;
        hwrite_i_cp: coverpoint hwrite_i;
        hready_i_cp: coverpoint hready_i;
        htrans_i_cp: coverpoint htrans_i;
        hsize_i_cp: coverpoint hsize_i;

        hresp_o_cp: coverpoint hresp_o;
        hreadyout_o_cp: coverpoint hreadyout_o;
        hrdata_o_cp: coverpoint hrdata_o;
      
        // OCP LOCK
        ocp_lock_in_progress_cp: coverpoint ocp_lock_in_progress;
        key_release_key_size_cp: coverpoint key_release_key_size {
            bins zero = {0};
            bins lt_64bytes = {[1:63]};
            bins eq_64bytes = {64};
            bins gt_64bytes = {[65:65535]};
        }

        // status signals
        input_ready_o_cp: coverpoint input_ready_o;
        output_valid_o_cp: coverpoint output_valid_o;
        status_idle_o_cp: coverpoint status_idle_o;
        
        // DMA CIF
        dma_req_dv_cp: coverpoint dma_req_dv;
        dma_req_write_cp: coverpoint dma_req_write;
        dma_req_addr_cp: coverpoint dma_req_addr;
        dma_req_wdata_cp: coverpoint dma_req_wdata;
        dma_req_hold_cp: coverpoint dma_req_hold;
        dma_req_error_cp: coverpoint dma_req_error;
        dma_req_rdata_cp: coverpoint dma_req_rdata;
      
        // kv interface
        kv_read_read_entry_cp:   coverpoint kv_read.read_entry;
        kv_read_read_offset_cp:  coverpoint kv_read.read_offset;
        kv_rd_resp_error_cp:     coverpoint kv_rd_resp.error;
        kv_rd_resp_last_cp:      coverpoint kv_rd_resp.last;
        kv_rd_resp_read_data_cp: coverpoint kv_rd_resp.read_data;
        kv_write_write_en_cp:         coverpoint kv_write.write_en;
        kv_write_write_entry_cp:      coverpoint kv_write.write_entry;
        kv_write_write_offset_cp:     coverpoint kv_write.write_offset;
        kv_write_write_data_cp:       coverpoint kv_write.write_data;
        kv_write_write_dest_valid_cp: coverpoint kv_write.write_dest_valid;
        kv_wr_resp_error_cp:          coverpoint kv_wr_resp.error;

        busy_o_cp: coverpoint busy_o;

        // Interrupt
        error_intr_cp: coverpoint error_intr;
        notif_intr_cp: coverpoint notif_intr;
        debugUnlock_or_scan_mode_switch_cp: coverpoint debugUnlock_or_scan_mode_switch;
    endgroup


    // KV read interface
    // KV write interface
    // OCP LOCK flows
    //  * MEK decryption
    covergroup aes_ocp_lock_flow_grp @(posedge clk);
        ocp_lock_in_progress_cp:  coverpoint ocp_lock_in_progress;
        key_is_kv_cp:             coverpoint busy_o && aes_inst.hw2reg.ctrl_shadowed.sideload.d;
        key_is_kv_rt_obf_key_cp:  coverpoint busy_o && aes_inst.hw2reg.ctrl_shadowed.sideload.d && (kv_key_present_slot == OCP_LOCK_RT_OBF_KEY_KV_SLOT);
        op_is_decrypt_cp:         coverpoint busy_o && (aes_op_e'(aes_inst.hw2reg.ctrl_shadowed.operation.d) == AES_DEC);
        mode_is_ecb_cp:           coverpoint busy_o && (aes_mode_e'(aes_inst.hw2reg.ctrl_shadowed.mode.d) == AES_ECB);
        output_is_kv_cp:          coverpoint busy_o && caliptra2aes.kv_en;
        output_is_kv_mek_slot_cp: coverpoint busy_o && caliptra2aes.kv_en && (kv_write_ctrl_reg.write_entry == OCP_LOCK_KEY_RELEASE_KV_SLOT);

        kv_read_entry_0_cp: coverpoint {kv_write_metrics.kv_data0_present, kv_write_metrics.kv_data0_entry} 
        iff (busy_o) {
            bins fw = {[0:23]}; //{1'b0, [0:$]};
            bins lower_slots = {[32:47]}; //{1'b1, [0:15]};
            bins upper_slots = {[48:54]}; //{1'b1, [16:22]};
            bins slot_23 = {55}; //{1'b1, 23};
        }

        kv_write_entry_cp: coverpoint {kv_write_ctrl_reg.write_en, kv_write_metrics.kv_write_entry}
        iff (busy_o) {
            bins fw = {[0:23]}; //{1'b0, [0:$]};
            bins lower_slots = {[32:47]}; //{1'b1, [0:15]};
            bins upper_slots = {[48:54]}; //{1'b1, [16:22]};
            bins slot_23 = {55}; //{1'b1, 23};
        }

        // Crosses
        ocp_lock_flow_mek_dec_X: cross ocp_lock_in_progress_cp,
                                       key_is_kv_rt_obf_key_cp,
                                       op_is_decrypt_cp,
                                       mode_is_ecb_cp,
                                       output_is_kv_mek_slot_cp;
        ocp_lock_flow_kv_write_ctx_clear_X: cross aes2caliptra.kv_data_out_valid, caliptra2aes.clear_secrets, aes_inst.reg2hw_caliptra.trigger.data_out_clear.q;
        ocp_lock_X_kv_entry: cross ocp_lock_in_progress_cp, kv_write_entry_cp, kv_read_entry_0_cp;
    endgroup

    aes_clp_wrapper_cov_grp aes_clp_wrapper_cov_grp1 = new();
    aes_ocp_lock_flow_grp   aes_ocp_lock_flow_grp1   = new();



endinterface


`endif

