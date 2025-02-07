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

`ifndef AXI_DMA_REG_COVERGROUPS
    `define AXI_DMA_REG_COVERGROUPS
    
    /*----------------------- AXI_DMA_REG__ID COVERGROUPS -----------------------*/
    covergroup axi_dma_reg__id_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup axi_dma_reg__id_fld_cg with function sample(
    input bit [32-1:0] id
    );
        option.per_instance = 1;
        id_cp : coverpoint id;

    endgroup

    /*----------------------- AXI_DMA_REG__CAP COVERGROUPS -----------------------*/
    covergroup axi_dma_reg__cap_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup axi_dma_reg__cap_fld_cg with function sample(
    input bit [12-1:0] fifo_max_depth,
    input bit [20-1:0] rsvd
    );
        option.per_instance = 1;
        fifo_max_depth_cp : coverpoint fifo_max_depth;
        rsvd_cp : coverpoint rsvd;

    endgroup

    /*----------------------- AXI_DMA_REG__CTRL COVERGROUPS -----------------------*/
    covergroup axi_dma_reg__ctrl_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup axi_dma_reg__ctrl_fld_cg with function sample(
    input bit [1-1:0] go,
    input bit [1-1:0] flush,
    input bit [14-1:0] rsvd0,
    input bit [2-1:0] rd_route,
    input bit [2-1:0] rsvd1,
    input bit [1-1:0] rd_fixed,
    input bit [3-1:0] rsvd2,
    input bit [2-1:0] wr_route,
    input bit [2-1:0] rsvd3,
    input bit [1-1:0] wr_fixed,
    input bit [3-1:0] rsvd4
    );
        option.per_instance = 1;
        go_cp : coverpoint go;
        flush_cp : coverpoint flush;
        rsvd0_cp : coverpoint rsvd0;
        rd_route_cp : coverpoint rd_route;
        rsvd1_cp : coverpoint rsvd1;
        rd_fixed_cp : coverpoint rd_fixed;
        rsvd2_cp : coverpoint rsvd2;
        wr_route_cp : coverpoint wr_route;
        rsvd3_cp : coverpoint rsvd3;
        wr_fixed_cp : coverpoint wr_fixed;
        rsvd4_cp : coverpoint rsvd4;

    endgroup

    /*----------------------- AXI_DMA_REG__STATUS0 COVERGROUPS -----------------------*/
    covergroup axi_dma_reg__status0_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup axi_dma_reg__status0_fld_cg with function sample(
    input bit [1-1:0] busy,
    input bit [1-1:0] error,
    input bit [2-1:0] rsvd0,
    input bit [12-1:0] fifo_depth,
    input bit [2-1:0] axi_dma_fsm_ps,
    input bit [1-1:0] payload_available,
    input bit [1-1:0] image_activated,
    input bit [12-1:0] rsvd1
    );
        option.per_instance = 1;
        busy_cp : coverpoint busy;
        error_cp : coverpoint error;
        rsvd0_cp : coverpoint rsvd0;
        fifo_depth_cp : coverpoint fifo_depth;
        axi_dma_fsm_ps_cp : coverpoint axi_dma_fsm_ps;
        payload_available_cp : coverpoint payload_available;
        image_activated_cp : coverpoint image_activated;
        rsvd1_cp : coverpoint rsvd1;

    endgroup

    /*----------------------- AXI_DMA_REG__STATUS1 COVERGROUPS -----------------------*/
    covergroup axi_dma_reg__status1_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup axi_dma_reg__status1_fld_cg with function sample(
    input bit [32-1:0] bytes_remaining
    );
        option.per_instance = 1;
        bytes_remaining_cp : coverpoint bytes_remaining;

    endgroup

    /*----------------------- AXI_DMA_REG__SRC_ADDR_L COVERGROUPS -----------------------*/
    covergroup axi_dma_reg__src_addr_l_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup axi_dma_reg__src_addr_l_fld_cg with function sample(
    input bit [32-1:0] addr_l
    );
        option.per_instance = 1;
        addr_l_cp : coverpoint addr_l;

    endgroup

    /*----------------------- AXI_DMA_REG__SRC_ADDR_H COVERGROUPS -----------------------*/
    covergroup axi_dma_reg__src_addr_h_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup axi_dma_reg__src_addr_h_fld_cg with function sample(
    input bit [32-1:0] addr_h
    );
        option.per_instance = 1;
        addr_h_cp : coverpoint addr_h;

    endgroup

    /*----------------------- AXI_DMA_REG__DST_ADDR_L COVERGROUPS -----------------------*/
    covergroup axi_dma_reg__dst_addr_l_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup axi_dma_reg__dst_addr_l_fld_cg with function sample(
    input bit [32-1:0] addr_l
    );
        option.per_instance = 1;
        addr_l_cp : coverpoint addr_l;

    endgroup

    /*----------------------- AXI_DMA_REG__DST_ADDR_H COVERGROUPS -----------------------*/
    covergroup axi_dma_reg__dst_addr_h_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup axi_dma_reg__dst_addr_h_fld_cg with function sample(
    input bit [32-1:0] addr_h
    );
        option.per_instance = 1;
        addr_h_cp : coverpoint addr_h;

    endgroup

    /*----------------------- AXI_DMA_REG__BYTE_COUNT COVERGROUPS -----------------------*/
    covergroup axi_dma_reg__byte_count_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup axi_dma_reg__byte_count_fld_cg with function sample(
    input bit [32-1:0] count
    );
        option.per_instance = 1;
        count_cp : coverpoint count;

    endgroup

    /*----------------------- AXI_DMA_REG__BLOCK_SIZE COVERGROUPS -----------------------*/
    covergroup axi_dma_reg__block_size_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup axi_dma_reg__block_size_fld_cg with function sample(
    input bit [12-1:0] size,
    input bit [20-1:0] rsvd
    );
        option.per_instance = 1;
        size_cp : coverpoint size;
        rsvd_cp : coverpoint rsvd;

    endgroup

    /*----------------------- AXI_DMA_REG__WRITE_DATA COVERGROUPS -----------------------*/
    covergroup axi_dma_reg__write_data_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup axi_dma_reg__write_data_fld_cg with function sample(
    input bit [32-1:0] wdata
    );
        option.per_instance = 1;
        wdata_cp : coverpoint wdata;

    endgroup

    /*----------------------- AXI_DMA_REG__READ_DATA COVERGROUPS -----------------------*/
    covergroup axi_dma_reg__read_data_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup axi_dma_reg__read_data_fld_cg with function sample(
    input bit [32-1:0] rdata
    );
        option.per_instance = 1;
        rdata_cp : coverpoint rdata;

    endgroup

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__GLOBAL_INTR_EN_T COVERGROUPS -----------------------*/
    covergroup axi_dma_reg__intr_block_t__global_intr_en_t_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup axi_dma_reg__intr_block_t__global_intr_en_t_fld_cg with function sample(
    input bit [1-1:0] error_en,
    input bit [1-1:0] notif_en
    );
        option.per_instance = 1;
        error_en_cp : coverpoint error_en;
        notif_en_cp : coverpoint notif_en;

    endgroup

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__ERROR_INTR_EN_T COVERGROUPS -----------------------*/
    covergroup axi_dma_reg__intr_block_t__error_intr_en_t_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup axi_dma_reg__intr_block_t__error_intr_en_t_fld_cg with function sample(
    input bit [1-1:0] error_cmd_dec_en,
    input bit [1-1:0] error_axi_rd_en,
    input bit [1-1:0] error_axi_wr_en,
    input bit [1-1:0] error_mbox_lock_en,
    input bit [1-1:0] error_sha_lock_en,
    input bit [1-1:0] error_fifo_oflow_en,
    input bit [1-1:0] error_fifo_uflow_en
    );
        option.per_instance = 1;
        error_cmd_dec_en_cp : coverpoint error_cmd_dec_en;
        error_axi_rd_en_cp : coverpoint error_axi_rd_en;
        error_axi_wr_en_cp : coverpoint error_axi_wr_en;
        error_mbox_lock_en_cp : coverpoint error_mbox_lock_en;
        error_sha_lock_en_cp : coverpoint error_sha_lock_en;
        error_fifo_oflow_en_cp : coverpoint error_fifo_oflow_en;
        error_fifo_uflow_en_cp : coverpoint error_fifo_uflow_en;

    endgroup

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__NOTIF_INTR_EN_T COVERGROUPS -----------------------*/
    covergroup axi_dma_reg__intr_block_t__notif_intr_en_t_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup axi_dma_reg__intr_block_t__notif_intr_en_t_fld_cg with function sample(
    input bit [1-1:0] notif_txn_done_en,
    input bit [1-1:0] notif_fifo_empty_en,
    input bit [1-1:0] notif_fifo_not_empty_en,
    input bit [1-1:0] notif_fifo_full_en,
    input bit [1-1:0] notif_fifo_not_full_en
    );
        option.per_instance = 1;
        notif_txn_done_en_cp : coverpoint notif_txn_done_en;
        notif_fifo_empty_en_cp : coverpoint notif_fifo_empty_en;
        notif_fifo_not_empty_en_cp : coverpoint notif_fifo_not_empty_en;
        notif_fifo_full_en_cp : coverpoint notif_fifo_full_en;
        notif_fifo_not_full_en_cp : coverpoint notif_fifo_not_full_en;

    endgroup

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__GLOBAL_INTR_T_AGG_STS_DD3DCF0A COVERGROUPS -----------------------*/
    covergroup axi_dma_reg__intr_block_t__global_intr_t_agg_sts_dd3dcf0a_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup axi_dma_reg__intr_block_t__global_intr_t_agg_sts_dd3dcf0a_fld_cg with function sample(
    input bit [1-1:0] agg_sts
    );
        option.per_instance = 1;
        agg_sts_cp : coverpoint agg_sts;

    endgroup

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__GLOBAL_INTR_T_AGG_STS_E6399B4A COVERGROUPS -----------------------*/
    covergroup axi_dma_reg__intr_block_t__global_intr_t_agg_sts_e6399b4a_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup axi_dma_reg__intr_block_t__global_intr_t_agg_sts_e6399b4a_fld_cg with function sample(
    input bit [1-1:0] agg_sts
    );
        option.per_instance = 1;
        agg_sts_cp : coverpoint agg_sts;

    endgroup

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__ERROR_INTR_T_ERROR_AXI_RD_STS_927E49CD_ERROR_AXI_WR_STS_F84E5C07_ERROR_CMD_DEC_STS_46039D92_ERROR_FIFO_OFLOW_STS_71B29A77_ERROR_FIFO_UFLOW_STS_119D122A_ERROR_MBOX_LOCK_STS_9E18C395_ERROR_SHA_LOCK_STS_4C7993A0 COVERGROUPS -----------------------*/
    covergroup axi_dma_reg__intr_block_t__error_intr_t_error_axi_rd_sts_927e49cd_error_axi_wr_sts_f84e5c07_error_cmd_dec_sts_46039d92_error_fifo_oflow_sts_71b29a77_error_fifo_uflow_sts_119d122a_error_mbox_lock_sts_9e18c395_error_sha_lock_sts_4c7993a0_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup axi_dma_reg__intr_block_t__error_intr_t_error_axi_rd_sts_927e49cd_error_axi_wr_sts_f84e5c07_error_cmd_dec_sts_46039d92_error_fifo_oflow_sts_71b29a77_error_fifo_uflow_sts_119d122a_error_mbox_lock_sts_9e18c395_error_sha_lock_sts_4c7993a0_fld_cg with function sample(
    input bit [1-1:0] error_cmd_dec_sts,
    input bit [1-1:0] error_axi_rd_sts,
    input bit [1-1:0] error_axi_wr_sts,
    input bit [1-1:0] error_mbox_lock_sts,
    input bit [1-1:0] error_sha_lock_sts,
    input bit [1-1:0] error_fifo_oflow_sts,
    input bit [1-1:0] error_fifo_uflow_sts
    );
        option.per_instance = 1;
        error_cmd_dec_sts_cp : coverpoint error_cmd_dec_sts;
        error_axi_rd_sts_cp : coverpoint error_axi_rd_sts;
        error_axi_wr_sts_cp : coverpoint error_axi_wr_sts;
        error_mbox_lock_sts_cp : coverpoint error_mbox_lock_sts;
        error_sha_lock_sts_cp : coverpoint error_sha_lock_sts;
        error_fifo_oflow_sts_cp : coverpoint error_fifo_oflow_sts;
        error_fifo_uflow_sts_cp : coverpoint error_fifo_uflow_sts;

    endgroup

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__NOTIF_INTR_T_NOTIF_FIFO_EMPTY_STS_D87D1786_NOTIF_FIFO_FULL_STS_64C66862_NOTIF_FIFO_NOT_EMPTY_STS_1A0E2460_NOTIF_FIFO_NOT_FULL_STS_0266FE07_NOTIF_TXN_DONE_STS_0EE2F120 COVERGROUPS -----------------------*/
    covergroup axi_dma_reg__intr_block_t__notif_intr_t_notif_fifo_empty_sts_d87d1786_notif_fifo_full_sts_64c66862_notif_fifo_not_empty_sts_1a0e2460_notif_fifo_not_full_sts_0266fe07_notif_txn_done_sts_0ee2f120_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup axi_dma_reg__intr_block_t__notif_intr_t_notif_fifo_empty_sts_d87d1786_notif_fifo_full_sts_64c66862_notif_fifo_not_empty_sts_1a0e2460_notif_fifo_not_full_sts_0266fe07_notif_txn_done_sts_0ee2f120_fld_cg with function sample(
    input bit [1-1:0] notif_txn_done_sts,
    input bit [1-1:0] notif_fifo_empty_sts,
    input bit [1-1:0] notif_fifo_not_empty_sts,
    input bit [1-1:0] notif_fifo_full_sts,
    input bit [1-1:0] notif_fifo_not_full_sts
    );
        option.per_instance = 1;
        notif_txn_done_sts_cp : coverpoint notif_txn_done_sts;
        notif_fifo_empty_sts_cp : coverpoint notif_fifo_empty_sts;
        notif_fifo_not_empty_sts_cp : coverpoint notif_fifo_not_empty_sts;
        notif_fifo_full_sts_cp : coverpoint notif_fifo_full_sts;
        notif_fifo_not_full_sts_cp : coverpoint notif_fifo_not_full_sts;

    endgroup

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__ERROR_INTR_TRIG_T COVERGROUPS -----------------------*/
    covergroup axi_dma_reg__intr_block_t__error_intr_trig_t_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup axi_dma_reg__intr_block_t__error_intr_trig_t_fld_cg with function sample(
    input bit [1-1:0] error_cmd_dec_trig,
    input bit [1-1:0] error_axi_rd_trig,
    input bit [1-1:0] error_axi_wr_trig,
    input bit [1-1:0] error_mbox_lock_trig,
    input bit [1-1:0] error_sha_lock_trig,
    input bit [1-1:0] error_fifo_oflow_trig,
    input bit [1-1:0] error_fifo_uflow_trig
    );
        option.per_instance = 1;
        error_cmd_dec_trig_cp : coverpoint error_cmd_dec_trig;
        error_axi_rd_trig_cp : coverpoint error_axi_rd_trig;
        error_axi_wr_trig_cp : coverpoint error_axi_wr_trig;
        error_mbox_lock_trig_cp : coverpoint error_mbox_lock_trig;
        error_sha_lock_trig_cp : coverpoint error_sha_lock_trig;
        error_fifo_oflow_trig_cp : coverpoint error_fifo_oflow_trig;
        error_fifo_uflow_trig_cp : coverpoint error_fifo_uflow_trig;

    endgroup

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__NOTIF_INTR_TRIG_T COVERGROUPS -----------------------*/
    covergroup axi_dma_reg__intr_block_t__notif_intr_trig_t_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup axi_dma_reg__intr_block_t__notif_intr_trig_t_fld_cg with function sample(
    input bit [1-1:0] notif_txn_done_trig,
    input bit [1-1:0] notif_fifo_empty_trig,
    input bit [1-1:0] notif_fifo_not_empty_trig,
    input bit [1-1:0] notif_fifo_full_trig,
    input bit [1-1:0] notif_fifo_not_full_trig
    );
        option.per_instance = 1;
        notif_txn_done_trig_cp : coverpoint notif_txn_done_trig;
        notif_fifo_empty_trig_cp : coverpoint notif_fifo_empty_trig;
        notif_fifo_not_empty_trig_cp : coverpoint notif_fifo_not_empty_trig;
        notif_fifo_full_trig_cp : coverpoint notif_fifo_full_trig;
        notif_fifo_not_full_trig_cp : coverpoint notif_fifo_not_full_trig;

    endgroup

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_FC5260B0 COVERGROUPS -----------------------*/
    covergroup axi_dma_reg__intr_block_t__intr_count_t_cnt_fc5260b0_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup axi_dma_reg__intr_block_t__intr_count_t_cnt_fc5260b0_fld_cg with function sample(
    input bit [32-1:0] cnt
    );
        option.per_instance = 1;
        cnt_cp : coverpoint cnt;

    endgroup

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_F6D7DE6B COVERGROUPS -----------------------*/
    covergroup axi_dma_reg__intr_block_t__intr_count_t_cnt_f6d7de6b_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup axi_dma_reg__intr_block_t__intr_count_t_cnt_f6d7de6b_fld_cg with function sample(
    input bit [32-1:0] cnt
    );
        option.per_instance = 1;
        cnt_cp : coverpoint cnt;

    endgroup

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_ABA31562 COVERGROUPS -----------------------*/
    covergroup axi_dma_reg__intr_block_t__intr_count_t_cnt_aba31562_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup axi_dma_reg__intr_block_t__intr_count_t_cnt_aba31562_fld_cg with function sample(
    input bit [32-1:0] cnt
    );
        option.per_instance = 1;
        cnt_cp : coverpoint cnt;

    endgroup

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_F73463F1 COVERGROUPS -----------------------*/
    covergroup axi_dma_reg__intr_block_t__intr_count_t_cnt_f73463f1_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup axi_dma_reg__intr_block_t__intr_count_t_cnt_f73463f1_fld_cg with function sample(
    input bit [32-1:0] cnt
    );
        option.per_instance = 1;
        cnt_cp : coverpoint cnt;

    endgroup

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_5381F2ED COVERGROUPS -----------------------*/
    covergroup axi_dma_reg__intr_block_t__intr_count_t_cnt_5381f2ed_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup axi_dma_reg__intr_block_t__intr_count_t_cnt_5381f2ed_fld_cg with function sample(
    input bit [32-1:0] cnt
    );
        option.per_instance = 1;
        cnt_cp : coverpoint cnt;

    endgroup

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_B056182D COVERGROUPS -----------------------*/
    covergroup axi_dma_reg__intr_block_t__intr_count_t_cnt_b056182d_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup axi_dma_reg__intr_block_t__intr_count_t_cnt_b056182d_fld_cg with function sample(
    input bit [32-1:0] cnt
    );
        option.per_instance = 1;
        cnt_cp : coverpoint cnt;

    endgroup

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_91EBC86D COVERGROUPS -----------------------*/
    covergroup axi_dma_reg__intr_block_t__intr_count_t_cnt_91ebc86d_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup axi_dma_reg__intr_block_t__intr_count_t_cnt_91ebc86d_fld_cg with function sample(
    input bit [32-1:0] cnt
    );
        option.per_instance = 1;
        cnt_cp : coverpoint cnt;

    endgroup

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_61104C6C COVERGROUPS -----------------------*/
    covergroup axi_dma_reg__intr_block_t__intr_count_t_cnt_61104c6c_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup axi_dma_reg__intr_block_t__intr_count_t_cnt_61104c6c_fld_cg with function sample(
    input bit [32-1:0] cnt
    );
        option.per_instance = 1;
        cnt_cp : coverpoint cnt;

    endgroup

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_9B030582 COVERGROUPS -----------------------*/
    covergroup axi_dma_reg__intr_block_t__intr_count_t_cnt_9b030582_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup axi_dma_reg__intr_block_t__intr_count_t_cnt_9b030582_fld_cg with function sample(
    input bit [32-1:0] cnt
    );
        option.per_instance = 1;
        cnt_cp : coverpoint cnt;

    endgroup

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_3709CB5B COVERGROUPS -----------------------*/
    covergroup axi_dma_reg__intr_block_t__intr_count_t_cnt_3709cb5b_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup axi_dma_reg__intr_block_t__intr_count_t_cnt_3709cb5b_fld_cg with function sample(
    input bit [32-1:0] cnt
    );
        option.per_instance = 1;
        cnt_cp : coverpoint cnt;

    endgroup

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_E250B023 COVERGROUPS -----------------------*/
    covergroup axi_dma_reg__intr_block_t__intr_count_t_cnt_e250b023_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup axi_dma_reg__intr_block_t__intr_count_t_cnt_e250b023_fld_cg with function sample(
    input bit [32-1:0] cnt
    );
        option.per_instance = 1;
        cnt_cp : coverpoint cnt;

    endgroup

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_FED3AE2D COVERGROUPS -----------------------*/
    covergroup axi_dma_reg__intr_block_t__intr_count_t_cnt_fed3ae2d_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup axi_dma_reg__intr_block_t__intr_count_t_cnt_fed3ae2d_fld_cg with function sample(
    input bit [32-1:0] cnt
    );
        option.per_instance = 1;
        cnt_cp : coverpoint cnt;

    endgroup

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_08678F4E COVERGROUPS -----------------------*/
    covergroup axi_dma_reg__intr_block_t__intr_count_incr_t_pulse_08678f4e_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup axi_dma_reg__intr_block_t__intr_count_incr_t_pulse_08678f4e_fld_cg with function sample(
    input bit [1-1:0] pulse
    );
        option.per_instance = 1;
        pulse_cp : coverpoint pulse;

    endgroup

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_E1020031 COVERGROUPS -----------------------*/
    covergroup axi_dma_reg__intr_block_t__intr_count_incr_t_pulse_e1020031_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup axi_dma_reg__intr_block_t__intr_count_incr_t_pulse_e1020031_fld_cg with function sample(
    input bit [1-1:0] pulse
    );
        option.per_instance = 1;
        pulse_cp : coverpoint pulse;

    endgroup

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_CFE70385 COVERGROUPS -----------------------*/
    covergroup axi_dma_reg__intr_block_t__intr_count_incr_t_pulse_cfe70385_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup axi_dma_reg__intr_block_t__intr_count_incr_t_pulse_cfe70385_fld_cg with function sample(
    input bit [1-1:0] pulse
    );
        option.per_instance = 1;
        pulse_cp : coverpoint pulse;

    endgroup

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_9A8B3FA0 COVERGROUPS -----------------------*/
    covergroup axi_dma_reg__intr_block_t__intr_count_incr_t_pulse_9a8b3fa0_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup axi_dma_reg__intr_block_t__intr_count_incr_t_pulse_9a8b3fa0_fld_cg with function sample(
    input bit [1-1:0] pulse
    );
        option.per_instance = 1;
        pulse_cp : coverpoint pulse;

    endgroup

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_F530DCC5 COVERGROUPS -----------------------*/
    covergroup axi_dma_reg__intr_block_t__intr_count_incr_t_pulse_f530dcc5_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup axi_dma_reg__intr_block_t__intr_count_incr_t_pulse_f530dcc5_fld_cg with function sample(
    input bit [1-1:0] pulse
    );
        option.per_instance = 1;
        pulse_cp : coverpoint pulse;

    endgroup

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_60D6F4E7 COVERGROUPS -----------------------*/
    covergroup axi_dma_reg__intr_block_t__intr_count_incr_t_pulse_60d6f4e7_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup axi_dma_reg__intr_block_t__intr_count_incr_t_pulse_60d6f4e7_fld_cg with function sample(
    input bit [1-1:0] pulse
    );
        option.per_instance = 1;
        pulse_cp : coverpoint pulse;

    endgroup

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_6907AF43 COVERGROUPS -----------------------*/
    covergroup axi_dma_reg__intr_block_t__intr_count_incr_t_pulse_6907af43_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup axi_dma_reg__intr_block_t__intr_count_incr_t_pulse_6907af43_fld_cg with function sample(
    input bit [1-1:0] pulse
    );
        option.per_instance = 1;
        pulse_cp : coverpoint pulse;

    endgroup

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_F1BDDE05 COVERGROUPS -----------------------*/
    covergroup axi_dma_reg__intr_block_t__intr_count_incr_t_pulse_f1bdde05_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup axi_dma_reg__intr_block_t__intr_count_incr_t_pulse_f1bdde05_fld_cg with function sample(
    input bit [1-1:0] pulse
    );
        option.per_instance = 1;
        pulse_cp : coverpoint pulse;

    endgroup

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_236C6006 COVERGROUPS -----------------------*/
    covergroup axi_dma_reg__intr_block_t__intr_count_incr_t_pulse_236c6006_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup axi_dma_reg__intr_block_t__intr_count_incr_t_pulse_236c6006_fld_cg with function sample(
    input bit [1-1:0] pulse
    );
        option.per_instance = 1;
        pulse_cp : coverpoint pulse;

    endgroup

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_E5E89525 COVERGROUPS -----------------------*/
    covergroup axi_dma_reg__intr_block_t__intr_count_incr_t_pulse_e5e89525_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup axi_dma_reg__intr_block_t__intr_count_incr_t_pulse_e5e89525_fld_cg with function sample(
    input bit [1-1:0] pulse
    );
        option.per_instance = 1;
        pulse_cp : coverpoint pulse;

    endgroup

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_BFB3930B COVERGROUPS -----------------------*/
    covergroup axi_dma_reg__intr_block_t__intr_count_incr_t_pulse_bfb3930b_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup axi_dma_reg__intr_block_t__intr_count_incr_t_pulse_bfb3930b_fld_cg with function sample(
    input bit [1-1:0] pulse
    );
        option.per_instance = 1;
        pulse_cp : coverpoint pulse;

    endgroup

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_2AA328EA COVERGROUPS -----------------------*/
    covergroup axi_dma_reg__intr_block_t__intr_count_incr_t_pulse_2aa328ea_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup axi_dma_reg__intr_block_t__intr_count_incr_t_pulse_2aa328ea_fld_cg with function sample(
    input bit [1-1:0] pulse
    );
        option.per_instance = 1;
        pulse_cp : coverpoint pulse;

    endgroup

`endif