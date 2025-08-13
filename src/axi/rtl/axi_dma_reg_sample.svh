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

`ifndef AXI_DMA_REG_SAMPLE
    `define AXI_DMA_REG_SAMPLE
    
    /*----------------------- AXI_DMA_REG__ID SAMPLE FUNCTIONS -----------------------*/
    function void axi_dma_reg__id::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(id_bit_cg[bt]) this.id_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*id*/   );
        end
    endfunction

    function void axi_dma_reg__id::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(id_bit_cg[bt]) this.id_bit_cg[bt].sample(id.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( id.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- AXI_DMA_REG__CAP SAMPLE FUNCTIONS -----------------------*/
    function void axi_dma_reg__cap::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(fifo_max_depth_bit_cg[bt]) this.fifo_max_depth_bit_cg[bt].sample(data[0 + bt]);
            foreach(rsvd_bit_cg[bt]) this.rsvd_bit_cg[bt].sample(data[12 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[11:0]/*fifo_max_depth*/  ,  data[31:12]/*rsvd*/   );
        end
    endfunction

    function void axi_dma_reg__cap::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(fifo_max_depth_bit_cg[bt]) this.fifo_max_depth_bit_cg[bt].sample(fifo_max_depth.get_mirrored_value() >> bt);
            foreach(rsvd_bit_cg[bt]) this.rsvd_bit_cg[bt].sample(rsvd.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( fifo_max_depth.get_mirrored_value()  ,  rsvd.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- AXI_DMA_REG__CTRL SAMPLE FUNCTIONS -----------------------*/
    function void axi_dma_reg__ctrl::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(go_bit_cg[bt]) this.go_bit_cg[bt].sample(data[0 + bt]);
            foreach(flush_bit_cg[bt]) this.flush_bit_cg[bt].sample(data[1 + bt]);
            foreach(aes_mode_en_bit_cg[bt]) this.aes_mode_en_bit_cg[bt].sample(data[2 + bt]);
            foreach(aes_gcm_mode_bit_cg[bt]) this.aes_gcm_mode_bit_cg[bt].sample(data[3 + bt]);
            foreach(rsvd0_bit_cg[bt]) this.rsvd0_bit_cg[bt].sample(data[4 + bt]);
            foreach(rd_route_bit_cg[bt]) this.rd_route_bit_cg[bt].sample(data[16 + bt]);
            foreach(rsvd1_bit_cg[bt]) this.rsvd1_bit_cg[bt].sample(data[18 + bt]);
            foreach(rd_fixed_bit_cg[bt]) this.rd_fixed_bit_cg[bt].sample(data[20 + bt]);
            foreach(rsvd2_bit_cg[bt]) this.rsvd2_bit_cg[bt].sample(data[21 + bt]);
            foreach(wr_route_bit_cg[bt]) this.wr_route_bit_cg[bt].sample(data[24 + bt]);
            foreach(rsvd3_bit_cg[bt]) this.rsvd3_bit_cg[bt].sample(data[27 + bt]);
            foreach(wr_fixed_bit_cg[bt]) this.wr_fixed_bit_cg[bt].sample(data[28 + bt]);
            foreach(rsvd4_bit_cg[bt]) this.rsvd4_bit_cg[bt].sample(data[29 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*go*/  ,  data[1:1]/*flush*/  ,  data[2:2]/*aes_mode_en*/  ,  data[3:3]/*aes_gcm_mode*/  ,  data[15:4]/*rsvd0*/  ,  data[17:16]/*rd_route*/  ,  data[19:18]/*rsvd1*/  ,  data[20:20]/*rd_fixed*/  ,  data[23:21]/*rsvd2*/  ,  data[26:24]/*wr_route*/  ,  data[27:27]/*rsvd3*/  ,  data[28:28]/*wr_fixed*/  ,  data[31:29]/*rsvd4*/   );
        end
    endfunction

    function void axi_dma_reg__ctrl::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(go_bit_cg[bt]) this.go_bit_cg[bt].sample(go.get_mirrored_value() >> bt);
            foreach(flush_bit_cg[bt]) this.flush_bit_cg[bt].sample(flush.get_mirrored_value() >> bt);
            foreach(aes_mode_en_bit_cg[bt]) this.aes_mode_en_bit_cg[bt].sample(aes_mode_en.get_mirrored_value() >> bt);
            foreach(aes_gcm_mode_bit_cg[bt]) this.aes_gcm_mode_bit_cg[bt].sample(aes_gcm_mode.get_mirrored_value() >> bt);
            foreach(rsvd0_bit_cg[bt]) this.rsvd0_bit_cg[bt].sample(rsvd0.get_mirrored_value() >> bt);
            foreach(rd_route_bit_cg[bt]) this.rd_route_bit_cg[bt].sample(rd_route.get_mirrored_value() >> bt);
            foreach(rsvd1_bit_cg[bt]) this.rsvd1_bit_cg[bt].sample(rsvd1.get_mirrored_value() >> bt);
            foreach(rd_fixed_bit_cg[bt]) this.rd_fixed_bit_cg[bt].sample(rd_fixed.get_mirrored_value() >> bt);
            foreach(rsvd2_bit_cg[bt]) this.rsvd2_bit_cg[bt].sample(rsvd2.get_mirrored_value() >> bt);
            foreach(wr_route_bit_cg[bt]) this.wr_route_bit_cg[bt].sample(wr_route.get_mirrored_value() >> bt);
            foreach(rsvd3_bit_cg[bt]) this.rsvd3_bit_cg[bt].sample(rsvd3.get_mirrored_value() >> bt);
            foreach(wr_fixed_bit_cg[bt]) this.wr_fixed_bit_cg[bt].sample(wr_fixed.get_mirrored_value() >> bt);
            foreach(rsvd4_bit_cg[bt]) this.rsvd4_bit_cg[bt].sample(rsvd4.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( go.get_mirrored_value()  ,  flush.get_mirrored_value()  ,  aes_mode_en.get_mirrored_value()  ,  aes_gcm_mode.get_mirrored_value()  ,  rsvd0.get_mirrored_value()  ,  rd_route.get_mirrored_value()  ,  rsvd1.get_mirrored_value()  ,  rd_fixed.get_mirrored_value()  ,  rsvd2.get_mirrored_value()  ,  wr_route.get_mirrored_value()  ,  rsvd3.get_mirrored_value()  ,  wr_fixed.get_mirrored_value()  ,  rsvd4.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- AXI_DMA_REG__STATUS0 SAMPLE FUNCTIONS -----------------------*/
    function void axi_dma_reg__status0::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(busy_bit_cg[bt]) this.busy_bit_cg[bt].sample(data[0 + bt]);
            foreach(error_bit_cg[bt]) this.error_bit_cg[bt].sample(data[1 + bt]);
            foreach(rsvd0_bit_cg[bt]) this.rsvd0_bit_cg[bt].sample(data[2 + bt]);
            foreach(fifo_depth_bit_cg[bt]) this.fifo_depth_bit_cg[bt].sample(data[4 + bt]);
            foreach(axi_dma_fsm_ps_bit_cg[bt]) this.axi_dma_fsm_ps_bit_cg[bt].sample(data[16 + bt]);
            foreach(payload_available_bit_cg[bt]) this.payload_available_bit_cg[bt].sample(data[18 + bt]);
            foreach(image_activated_bit_cg[bt]) this.image_activated_bit_cg[bt].sample(data[19 + bt]);
            foreach(axi_dma_aes_fsm_ps_bit_cg[bt]) this.axi_dma_aes_fsm_ps_bit_cg[bt].sample(data[20 + bt]);
            foreach(rsvd1_bit_cg[bt]) this.rsvd1_bit_cg[bt].sample(data[24 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*busy*/  ,  data[1:1]/*error*/  ,  data[3:2]/*rsvd0*/  ,  data[15:4]/*fifo_depth*/  ,  data[17:16]/*axi_dma_fsm_ps*/  ,  data[18:18]/*payload_available*/  ,  data[19:19]/*image_activated*/  ,  data[23:20]/*axi_dma_aes_fsm_ps*/  ,  data[31:24]/*rsvd1*/   );
        end
    endfunction

    function void axi_dma_reg__status0::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(busy_bit_cg[bt]) this.busy_bit_cg[bt].sample(busy.get_mirrored_value() >> bt);
            foreach(error_bit_cg[bt]) this.error_bit_cg[bt].sample(error.get_mirrored_value() >> bt);
            foreach(rsvd0_bit_cg[bt]) this.rsvd0_bit_cg[bt].sample(rsvd0.get_mirrored_value() >> bt);
            foreach(fifo_depth_bit_cg[bt]) this.fifo_depth_bit_cg[bt].sample(fifo_depth.get_mirrored_value() >> bt);
            foreach(axi_dma_fsm_ps_bit_cg[bt]) this.axi_dma_fsm_ps_bit_cg[bt].sample(axi_dma_fsm_ps.get_mirrored_value() >> bt);
            foreach(payload_available_bit_cg[bt]) this.payload_available_bit_cg[bt].sample(payload_available.get_mirrored_value() >> bt);
            foreach(image_activated_bit_cg[bt]) this.image_activated_bit_cg[bt].sample(image_activated.get_mirrored_value() >> bt);
            foreach(axi_dma_aes_fsm_ps_bit_cg[bt]) this.axi_dma_aes_fsm_ps_bit_cg[bt].sample(axi_dma_aes_fsm_ps.get_mirrored_value() >> bt);
            foreach(rsvd1_bit_cg[bt]) this.rsvd1_bit_cg[bt].sample(rsvd1.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( busy.get_mirrored_value()  ,  error.get_mirrored_value()  ,  rsvd0.get_mirrored_value()  ,  fifo_depth.get_mirrored_value()  ,  axi_dma_fsm_ps.get_mirrored_value()  ,  payload_available.get_mirrored_value()  ,  image_activated.get_mirrored_value()  ,  axi_dma_aes_fsm_ps.get_mirrored_value()  ,  rsvd1.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- AXI_DMA_REG__STATUS1 SAMPLE FUNCTIONS -----------------------*/
    function void axi_dma_reg__status1::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(bytes_remaining_bit_cg[bt]) this.bytes_remaining_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*bytes_remaining*/   );
        end
    endfunction

    function void axi_dma_reg__status1::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(bytes_remaining_bit_cg[bt]) this.bytes_remaining_bit_cg[bt].sample(bytes_remaining.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( bytes_remaining.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- AXI_DMA_REG__SRC_ADDR_L SAMPLE FUNCTIONS -----------------------*/
    function void axi_dma_reg__src_addr_l::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(addr_l_bit_cg[bt]) this.addr_l_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*addr_l*/   );
        end
    endfunction

    function void axi_dma_reg__src_addr_l::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(addr_l_bit_cg[bt]) this.addr_l_bit_cg[bt].sample(addr_l.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( addr_l.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- AXI_DMA_REG__SRC_ADDR_H SAMPLE FUNCTIONS -----------------------*/
    function void axi_dma_reg__src_addr_h::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(addr_h_bit_cg[bt]) this.addr_h_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*addr_h*/   );
        end
    endfunction

    function void axi_dma_reg__src_addr_h::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(addr_h_bit_cg[bt]) this.addr_h_bit_cg[bt].sample(addr_h.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( addr_h.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- AXI_DMA_REG__DST_ADDR_L SAMPLE FUNCTIONS -----------------------*/
    function void axi_dma_reg__dst_addr_l::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(addr_l_bit_cg[bt]) this.addr_l_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*addr_l*/   );
        end
    endfunction

    function void axi_dma_reg__dst_addr_l::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(addr_l_bit_cg[bt]) this.addr_l_bit_cg[bt].sample(addr_l.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( addr_l.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- AXI_DMA_REG__DST_ADDR_H SAMPLE FUNCTIONS -----------------------*/
    function void axi_dma_reg__dst_addr_h::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(addr_h_bit_cg[bt]) this.addr_h_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*addr_h*/   );
        end
    endfunction

    function void axi_dma_reg__dst_addr_h::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(addr_h_bit_cg[bt]) this.addr_h_bit_cg[bt].sample(addr_h.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( addr_h.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- AXI_DMA_REG__BYTE_COUNT SAMPLE FUNCTIONS -----------------------*/
    function void axi_dma_reg__byte_count::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(count_bit_cg[bt]) this.count_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*count*/   );
        end
    endfunction

    function void axi_dma_reg__byte_count::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(count_bit_cg[bt]) this.count_bit_cg[bt].sample(count.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( count.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- AXI_DMA_REG__BLOCK_SIZE SAMPLE FUNCTIONS -----------------------*/
    function void axi_dma_reg__block_size::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(size_bit_cg[bt]) this.size_bit_cg[bt].sample(data[0 + bt]);
            foreach(rsvd_bit_cg[bt]) this.rsvd_bit_cg[bt].sample(data[12 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[11:0]/*size*/  ,  data[31:12]/*rsvd*/   );
        end
    endfunction

    function void axi_dma_reg__block_size::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(size_bit_cg[bt]) this.size_bit_cg[bt].sample(size.get_mirrored_value() >> bt);
            foreach(rsvd_bit_cg[bt]) this.rsvd_bit_cg[bt].sample(rsvd.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( size.get_mirrored_value()  ,  rsvd.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- AXI_DMA_REG__WRITE_DATA SAMPLE FUNCTIONS -----------------------*/
    function void axi_dma_reg__write_data::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(wdata_bit_cg[bt]) this.wdata_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*wdata*/   );
        end
    endfunction

    function void axi_dma_reg__write_data::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(wdata_bit_cg[bt]) this.wdata_bit_cg[bt].sample(wdata.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( wdata.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- AXI_DMA_REG__READ_DATA SAMPLE FUNCTIONS -----------------------*/
    function void axi_dma_reg__read_data::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(rdata_bit_cg[bt]) this.rdata_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*rdata*/   );
        end
    endfunction

    function void axi_dma_reg__read_data::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(rdata_bit_cg[bt]) this.rdata_bit_cg[bt].sample(rdata.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( rdata.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__GLOBAL_INTR_EN_T SAMPLE FUNCTIONS -----------------------*/
    function void axi_dma_reg__intr_block_t__global_intr_en_t::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(error_en_bit_cg[bt]) this.error_en_bit_cg[bt].sample(data[0 + bt]);
            foreach(notif_en_bit_cg[bt]) this.notif_en_bit_cg[bt].sample(data[1 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*error_en*/  ,  data[1:1]/*notif_en*/   );
        end
    endfunction

    function void axi_dma_reg__intr_block_t__global_intr_en_t::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(error_en_bit_cg[bt]) this.error_en_bit_cg[bt].sample(error_en.get_mirrored_value() >> bt);
            foreach(notif_en_bit_cg[bt]) this.notif_en_bit_cg[bt].sample(notif_en.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( error_en.get_mirrored_value()  ,  notif_en.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__ERROR_INTR_EN_T SAMPLE FUNCTIONS -----------------------*/
    function void axi_dma_reg__intr_block_t__error_intr_en_t::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(error_cmd_dec_en_bit_cg[bt]) this.error_cmd_dec_en_bit_cg[bt].sample(data[0 + bt]);
            foreach(error_axi_rd_en_bit_cg[bt]) this.error_axi_rd_en_bit_cg[bt].sample(data[1 + bt]);
            foreach(error_axi_wr_en_bit_cg[bt]) this.error_axi_wr_en_bit_cg[bt].sample(data[2 + bt]);
            foreach(error_mbox_lock_en_bit_cg[bt]) this.error_mbox_lock_en_bit_cg[bt].sample(data[3 + bt]);
            foreach(error_sha_lock_en_bit_cg[bt]) this.error_sha_lock_en_bit_cg[bt].sample(data[4 + bt]);
            foreach(error_fifo_oflow_en_bit_cg[bt]) this.error_fifo_oflow_en_bit_cg[bt].sample(data[5 + bt]);
            foreach(error_fifo_uflow_en_bit_cg[bt]) this.error_fifo_uflow_en_bit_cg[bt].sample(data[6 + bt]);
            foreach(error_aes_cif_en_bit_cg[bt]) this.error_aes_cif_en_bit_cg[bt].sample(data[7 + bt]);
            foreach(error_kv_rd_en_bit_cg[bt]) this.error_kv_rd_en_bit_cg[bt].sample(data[8 + bt]);
            foreach(error_kv_rd_large_en_bit_cg[bt]) this.error_kv_rd_large_en_bit_cg[bt].sample(data[9 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*error_cmd_dec_en*/  ,  data[1:1]/*error_axi_rd_en*/  ,  data[2:2]/*error_axi_wr_en*/  ,  data[3:3]/*error_mbox_lock_en*/  ,  data[4:4]/*error_sha_lock_en*/  ,  data[5:5]/*error_fifo_oflow_en*/  ,  data[6:6]/*error_fifo_uflow_en*/  ,  data[7:7]/*error_aes_cif_en*/  ,  data[8:8]/*error_kv_rd_en*/  ,  data[9:9]/*error_kv_rd_large_en*/   );
        end
    endfunction

    function void axi_dma_reg__intr_block_t__error_intr_en_t::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(error_cmd_dec_en_bit_cg[bt]) this.error_cmd_dec_en_bit_cg[bt].sample(error_cmd_dec_en.get_mirrored_value() >> bt);
            foreach(error_axi_rd_en_bit_cg[bt]) this.error_axi_rd_en_bit_cg[bt].sample(error_axi_rd_en.get_mirrored_value() >> bt);
            foreach(error_axi_wr_en_bit_cg[bt]) this.error_axi_wr_en_bit_cg[bt].sample(error_axi_wr_en.get_mirrored_value() >> bt);
            foreach(error_mbox_lock_en_bit_cg[bt]) this.error_mbox_lock_en_bit_cg[bt].sample(error_mbox_lock_en.get_mirrored_value() >> bt);
            foreach(error_sha_lock_en_bit_cg[bt]) this.error_sha_lock_en_bit_cg[bt].sample(error_sha_lock_en.get_mirrored_value() >> bt);
            foreach(error_fifo_oflow_en_bit_cg[bt]) this.error_fifo_oflow_en_bit_cg[bt].sample(error_fifo_oflow_en.get_mirrored_value() >> bt);
            foreach(error_fifo_uflow_en_bit_cg[bt]) this.error_fifo_uflow_en_bit_cg[bt].sample(error_fifo_uflow_en.get_mirrored_value() >> bt);
            foreach(error_aes_cif_en_bit_cg[bt]) this.error_aes_cif_en_bit_cg[bt].sample(error_aes_cif_en.get_mirrored_value() >> bt);
            foreach(error_kv_rd_en_bit_cg[bt]) this.error_kv_rd_en_bit_cg[bt].sample(error_kv_rd_en.get_mirrored_value() >> bt);
            foreach(error_kv_rd_large_en_bit_cg[bt]) this.error_kv_rd_large_en_bit_cg[bt].sample(error_kv_rd_large_en.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( error_cmd_dec_en.get_mirrored_value()  ,  error_axi_rd_en.get_mirrored_value()  ,  error_axi_wr_en.get_mirrored_value()  ,  error_mbox_lock_en.get_mirrored_value()  ,  error_sha_lock_en.get_mirrored_value()  ,  error_fifo_oflow_en.get_mirrored_value()  ,  error_fifo_uflow_en.get_mirrored_value()  ,  error_aes_cif_en.get_mirrored_value()  ,  error_kv_rd_en.get_mirrored_value()  ,  error_kv_rd_large_en.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__NOTIF_INTR_EN_T SAMPLE FUNCTIONS -----------------------*/
    function void axi_dma_reg__intr_block_t__notif_intr_en_t::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(notif_txn_done_en_bit_cg[bt]) this.notif_txn_done_en_bit_cg[bt].sample(data[0 + bt]);
            foreach(notif_fifo_empty_en_bit_cg[bt]) this.notif_fifo_empty_en_bit_cg[bt].sample(data[1 + bt]);
            foreach(notif_fifo_not_empty_en_bit_cg[bt]) this.notif_fifo_not_empty_en_bit_cg[bt].sample(data[2 + bt]);
            foreach(notif_fifo_full_en_bit_cg[bt]) this.notif_fifo_full_en_bit_cg[bt].sample(data[3 + bt]);
            foreach(notif_fifo_not_full_en_bit_cg[bt]) this.notif_fifo_not_full_en_bit_cg[bt].sample(data[4 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*notif_txn_done_en*/  ,  data[1:1]/*notif_fifo_empty_en*/  ,  data[2:2]/*notif_fifo_not_empty_en*/  ,  data[3:3]/*notif_fifo_full_en*/  ,  data[4:4]/*notif_fifo_not_full_en*/   );
        end
    endfunction

    function void axi_dma_reg__intr_block_t__notif_intr_en_t::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(notif_txn_done_en_bit_cg[bt]) this.notif_txn_done_en_bit_cg[bt].sample(notif_txn_done_en.get_mirrored_value() >> bt);
            foreach(notif_fifo_empty_en_bit_cg[bt]) this.notif_fifo_empty_en_bit_cg[bt].sample(notif_fifo_empty_en.get_mirrored_value() >> bt);
            foreach(notif_fifo_not_empty_en_bit_cg[bt]) this.notif_fifo_not_empty_en_bit_cg[bt].sample(notif_fifo_not_empty_en.get_mirrored_value() >> bt);
            foreach(notif_fifo_full_en_bit_cg[bt]) this.notif_fifo_full_en_bit_cg[bt].sample(notif_fifo_full_en.get_mirrored_value() >> bt);
            foreach(notif_fifo_not_full_en_bit_cg[bt]) this.notif_fifo_not_full_en_bit_cg[bt].sample(notif_fifo_not_full_en.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( notif_txn_done_en.get_mirrored_value()  ,  notif_fifo_empty_en.get_mirrored_value()  ,  notif_fifo_not_empty_en.get_mirrored_value()  ,  notif_fifo_full_en.get_mirrored_value()  ,  notif_fifo_not_full_en.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__GLOBAL_INTR_T_AGG_STS_DD3DCF0A SAMPLE FUNCTIONS -----------------------*/
    function void axi_dma_reg__intr_block_t__global_intr_t_agg_sts_dd3dcf0a::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(agg_sts_bit_cg[bt]) this.agg_sts_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*agg_sts*/   );
        end
    endfunction

    function void axi_dma_reg__intr_block_t__global_intr_t_agg_sts_dd3dcf0a::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(agg_sts_bit_cg[bt]) this.agg_sts_bit_cg[bt].sample(agg_sts.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( agg_sts.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__GLOBAL_INTR_T_AGG_STS_E6399B4A SAMPLE FUNCTIONS -----------------------*/
    function void axi_dma_reg__intr_block_t__global_intr_t_agg_sts_e6399b4a::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(agg_sts_bit_cg[bt]) this.agg_sts_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*agg_sts*/   );
        end
    endfunction

    function void axi_dma_reg__intr_block_t__global_intr_t_agg_sts_e6399b4a::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(agg_sts_bit_cg[bt]) this.agg_sts_bit_cg[bt].sample(agg_sts.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( agg_sts.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__ERROR_INTR_T_ERROR_AES_CIF_STS_63385A16_ERROR_AXI_RD_STS_927E49CD_ERROR_AXI_WR_STS_F84E5C07_ERROR_CMD_DEC_STS_46039D92_ERROR_FIFO_OFLOW_STS_71B29A77_ERROR_FIFO_UFLOW_STS_119D122A_ERROR_KV_RD_LARGE_STS_AA293A66_ERROR_KV_RD_STS_DF1AD5DD_ERROR_MBOX_LOCK_STS_9E18C395_ERROR_SHA_LOCK_STS_4C7993A0 SAMPLE FUNCTIONS -----------------------*/
    function void axi_dma_reg__intr_block_t__error_intr_t_error_aes_cif_sts_63385a16_error_axi_rd_sts_927e49cd_error_axi_wr_sts_f84e5c07_error_cmd_dec_sts_46039d92_error_fifo_oflow_sts_71b29a77_error_fifo_uflow_sts_119d122a_error_kv_rd_large_sts_aa293a66_error_kv_rd_sts_df1ad5dd_error_mbox_lock_sts_9e18c395_error_sha_lock_sts_4c7993a0::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(error_cmd_dec_sts_bit_cg[bt]) this.error_cmd_dec_sts_bit_cg[bt].sample(data[0 + bt]);
            foreach(error_axi_rd_sts_bit_cg[bt]) this.error_axi_rd_sts_bit_cg[bt].sample(data[1 + bt]);
            foreach(error_axi_wr_sts_bit_cg[bt]) this.error_axi_wr_sts_bit_cg[bt].sample(data[2 + bt]);
            foreach(error_mbox_lock_sts_bit_cg[bt]) this.error_mbox_lock_sts_bit_cg[bt].sample(data[3 + bt]);
            foreach(error_sha_lock_sts_bit_cg[bt]) this.error_sha_lock_sts_bit_cg[bt].sample(data[4 + bt]);
            foreach(error_fifo_oflow_sts_bit_cg[bt]) this.error_fifo_oflow_sts_bit_cg[bt].sample(data[5 + bt]);
            foreach(error_fifo_uflow_sts_bit_cg[bt]) this.error_fifo_uflow_sts_bit_cg[bt].sample(data[6 + bt]);
            foreach(error_aes_cif_sts_bit_cg[bt]) this.error_aes_cif_sts_bit_cg[bt].sample(data[7 + bt]);
            foreach(error_kv_rd_sts_bit_cg[bt]) this.error_kv_rd_sts_bit_cg[bt].sample(data[8 + bt]);
            foreach(error_kv_rd_large_sts_bit_cg[bt]) this.error_kv_rd_large_sts_bit_cg[bt].sample(data[9 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*error_cmd_dec_sts*/  ,  data[1:1]/*error_axi_rd_sts*/  ,  data[2:2]/*error_axi_wr_sts*/  ,  data[3:3]/*error_mbox_lock_sts*/  ,  data[4:4]/*error_sha_lock_sts*/  ,  data[5:5]/*error_fifo_oflow_sts*/  ,  data[6:6]/*error_fifo_uflow_sts*/  ,  data[7:7]/*error_aes_cif_sts*/  ,  data[8:8]/*error_kv_rd_sts*/  ,  data[9:9]/*error_kv_rd_large_sts*/   );
        end
    endfunction

    function void axi_dma_reg__intr_block_t__error_intr_t_error_aes_cif_sts_63385a16_error_axi_rd_sts_927e49cd_error_axi_wr_sts_f84e5c07_error_cmd_dec_sts_46039d92_error_fifo_oflow_sts_71b29a77_error_fifo_uflow_sts_119d122a_error_kv_rd_large_sts_aa293a66_error_kv_rd_sts_df1ad5dd_error_mbox_lock_sts_9e18c395_error_sha_lock_sts_4c7993a0::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(error_cmd_dec_sts_bit_cg[bt]) this.error_cmd_dec_sts_bit_cg[bt].sample(error_cmd_dec_sts.get_mirrored_value() >> bt);
            foreach(error_axi_rd_sts_bit_cg[bt]) this.error_axi_rd_sts_bit_cg[bt].sample(error_axi_rd_sts.get_mirrored_value() >> bt);
            foreach(error_axi_wr_sts_bit_cg[bt]) this.error_axi_wr_sts_bit_cg[bt].sample(error_axi_wr_sts.get_mirrored_value() >> bt);
            foreach(error_mbox_lock_sts_bit_cg[bt]) this.error_mbox_lock_sts_bit_cg[bt].sample(error_mbox_lock_sts.get_mirrored_value() >> bt);
            foreach(error_sha_lock_sts_bit_cg[bt]) this.error_sha_lock_sts_bit_cg[bt].sample(error_sha_lock_sts.get_mirrored_value() >> bt);
            foreach(error_fifo_oflow_sts_bit_cg[bt]) this.error_fifo_oflow_sts_bit_cg[bt].sample(error_fifo_oflow_sts.get_mirrored_value() >> bt);
            foreach(error_fifo_uflow_sts_bit_cg[bt]) this.error_fifo_uflow_sts_bit_cg[bt].sample(error_fifo_uflow_sts.get_mirrored_value() >> bt);
            foreach(error_aes_cif_sts_bit_cg[bt]) this.error_aes_cif_sts_bit_cg[bt].sample(error_aes_cif_sts.get_mirrored_value() >> bt);
            foreach(error_kv_rd_sts_bit_cg[bt]) this.error_kv_rd_sts_bit_cg[bt].sample(error_kv_rd_sts.get_mirrored_value() >> bt);
            foreach(error_kv_rd_large_sts_bit_cg[bt]) this.error_kv_rd_large_sts_bit_cg[bt].sample(error_kv_rd_large_sts.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( error_cmd_dec_sts.get_mirrored_value()  ,  error_axi_rd_sts.get_mirrored_value()  ,  error_axi_wr_sts.get_mirrored_value()  ,  error_mbox_lock_sts.get_mirrored_value()  ,  error_sha_lock_sts.get_mirrored_value()  ,  error_fifo_oflow_sts.get_mirrored_value()  ,  error_fifo_uflow_sts.get_mirrored_value()  ,  error_aes_cif_sts.get_mirrored_value()  ,  error_kv_rd_sts.get_mirrored_value()  ,  error_kv_rd_large_sts.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__NOTIF_INTR_T_NOTIF_FIFO_EMPTY_STS_D87D1786_NOTIF_FIFO_FULL_STS_64C66862_NOTIF_FIFO_NOT_EMPTY_STS_1A0E2460_NOTIF_FIFO_NOT_FULL_STS_0266FE07_NOTIF_TXN_DONE_STS_0EE2F120 SAMPLE FUNCTIONS -----------------------*/
    function void axi_dma_reg__intr_block_t__notif_intr_t_notif_fifo_empty_sts_d87d1786_notif_fifo_full_sts_64c66862_notif_fifo_not_empty_sts_1a0e2460_notif_fifo_not_full_sts_0266fe07_notif_txn_done_sts_0ee2f120::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(notif_txn_done_sts_bit_cg[bt]) this.notif_txn_done_sts_bit_cg[bt].sample(data[0 + bt]);
            foreach(notif_fifo_empty_sts_bit_cg[bt]) this.notif_fifo_empty_sts_bit_cg[bt].sample(data[1 + bt]);
            foreach(notif_fifo_not_empty_sts_bit_cg[bt]) this.notif_fifo_not_empty_sts_bit_cg[bt].sample(data[2 + bt]);
            foreach(notif_fifo_full_sts_bit_cg[bt]) this.notif_fifo_full_sts_bit_cg[bt].sample(data[3 + bt]);
            foreach(notif_fifo_not_full_sts_bit_cg[bt]) this.notif_fifo_not_full_sts_bit_cg[bt].sample(data[4 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*notif_txn_done_sts*/  ,  data[1:1]/*notif_fifo_empty_sts*/  ,  data[2:2]/*notif_fifo_not_empty_sts*/  ,  data[3:3]/*notif_fifo_full_sts*/  ,  data[4:4]/*notif_fifo_not_full_sts*/   );
        end
    endfunction

    function void axi_dma_reg__intr_block_t__notif_intr_t_notif_fifo_empty_sts_d87d1786_notif_fifo_full_sts_64c66862_notif_fifo_not_empty_sts_1a0e2460_notif_fifo_not_full_sts_0266fe07_notif_txn_done_sts_0ee2f120::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(notif_txn_done_sts_bit_cg[bt]) this.notif_txn_done_sts_bit_cg[bt].sample(notif_txn_done_sts.get_mirrored_value() >> bt);
            foreach(notif_fifo_empty_sts_bit_cg[bt]) this.notif_fifo_empty_sts_bit_cg[bt].sample(notif_fifo_empty_sts.get_mirrored_value() >> bt);
            foreach(notif_fifo_not_empty_sts_bit_cg[bt]) this.notif_fifo_not_empty_sts_bit_cg[bt].sample(notif_fifo_not_empty_sts.get_mirrored_value() >> bt);
            foreach(notif_fifo_full_sts_bit_cg[bt]) this.notif_fifo_full_sts_bit_cg[bt].sample(notif_fifo_full_sts.get_mirrored_value() >> bt);
            foreach(notif_fifo_not_full_sts_bit_cg[bt]) this.notif_fifo_not_full_sts_bit_cg[bt].sample(notif_fifo_not_full_sts.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( notif_txn_done_sts.get_mirrored_value()  ,  notif_fifo_empty_sts.get_mirrored_value()  ,  notif_fifo_not_empty_sts.get_mirrored_value()  ,  notif_fifo_full_sts.get_mirrored_value()  ,  notif_fifo_not_full_sts.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__ERROR_INTR_TRIG_T SAMPLE FUNCTIONS -----------------------*/
    function void axi_dma_reg__intr_block_t__error_intr_trig_t::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(error_cmd_dec_trig_bit_cg[bt]) this.error_cmd_dec_trig_bit_cg[bt].sample(data[0 + bt]);
            foreach(error_axi_rd_trig_bit_cg[bt]) this.error_axi_rd_trig_bit_cg[bt].sample(data[1 + bt]);
            foreach(error_axi_wr_trig_bit_cg[bt]) this.error_axi_wr_trig_bit_cg[bt].sample(data[2 + bt]);
            foreach(error_mbox_lock_trig_bit_cg[bt]) this.error_mbox_lock_trig_bit_cg[bt].sample(data[3 + bt]);
            foreach(error_sha_lock_trig_bit_cg[bt]) this.error_sha_lock_trig_bit_cg[bt].sample(data[4 + bt]);
            foreach(error_fifo_oflow_trig_bit_cg[bt]) this.error_fifo_oflow_trig_bit_cg[bt].sample(data[5 + bt]);
            foreach(error_fifo_uflow_trig_bit_cg[bt]) this.error_fifo_uflow_trig_bit_cg[bt].sample(data[6 + bt]);
            foreach(error_aes_cif_trig_bit_cg[bt]) this.error_aes_cif_trig_bit_cg[bt].sample(data[7 + bt]);
            foreach(error_kv_rd_trig_bit_cg[bt]) this.error_kv_rd_trig_bit_cg[bt].sample(data[8 + bt]);
            foreach(error_kv_rd_large_trig_bit_cg[bt]) this.error_kv_rd_large_trig_bit_cg[bt].sample(data[9 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*error_cmd_dec_trig*/  ,  data[1:1]/*error_axi_rd_trig*/  ,  data[2:2]/*error_axi_wr_trig*/  ,  data[3:3]/*error_mbox_lock_trig*/  ,  data[4:4]/*error_sha_lock_trig*/  ,  data[5:5]/*error_fifo_oflow_trig*/  ,  data[6:6]/*error_fifo_uflow_trig*/  ,  data[7:7]/*error_aes_cif_trig*/  ,  data[8:8]/*error_kv_rd_trig*/  ,  data[9:9]/*error_kv_rd_large_trig*/   );
        end
    endfunction

    function void axi_dma_reg__intr_block_t__error_intr_trig_t::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(error_cmd_dec_trig_bit_cg[bt]) this.error_cmd_dec_trig_bit_cg[bt].sample(error_cmd_dec_trig.get_mirrored_value() >> bt);
            foreach(error_axi_rd_trig_bit_cg[bt]) this.error_axi_rd_trig_bit_cg[bt].sample(error_axi_rd_trig.get_mirrored_value() >> bt);
            foreach(error_axi_wr_trig_bit_cg[bt]) this.error_axi_wr_trig_bit_cg[bt].sample(error_axi_wr_trig.get_mirrored_value() >> bt);
            foreach(error_mbox_lock_trig_bit_cg[bt]) this.error_mbox_lock_trig_bit_cg[bt].sample(error_mbox_lock_trig.get_mirrored_value() >> bt);
            foreach(error_sha_lock_trig_bit_cg[bt]) this.error_sha_lock_trig_bit_cg[bt].sample(error_sha_lock_trig.get_mirrored_value() >> bt);
            foreach(error_fifo_oflow_trig_bit_cg[bt]) this.error_fifo_oflow_trig_bit_cg[bt].sample(error_fifo_oflow_trig.get_mirrored_value() >> bt);
            foreach(error_fifo_uflow_trig_bit_cg[bt]) this.error_fifo_uflow_trig_bit_cg[bt].sample(error_fifo_uflow_trig.get_mirrored_value() >> bt);
            foreach(error_aes_cif_trig_bit_cg[bt]) this.error_aes_cif_trig_bit_cg[bt].sample(error_aes_cif_trig.get_mirrored_value() >> bt);
            foreach(error_kv_rd_trig_bit_cg[bt]) this.error_kv_rd_trig_bit_cg[bt].sample(error_kv_rd_trig.get_mirrored_value() >> bt);
            foreach(error_kv_rd_large_trig_bit_cg[bt]) this.error_kv_rd_large_trig_bit_cg[bt].sample(error_kv_rd_large_trig.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( error_cmd_dec_trig.get_mirrored_value()  ,  error_axi_rd_trig.get_mirrored_value()  ,  error_axi_wr_trig.get_mirrored_value()  ,  error_mbox_lock_trig.get_mirrored_value()  ,  error_sha_lock_trig.get_mirrored_value()  ,  error_fifo_oflow_trig.get_mirrored_value()  ,  error_fifo_uflow_trig.get_mirrored_value()  ,  error_aes_cif_trig.get_mirrored_value()  ,  error_kv_rd_trig.get_mirrored_value()  ,  error_kv_rd_large_trig.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__NOTIF_INTR_TRIG_T SAMPLE FUNCTIONS -----------------------*/
    function void axi_dma_reg__intr_block_t__notif_intr_trig_t::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(notif_txn_done_trig_bit_cg[bt]) this.notif_txn_done_trig_bit_cg[bt].sample(data[0 + bt]);
            foreach(notif_fifo_empty_trig_bit_cg[bt]) this.notif_fifo_empty_trig_bit_cg[bt].sample(data[1 + bt]);
            foreach(notif_fifo_not_empty_trig_bit_cg[bt]) this.notif_fifo_not_empty_trig_bit_cg[bt].sample(data[2 + bt]);
            foreach(notif_fifo_full_trig_bit_cg[bt]) this.notif_fifo_full_trig_bit_cg[bt].sample(data[3 + bt]);
            foreach(notif_fifo_not_full_trig_bit_cg[bt]) this.notif_fifo_not_full_trig_bit_cg[bt].sample(data[4 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*notif_txn_done_trig*/  ,  data[1:1]/*notif_fifo_empty_trig*/  ,  data[2:2]/*notif_fifo_not_empty_trig*/  ,  data[3:3]/*notif_fifo_full_trig*/  ,  data[4:4]/*notif_fifo_not_full_trig*/   );
        end
    endfunction

    function void axi_dma_reg__intr_block_t__notif_intr_trig_t::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(notif_txn_done_trig_bit_cg[bt]) this.notif_txn_done_trig_bit_cg[bt].sample(notif_txn_done_trig.get_mirrored_value() >> bt);
            foreach(notif_fifo_empty_trig_bit_cg[bt]) this.notif_fifo_empty_trig_bit_cg[bt].sample(notif_fifo_empty_trig.get_mirrored_value() >> bt);
            foreach(notif_fifo_not_empty_trig_bit_cg[bt]) this.notif_fifo_not_empty_trig_bit_cg[bt].sample(notif_fifo_not_empty_trig.get_mirrored_value() >> bt);
            foreach(notif_fifo_full_trig_bit_cg[bt]) this.notif_fifo_full_trig_bit_cg[bt].sample(notif_fifo_full_trig.get_mirrored_value() >> bt);
            foreach(notif_fifo_not_full_trig_bit_cg[bt]) this.notif_fifo_not_full_trig_bit_cg[bt].sample(notif_fifo_not_full_trig.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( notif_txn_done_trig.get_mirrored_value()  ,  notif_fifo_empty_trig.get_mirrored_value()  ,  notif_fifo_not_empty_trig.get_mirrored_value()  ,  notif_fifo_full_trig.get_mirrored_value()  ,  notif_fifo_not_full_trig.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_FC5260B0 SAMPLE FUNCTIONS -----------------------*/
    function void axi_dma_reg__intr_block_t__intr_count_t_cnt_fc5260b0::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*cnt*/   );
        end
    endfunction

    function void axi_dma_reg__intr_block_t__intr_count_t_cnt_fc5260b0::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(cnt.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( cnt.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_F6D7DE6B SAMPLE FUNCTIONS -----------------------*/
    function void axi_dma_reg__intr_block_t__intr_count_t_cnt_f6d7de6b::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*cnt*/   );
        end
    endfunction

    function void axi_dma_reg__intr_block_t__intr_count_t_cnt_f6d7de6b::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(cnt.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( cnt.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_ABA31562 SAMPLE FUNCTIONS -----------------------*/
    function void axi_dma_reg__intr_block_t__intr_count_t_cnt_aba31562::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*cnt*/   );
        end
    endfunction

    function void axi_dma_reg__intr_block_t__intr_count_t_cnt_aba31562::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(cnt.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( cnt.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_F73463F1 SAMPLE FUNCTIONS -----------------------*/
    function void axi_dma_reg__intr_block_t__intr_count_t_cnt_f73463f1::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*cnt*/   );
        end
    endfunction

    function void axi_dma_reg__intr_block_t__intr_count_t_cnt_f73463f1::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(cnt.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( cnt.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_5381F2ED SAMPLE FUNCTIONS -----------------------*/
    function void axi_dma_reg__intr_block_t__intr_count_t_cnt_5381f2ed::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*cnt*/   );
        end
    endfunction

    function void axi_dma_reg__intr_block_t__intr_count_t_cnt_5381f2ed::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(cnt.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( cnt.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_B056182D SAMPLE FUNCTIONS -----------------------*/
    function void axi_dma_reg__intr_block_t__intr_count_t_cnt_b056182d::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*cnt*/   );
        end
    endfunction

    function void axi_dma_reg__intr_block_t__intr_count_t_cnt_b056182d::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(cnt.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( cnt.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_91EBC86D SAMPLE FUNCTIONS -----------------------*/
    function void axi_dma_reg__intr_block_t__intr_count_t_cnt_91ebc86d::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*cnt*/   );
        end
    endfunction

    function void axi_dma_reg__intr_block_t__intr_count_t_cnt_91ebc86d::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(cnt.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( cnt.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_30AF74C6 SAMPLE FUNCTIONS -----------------------*/
    function void axi_dma_reg__intr_block_t__intr_count_t_cnt_30af74c6::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*cnt*/   );
        end
    endfunction

    function void axi_dma_reg__intr_block_t__intr_count_t_cnt_30af74c6::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(cnt.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( cnt.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_57BF69A0 SAMPLE FUNCTIONS -----------------------*/
    function void axi_dma_reg__intr_block_t__intr_count_t_cnt_57bf69a0::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*cnt*/   );
        end
    endfunction

    function void axi_dma_reg__intr_block_t__intr_count_t_cnt_57bf69a0::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(cnt.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( cnt.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_8FBC7B72 SAMPLE FUNCTIONS -----------------------*/
    function void axi_dma_reg__intr_block_t__intr_count_t_cnt_8fbc7b72::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*cnt*/   );
        end
    endfunction

    function void axi_dma_reg__intr_block_t__intr_count_t_cnt_8fbc7b72::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(cnt.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( cnt.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_61104C6C SAMPLE FUNCTIONS -----------------------*/
    function void axi_dma_reg__intr_block_t__intr_count_t_cnt_61104c6c::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*cnt*/   );
        end
    endfunction

    function void axi_dma_reg__intr_block_t__intr_count_t_cnt_61104c6c::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(cnt.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( cnt.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_9B030582 SAMPLE FUNCTIONS -----------------------*/
    function void axi_dma_reg__intr_block_t__intr_count_t_cnt_9b030582::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*cnt*/   );
        end
    endfunction

    function void axi_dma_reg__intr_block_t__intr_count_t_cnt_9b030582::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(cnt.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( cnt.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_3709CB5B SAMPLE FUNCTIONS -----------------------*/
    function void axi_dma_reg__intr_block_t__intr_count_t_cnt_3709cb5b::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*cnt*/   );
        end
    endfunction

    function void axi_dma_reg__intr_block_t__intr_count_t_cnt_3709cb5b::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(cnt.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( cnt.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_E250B023 SAMPLE FUNCTIONS -----------------------*/
    function void axi_dma_reg__intr_block_t__intr_count_t_cnt_e250b023::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*cnt*/   );
        end
    endfunction

    function void axi_dma_reg__intr_block_t__intr_count_t_cnt_e250b023::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(cnt.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( cnt.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_FED3AE2D SAMPLE FUNCTIONS -----------------------*/
    function void axi_dma_reg__intr_block_t__intr_count_t_cnt_fed3ae2d::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*cnt*/   );
        end
    endfunction

    function void axi_dma_reg__intr_block_t__intr_count_t_cnt_fed3ae2d::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(cnt.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( cnt.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_08678F4E SAMPLE FUNCTIONS -----------------------*/
    function void axi_dma_reg__intr_block_t__intr_count_incr_t_pulse_08678f4e::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*pulse*/   );
        end
    endfunction

    function void axi_dma_reg__intr_block_t__intr_count_incr_t_pulse_08678f4e::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(pulse.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( pulse.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_E1020031 SAMPLE FUNCTIONS -----------------------*/
    function void axi_dma_reg__intr_block_t__intr_count_incr_t_pulse_e1020031::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*pulse*/   );
        end
    endfunction

    function void axi_dma_reg__intr_block_t__intr_count_incr_t_pulse_e1020031::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(pulse.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( pulse.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_CFE70385 SAMPLE FUNCTIONS -----------------------*/
    function void axi_dma_reg__intr_block_t__intr_count_incr_t_pulse_cfe70385::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*pulse*/   );
        end
    endfunction

    function void axi_dma_reg__intr_block_t__intr_count_incr_t_pulse_cfe70385::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(pulse.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( pulse.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_9A8B3FA0 SAMPLE FUNCTIONS -----------------------*/
    function void axi_dma_reg__intr_block_t__intr_count_incr_t_pulse_9a8b3fa0::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*pulse*/   );
        end
    endfunction

    function void axi_dma_reg__intr_block_t__intr_count_incr_t_pulse_9a8b3fa0::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(pulse.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( pulse.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_F530DCC5 SAMPLE FUNCTIONS -----------------------*/
    function void axi_dma_reg__intr_block_t__intr_count_incr_t_pulse_f530dcc5::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*pulse*/   );
        end
    endfunction

    function void axi_dma_reg__intr_block_t__intr_count_incr_t_pulse_f530dcc5::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(pulse.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( pulse.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_60D6F4E7 SAMPLE FUNCTIONS -----------------------*/
    function void axi_dma_reg__intr_block_t__intr_count_incr_t_pulse_60d6f4e7::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*pulse*/   );
        end
    endfunction

    function void axi_dma_reg__intr_block_t__intr_count_incr_t_pulse_60d6f4e7::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(pulse.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( pulse.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_6907AF43 SAMPLE FUNCTIONS -----------------------*/
    function void axi_dma_reg__intr_block_t__intr_count_incr_t_pulse_6907af43::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*pulse*/   );
        end
    endfunction

    function void axi_dma_reg__intr_block_t__intr_count_incr_t_pulse_6907af43::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(pulse.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( pulse.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_E2DA7281 SAMPLE FUNCTIONS -----------------------*/
    function void axi_dma_reg__intr_block_t__intr_count_incr_t_pulse_e2da7281::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*pulse*/   );
        end
    endfunction

    function void axi_dma_reg__intr_block_t__intr_count_incr_t_pulse_e2da7281::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(pulse.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( pulse.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_3B30AC93 SAMPLE FUNCTIONS -----------------------*/
    function void axi_dma_reg__intr_block_t__intr_count_incr_t_pulse_3b30ac93::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*pulse*/   );
        end
    endfunction

    function void axi_dma_reg__intr_block_t__intr_count_incr_t_pulse_3b30ac93::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(pulse.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( pulse.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_1AB3C91C SAMPLE FUNCTIONS -----------------------*/
    function void axi_dma_reg__intr_block_t__intr_count_incr_t_pulse_1ab3c91c::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*pulse*/   );
        end
    endfunction

    function void axi_dma_reg__intr_block_t__intr_count_incr_t_pulse_1ab3c91c::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(pulse.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( pulse.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_F1BDDE05 SAMPLE FUNCTIONS -----------------------*/
    function void axi_dma_reg__intr_block_t__intr_count_incr_t_pulse_f1bdde05::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*pulse*/   );
        end
    endfunction

    function void axi_dma_reg__intr_block_t__intr_count_incr_t_pulse_f1bdde05::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(pulse.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( pulse.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_236C6006 SAMPLE FUNCTIONS -----------------------*/
    function void axi_dma_reg__intr_block_t__intr_count_incr_t_pulse_236c6006::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*pulse*/   );
        end
    endfunction

    function void axi_dma_reg__intr_block_t__intr_count_incr_t_pulse_236c6006::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(pulse.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( pulse.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_E5E89525 SAMPLE FUNCTIONS -----------------------*/
    function void axi_dma_reg__intr_block_t__intr_count_incr_t_pulse_e5e89525::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*pulse*/   );
        end
    endfunction

    function void axi_dma_reg__intr_block_t__intr_count_incr_t_pulse_e5e89525::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(pulse.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( pulse.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_BFB3930B SAMPLE FUNCTIONS -----------------------*/
    function void axi_dma_reg__intr_block_t__intr_count_incr_t_pulse_bfb3930b::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*pulse*/   );
        end
    endfunction

    function void axi_dma_reg__intr_block_t__intr_count_incr_t_pulse_bfb3930b::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(pulse.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( pulse.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- AXI_DMA_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_2AA328EA SAMPLE FUNCTIONS -----------------------*/
    function void axi_dma_reg__intr_block_t__intr_count_incr_t_pulse_2aa328ea::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*pulse*/   );
        end
    endfunction

    function void axi_dma_reg__intr_block_t__intr_count_incr_t_pulse_2aa328ea::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(pulse.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( pulse.get_mirrored_value()   );
        end
    endfunction

`endif