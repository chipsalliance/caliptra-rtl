// Generated by PeakRDL-regblock - A free and open-source SystemVerilog generator
//  https://github.com/SystemRDL/PeakRDL-regblock

package axi_dma_reg_pkg;

    localparam AXI_DMA_REG_DATA_WIDTH = 32;
    localparam AXI_DMA_REG_MIN_ADDR_WIDTH = 12;

    typedef struct packed{
        logic [11:0] next;
    } axi_dma_reg__cap__fifo_max_depth__in_t;

    typedef struct packed{
        axi_dma_reg__cap__fifo_max_depth__in_t fifo_max_depth;
    } axi_dma_reg__cap__in_t;

    typedef struct packed{
        logic hwclr;
    } axi_dma_reg__ctrl__go__in_t;

    typedef struct packed{
        logic hwclr;
    } axi_dma_reg__ctrl__flush__in_t;

    typedef struct packed{
        axi_dma_reg__ctrl__go__in_t go;
        axi_dma_reg__ctrl__flush__in_t flush;
    } axi_dma_reg__ctrl__in_t;

    typedef struct packed{
        logic next;
    } axi_dma_reg__status0__busy__in_t;

    typedef struct packed{
        logic next;
    } axi_dma_reg__status0__error__in_t;

    typedef struct packed{
        logic [11:0] next;
    } axi_dma_reg__status0__fifo_depth__in_t;

    typedef struct packed{
        logic [1:0] next;
    } axi_dma_reg__status0__axi_dma_fsm_ps__in_t;

    typedef struct packed{
        logic next;
    } axi_dma_reg__status0__payload_available__in_t;

    typedef struct packed{
        logic next;
    } axi_dma_reg__status0__image_activated__in_t;

    typedef struct packed{
        logic [3:0] next;
    } axi_dma_reg__status0__axi_dma_aes_fsm_ps__in_t;

    typedef struct packed{
        axi_dma_reg__status0__busy__in_t busy;
        axi_dma_reg__status0__error__in_t error;
        axi_dma_reg__status0__fifo_depth__in_t fifo_depth;
        axi_dma_reg__status0__axi_dma_fsm_ps__in_t axi_dma_fsm_ps;
        axi_dma_reg__status0__payload_available__in_t payload_available;
        axi_dma_reg__status0__image_activated__in_t image_activated;
        axi_dma_reg__status0__axi_dma_aes_fsm_ps__in_t axi_dma_aes_fsm_ps;
    } axi_dma_reg__status0__in_t;

    typedef struct packed{
        logic [31:0] next;
    } axi_dma_reg__status1__bytes_remaining__in_t;

    typedef struct packed{
        axi_dma_reg__status1__bytes_remaining__in_t bytes_remaining;
    } axi_dma_reg__status1__in_t;

    typedef struct packed{
        logic [31:0] next;
    } axi_dma_reg__read_data__rdata__in_t;

    typedef struct packed{
        axi_dma_reg__read_data__rdata__in_t rdata;
    } axi_dma_reg__read_data__in_t;

    typedef struct packed{
        logic hwset;
    } axi_dma_reg__intr_block_t__error_intr_t_error_aes_cif_sts_63385a16_error_axi_rd_sts_927e49cd_error_axi_wr_sts_f84e5c07_error_cmd_dec_sts_46039d92_error_fifo_oflow_sts_71b29a77_error_fifo_uflow_sts_119d122a_error_mbox_lock_sts_9e18c395_error_sha_lock_sts_4c7993a0__error_cmd_dec_sts_enable_3fe3f38e_next_81a41b0f_resetsignal_f7aac87a__in_t;

    typedef struct packed{
        logic hwset;
    } axi_dma_reg__intr_block_t__error_intr_t_error_aes_cif_sts_63385a16_error_axi_rd_sts_927e49cd_error_axi_wr_sts_f84e5c07_error_cmd_dec_sts_46039d92_error_fifo_oflow_sts_71b29a77_error_fifo_uflow_sts_119d122a_error_mbox_lock_sts_9e18c395_error_sha_lock_sts_4c7993a0__error_axi_rd_sts_enable_ade70b75_next_9749130e_resetsignal_f7aac87a__in_t;

    typedef struct packed{
        logic hwset;
    } axi_dma_reg__intr_block_t__error_intr_t_error_aes_cif_sts_63385a16_error_axi_rd_sts_927e49cd_error_axi_wr_sts_f84e5c07_error_cmd_dec_sts_46039d92_error_fifo_oflow_sts_71b29a77_error_fifo_uflow_sts_119d122a_error_mbox_lock_sts_9e18c395_error_sha_lock_sts_4c7993a0__error_axi_wr_sts_enable_8302157e_next_d030e286_resetsignal_f7aac87a__in_t;

    typedef struct packed{
        logic hwset;
    } axi_dma_reg__intr_block_t__error_intr_t_error_aes_cif_sts_63385a16_error_axi_rd_sts_927e49cd_error_axi_wr_sts_f84e5c07_error_cmd_dec_sts_46039d92_error_fifo_oflow_sts_71b29a77_error_fifo_uflow_sts_119d122a_error_mbox_lock_sts_9e18c395_error_sha_lock_sts_4c7993a0__error_mbox_lock_sts_enable_2200d685_next_dd20251c_resetsignal_f7aac87a__in_t;

    typedef struct packed{
        logic hwset;
    } axi_dma_reg__intr_block_t__error_intr_t_error_aes_cif_sts_63385a16_error_axi_rd_sts_927e49cd_error_axi_wr_sts_f84e5c07_error_cmd_dec_sts_46039d92_error_fifo_oflow_sts_71b29a77_error_fifo_uflow_sts_119d122a_error_mbox_lock_sts_9e18c395_error_sha_lock_sts_4c7993a0__error_sha_lock_sts_enable_b89b863e_next_78f72dee_resetsignal_f7aac87a__in_t;

    typedef struct packed{
        logic hwset;
    } axi_dma_reg__intr_block_t__error_intr_t_error_aes_cif_sts_63385a16_error_axi_rd_sts_927e49cd_error_axi_wr_sts_f84e5c07_error_cmd_dec_sts_46039d92_error_fifo_oflow_sts_71b29a77_error_fifo_uflow_sts_119d122a_error_mbox_lock_sts_9e18c395_error_sha_lock_sts_4c7993a0__error_fifo_oflow_sts_enable_db42b065_next_8d43e112_resetsignal_f7aac87a__in_t;

    typedef struct packed{
        logic hwset;
    } axi_dma_reg__intr_block_t__error_intr_t_error_aes_cif_sts_63385a16_error_axi_rd_sts_927e49cd_error_axi_wr_sts_f84e5c07_error_cmd_dec_sts_46039d92_error_fifo_oflow_sts_71b29a77_error_fifo_uflow_sts_119d122a_error_mbox_lock_sts_9e18c395_error_sha_lock_sts_4c7993a0__error_fifo_uflow_sts_enable_fec90e1d_next_a25205a2_resetsignal_f7aac87a__in_t;

    typedef struct packed{
        logic hwset;
    } axi_dma_reg__intr_block_t__error_intr_t_error_aes_cif_sts_63385a16_error_axi_rd_sts_927e49cd_error_axi_wr_sts_f84e5c07_error_cmd_dec_sts_46039d92_error_fifo_oflow_sts_71b29a77_error_fifo_uflow_sts_119d122a_error_mbox_lock_sts_9e18c395_error_sha_lock_sts_4c7993a0__error_aes_cif_sts_enable_427cc14a_next_cae765d7_resetsignal_f7aac87a__in_t;

    typedef struct packed{
        axi_dma_reg__intr_block_t__error_intr_t_error_aes_cif_sts_63385a16_error_axi_rd_sts_927e49cd_error_axi_wr_sts_f84e5c07_error_cmd_dec_sts_46039d92_error_fifo_oflow_sts_71b29a77_error_fifo_uflow_sts_119d122a_error_mbox_lock_sts_9e18c395_error_sha_lock_sts_4c7993a0__error_cmd_dec_sts_enable_3fe3f38e_next_81a41b0f_resetsignal_f7aac87a__in_t error_cmd_dec_sts;
        axi_dma_reg__intr_block_t__error_intr_t_error_aes_cif_sts_63385a16_error_axi_rd_sts_927e49cd_error_axi_wr_sts_f84e5c07_error_cmd_dec_sts_46039d92_error_fifo_oflow_sts_71b29a77_error_fifo_uflow_sts_119d122a_error_mbox_lock_sts_9e18c395_error_sha_lock_sts_4c7993a0__error_axi_rd_sts_enable_ade70b75_next_9749130e_resetsignal_f7aac87a__in_t error_axi_rd_sts;
        axi_dma_reg__intr_block_t__error_intr_t_error_aes_cif_sts_63385a16_error_axi_rd_sts_927e49cd_error_axi_wr_sts_f84e5c07_error_cmd_dec_sts_46039d92_error_fifo_oflow_sts_71b29a77_error_fifo_uflow_sts_119d122a_error_mbox_lock_sts_9e18c395_error_sha_lock_sts_4c7993a0__error_axi_wr_sts_enable_8302157e_next_d030e286_resetsignal_f7aac87a__in_t error_axi_wr_sts;
        axi_dma_reg__intr_block_t__error_intr_t_error_aes_cif_sts_63385a16_error_axi_rd_sts_927e49cd_error_axi_wr_sts_f84e5c07_error_cmd_dec_sts_46039d92_error_fifo_oflow_sts_71b29a77_error_fifo_uflow_sts_119d122a_error_mbox_lock_sts_9e18c395_error_sha_lock_sts_4c7993a0__error_mbox_lock_sts_enable_2200d685_next_dd20251c_resetsignal_f7aac87a__in_t error_mbox_lock_sts;
        axi_dma_reg__intr_block_t__error_intr_t_error_aes_cif_sts_63385a16_error_axi_rd_sts_927e49cd_error_axi_wr_sts_f84e5c07_error_cmd_dec_sts_46039d92_error_fifo_oflow_sts_71b29a77_error_fifo_uflow_sts_119d122a_error_mbox_lock_sts_9e18c395_error_sha_lock_sts_4c7993a0__error_sha_lock_sts_enable_b89b863e_next_78f72dee_resetsignal_f7aac87a__in_t error_sha_lock_sts;
        axi_dma_reg__intr_block_t__error_intr_t_error_aes_cif_sts_63385a16_error_axi_rd_sts_927e49cd_error_axi_wr_sts_f84e5c07_error_cmd_dec_sts_46039d92_error_fifo_oflow_sts_71b29a77_error_fifo_uflow_sts_119d122a_error_mbox_lock_sts_9e18c395_error_sha_lock_sts_4c7993a0__error_fifo_oflow_sts_enable_db42b065_next_8d43e112_resetsignal_f7aac87a__in_t error_fifo_oflow_sts;
        axi_dma_reg__intr_block_t__error_intr_t_error_aes_cif_sts_63385a16_error_axi_rd_sts_927e49cd_error_axi_wr_sts_f84e5c07_error_cmd_dec_sts_46039d92_error_fifo_oflow_sts_71b29a77_error_fifo_uflow_sts_119d122a_error_mbox_lock_sts_9e18c395_error_sha_lock_sts_4c7993a0__error_fifo_uflow_sts_enable_fec90e1d_next_a25205a2_resetsignal_f7aac87a__in_t error_fifo_uflow_sts;
        axi_dma_reg__intr_block_t__error_intr_t_error_aes_cif_sts_63385a16_error_axi_rd_sts_927e49cd_error_axi_wr_sts_f84e5c07_error_cmd_dec_sts_46039d92_error_fifo_oflow_sts_71b29a77_error_fifo_uflow_sts_119d122a_error_mbox_lock_sts_9e18c395_error_sha_lock_sts_4c7993a0__error_aes_cif_sts_enable_427cc14a_next_cae765d7_resetsignal_f7aac87a__in_t error_aes_cif_sts;
    } axi_dma_reg__intr_block_t__error_intr_t_error_aes_cif_sts_63385a16_error_axi_rd_sts_927e49cd_error_axi_wr_sts_f84e5c07_error_cmd_dec_sts_46039d92_error_fifo_oflow_sts_71b29a77_error_fifo_uflow_sts_119d122a_error_mbox_lock_sts_9e18c395_error_sha_lock_sts_4c7993a0__in_t;

    typedef struct packed{
        logic hwset;
    } axi_dma_reg__intr_block_t__notif_intr_t_notif_fifo_empty_sts_d87d1786_notif_fifo_full_sts_64c66862_notif_fifo_not_empty_sts_1a0e2460_notif_fifo_not_full_sts_0266fe07_notif_txn_done_sts_0ee2f120__notif_txn_done_sts_enable_f3ace5c8_next_c04384c4__in_t;

    typedef struct packed{
        logic hwset;
    } axi_dma_reg__intr_block_t__notif_intr_t_notif_fifo_empty_sts_d87d1786_notif_fifo_full_sts_64c66862_notif_fifo_not_empty_sts_1a0e2460_notif_fifo_not_full_sts_0266fe07_notif_txn_done_sts_0ee2f120__notif_fifo_empty_sts_enable_13fbeac1_next_3b1b70cb__in_t;

    typedef struct packed{
        logic hwset;
    } axi_dma_reg__intr_block_t__notif_intr_t_notif_fifo_empty_sts_d87d1786_notif_fifo_full_sts_64c66862_notif_fifo_not_empty_sts_1a0e2460_notif_fifo_not_full_sts_0266fe07_notif_txn_done_sts_0ee2f120__notif_fifo_not_empty_sts_enable_fc6f2a07_next_53ecda05__in_t;

    typedef struct packed{
        logic hwset;
    } axi_dma_reg__intr_block_t__notif_intr_t_notif_fifo_empty_sts_d87d1786_notif_fifo_full_sts_64c66862_notif_fifo_not_empty_sts_1a0e2460_notif_fifo_not_full_sts_0266fe07_notif_txn_done_sts_0ee2f120__notif_fifo_full_sts_enable_d59af270_next_5df4004b__in_t;

    typedef struct packed{
        logic hwset;
    } axi_dma_reg__intr_block_t__notif_intr_t_notif_fifo_empty_sts_d87d1786_notif_fifo_full_sts_64c66862_notif_fifo_not_empty_sts_1a0e2460_notif_fifo_not_full_sts_0266fe07_notif_txn_done_sts_0ee2f120__notif_fifo_not_full_sts_enable_9ba0ed48_next_ed3f253d__in_t;

    typedef struct packed{
        axi_dma_reg__intr_block_t__notif_intr_t_notif_fifo_empty_sts_d87d1786_notif_fifo_full_sts_64c66862_notif_fifo_not_empty_sts_1a0e2460_notif_fifo_not_full_sts_0266fe07_notif_txn_done_sts_0ee2f120__notif_txn_done_sts_enable_f3ace5c8_next_c04384c4__in_t notif_txn_done_sts;
        axi_dma_reg__intr_block_t__notif_intr_t_notif_fifo_empty_sts_d87d1786_notif_fifo_full_sts_64c66862_notif_fifo_not_empty_sts_1a0e2460_notif_fifo_not_full_sts_0266fe07_notif_txn_done_sts_0ee2f120__notif_fifo_empty_sts_enable_13fbeac1_next_3b1b70cb__in_t notif_fifo_empty_sts;
        axi_dma_reg__intr_block_t__notif_intr_t_notif_fifo_empty_sts_d87d1786_notif_fifo_full_sts_64c66862_notif_fifo_not_empty_sts_1a0e2460_notif_fifo_not_full_sts_0266fe07_notif_txn_done_sts_0ee2f120__notif_fifo_not_empty_sts_enable_fc6f2a07_next_53ecda05__in_t notif_fifo_not_empty_sts;
        axi_dma_reg__intr_block_t__notif_intr_t_notif_fifo_empty_sts_d87d1786_notif_fifo_full_sts_64c66862_notif_fifo_not_empty_sts_1a0e2460_notif_fifo_not_full_sts_0266fe07_notif_txn_done_sts_0ee2f120__notif_fifo_full_sts_enable_d59af270_next_5df4004b__in_t notif_fifo_full_sts;
        axi_dma_reg__intr_block_t__notif_intr_t_notif_fifo_empty_sts_d87d1786_notif_fifo_full_sts_64c66862_notif_fifo_not_empty_sts_1a0e2460_notif_fifo_not_full_sts_0266fe07_notif_txn_done_sts_0ee2f120__notif_fifo_not_full_sts_enable_9ba0ed48_next_ed3f253d__in_t notif_fifo_not_full_sts;
    } axi_dma_reg__intr_block_t__notif_intr_t_notif_fifo_empty_sts_d87d1786_notif_fifo_full_sts_64c66862_notif_fifo_not_empty_sts_1a0e2460_notif_fifo_not_full_sts_0266fe07_notif_txn_done_sts_0ee2f120__in_t;

    typedef struct packed{
        axi_dma_reg__intr_block_t__error_intr_t_error_aes_cif_sts_63385a16_error_axi_rd_sts_927e49cd_error_axi_wr_sts_f84e5c07_error_cmd_dec_sts_46039d92_error_fifo_oflow_sts_71b29a77_error_fifo_uflow_sts_119d122a_error_mbox_lock_sts_9e18c395_error_sha_lock_sts_4c7993a0__in_t error_internal_intr_r;
        axi_dma_reg__intr_block_t__notif_intr_t_notif_fifo_empty_sts_d87d1786_notif_fifo_full_sts_64c66862_notif_fifo_not_empty_sts_1a0e2460_notif_fifo_not_full_sts_0266fe07_notif_txn_done_sts_0ee2f120__in_t notif_internal_intr_r;
    } axi_dma_reg__intr_block_t__in_t;

    typedef struct packed{
        logic cptra_rst_b;
        logic cptra_pwrgood;
        logic soc_req;
        logic dma_swwel;
        axi_dma_reg__cap__in_t cap;
        axi_dma_reg__ctrl__in_t ctrl;
        axi_dma_reg__status0__in_t status0;
        axi_dma_reg__status1__in_t status1;
        axi_dma_reg__read_data__in_t read_data;
        axi_dma_reg__intr_block_t__in_t intr_block_rf;
    } axi_dma_reg__in_t;

    typedef struct packed{
        logic value;
        logic swmod;
    } axi_dma_reg__ctrl__go__out_t;

    typedef struct packed{
        logic value;
    } axi_dma_reg__ctrl__flush__out_t;

    typedef struct packed{
        logic value;
    } axi_dma_reg__ctrl__aes_mode_en__out_t;

    typedef struct packed{
        logic value;
    } axi_dma_reg__ctrl__aes_gcm_mode__out_t;

    typedef struct packed{
        logic [1:0] value;
    } axi_dma_reg__ctrl__rd_route__out_t;

    typedef struct packed{
        logic value;
    } axi_dma_reg__ctrl__rd_fixed__out_t;

    typedef struct packed{
        logic [1:0] value;
    } axi_dma_reg__ctrl__wr_route__out_t;

    typedef struct packed{
        logic value;
    } axi_dma_reg__ctrl__wr_fixed__out_t;

    typedef struct packed{
        axi_dma_reg__ctrl__go__out_t go;
        axi_dma_reg__ctrl__flush__out_t flush;
        axi_dma_reg__ctrl__aes_mode_en__out_t aes_mode_en;
        axi_dma_reg__ctrl__aes_gcm_mode__out_t aes_gcm_mode;
        axi_dma_reg__ctrl__rd_route__out_t rd_route;
        axi_dma_reg__ctrl__rd_fixed__out_t rd_fixed;
        axi_dma_reg__ctrl__wr_route__out_t wr_route;
        axi_dma_reg__ctrl__wr_fixed__out_t wr_fixed;
    } axi_dma_reg__ctrl__out_t;

    typedef struct packed{
        logic [1:0] value;
    } axi_dma_reg__status0__axi_dma_fsm_ps__out_t;

    typedef struct packed{
        logic [3:0] value;
    } axi_dma_reg__status0__axi_dma_aes_fsm_ps__out_t;

    typedef struct packed{
        axi_dma_reg__status0__axi_dma_fsm_ps__out_t axi_dma_fsm_ps;
        axi_dma_reg__status0__axi_dma_aes_fsm_ps__out_t axi_dma_aes_fsm_ps;
    } axi_dma_reg__status0__out_t;

    typedef struct packed{
        logic [31:0] value;
    } axi_dma_reg__src_addr_l__addr_l__out_t;

    typedef struct packed{
        axi_dma_reg__src_addr_l__addr_l__out_t addr_l;
    } axi_dma_reg__src_addr_l__out_t;

    typedef struct packed{
        logic [31:0] value;
    } axi_dma_reg__src_addr_h__addr_h__out_t;

    typedef struct packed{
        axi_dma_reg__src_addr_h__addr_h__out_t addr_h;
    } axi_dma_reg__src_addr_h__out_t;

    typedef struct packed{
        logic [31:0] value;
    } axi_dma_reg__dst_addr_l__addr_l__out_t;

    typedef struct packed{
        axi_dma_reg__dst_addr_l__addr_l__out_t addr_l;
    } axi_dma_reg__dst_addr_l__out_t;

    typedef struct packed{
        logic [31:0] value;
    } axi_dma_reg__dst_addr_h__addr_h__out_t;

    typedef struct packed{
        axi_dma_reg__dst_addr_h__addr_h__out_t addr_h;
    } axi_dma_reg__dst_addr_h__out_t;

    typedef struct packed{
        logic [31:0] value;
    } axi_dma_reg__byte_count__count__out_t;

    typedef struct packed{
        axi_dma_reg__byte_count__count__out_t count;
    } axi_dma_reg__byte_count__out_t;

    typedef struct packed{
        logic [11:0] value;
    } axi_dma_reg__block_size__size__out_t;

    typedef struct packed{
        axi_dma_reg__block_size__size__out_t size;
    } axi_dma_reg__block_size__out_t;

    typedef struct packed{
        logic swmod;
    } axi_dma_reg__write_data__wdata__out_t;

    typedef struct packed{
        axi_dma_reg__write_data__wdata__out_t wdata;
    } axi_dma_reg__write_data__out_t;

    typedef struct packed{
        logic swacc;
    } axi_dma_reg__read_data__rdata__out_t;

    typedef struct packed{
        axi_dma_reg__read_data__rdata__out_t rdata;
    } axi_dma_reg__read_data__out_t;

    typedef struct packed{
        logic intr;
    } axi_dma_reg__intr_block_t__global_intr_t_agg_sts_dd3dcf0a__out_t;

    typedef struct packed{
        logic intr;
    } axi_dma_reg__intr_block_t__global_intr_t_agg_sts_e6399b4a__out_t;

    typedef struct packed{
        logic intr;
    } axi_dma_reg__intr_block_t__error_intr_t_error_aes_cif_sts_63385a16_error_axi_rd_sts_927e49cd_error_axi_wr_sts_f84e5c07_error_cmd_dec_sts_46039d92_error_fifo_oflow_sts_71b29a77_error_fifo_uflow_sts_119d122a_error_mbox_lock_sts_9e18c395_error_sha_lock_sts_4c7993a0__out_t;

    typedef struct packed{
        logic intr;
    } axi_dma_reg__intr_block_t__notif_intr_t_notif_fifo_empty_sts_d87d1786_notif_fifo_full_sts_64c66862_notif_fifo_not_empty_sts_1a0e2460_notif_fifo_not_full_sts_0266fe07_notif_txn_done_sts_0ee2f120__out_t;

    typedef struct packed{
        axi_dma_reg__intr_block_t__global_intr_t_agg_sts_dd3dcf0a__out_t error_global_intr_r;
        axi_dma_reg__intr_block_t__global_intr_t_agg_sts_e6399b4a__out_t notif_global_intr_r;
        axi_dma_reg__intr_block_t__error_intr_t_error_aes_cif_sts_63385a16_error_axi_rd_sts_927e49cd_error_axi_wr_sts_f84e5c07_error_cmd_dec_sts_46039d92_error_fifo_oflow_sts_71b29a77_error_fifo_uflow_sts_119d122a_error_mbox_lock_sts_9e18c395_error_sha_lock_sts_4c7993a0__out_t error_internal_intr_r;
        axi_dma_reg__intr_block_t__notif_intr_t_notif_fifo_empty_sts_d87d1786_notif_fifo_full_sts_64c66862_notif_fifo_not_empty_sts_1a0e2460_notif_fifo_not_full_sts_0266fe07_notif_txn_done_sts_0ee2f120__out_t notif_internal_intr_r;
    } axi_dma_reg__intr_block_t__out_t;

    typedef struct packed{
        axi_dma_reg__ctrl__out_t ctrl;
        axi_dma_reg__status0__out_t status0;
        axi_dma_reg__src_addr_l__out_t src_addr_l;
        axi_dma_reg__src_addr_h__out_t src_addr_h;
        axi_dma_reg__dst_addr_l__out_t dst_addr_l;
        axi_dma_reg__dst_addr_h__out_t dst_addr_h;
        axi_dma_reg__byte_count__out_t byte_count;
        axi_dma_reg__block_size__out_t block_size;
        axi_dma_reg__write_data__out_t write_data;
        axi_dma_reg__read_data__out_t read_data;
        axi_dma_reg__intr_block_t__out_t intr_block_rf;
    } axi_dma_reg__out_t;

    typedef enum logic [31:0] {
        axi_dma_reg__ctrl__rd_route__rd_route_e__DISABLE = 'h0,
        axi_dma_reg__ctrl__rd_route__rd_route_e__MBOX = 'h1,
        axi_dma_reg__ctrl__rd_route__rd_route_e__AHB_FIFO = 'h2,
        axi_dma_reg__ctrl__rd_route__rd_route_e__AXI_WR = 'h3
    } axi_dma_reg__ctrl__rd_route__rd_route_e_e;

    typedef enum logic [31:0] {
        axi_dma_reg__ctrl__wr_route__wr_route_e__DISABLE = 'h0,
        axi_dma_reg__ctrl__wr_route__wr_route_e__MBOX = 'h1,
        axi_dma_reg__ctrl__wr_route__wr_route_e__AHB_FIFO = 'h2,
        axi_dma_reg__ctrl__wr_route__wr_route_e__AXI_RD = 'h3
    } axi_dma_reg__ctrl__wr_route__wr_route_e_e;

    typedef enum logic [31:0] {
        axi_dma_reg__status0__axi_dma_fsm_ps__axi_dma_fsm_e__DMA_IDLE = 'h0,
        axi_dma_reg__status0__axi_dma_fsm_ps__axi_dma_fsm_e__DMA_WAIT_DATA = 'h1,
        axi_dma_reg__status0__axi_dma_fsm_ps__axi_dma_fsm_e__DMA_DONE = 'h2,
        axi_dma_reg__status0__axi_dma_fsm_ps__axi_dma_fsm_e__DMA_ERROR = 'h3
    } axi_dma_reg__status0__axi_dma_fsm_ps__axi_dma_fsm_e_e;

    typedef enum logic [31:0] {
        axi_dma_reg__status0__axi_dma_aes_fsm_ps__axi_dma_aes_fsm_e__AES_IDLE = 'h0,
        axi_dma_reg__status0__axi_dma_aes_fsm_ps__axi_dma_aes_fsm_e__AES_WAIT_INPUT_READY = 'h1,
        axi_dma_reg__status0__axi_dma_aes_fsm_ps__axi_dma_aes_fsm_e__AES_WAIT_IDLE = 'h2,
        axi_dma_reg__status0__axi_dma_aes_fsm_ps__axi_dma_aes_fsm_e__AES_UPDATE_BYTE_COUNT = 'h3,
        axi_dma_reg__status0__axi_dma_aes_fsm_ps__axi_dma_aes_fsm_e__AES_WRITE_BLOCK = 'h4,
        axi_dma_reg__status0__axi_dma_aes_fsm_ps__axi_dma_aes_fsm_e__AES_WAIT_OUTPUT_VALID = 'h5,
        axi_dma_reg__status0__axi_dma_aes_fsm_ps__axi_dma_aes_fsm_e__AES_READ_OUTPUT = 'h6,
        axi_dma_reg__status0__axi_dma_aes_fsm_ps__axi_dma_aes_fsm_e__AES_DONE = 'h7,
        axi_dma_reg__status0__axi_dma_aes_fsm_ps__axi_dma_aes_fsm_e__AES_ERROR = 'h8
    } axi_dma_reg__status0__axi_dma_aes_fsm_ps__axi_dma_aes_fsm_e_e;

    localparam AXI_DMA_REG_ADDR_WIDTH = 32'd12;

endpackage