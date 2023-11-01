//
// File: ahb_lite_slave_0_config_policy.sv
//
// Generated from Mentor VIP Configurator (20220406)
// Generated using Mentor VIP Library ( 2022.2 : 04/20/2022:16:06 )
//
class ahb_lite_slave_0_config_policy;
    static function void configure
    (
        input ahb_lite_slave_0_cfg_t cfg,
        input address_map addrm
    );
        //
        // Agent setup configurations:
        //
        //
        //
        // Active or Passive
        cfg.agent_cfg.is_active = 1;
        // VIP agent type
        cfg.agent_cfg.agent_type = mgc_ahb_v2_0_pkg::AHB_MASTER;
        // Interface type
        cfg.agent_cfg.if_type = mgc_ahb_v2_0_pkg::AHB_LITE;
        // Master / Slave index
        cfg.agent_cfg.index = 0;
        // Use external decoder
        cfg.agent_cfg.ext_decoder = 1'b0;
        // Use external clock
        cfg.agent_cfg.ext_clock = 1;
        // Use external reset
        cfg.agent_cfg.ext_reset = 1;
        // Enable master coverage
        cfg.agent_cfg.en_cvg.master = 1'b0;
        // Enable slave coverage
        cfg.agent_cfg.en_cvg.slave = 1'b0;
        // Enable response coverage
        cfg.agent_cfg.en_cvg.response = 1'b0;
        // Enable arbitration coverage
        cfg.agent_cfg.en_cvg.arbiter = 1'b0;
        // Enable arbiter reset coverage
        cfg.agent_cfg.en_cvg.arbiter_reset = 1'b0;
        // Enable transaction logger
        cfg.agent_cfg.en_logger.txn_log = 0;
        // Enable beat logger
        cfg.agent_cfg.en_logger.beat_log = 0;
        // Transaction logger file name
        cfg.agent_cfg.en_logger.txn_log_name = "txn.log";
        // Beat logger file name
        cfg.agent_cfg.en_logger.beat_log_name = "beat.log";
        cfg.agent_cfg.en_logger.txn_column.tr = 1;
        cfg.agent_cfg.en_logger.txn_column.addr = 1;
        cfg.agent_cfg.en_logger.txn_column.nonseq_time = 1;
        cfg.agent_cfg.en_logger.txn_column.data = 1;
        cfg.agent_cfg.en_logger.txn_column.data_time = 1;
        cfg.agent_cfg.en_logger.txn_column.resp = 1;
        cfg.agent_cfg.en_logger.txn_column.len = 1;
        cfg.agent_cfg.en_logger.txn_column.burst_type = 1;
        cfg.agent_cfg.en_logger.txn_column.burst_size = 1;
        cfg.agent_cfg.en_logger.txn_column.lock = 1;
        cfg.agent_cfg.en_logger.txn_column.hsel = 1;
        cfg.agent_cfg.en_logger.beat_column.nonseq_time = 1;
        cfg.agent_cfg.en_logger.beat_column.ready_time = 1;
        cfg.agent_cfg.en_logger.beat_column.dir_ph = 1;
        cfg.agent_cfg.en_logger.beat_column.addr = 1;
        cfg.agent_cfg.en_logger.beat_column.beat_num = 1;
        cfg.agent_cfg.en_logger.beat_column.len = 1;
        cfg.agent_cfg.en_logger.beat_column.data = 1;
        cfg.agent_cfg.en_logger.beat_column.resp = 1;
        cfg.agent_cfg.en_logger.beat_column.burst_type = 1;
        cfg.agent_cfg.en_logger.beat_column.burst_size = 1;
        cfg.agent_cfg.en_logger.beat_column.prot = 1;
        cfg.agent_cfg.en_logger.beat_column.hsel = 1;
        // Transaction logger data mask
        cfg.agent_cfg.en_logger.txn_data_mask = 1;
        // Beat logger data mask
        cfg.agent_cfg.en_logger.beat_data_mask = 1;
        // Enable clock period change logging
        cfg.agent_cfg.en_logger.clk_mon = 0;
        // Enable HSEL value printing
        cfg.agent_cfg.en_logger.hsel_val = 1;
        // Enable scoreboard
        cfg.agent_cfg.en_sb = 1;
        // Enable transaction listener
        cfg.agent_cfg.en_txn_ltnr = 1'b0;
        // Enable generic payload adapter
        cfg.agent_cfg.en_rw_adapter = 1'b0;
        cfg.agent_cfg.en_perf_stats.enable = 0;
        cfg.agent_cfg.en_perf_stats.step = 100;
        cfg.agent_cfg.en_perf_stats.multiple = 5;
        cfg.agent_cfg.en_debug.arbiter_seq = 1'b0;
        cfg.agent_cfg.en_debug.master_seq = 1'b0;
        cfg.agent_cfg.en_debug.slave_seq = 1'b0;
        cfg.agent_cfg.en_debug.vip_config = 1'b0;
        //
        // VIP Config setup configurations:
        //
        //
        //
        // Slave IDs for all slaves
        cfg.slave_id = '{1{-1}};
        if ( addrm != null )
        begin
            cfg.addr_map = addrm;
        end
        //
        // VIP Config setup configurations at default value:
        //    // Enable warning for uninitialized reads
        //    cfg.m_warn_on_uninitialized_read = 1'b0;
        //
        
        //
        // BFM setup configurations at default value:
        //    // Maximum beats in increment burst
        //    cfg.m_bfm.config_max_incr_burst_beats = 32;
        //    // Default master number in environment
        //    cfg.m_bfm.config_default_master = 0;
        //    // Enables master to send new transfer after it receives error response
        //    cfg.m_bfm.config_master_idle_on_error = 1'b0;
        //    // Enables hready driven externally
        //    cfg.m_bfm.config_HREADYin_external = 1'b0;
        //    // If true, drives previous address when bus is IDLE
        //    cfg.m_bfm.config_address_on_idle = 1'b0;
        //    // Maximum number of successive wait states
              cfg.m_bfm.config_max_wait_states_count = 33;
        //    // Data endianness
        //    cfg.m_bfm.config_endianness = AHB_LITTLE_ENDIAN;
        //    // Sets the domain
        //    cfg.m_bfm.config_domain = '{AHB_NUM_MASTERS{0}};
        //    // Asserts HUNALIGN signal even if address is aligned with no sparse strobes
        //    cfg.m_bfm.config_assert_hunalign_high = 16'h0000;
        //    // Enables ahblite specification update features
        //    cfg.m_bfm.config_en_ahblite_spec_updt = 1'b0;
        //    // Enables signals to be stable for extended transfers
        //    cfg.m_bfm.config_en_stable_btw_clk = 1'b1;
        //    // Enables secure transfers
        //    cfg.m_bfm.config_en_sec_xfer = 1'b1;
        //    // Enables extended memory types
        //    cfg.m_bfm.config_en_ext_mem_types = 1'b1;
        //    // Enables multiple slave select signal
        //    cfg.m_bfm.config_en_mult_slv_sel = 1'b0;
        //    // Enables exclusive transfers
        //    cfg.m_bfm.config_en_excl_xfer = 1'b1;
        //    // Enables slave to drive default value of data for idle transfers
        //    cfg.m_bfm.config_slave_drive_default_value_idle = 1'b0;
        //    // Enable all protocol assertions
        //    cfg.m_bfm.config_enable_all_assertions = 1'b1;
        //    // Enable individual protocol assertion
        //    cfg.m_bfm.config_enable_assertion = 128'hFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF;
        //    // Enables user data signals
        //    cfg.m_bfm.config_user_data_support = 1'b0;
        //    // Enables user address signals
        //    cfg.m_bfm.config_user_address_support = 1'b0;
        //    // Timeout for complete read/write transaction
        //    cfg.m_bfm.config_transaction_timeout_factor = 100000;
        //    // Arbitration timeout between request initiated by master to request completed
        //    cfg.m_bfm.config_arbitration_timeout_factor = 1000;
        //    cfg.m_bfm.config_clk_init_value = 1'b0;
        //    cfg.m_bfm.config_clk_phase_shift = QUESTA_MVC::questa_mvc_sv_convert_to_precision(0, QUESTA_MVC::QUESTA_MVC_TIME_X);
        //    cfg.m_bfm.config_clk_1st_time = QUESTA_MVC::questa_mvc_sv_convert_to_precision(5, QUESTA_MVC::QUESTA_MVC_TIME_X);
        //    cfg.m_bfm.config_clk_2nd_time = QUESTA_MVC::questa_mvc_sv_convert_to_precision(5, QUESTA_MVC::QUESTA_MVC_TIME_X);
        //    cfg.m_bfm.config_reset_low_clocks = 5;
        //    // Configures checking addr in addr_map
        //    cfg.m_bfm.check_addr_map = AHB_CHK_LEGAL;
        //
        
    endfunction: configure
    
endclass: ahb_lite_slave_0_config_policy

