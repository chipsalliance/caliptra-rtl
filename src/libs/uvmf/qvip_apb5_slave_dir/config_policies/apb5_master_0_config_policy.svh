//
// File: apb5_master_0_config_policy.sv
//
// Generated from Mentor VIP Configurator (20220406)
// Generated using Mentor VIP Library ( 2022.2 : 04/20/2022:16:06 )
//
class apb5_master_0_config_policy;
    static function void configure
    (
        input apb5_master_0_cfg_t cfg,
        input address_map addrm
    );
        //
        // Agent setup configurations:
        //
        cfg.agent_cfg.is_active = 1;
        cfg.agent_cfg.agent_type = mgc_apb3_v1_0_pkg::APB_MASTER;
        // APB interface type
        cfg.agent_cfg.if_type = mgc_apb3_v1_0_pkg::APB5;
        // Use external clock
        cfg.agent_cfg.ext_clock = 1;
        // Use external reset
        cfg.agent_cfg.ext_reset = 1;
        // Enable functional coverage
        cfg.agent_cfg.en_cvg = 1'b0;
        // Enable scoreboard
        cfg.agent_cfg.en_sb = 1;
        // Enable transaction listener
        cfg.agent_cfg.en_txn_ltnr = 1'b0;
        // Enable transaction logger
        cfg.agent_cfg.en_logger.txn_log = 0;
        // Transaction logger file name
        cfg.agent_cfg.en_logger.txn_log_name = "txn.log";
        cfg.agent_cfg.en_logger.txn_column.tr = 1;
        cfg.agent_cfg.en_logger.txn_column.slv_id = 1;
        cfg.agent_cfg.en_logger.txn_column.addr = 1;
        cfg.agent_cfg.en_logger.txn_column.data = 1;
        cfg.agent_cfg.en_logger.txn_column.strb = 1;
        cfg.agent_cfg.en_logger.txn_column.prot = 1;
        cfg.agent_cfg.en_logger.txn_column.slverr = 1;
        cfg.agent_cfg.en_logger.txn_column.start_time = 1;
        cfg.agent_cfg.en_logger.txn_column.end_time = 1;
        // Transaction logger data mask
        cfg.agent_cfg.en_logger.txn_data_mask = 1;
        // Enable clock period change logging
        cfg.agent_cfg.en_logger.clk_mon = 0;
        // Enable error reporting in logger
        cfg.agent_cfg.en_logger.en_assertions_log = 0;
        // Enable generic payload adapter
        cfg.agent_cfg.en_rw_adapter = 1'b0;
        //
        // VIP Config setup configurations:
        //
        if ( addrm != null )
        begin
            cfg.addr_map = addrm;
        end
        // Modify the slave and scoreboard memory type use byte/word/dword memory
        cfg.mem_type = mgc_apb3_v1_0_pkg::APB_MEM_DWORD;
        //
        // VIP Config setup configurations at default value:
        //    // Enable warning for uninitialized reads
        //    cfg.m_warn_on_uninitialized_read = 1'b0;
        //
        
        //
        // BFM setup configurations:
        //
        //
        //
        // Width of PAUSER signal
        cfg.m_bfm.config_pauser_width = 32;
        //
        // BFM setup configurations at default value:
        //    // Enable all protocol assertions
        //    cfg.m_bfm.config_enable_all_assertions = 2'h3;
        //    // Enable individual protocol assertion
        //    cfg.m_bfm.config_enable_assertion = 91'h7FFFFFFFFFFFFFFFFFFFFFF;
        //    // Enable APB protocol recommended Checks
        //    cfg.m_bfm.config_en_recom_check = 1'b0;
        //    // Width of PWUSER signal
        //    cfg.m_bfm.config_pwuser_width = 4;
        //    // Width of PRUSER signal
        //    cfg.m_bfm.config_pruser_width = 4;
        //    // Width of PBUSER signal
        //    cfg.m_bfm.config_pbuser_width = 4;
        //    // Check Signal property
        //    cfg.m_bfm.config_parity_chk = APB_PARITY_CHK_FALSE;
        //    // Wakeup Signal property
        //    cfg.m_bfm.config_enable_wakeup = APB_WAKEUP_DISABLE;
        //    // Default value for PREADY
        //    cfg.m_bfm.config_default_pready = 1'b0;
        //    // Default value for PSLVERR
        //    cfg.m_bfm.config_default_pslverr = 1'b0;
        //    // Default read data value (PRDATA)
        //    cfg.m_bfm.config_default_prdata = 32'h00000000;
        //    // Response timeout for slave response
        //    cfg.m_bfm.config_response_max_timeout = 500;
        //    cfg.m_bfm.config_clk_init_value = 1'b0;
        //    cfg.m_bfm.config_clk_phase_shift = QUESTA_MVC::questa_mvc_sv_convert_to_precision(10, QUESTA_MVC::QUESTA_MVC_TIME_X);
        //    cfg.m_bfm.config_clk_1st_time = QUESTA_MVC::questa_mvc_sv_convert_to_precision(10, QUESTA_MVC::QUESTA_MVC_TIME_X);
        //    cfg.m_bfm.config_clk_2nd_time = QUESTA_MVC::questa_mvc_sv_convert_to_precision(10, QUESTA_MVC::QUESTA_MVC_TIME_X);
        //    cfg.m_bfm.config_reset_low_clocks = 10;
        //    cfg.m_bfm.config_reset_hold_time = QUESTA_MVC::questa_mvc_sv_convert_to_precision(1, QUESTA_MVC::QUESTA_MVC_TIME_X);
        //    // Configures checking addr in addr_map
        //    cfg.m_bfm.check_addr_map = APB_CHK_LEGAL;
        //    // Error injection
        //    cfg.m_bfm.config_error_injection = APB_ERR_NONE;
        //
        
    endfunction: configure
    
endclass: apb5_master_0_config_policy

