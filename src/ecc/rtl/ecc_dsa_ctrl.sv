//======================================================================
//
// ecc_core_ctrl.sv
// --------
// 
//
//
// Author: Mojtaba Bisheh-Niasar
//======================================================================

module ecc_dsa_ctrl(
    // Clock and reset.
    input wire           clk,
    input wire           reset_n,

    // Reg ports.
    input ecc_reg_pkg::ecc_reg__out_t hwif_in,
    output ecc_reg_pkg::ecc_reg__in_t hwif_out
    );

    //----------------------------------------------------------------
    // Internal constant and parameter definitions.
    //----------------------------------------------------------------
    `include "ecc_params.sv"
    `include "ecc_dsa_uop.sv"

    localparam DSA_PROG_LENGTH          = 2**DSA_PROG_ADDR_W;

    //----------------------------------------------------------------
    // Registers including update variables and write enable.
    //----------------------------------------------------------------
    logic [DSA_PROG_ADDR_W-1 : 0]        prog_cntr;
    logic [DSA_INSTRUCTION_LENGTH-1 : 0] prog_line;   
    
    logic [REG_SIZE   : 0]  read_reg;
    logic [REG_SIZE   : 0]  write_reg;
    logic [7 : 0]           addr_reg;
    logic [1 : 0]           cycle_cnt;

    logic                   dsa_busy;
    logic                   pm_busy_o;
    
    logic hw_seed_we;
    logic hw_privkey_we;
    logic hw_pubkeyx_we;
    logic hw_pubkeyy_we;
    logic hw_r_we;
    logic hw_s_we;
    logic hw_scalar_G_we;
    logic hw_scalar_PK_we;
    logic hw_verify_r_we;
    logic scalar_G_sel;

    logic dsa_valid_reg;
    logic dsa_ready_reg;

    logic [1  : 0]          cmd_reg;
    logic [REG_SIZE-1 : 0]  msg_reg;
    logic [REG_SIZE-1 : 0]  privkey_reg;
    logic [REG_SIZE-1 : 0]  pubkeyx_reg;
    logic [REG_SIZE-1 : 0]  pubkeyy_reg;
    logic [REG_SIZE-1 : 0]  seed_reg;
    logic [REG_SIZE-1 : 0]  r_reg;
    logic [REG_SIZE-1 : 0]  s_reg;

    logic [REG_SIZE-1 : 0]  scalar_G_reg;
    logic [REG_SIZE-1 : 0]  scalar_PK_reg;
    logic [REG_SIZE-1 : 0]  scalar_in_reg;
    logic [REG_SIZE   : 0]  scalar_out_reg;
    logic                   fixed_msb_en;
    logic [2  : 0]          PM_cmd_reg;

    logic                   hmac_mode;
    logic                   hmac_init;
    logic                   hmac_ready;
    logic                   hmac_valid;
    logic [REG_SIZE-1 : 0]  hmac_nonce;
    logic                   hmac_busy;

    //----------------------------------------------------------------
    // Module instantiantions.
    //----------------------------------------------------------------
    ecc_dsa_sequencer #(
        .ADDR_WIDTH(DSA_PROG_ADDR_W),
        .DATA_WIDTH(DSA_INSTRUCTION_LENGTH)
        )
        ecc_dsa_sequencer_i(
        .clka(clk),
        .ena(1'b1),
        .addra(prog_cntr),
        .douta(prog_line)
    );

    ecc_fixed_msb #(
        .REG_SIZE(REG_SIZE),
        .GROUP_ORDER(GROUP_ORDER)
        )
        ecc_fixed_msb_i(
        .clk(clk),
        .reset_n(reset_n),
        .en_i(fixed_msb_en),
        .data_i(scalar_in_reg),
        .data_o(scalar_out_reg)
    );

    ecc_arith_unit #(
        .REG_SIZE(REG_SIZE),
        .RADIX(RADIX),
        .p_prime(PRIME),
        .p_mu(PRIME_mu),
        .q_grouporder(GROUP_ORDER),
        .q_mu(GROUP_ORDER_mu),
        .ADD_NUM_ADDS(ADD_NUM_ADDS),
        .ADD_BASE_SZ(ADD_BASE_SZ)
        )
        ecc_arith_unit_i (
        .clk(clk),
        .reset_n(reset_n),
        .ecc_cmd_i(PM_cmd_reg),
        .addr_i(prog_line[7 : 0]),
        .wr_op_sel_i(prog_line[16]),
        .wr_en_i(prog_line[17]),
        .rd_reg_i(prog_line[18]),
        .data_i(write_reg),
        .data_o(read_reg),
        .busy_o(pm_busy_o)
        );


    hmac_drbg #(
        .SEED_LENGTH(REG_SIZE)
        )    
        hmac_drbg_i (
        .clk(clk),
        .reset_n(reset_n),
        .KEYGEN_SIGN(hmac_mode),
        .init(hmac_init),
        .ready(hmac_ready),
        .valid(hmac_valid),
        .seed(seed_reg),
        .privKey(privkey_reg),
        .h1(msg_reg),
        .nonce(hmac_nonce)
        );


    //----------------------------------------------------------------
    // ecc_reg_update
    // Update functionality for all interface registers in the core.
    //----------------------------------------------------------------

    // read the registers written by sw
    assign cmd_reg = hwif_in.ecc_CTRL.CTRL.value[1 : 0];

    always_comb 
    begin : ecc_reg_reading
        for(int i0=0; i0<12; i0++) begin
            seed_reg[i0*32 +: 32]    = hwif_in.ecc_SEED[i0].SEED.value;
            msg_reg[i0*32 +: 32]     = hwif_in.ecc_MSG[i0].MSG.value;
            privkey_reg[i0*32 +: 32] = hwif_in.ecc_PRIVKEY[i0].PRIVKEY.value;
            pubkeyx_reg[i0*32 +: 32] = hwif_in.ecc_PUBKEY_X[i0].PUBKEY_X.value;
            pubkeyy_reg[i0*32 +: 32] = hwif_in.ecc_PUBKEY_Y[i0].PUBKEY_Y.value;
            r_reg[i0*32 +: 32]       = hwif_in.ecc_R[i0].R.value;
            s_reg[i0*32 +: 32]       = hwif_in.ecc_S[i0].S.value;
        end
    end // ecc_reg_reading

    // write the registers by hw
    always_comb hwif_out.ecc_NAME[0].NAME.next = ECC_CORE_NAME[31 : 0];
    always_comb hwif_out.ecc_NAME[1].NAME.next = ECC_CORE_NAME[63 : 32];
    always_comb hwif_out.ecc_VERSION[0].VERSION.next = ECC_CORE_VERSION[31 : 0];
    always_comb hwif_out.ecc_VERSION[1].VERSION.next = ECC_CORE_VERSION[63 : 32];

    always_comb hwif_out.ecc_STATUS.STATUS.next = {30'h0, dsa_valid_reg, dsa_ready_reg};

    always_comb 
    begin : ecc_reg_writing
        for(int i0=0; i0<12; i0++) begin
            hwif_out.ecc_CTRL.CTRL.next = 0;
            hwif_out.ecc_SEED[i0].SEED.next = hw_seed_we? read_reg[i0*32 +: 32] : hwif_in.ecc_SEED[i0].SEED.value;
            hwif_out.ecc_PRIVKEY[i0].PRIVKEY.next = hw_privkey_we? read_reg[i0*32 +: 32] : hwif_in.ecc_PRIVKEY[i0].PRIVKEY.value;
            hwif_out.ecc_PUBKEY_X[i0].PUBKEY_X.next = hw_pubkeyx_we? read_reg[i0*32 +: 32] : hwif_in.ecc_PUBKEY_X[i0].PUBKEY_X.value;
            hwif_out.ecc_PUBKEY_Y[i0].PUBKEY_Y.next = hw_pubkeyy_we? read_reg[i0*32 +: 32] : hwif_in.ecc_PUBKEY_Y[i0].PUBKEY_Y.value;
            hwif_out.ecc_R[i0].R.next = hw_r_we? read_reg[i0*32 +: 32] : hwif_in.ecc_R[i0].R.value;
            hwif_out.ecc_S[i0].S.next = hw_s_we? read_reg[i0*32 +: 32] : hwif_in.ecc_S[i0].S.value;
            hwif_out.ecc_VERIFY_R[i0].VERIFY_R.next = hw_verify_r_we? read_reg[i0*32 +: 32] : hwif_in.ecc_VERIFY_R[i0].VERIFY_R.value;
        end
    end // ecc_reg_writing

    //----------------------------------------------------------------
    // register updates
    //
    // update the internal registers and their wr_en
    //----------------------------------------------------------------
    always_comb begin
        assign scalar_G_reg = (!scalar_G_sel)? hmac_nonce : (hw_scalar_G_we)? read_reg : scalar_G_reg;
        assign scalar_PK_reg = (hw_scalar_PK_we)? read_reg : scalar_PK_reg;
    end

    always_comb 
    begin : wr_en_signals
        hw_seed_we = 0;
        hw_privkey_we = 0;
        hw_pubkeyx_we = 0;
        hw_pubkeyy_we = 0;
        hw_r_we = 0;
        hw_s_we = 0;
        hw_scalar_G_we = 0;
        hw_scalar_PK_we = 0;
        hw_verify_r_we = 0;
        if (prog_line[23 : 16] == DSA_UOP_RD_CORE)begin
            case (prog_line[15 : 8])
                //SEED_ID         : hw_seed_we = 1;
                PRIVKEY_ID      : hw_privkey_we = 1;
                PUBKEYX_ID      : hw_pubkeyx_we = 1;
                PUBKEYY_ID      : hw_pubkeyy_we = 1;
                R_ID            : hw_r_we = 1;
                S_ID            : hw_s_we = 1;
                SCALAR_G_ID     : hw_scalar_G_we = 1;
                SCALAR_PK_ID    : hw_scalar_PK_we = 1;
                VERIFY_R_ID     : hw_verify_r_we = 1;
                default         : begin end
            endcase
        end
    end // wr_en_signals


    always_comb 
    begin : write_to_pm_core
        write_reg = 0;
        if (prog_line[23 : 16] == DSA_UOP_WR_CORE) begin
            case (prog_line[15 : 8])
                CONST_ZERO_ID         : assign write_reg = 0;
                CONST_ONE_ID          : assign write_reg = 1;
                CONST_E_a_MONT_ID     : assign write_reg = {1'b0, E_a_MONT};
                CONST_ONE_p_MONT_ID   : assign write_reg = {1'b0, ONE_p_MONT};
                CONST_R2_p_MONT_ID    : assign write_reg = {1'b0, R2_p_MONT};
                CONST_G_X_MONT_ID     : assign write_reg = {1'b0, G_X_MONT};
                CONST_G_Y_MONT_ID     : assign write_reg = {1'b0, G_Y_MONT};
                CONST_G_Z_MONT_ID     : assign write_reg = {1'b0, G_Z_MONT};
                CONST_R2_q_MONT_ID    : assign write_reg = {1'b0, R2_q_MONT};
                CONST_ONE_q_MONT_ID   : assign write_reg = {1'b0, ONE_q_MONT};
                MSG_ID                : assign write_reg = {1'b0, msg_reg};
                PRIVKEY_ID            : assign write_reg = {1'b0, privkey_reg};
                PUBKEYX_ID            : assign write_reg = {1'b0, pubkeyx_reg};
                PUBKEYY_ID            : assign write_reg = {1'b0, pubkeyy_reg};
                R_ID                  : assign write_reg = {1'b0, r_reg};
                S_ID                  : assign write_reg = {1'b0, s_reg};
                SCALAR_G_ID           : assign write_reg = {1'b0, scalar_G_reg};
                default               : assign write_reg = 0;
            endcase
        end
        else if (prog_line[23 : 16] == DSA_UOP_WR_SCALAR) begin
            assign write_reg = scalar_out_reg;
        end
    end // write_to_pm_core

    always_comb 
    begin : fixed_msb_ctrl
        if (prog_line[23 : 16] == DSA_UOP_FIXED_MSB) begin
            case (prog_line[15 : 8])
                SCALAR_PK_ID        : assign scalar_in_reg = scalar_PK_reg;
                default             : assign scalar_in_reg = scalar_G_reg;
            endcase
            assign fixed_msb_en = 1;
        end
        else
            assign fixed_msb_en = 0;
    end // fixed_msb_ctrl
    

    assign hmac_busy = ~hmac_ready;

    always_ff @(posedge clk) 
    begin : ECDSA_FSM
        if(!reset_n) begin
            prog_cntr <= 0;
            cycle_cnt <= 0;
            dsa_valid_reg <= 0;
            scalar_G_sel <= 0;
            hmac_mode <= 0;
            hmac_init <= 0;
        end
        else begin
            if (pm_busy_o | hmac_busy) begin //Stalled until PM is done
                prog_cntr <= prog_cntr;
                cycle_cnt <= 3;
                PM_cmd_reg <= 0;
                hmac_init <= 0;
            end
            else if (dsa_busy & (cycle_cnt != 3)) begin
                cycle_cnt <= cycle_cnt + 1;
            end
            else begin
                cycle_cnt <= 0;
                case (prog_cntr)
                    DSA_NOP : begin 
                        // Waiting for new valid command 
                        case (cmd_reg)
                            KEYGEN : begin  // keygen
                                prog_cntr <= DSA_KG_S;
                                dsa_valid_reg <= 0;
                                scalar_G_sel <= 0;
                                hmac_mode <= 0;
                            end   

                            SIGN : begin  // signing
                                prog_cntr <= DSA_SGN_S;
                                dsa_valid_reg <= 0;
                                scalar_G_sel <= 0;
                                hmac_mode <= 1;
                            end                                   

                            VERIFY : begin  // verifying
                                prog_cntr <= DSA_VER_S;
                                dsa_valid_reg <= 0;
                                scalar_G_sel <= 1;
                            end
                            default : begin
                                prog_cntr <= DSA_NOP;
                                scalar_G_sel <= 0;
                            end
                        endcase
                        PM_cmd_reg <= 0;
                        hmac_init <= 0;
                    end                

                    DSA_KG_E : begin // end of keygen
                        prog_cntr <= DSA_NOP;
                        dsa_valid_reg <= 1;
                    end

                    DSA_SGN_E : begin // end of signing
                        prog_cntr <= DSA_NOP;
                        dsa_valid_reg <= 1;
                    end

                    DSA_VER_E : begin // end of verifying
                        prog_cntr <= DSA_NOP;
                        dsa_valid_reg <= 1;
                    end

                    default : begin
                        prog_cntr <= prog_cntr + 1;
                        PM_cmd_reg <= prog_line[21 : 19];
                        hmac_init  <= prog_line[22];
                    end
                endcase
            end
        end
    end // ECDSA_FSM

    assign dsa_busy = (prog_cntr == DSA_NOP)? 0 : 1;

    always_comb 
    begin : ready_flag
        dsa_ready_reg = !(dsa_busy | pm_busy_o);
    end // ready_flag
    
endmodule