//======================================================================
//
// ecc_core_ctrl.sv
// --------
// 
//
//
// Author: Mojtaba Bisheh-Niasar
//======================================================================

//`include "ecc_defines.svh"

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

    logic dsa_valid_reg;
    logic dsa_ready_reg;

    logic [1  : 0]          cmd_reg;
    logic                   verify_reg;
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

    assign cmd_reg = hwif_in.ecc_CTRL.CTRL.value[1 : 0];
    always_comb begin
        for(int i0=0; i0<12; i0++) begin
            seed_reg[i0*32 +: 32]    = hwif_in.ecc_SEED[i0].SEED.value;
            msg_reg[i0*32 +: 32]     = hwif_in.ecc_MSG[i0].MSG.value;
            privkey_reg[i0*32 +: 32] = hwif_in.ecc_PRIVKEY[i0].PRIVKEY.value;
            pubkeyx_reg[i0*32 +: 32] = hwif_in.ecc_PUBKEY_X[i0].PUBKEY_X.value;
            pubkeyy_reg[i0*32 +: 32] = hwif_in.ecc_PUBKEY_Y[i0].PUBKEY_Y.value;
            r_reg[i0*32 +: 32]       = hwif_in.ecc_R[i0].R.value;
            s_reg[i0*32 +: 32]       = hwif_in.ecc_S[i0].S.value;
        end
    end

    always_comb hwif_out.ecc_NAME[0].NAME.next = CORE_NAME[31 : 0];
    always_comb hwif_out.ecc_NAME[1].NAME.next = CORE_NAME[63 : 32];
    always_comb hwif_out.ecc_VERSION[0].VERSION.next = CORE_VERSION[31 : 0];
    always_comb hwif_out.ecc_VERSION[1].VERSION.next = CORE_VERSION[63 : 32];
    
    always_comb hwif_out.ecc_STATUS.STATUS.next = {30'h0, dsa_valid_reg, dsa_ready_reg};
    always_comb hwif_out.ecc_VERIFY.VERIFY.next = {31'h0, verify_reg};

    always_comb begin
        for(int i0=0; i0<12; i0++) begin
            hwif_out.ecc_SEED[i0].SEED.next = hw_seed_we? read_reg[i0*32 +: 32] : hwif_in.ecc_SEED[i0].SEED.value;
            hwif_out.ecc_PRIVKEY[i0].PRIVKEY.next = hw_privkey_we? read_reg[i0*32 +: 32] : hwif_in.ecc_PRIVKEY[i0].PRIVKEY.value;
            hwif_out.ecc_PUBKEY_X[i0].PUBKEY_X.next = hw_pubkeyx_we? read_reg[i0*32 +: 32] : hwif_in.ecc_PUBKEY_X[i0].PUBKEY_X.value;
            hwif_out.ecc_PUBKEY_Y[i0].PUBKEY_Y.next = hw_pubkeyy_we? read_reg[i0*32 +: 32] : hwif_in.ecc_PUBKEY_Y[i0].PUBKEY_Y.value;
            hwif_out.ecc_R[i0].R.next = hw_r_we? read_reg[i0*32 +: 32] : hwif_in.ecc_R[i0].R.value;
            hwif_out.ecc_S[i0].S.next = hw_s_we? read_reg[i0*32 +: 32] : hwif_in.ecc_S[i0].S.value;
        end
    end

    always_comb begin
        hw_seed_we = 0;
        hw_privkey_we = 0;
        hw_pubkeyx_we = 0;
        hw_pubkeyy_we = 0;
        hw_r_we = 0;
        hw_s_we = 0;
        hw_scalar_G_we = 0;
        hw_scalar_PK_we = 0;
        if (prog_line[23 : 16] == DSA_UOP_RD_CORE)begin
            case (prog_line[15 : 8])
                SEED_ID         : hw_seed_we = 1;
                PRIVKEY_ID      : hw_privkey_we = 1;
                PUBKEYX_ID      : hw_pubkeyx_we = 1;
                PUBKEYY_ID      : hw_pubkeyy_we = 1;
                R_ID            : hw_r_we = 1;
                S_ID            : hw_s_we = 1;
                SCALAR_G_ID     : hw_scalar_G_we = 1;
                SCALAR_PK_ID    : hw_scalar_PK_we = 1;
                default         : begin end
            endcase
        end
    end

    always_comb begin
        write_reg = 0;
        if (prog_line[23 : 16] == DSA_UOP_WR_CORE) begin
            case (prog_line[15 : 8])
                CONST_ZERO_ID         : assign write_reg = 0;
                CONST_ONE_ID          : assign write_reg = 1;
                CONST_E_a_MONT_ID     : assign write_reg = {1'b0, E_a_MONT};
                CONST_ONE_p_MONT_ID   : assign write_reg = {1'b0, ONE_p_MONT};
                CONST_G_X_MONT_ID     : assign write_reg = {1'b0, G_X_MONT};
                CONST_G_Y_MONT_ID     : assign write_reg = {1'b0, G_Y_MONT};
                CONST_G_Z_MONT_ID     : assign write_reg = {1'b0, G_Z_MONT};
                CONST_R2_q_MONT_ID    : assign write_reg = {1'b0, R2_q_MONT};
                CONST_ONE_q_MONT_ID   : assign write_reg = {1'b0, ONE_q_MONT};
                //SEED_ID               : assign write_reg = {1'b0, seed_reg};
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
    end

    assign scalar_G_reg = seed_reg;

    always_comb begin
        if (prog_line[23 : 16] == DSA_UOP_FIXED_MSB) begin
            case (prog_line[15 : 8])
                SCALAR_PK_ID        : assign scalar_in_reg = scalar_PK_reg;
                default             : assign scalar_in_reg = scalar_G_reg;
            endcase
            assign fixed_msb_en = 1;
        end
        else
            assign fixed_msb_en = 0;
    end
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
        //.wr_input_sel_i(wr_input_sel),
        .wr_op_sel_i(prog_line[16]),
        //.wr_word_sel_i(),
        .wr_en_i(prog_line[17]),
        .rd_reg_i(prog_line[18]),
        //.rd_op_sel_i(rd_op_sel_i_tb),
        //.rd_word_sel_i(rd_word_sel_i_tb),
        .data_i(write_reg),
        .data_o(read_reg),
        .busy_o(pm_busy_o)
        );


    always_ff @(posedge clk) begin
        if(!reset_n) begin
            prog_cntr <= DSA_RE_START;
            cycle_cnt <= 0;
            dsa_valid_reg <= 0;
        end
        else begin
            if (pm_busy_o) begin //Stalled until command is done
                prog_cntr <= prog_cntr;
                cycle_cnt <= 3;
                PM_cmd_reg <= 0;
            end
            else if (cycle_cnt != 3) begin
                cycle_cnt <= cycle_cnt + 1;
            end
            else begin
                cycle_cnt <= 0;
                case (prog_cntr)
                    DSA_RE_START : begin
                        prog_cntr <= DSA_INIT_S;
                    end

                    DSA_INIT_E : begin
                        prog_cntr <= DSA_NOP;
                    end

                    DSA_NOP : begin 
                        // Waiting for new valid command 
                        case (cmd_reg)
                            KEYGEN : begin  // keygen
                                prog_cntr <= DSA_KG_INIT_S;
                                dsa_valid_reg <= 0;
                            end   

                            SIGN : begin  // signing
                                prog_cntr <= DSA_SGN_INIT_S;
                                dsa_valid_reg <= 0;
                            end                                   

                            VERIFY : begin  // verifying
                                prog_cntr <= DSA_VER0_INIT_S;
                                dsa_valid_reg <= 0;
                            end
                            default : begin
                                prog_cntr <= DSA_NOP;
                                PM_cmd_reg <= 0;
                            end
                        endcase
                    end                

                    DSA_KG_INIT_E : begin
                        prog_cntr <= DSA_KG_RES_S;
                        PM_cmd_reg <= 0;
                    end

                    DSA_KG_RES_E : begin
                        prog_cntr <= DSA_NOP;
                        dsa_valid_reg <= 1;
                    end

                    DSA_SGN_INIT_E : begin
                        prog_cntr <= DSA_SGN_RES_S;
                        PM_cmd_reg <= 0;
                    end

                    DSA_SGN_RES_E : begin
                        prog_cntr <= DSA_NOP;
                        dsa_valid_reg <= 1;
                    end

                    default : begin
                        prog_cntr <= prog_cntr + 1;
                        PM_cmd_reg <= prog_line[21 : 19];
                    end
                endcase
            end
        end
    end

    assign dsa_busy = (prog_cntr == DSA_NOP)? 0 : 1;

    always_ff @(posedge clk) begin
        dsa_ready_reg <= !(dsa_busy | pm_busy_o);
    end
    
endmodule