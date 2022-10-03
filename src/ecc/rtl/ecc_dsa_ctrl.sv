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
//======================================================================
//
// ecc_dsa_ctrl.sv
// --------
// Elliptic Curve Cryptography (ECC) digital signature algorithm (DSA) 
// controller to support deterministic ECDSA based on RFC 6979.
// The dsa architecture includes several countermeasuress to be protected
// against a subset of side-channel analysis (SCA) attacks. The embedded
// countermeasures are:
// - scalar blinding
// - point randomization
//
// The architecture includes:
// 1) ecc_dsa_sequencer: including the required sequence to perform 
//    keygen, signing, and verifying.
// 2) ecc_arith_unit: the arithmetic unit to perform point multiplication
//    and other required operations
// 3) hmac_drbg: the hmac384 drbg component to support RFC 6979
// 4) ecc_scalar_blinding: the SCA countermeasure to randomized scalar
//    to avoid information leakage.
//
//
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
    
    logic [REG_SIZE-1 : 0]          read_reg;
    logic [REG_SIZE+RND_SIZE-1 : 0] write_reg;
    logic [7 : 0]                   addr_reg;
    logic [1 : 0]                   cycle_cnt;

    logic                   dsa_busy;
    logic                   subcomponent_busy;
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
    logic [2  : 0]          pm_cmd_reg;
    logic [REG_SIZE-1 : 0]  msg_reg;
    logic [REG_SIZE-1 : 0]  privkey_reg;
    logic [REG_SIZE-1 : 0]  pubkeyx_reg;
    logic [REG_SIZE-1 : 0]  pubkeyy_reg;
    logic [REG_SIZE-1 : 0]  seed_reg;
    logic [REG_SIZE-1 : 0]  r_reg;
    logic [REG_SIZE-1 : 0]  s_reg;
    logic [REG_SIZE-1 : 0]  IV_reg;
    logic [REG_SIZE-1 : 0]  lambda_reg;
    logic [REG_SIZE-1 : 0]  masking_rnd_reg;

    logic [REG_SIZE-1 : 0]  scalar_G_reg;
    logic [REG_SIZE-1 : 0]  scalar_PK_reg;

    logic [REG_SIZE-1 : 0]          scalar_in_reg;
    logic [RND_SIZE-1 : 0]          scalar_rnd_reg;
    logic [REG_SIZE+RND_SIZE-1 : 0] scalar_out_reg;
    logic                           scalar_sca_en;
    logic                           scalar_sca_busy_o;

    logic                   hmac_mode;
    logic                   hmac_init;
    logic                   hmac_next;
    logic                   hmac_ready;
    logic                   hmac_valid;
    logic [REG_SIZE-1 : 0]  hmac_seed;
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

    /*ecc_fixed_msb #(
        .REG_SIZE(REG_SIZE),
        .GROUP_ORDER(GROUP_ORDER)
        )
        ecc_fixed_msb_i(
        .clk(clk),
        .reset_n(reset_n),
        .en_i(fixed_msb_en),
        .data_i(scalar_in_reg),
        .data_o(scalar_out_reg)
    );*/

    ecc_scalar_blinding #(
        .REG_SIZE(REG_SIZE),
        .RND_SIZE(RND_SIZE),
        .RADIX(RADIX),
        .GROUP_ORDER(GROUP_ORDER)
        )
        ecc_scalar_blinding_i(
        .clk(clk),
        .reset_n(reset_n),
        .en_i(scalar_sca_en),
        .data_i(scalar_in_reg),
        .rnd_i(scalar_rnd_reg),
        .data_o(scalar_out_reg),
        .busy_o(scalar_sca_busy_o)
    );

    ecc_arith_unit #(
        .REG_SIZE(REG_SIZE),
        .RND_SIZE(RND_SIZE),
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
        .ecc_cmd_i(pm_cmd_reg),
        .addr_i(prog_line[7 : 0]),
        .wr_op_sel_i(prog_line[16]),
        .wr_en_i(prog_line[17]),
        .rd_reg_i(prog_line[18]),
        .data_i(write_reg),
        .data_o(read_reg),
        .busy_o(pm_busy_o)
        );



    ecc_hmac_drbg_interface #(
        .REG_SIZE(REG_SIZE),
        .SEED_SIZE(REG_SIZE),
        .RND_SIZE(RND_SIZE),
        .GROUP_ORDER(GROUP_ORDER)
        )    
        ecc_hmac_drbg_interface_i (
        .clk(clk),
        .reset_n(reset_n),
        .keygen_sign(hmac_mode),
        .en(hmac_init),
        .ready(hmac_ready),
        .valid(hmac_valid),
        .seed(seed_reg),
        .privKey(privkey_reg),
        .IV(IV_reg),
        .hashed_msg(msg_reg),
        .lambda(lambda_reg),
        .scalar_rnd(scalar_rnd_reg),
        .masking_rnd(masking_rnd_reg),
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
            IV_reg[i0*32 +: 32]      = hwif_in.ecc_IV[i0].IV.value;
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
    always_ff @(posedge clk) 
    begin : SCALAR_REG
        if(!reset_n) begin
            scalar_G_reg <= 0;
            scalar_PK_reg <= 0;
        end
        else begin
            if (!scalar_G_sel)
                scalar_G_reg <= hmac_nonce;
            else if (hw_scalar_G_we)
                scalar_G_reg <= read_reg;
            
            if (hw_scalar_PK_we)
                scalar_PK_reg <= read_reg;
        end
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
                CONST_ZERO_ID         : write_reg = 0;
                CONST_ONE_ID          : write_reg = 1;
                CONST_E_a_MONT_ID     : write_reg = E_a_MONT;
                CONST_E_3b_MONT_ID    : write_reg = E_3b_MONT;
                CONST_ONE_p_MONT_ID   : write_reg = ONE_p_MONT;
                CONST_R2_p_MONT_ID    : write_reg = R2_p_MONT;
                CONST_G_X_MONT_ID     : write_reg = G_X_MONT;
                CONST_G_Y_MONT_ID     : write_reg = G_Y_MONT;
                CONST_R2_q_MONT_ID    : write_reg = R2_q_MONT;
                CONST_ONE_q_MONT_ID   : write_reg = ONE_q_MONT;
                MSG_ID                : write_reg = msg_reg;
                PRIVKEY_ID            : write_reg = privkey_reg;
                PUBKEYX_ID            : write_reg = pubkeyx_reg;
                PUBKEYY_ID            : write_reg = pubkeyy_reg;
                R_ID                  : write_reg = r_reg;
                S_ID                  : write_reg = s_reg;
                SCALAR_G_ID           : write_reg = scalar_G_reg;
                LAMBDA_ID             : write_reg = lambda_reg;
                MASKING_ID            : write_reg = masking_rnd_reg;
                default               : write_reg = 0;
            endcase
        end
        else if (prog_line[23 : 16] == DSA_UOP_WR_SCALAR) begin
            case (prog_line[15 : 8])
                SCALAR_PK_ID          : write_reg = (scalar_PK_reg << RND_SIZE);
                SCALAR_G_ID           : write_reg = (scalar_G_reg << RND_SIZE);
                default               : write_reg = scalar_out_reg; // SCA
            endcase
        end
    end // write_to_pm_core

    always_ff @(posedge clk) 
    begin : scalar_sca_ctrl
        if(!reset_n) begin
            scalar_in_reg <= 0;
        end
        else begin
            if (prog_line[23 : 16] == DSA_UOP_SCALAR_SCA) begin
                scalar_in_reg <= scalar_G_reg;
            end
        end
    end // scalar_sca_ctrl

    assign hmac_busy = ~hmac_ready;
    assign subcomponent_busy = pm_busy_o | hmac_busy | scalar_sca_busy_o;

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
            if (subcomponent_busy) begin //Stalled until sub-component is done
                prog_cntr       <= prog_cntr;
                cycle_cnt       <= 3;
                pm_cmd_reg      <= 0;
                scalar_sca_en   <= 0;
                hmac_init       <= 0;
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
                        pm_cmd_reg <= 0;
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
                        prog_cntr       <= prog_cntr + 1;
                        pm_cmd_reg      <= prog_line[21 : 19];
                        hmac_init       <= prog_line[22];
                        scalar_sca_en   <= prog_line[23];
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
