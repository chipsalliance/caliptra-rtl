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

module ecc_dsa_ctrl
    import ecc_params_pkg::*;
    import ecc_dsa_uop_pkg::*;
    import ecc_reg_pkg::*;
    (
    // Clock and reset.
    input wire           clk,
    input wire           reset_n,
    input wire           cptra_pwrgood,

    // Reg ports.
    input ecc_reg__out_t hwif_in,
    output ecc_reg__in_t hwif_out,

    // Interrupts (from ecc_reg)
    output logic error_intr,
    output logic notif_intr
    );

    //----------------------------------------------------------------
    // Internal constant and parameter definitions.
    //----------------------------------------------------------------

    localparam [RND_SIZE-1 : 0]  zero_pad               = '0;
    
    //----------------------------------------------------------------
    // Registers including update variables and write enable.
    //----------------------------------------------------------------
    logic [DSA_PROG_ADDR_W-1 : 0]           prog_cntr;
    logic [(DSA_INSTRUCTION_LENGTH)-1 : 0]  prog_line;   
    
    logic [REG_SIZE-1 : 0]                  read_reg;
    logic [(REG_SIZE+RND_SIZE)-1 : 0]       write_reg;
    logic [1 : 0]                           cycle_cnt;

    logic dsa_busy;
    logic subcomponent_busy;
    logic pm_busy_o;
    
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

    logic ecc_status_done_d;
    logic ecc_status_done_p;

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
    logic [REG_SIZE-1 : 0]  lambda;
    logic [REG_SIZE-1 : 0]  lambda_reg;
    logic [REG_SIZE-1 : 0]  masking_rnd;
    logic [REG_SIZE-1 : 0]  masking_rnd_reg;

    logic [REG_SIZE-1 : 0]  scalar_G_reg;
    logic [REG_SIZE-1 : 0]  scalar_PK_reg;

    logic [REG_SIZE-1 : 0]              scalar_in_reg;
    logic [REG_SIZE-1 : 0]              scalar_rnd_reg;
    logic [(REG_SIZE+RND_SIZE)-1 : 0]   scalar_out;
    logic [(REG_SIZE+RND_SIZE)-1 : 0]   scalar_out_reg;
    logic                               scalar_sca_en;
    logic                               scalar_sca_busy_o;

    logic                   hmac_mode;
    logic                   hmac_init;
    logic                   hmac_ready;
    logic [REG_SIZE-1 : 0]  hmac_nonce;
    logic                   hmac_busy;

    logic                   sca_point_rnd_en;
    logic                   sca_mask_sign_en;
    logic                   sca_scalar_rnd_en;

    logic                   openssl_test_en;  // without hmac-drbg

    //----------------------------------------------------------------
    // Module instantiantions.
    //----------------------------------------------------------------
    ecc_dsa_sequencer #(
        .ADDR_WIDTH(DSA_PROG_ADDR_W),
        .DATA_WIDTH(DSA_INSTRUCTION_LENGTH)
        )
        ecc_dsa_sequencer_i(
        .clka(clk),
        .reset_n(reset_n),
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

    ecc_arith_unit #(
        .REG_SIZE(REG_SIZE),
        .RND_SIZE(RND_SIZE),
        .RADIX(RADIX),
        .ADDR_WIDTH(DSA_OPR_ADDR_WIDTH),
        .p_prime(PRIME),
        .p_mu(PRIME_mu),
        .q_grouporder(GROUP_ORDER),
        .q_mu(GROUP_ORDER_mu)
        )
        ecc_arith_unit_i (
        .clk(clk),
        .reset_n(reset_n),
        .ecc_cmd_i(pm_cmd_reg),
        .sca_en_i(sca_scalar_rnd_en),
        .addr_i(prog_line[DSA_OPR_ADDR_WIDTH-1 : 0]),
        .wr_op_sel_i(prog_line[2*DSA_OPR_ADDR_WIDTH]),
        .wr_en_i(prog_line[(2*DSA_OPR_ADDR_WIDTH)+1]),
        .rd_reg_i(prog_line[(2*DSA_OPR_ADDR_WIDTH)+2]),
        .data_i(write_reg),
        .data_o(read_reg),
        .busy_o(pm_busy_o)
        );

    ecc_hmac_drbg_interface #(
        .REG_SIZE(REG_SIZE),
        .SEED_SIZE(REG_SIZE),
        .GROUP_ORDER(GROUP_ORDER)
        )    
        ecc_hmac_drbg_interface_i (
        .clk(clk),
        .reset_n(reset_n),
        .keygen_sign(hmac_mode),
        .en(hmac_init),
        .ready(hmac_ready),
        .seed(seed_reg),
        .privKey(privkey_reg),
        .IV(IV_reg),
        .hashed_msg(msg_reg),
        .lambda(lambda),
        .scalar_rnd(scalar_rnd_reg),
        .masking_rnd(masking_rnd),
        .nonce(hmac_nonce)
        );

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
        .rnd_i(scalar_rnd_reg[RND_SIZE-1 : 0]),
        .data_o(scalar_out),
        .busy_o(scalar_sca_busy_o)
    );

    //----------------------------------------------------------------
    // side-channel config update
    // Update functionality for SCA registers in the core.
    //----------------------------------------------------------------

    always_comb 
    begin : SCA_config
        if (sca_scalar_rnd_en)
            scalar_out_reg = scalar_out;
        else
            scalar_out_reg = (scalar_in_reg << RND_SIZE);

        if (sca_point_rnd_en)
            lambda_reg = lambda;
        else
            lambda_reg = ONE_CONST;

        if (sca_mask_sign_en)
            masking_rnd_reg = masking_rnd;
        else
            masking_rnd_reg = ZERO_CONST;
    end // SCA_config

    //----------------------------------------------------------------
    // ecc_reg_update
    // Update functionality for all interface registers in the core.
    //----------------------------------------------------------------

    // read the registers written by sw
    always_ff @(posedge clk or negedge reset_n) 
    begin : ecc_reg_reading
        if (!reset_n) begin
            cmd_reg  <= '0;
            sca_point_rnd_en  <= '0;
            sca_mask_sign_en  <= '0;
            sca_scalar_rnd_en <= '0;
            openssl_test_en <= '0;
            seed_reg    <= '0;
            msg_reg     <= '0;
            privkey_reg <= '0;
            pubkeyx_reg <= '0;
            pubkeyy_reg <= '0;
            r_reg       <= '0;
            s_reg       <= '0;
            IV_reg      <= '0;
        end
        else if (dsa_ready_reg) begin
            cmd_reg <= hwif_in.ECC_CTRL.CTRL.value;
            
            sca_point_rnd_en  <= hwif_in.ECC_SCACONFIG.POINT_RND_EN.value;
            sca_mask_sign_en  <= hwif_in.ECC_SCACONFIG.MASK_SIGN_EN.value;
            sca_scalar_rnd_en <= hwif_in.ECC_SCACONFIG.SCALAR_RND_EN.value;
            openssl_test_en   <= hwif_in.ECC_SCACONFIG.OPENSSL_EN.value; // this bit should be deleted after openssl keygen test.

            for(int i0=0; i0<12; i0++) begin
                seed_reg[i0*32 +: 32]    <= hwif_in.ECC_SEED[i0].SEED.value;
                msg_reg[i0*32 +: 32]     <= hwif_in.ECC_MSG[i0].MSG.value;
                privkey_reg[i0*32 +: 32] <= hwif_in.ECC_PRIVKEY[i0].PRIVKEY.value;
                pubkeyx_reg[i0*32 +: 32] <= hwif_in.ECC_PUBKEY_X[i0].PUBKEY_X.value;
                pubkeyy_reg[i0*32 +: 32] <= hwif_in.ECC_PUBKEY_Y[i0].PUBKEY_Y.value;
                r_reg[i0*32 +: 32]       <= hwif_in.ECC_SIGN_R[i0].SIGN_R.value;
                s_reg[i0*32 +: 32]       <= hwif_in.ECC_SIGN_S[i0].SIGN_S.value;
                IV_reg[i0*32 +: 32]      <= hwif_in.ECC_IV[i0].IV.value;
            end
        end
    end // ecc_reg_reading

    assign error_intr = hwif_in.intr_block_rf.error_global_intr_r.intr;
    assign notif_intr = hwif_in.intr_block_rf.notif_global_intr_r.intr;

    // write the registers by hw
    always_comb hwif_out.reset_b = reset_n;
    always_comb hwif_out.hard_reset_b = cptra_pwrgood;
    always_comb hwif_out.ECC_NAME[0].NAME.next = ECC_CORE_NAME[31 : 0];
    always_comb hwif_out.ECC_NAME[1].NAME.next = ECC_CORE_NAME[63 : 32];
    always_comb hwif_out.ECC_VERSION[0].VERSION.next = ECC_CORE_VERSION[31 : 0];
    always_comb hwif_out.ECC_VERSION[1].VERSION.next = ECC_CORE_VERSION[63 : 32];

    always_comb hwif_out.ECC_STATUS.READY.next = dsa_ready_reg;
    always_comb hwif_out.ECC_STATUS.VALID.next = dsa_valid_reg;

    always_comb hwif_out.ECC_CTRL.CTRL.next = '0;
    // TODO add other interrupt hwset signals (errors)
    always_comb hwif_out.intr_block_rf.error_internal_intr_r.error_internal_sts.hwset = 1'b0;
    always_comb hwif_out.intr_block_rf.notif_internal_intr_r.notif_cmd_done_sts.hwset = ecc_status_done_p;


    genvar i0;
    generate 
        for (i0=0; i0 < 12; i0++) begin : ecc_reg_writing
            always_comb 
            begin
                hwif_out.ECC_PRIVKEY[i0].PRIVKEY.next = hw_privkey_we? read_reg[i0*32 +: 32] : hwif_in.ECC_PRIVKEY[i0].PRIVKEY.value;
                hwif_out.ECC_PUBKEY_X[i0].PUBKEY_X.next = hw_pubkeyx_we? read_reg[i0*32 +: 32] : hwif_in.ECC_PUBKEY_X[i0].PUBKEY_X.value;
                hwif_out.ECC_PUBKEY_Y[i0].PUBKEY_Y.next = hw_pubkeyy_we? read_reg[i0*32 +: 32] : hwif_in.ECC_PUBKEY_Y[i0].PUBKEY_Y.value;
                hwif_out.ECC_SIGN_R[i0].SIGN_R.next = hw_r_we? read_reg[i0*32 +: 32] : hwif_in.ECC_SIGN_R[i0].SIGN_R.value;
                hwif_out.ECC_SIGN_S[i0].SIGN_S.next = hw_s_we? read_reg[i0*32 +: 32] : hwif_in.ECC_SIGN_S[i0].SIGN_S.value;
                hwif_out.ECC_VERIFY_R[i0].VERIFY_R.next = hw_verify_r_we? read_reg[i0*32 +: 32] : hwif_in.ECC_VERIFY_R[i0].VERIFY_R.value;
            end
        end
    endgenerate // ecc_reg_writing


    //----------------------------------------------------------------
    // register updates
    //
    // update the internal registers and their wr_en
    //----------------------------------------------------------------
    always_ff @(posedge clk or negedge reset_n) 
    begin : SCALAR_REG
        if(!reset_n) begin
            scalar_G_reg <= '0;
            scalar_PK_reg <= '0;
        end
        else begin
            if (!scalar_G_sel)
                if (openssl_test_en) // this feature should be deleted after openssl keygen test.
                    scalar_G_reg <= seed_reg;
                else
                    scalar_G_reg <= hmac_nonce;
            else if (hw_scalar_G_we)
                scalar_G_reg <= read_reg;
            
            if (hw_scalar_PK_we)
                scalar_PK_reg <= read_reg;
        end
    end

    always_comb 
    begin : wr_en_signals
        hw_privkey_we = 0;
        hw_pubkeyx_we = 0;
        hw_pubkeyy_we = 0;
        hw_r_we = 0;
        hw_s_we = 0;
        hw_scalar_G_we = 0;
        hw_scalar_PK_we = 0;
        hw_verify_r_we = 0;
        if (prog_line[2*DSA_OPR_ADDR_WIDTH +: DSA_UOP_ADDR_WIDTH] == DSA_UOP_RD_CORE)begin
            unique casez (prog_line[DSA_OPR_ADDR_WIDTH +: DSA_OPR_ADDR_WIDTH])
                PRIVKEY_ID      : hw_privkey_we = 1;
                PUBKEYX_ID      : hw_pubkeyx_we = 1;
                PUBKEYY_ID      : hw_pubkeyy_we = 1;
                R_ID            : hw_r_we = 1;
                S_ID            : hw_s_we = 1;
                SCALAR_G_ID     : hw_scalar_G_we = 1;
                SCALAR_PK_ID    : hw_scalar_PK_we = 1;
                VERIFY_R_ID     : hw_verify_r_we = 1;
                default         : 
                    begin 
                        hw_privkey_we = 0;
                        hw_pubkeyx_we = 0;
                        hw_pubkeyy_we = 0;
                        hw_r_we = 0;
                        hw_s_we = 0;
                        hw_scalar_G_we = 0;
                        hw_scalar_PK_we = 0;
                        hw_verify_r_we = 0;
                    end
            endcase
        end
    end // wr_en_signals

    

    always_comb 
    begin : write_to_pm_core
        write_reg = '0;
        if (prog_line[2*DSA_OPR_ADDR_WIDTH +: DSA_UOP_ADDR_WIDTH] == DSA_UOP_WR_CORE) begin
            unique casez (prog_line[DSA_OPR_ADDR_WIDTH +: DSA_OPR_ADDR_WIDTH])
                CONST_ZERO_ID         : write_reg = {zero_pad, ZERO_CONST};
                CONST_ONE_ID          : write_reg = {zero_pad, ONE_CONST};
                CONST_E_a_MONT_ID     : write_reg = {zero_pad, E_a_MONT};
                CONST_E_3b_MONT_ID    : write_reg = {zero_pad, E_3b_MONT};
                CONST_ONE_p_MONT_ID   : write_reg = {zero_pad, ONE_p_MONT};
                CONST_R2_p_MONT_ID    : write_reg = {zero_pad, R2_p_MONT};
                CONST_G_X_MONT_ID     : write_reg = {zero_pad, G_X_MONT};
                CONST_G_Y_MONT_ID     : write_reg = {zero_pad, G_Y_MONT};
                CONST_R2_q_MONT_ID    : write_reg = {zero_pad, R2_q_MONT};
                CONST_ONE_q_MONT_ID   : write_reg = {zero_pad, ONE_q_MONT};
                MSG_ID                : write_reg = {zero_pad, msg_reg};
                PRIVKEY_ID            : write_reg = {zero_pad, privkey_reg};
                PUBKEYX_ID            : write_reg = {zero_pad, pubkeyx_reg};
                PUBKEYY_ID            : write_reg = {zero_pad, pubkeyy_reg};
                R_ID                  : write_reg = {zero_pad, r_reg};
                S_ID                  : write_reg = {zero_pad, s_reg};
                SCALAR_G_ID           : write_reg = {zero_pad, scalar_G_reg};
                LAMBDA_ID             : write_reg = {zero_pad, lambda_reg};
                MASKING_ID            : write_reg = {zero_pad, masking_rnd_reg};
                default               : write_reg = '0;
            endcase
        end
        else if (prog_line[2*DSA_OPR_ADDR_WIDTH +: DSA_UOP_ADDR_WIDTH] == DSA_UOP_WR_SCALAR) begin
            unique casez (prog_line[DSA_OPR_ADDR_WIDTH +: DSA_OPR_ADDR_WIDTH])
                SCALAR_PK_ID          : write_reg = (scalar_PK_reg << RND_SIZE);
                SCALAR_G_ID           : write_reg = (scalar_G_reg << RND_SIZE);
                SCALAR_ID             : write_reg = scalar_out_reg; // SCA
                default               : write_reg = '0;
            endcase
        end
    end // write_to_pm_core

    always_ff @(posedge clk or negedge reset_n) 
    begin : scalar_sca_ctrl
        if(!reset_n) begin
            scalar_in_reg <= '0;
        end
        else begin
            if (prog_line[2*DSA_OPR_ADDR_WIDTH +: DSA_UOP_ADDR_WIDTH] == DSA_UOP_SCALAR_SCA) begin
                scalar_in_reg <= scalar_G_reg;
            end
        end
    end // scalar_sca_ctrl

    assign hmac_busy = ~hmac_ready;
    assign subcomponent_busy = pm_busy_o | hmac_busy | scalar_sca_busy_o;

    always_ff @(posedge clk or negedge reset_n) 
    begin : ECDSA_FSM
        if(!reset_n) begin
            prog_cntr       <= DSA_RESET;
            cycle_cnt       <= '0;
            pm_cmd_reg      <= '0;
            dsa_valid_reg   <= 0;
            scalar_G_sel    <= 0;
            hmac_mode       <= 0;
            hmac_init       <= 0;
            scalar_sca_en   <= 0;
        end
        else begin
            if (subcomponent_busy) begin //Stalled until sub-component is done
                prog_cntr       <= prog_cntr;
                cycle_cnt       <= 2'd3;
                pm_cmd_reg      <= '0;
                scalar_sca_en   <= 0;
                hmac_init       <= 0;
            end
            else if (dsa_busy & (cycle_cnt != 2'd3)) begin
                cycle_cnt <= cycle_cnt + 1;
            end
            else begin
                cycle_cnt <= '0;
                unique casez (prog_cntr)
                    DSA_NOP : begin 
                        // Waiting for new valid command 
                        unique casez (cmd_reg)
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
                        pm_cmd_reg  <= '0;
                        hmac_init   <= 0;
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
                    
                    DSA_RESET,
                    DSA_KG_S,
                    DSA_SGN_S,
                    DSA_VER_S : begin
                        prog_cntr       <= prog_cntr + 1;
                        pm_cmd_reg      <= prog_line[(2*DSA_OPR_ADDR_WIDTH)+3 +: 3];
                        hmac_init       <= prog_line[(2*DSA_OPR_ADDR_WIDTH)+6];
                        scalar_sca_en   <= prog_line[(2*DSA_OPR_ADDR_WIDTH)+7];
                    end

                    default : begin
                        prog_cntr       <= prog_cntr + 1;
                        pm_cmd_reg      <= prog_line[(2*DSA_OPR_ADDR_WIDTH)+3 +: 3];
                        hmac_init       <= prog_line[(2*DSA_OPR_ADDR_WIDTH)+6];
                        scalar_sca_en   <= prog_line[(2*DSA_OPR_ADDR_WIDTH)+7];
                    end
                endcase
            end
        end
    end // ECDSA_FSM

    always_ff @(posedge clk or negedge reset_n)
        if (!reset_n)
            ecc_status_done_d <= 1'b0;
        else
            ecc_status_done_d <= hwif_out.ECC_STATUS.VALID.next;
    always_comb ecc_status_done_p = hwif_out.ECC_STATUS.VALID.next && !ecc_status_done_d;

    assign dsa_busy = (prog_cntr == DSA_NOP)? 1'b0 : 1'b1;

    always_comb 
    begin : ready_flag
        dsa_ready_reg = !(dsa_busy | pm_busy_o);
    end // ready_flag
    
endmodule
