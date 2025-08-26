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
// against a subset of side-channel analysis (SCA) attacks. 
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
// The embedded countermeasures are:
// - point randomization: 
//      Randomized Projective Coordinates countermeasure based on section 5.3 
//      "Resistance against Differential Power Analysis for Elliptic Curve 
//      Cryptosystems" in CHES 1999 by Coron, J.  
//      This countermesure uses a random value "lambda" in point multiplication
//      (Q = k * P) in keygen/signing to randomiza base point P = (X, Y, 1)
//      as follows:
//      P = (X * Lambda, Y * lambda, Lambda)
// - scalar blinding: 
//      Scalar blinding countermeasure based on section 5.1 
//      "Resistance against Differential Power Analysis for Elliptic Curve 
//      Cryptosystems" in CHES 1999 by Coron, J.  
//      This countermeasure uses a random value "r" in the point multiplication
//      (Q = k * P) in keygen/signing to randomiza scalar k as follows:
//      k = k + r*group_order
// - masking signature: 
//      Masking sign countermeasure uses a random value "d" in the signing 
//      operation to generate signature proof s = (privkey * r + h)*k_inv 
//      as follows:
//      s = [((privkey - d) * r + (h - d)) * k_inv] + [(d * r + d) * k_inv
//======================================================================

`include "kv_macros.svh"

module ecc_dsa_ctrl
    import ecc_params_pkg::*;
    import ecc_dsa_uop_pkg::*;
    import ecc_reg_pkg::*;
    import kv_defines_pkg::*;
    (
    // Clock and reset.
    input wire           clk,
    input wire           reset_n,
    input wire           cptra_pwrgood,

    // Reg ports.
    input ecc_reg__out_t hwif_out,
    output ecc_reg__in_t hwif_in,

    // KV interface
    output kv_read_t [1:0] kv_read,
    output kv_write_t kv_write,
    input kv_rd_resp_t [1:0] kv_rd_resp,
    input kv_wr_resp_t kv_wr_resp,

    //PCR Signing
    input pcr_signing_t pcr_signing_data,

    input  logic ocp_lock_in_progress,
    output logic busy_o,

    // Interrupts (from ecc_reg)
    output logic error_intr,
    output logic notif_intr,
    input  logic debugUnlock_or_scan_mode_switch
    );

    //----------------------------------------------------------------
    // Internal constant and parameter definitions.
    //----------------------------------------------------------------

    localparam [RND_SIZE-1 : 0]  zero_pad               = '0;
    localparam REG_NUM_DWORDS = REG_SIZE / DATA_WIDTH;
    //----------------------------------------------------------------
    // Registers including update variables and write enable.
    //----------------------------------------------------------------
    logic [DSA_PROG_ADDR_W-1 : 0]                prog_cntr;
    
    logic [REG_NUM_DWORDS-1 : 0][DATA_WIDTH-1:0] read_reg;
    logic [(REG_SIZE+RND_SIZE)-1 : 0]            write_reg;
    logic [1 : 0]                                cycle_cnt;

    logic zeroize_reg;

    logic dsa_busy;
    logic subcomponent_busy;
    logic pm_busy_o;
    
    logic hw_privkey_we;
    logic privkey_we_reg;
    logic sharedkey_we_reg;
    logic secretkey_we;
    logic hw_pubkeyx_we;
    logic hw_pubkeyy_we;
    logic hw_r_we;
    logic hw_s_we;
    logic hw_scalar_G_we;
    logic hw_scalar_PK_we;
    logic hw_verify_r_we;
    logic hw_pk_chk_we;
    logic hw_sharedkey_we;
    logic scalar_G_sel;

    logic ecc_valid_reg;
    logic ecc_ready_reg;

    logic ecc_status_done_d;
    logic ecc_status_done_p;

    logic [2  : 0]          cmd_reg;
    logic [3  : 0]          pm_cmd_reg;
    logic [REG_NUM_DWORDS-1 : 0][DATA_WIDTH-1:0]  msg_reg;
    logic [REG_NUM_DWORDS-1 : 0][DATA_WIDTH-1:0]  msg_reduced_reg;
    logic [REG_NUM_DWORDS-1 : 0][DATA_WIDTH-1:0]  privkey_reg;
    logic [REG_NUM_DWORDS-1 : 0][DATA_WIDTH-1:0]  kv_reg;
    logic [REG_NUM_DWORDS-1 : 0][DATA_WIDTH-1:0]  pubkeyx_reg;
    logic [REG_NUM_DWORDS-1 : 0][DATA_WIDTH-1:0]  pubkeyy_reg;
    logic [REG_NUM_DWORDS-1 : 0][DATA_WIDTH-1:0]  seed_reg;
    logic [REG_NUM_DWORDS-1 : 0][DATA_WIDTH-1:0]  nonce_reg;
    logic [REG_NUM_DWORDS-1 : 0][DATA_WIDTH-1:0]  r_reg;
    logic [REG_NUM_DWORDS-1 : 0][DATA_WIDTH-1:0]  s_reg;
    logic [REG_NUM_DWORDS-1 : 0][DATA_WIDTH-1:0]  IV_reg;
    logic [REG_SIZE-1 : 0]  lambda_reg;
    logic [REG_SIZE-1 : 0]  masking_rnd_reg;
    logic [REG_SIZE-1 : 0]  pk_chk_reg;

    logic [REG_SIZE-1 : 0]  scalar_G_reg;
    logic [REG_SIZE-1 : 0]  scalar_PK_reg;

    logic [REG_SIZE-1 : 0]              scalar_in_reg;
    logic [REG_SIZE-1 : 0]              scalar_rnd_reg;
    logic [(REG_SIZE+RND_SIZE)-1 : 0]   scalar_out_reg;
    logic                               scalar_sca_en;
    logic                               scalar_sca_busy_o;

    logic [1 : 0]           hmac_mode;
    logic                   hmac_init;
    logic                   hmac_ready;
    logic [REG_SIZE-1 : 0]  hmac_drbg_result;
    logic                   hmac_busy;

    //interface with kv client
    logic kv_privkey_write_en;
    logic [REG_OFFSET_W-1:0] kv_privkey_write_offset;
    logic [31:0] kv_privkey_write_data;
    logic kv_seed_write_en;
    logic [REG_OFFSET_W-1:0] kv_seed_write_offset;
    logic [31:0] kv_seed_write_data;
  
    logic dest_keyvault;
    kv_error_code_e kv_privkey_error, kv_seed_error, kv_nonce_error, kv_write_error;
    logic kv_privkey_ready, kv_privkey_done;
    logic kv_seed_ready, kv_seed_done ;
    logic kv_write_ready, kv_write_done;
    //KV Seed Data Present
    logic kv_seed_data_present;
    logic kv_seed_data_present_set, kv_seed_data_present_reset;
    //KV Key Data Present
    logic kv_key_data_present;
    logic kv_key_data_present_set, kv_key_data_present_reset;
    
    kv_read_ctrl_reg_t kv_privkey_read_ctrl_reg;
    kv_read_ctrl_reg_t kv_seed_read_ctrl_reg;
    kv_write_ctrl_reg_t kv_write_ctrl_reg;
    kv_read_filter_metrics_t kv_privkey_read_metrics;
    kv_read_filter_metrics_t kv_seed_read_metrics;
    kv_write_filter_metrics_t kv_write_metrics;

    logic pcr_sign_mode;
    
    instr_struct_t prog_instr;
    
    // ERROR
    logic keygen_process;
    logic signing_process;
    logic verifying_process;
    logic sharedkey_process;

    logic privkey_input_outofrange;
    logic r_output_outofrange;
    logic s_output_outofrange;
    logic r_input_outofrange;
    logic s_input_outofrange;
    logic pubkeyx_input_outofrange;
    logic pubkeyy_input_outofrange;
    logic pubkey_input_invalid;
    logic pcr_sign_input_invalid;
    logic privkey_output_outofrange, pubkeyx_output_outofrange, pubkeyy_output_outofrange;
    logic sharedkey_outofrange;

    logic error_flag;
    logic error_flag_reg;
    logic error_flag_edge;

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
        .zeroize(zeroize_reg),
        .ena(1'b1),
        .addra(prog_cntr),
        .douta(prog_instr)
        );

    ecc_arith_unit #(
        .REG_SIZE(REG_SIZE),
        .RND_SIZE(RND_SIZE),
        .RADIX(MULT_RADIX),
        .ADDR_WIDTH(DSA_OPR_ADDR_WIDTH),
        .p_prime(PRIME),
        .p_mu(PRIME_mu),
        .q_grouporder(GROUP_ORDER),
        .q_mu(GROUP_ORDER_mu)
        )
        ecc_arith_unit_i (
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize_reg),
        .ecc_cmd_i(pm_cmd_reg),
        .addr_i(prog_instr.mem_addr),
        .wr_op_sel_i(prog_instr.opcode.op_sel),

        .wr_en_i(prog_instr.opcode.wr_en),
        .rd_reg_i(prog_instr.opcode.rd_en),
        .data_i(write_reg),
        .data_o(read_reg),
        .busy_o(pm_busy_o)
        );

    ecc_hmac_drbg_interface #(
        .REG_SIZE(REG_SIZE),
        .GROUP_ORDER(GROUP_ORDER)
        )    
        ecc_hmac_drbg_interface_i (
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize_reg),
        .hmac_mode(hmac_mode),
        .en(hmac_init),
        .ready(hmac_ready),
        .keygen_seed(seed_reg),
        .keygen_nonce(nonce_reg),
        .privKey(privkey_reg),
        .hashed_msg(msg_reduced_reg),
        .IV(IV_reg),
        .lambda(lambda_reg),
        .scalar_rnd(scalar_rnd_reg),
        .masking_rnd(masking_rnd_reg),
        .drbg(hmac_drbg_result)
        );

    ecc_scalar_blinding #(
        .REG_SIZE(REG_SIZE),
        .RND_SIZE(RND_SIZE),
        .RADIX(SCALAR_BLIND_RADIX),
        .GROUP_ORDER(GROUP_ORDER)
        )
        ecc_scalar_blinding_i(
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize_reg),
        .en_i(scalar_sca_en),
        .data_i(scalar_in_reg),
        .rnd_i(scalar_rnd_reg[RND_SIZE-1 : 0]),
        .data_o(scalar_out_reg),
        .busy_o(scalar_sca_busy_o)
        );


    //----------------------------------------------------------------
    // ecc_reg_update
    // Update functionality for all interface registers in the core.
    //----------------------------------------------------------------

    // read the registers written by sw
    always_comb begin
        //Mask the command if KV clients are not idle
        cmd_reg = {hwif_out.ECC_CTRL.DH_SHAREDKEY.value, hwif_out.ECC_CTRL.CTRL.value} & {3{kv_seed_ready}} & {3{kv_privkey_ready}};
        zeroize_reg = hwif_out.ECC_CTRL.ZEROIZE.value || debugUnlock_or_scan_mode_switch;
    end

    //there is a clk cycle memory read delay between hw_privkey_we and read_reg
    always_ff @(posedge clk or negedge reset_n) 
    begin : ecc_kv_reg
        if (!reset_n) begin
            privkey_we_reg       <= '0;
            sharedkey_we_reg     <= '0;
            kv_reg               <= '0;
            kv_seed_data_present <= '0;
            kv_key_data_present  <= '0;
        end
        else if (zeroize_reg) begin
            privkey_we_reg       <= '0;
            sharedkey_we_reg     <= '0;
            kv_reg               <= '0;
            kv_seed_data_present <= '0;
            kv_key_data_present  <= '0;
        end
        //Store private key here before pushing to keyvault
        else begin
            privkey_we_reg <= hw_privkey_we;
            sharedkey_we_reg <= hw_sharedkey_we;
            if (secretkey_we & (dest_keyvault | kv_seed_data_present))            
                kv_reg <= read_reg;

            kv_seed_data_present <= kv_seed_data_present_set ? '1 :
                                    kv_seed_data_present_reset ? '0 : kv_seed_data_present;
            kv_key_data_present  <= kv_key_data_present_set ? '1 :
                                    kv_key_data_present_reset ? '0 : kv_key_data_present;
        end
    end

    always_comb secretkey_we = (privkey_we_reg | sharedkey_we_reg);

    assign error_intr = hwif_out.intr_block_rf.error_global_intr_r.intr;
    assign notif_intr = hwif_out.intr_block_rf.notif_global_intr_r.intr;

    // write the registers by hw
    always_comb hwif_in.reset_b = reset_n;
    always_comb hwif_in.hard_reset_b = cptra_pwrgood;
    always_comb hwif_in.ecc_ready = ecc_ready_reg;
    always_comb hwif_in.ECC_NAME[0].NAME.next = ECC_CORE_NAME[31 : 0];
    always_comb hwif_in.ECC_NAME[1].NAME.next = ECC_CORE_NAME[63 : 32];
    always_comb hwif_in.ECC_VERSION[0].VERSION.next = ECC_CORE_VERSION[31 : 0];
    always_comb hwif_in.ECC_VERSION[1].VERSION.next = ECC_CORE_VERSION[63 : 32];

    always_comb hwif_in.ECC_STATUS.READY.next = ecc_ready_reg;
    always_comb hwif_in.ECC_STATUS.VALID.next = ecc_valid_reg;

    
    always_comb begin // ecc_reg_writing
        for (int dword=0; dword < 12; dword++)begin
            //Key Vault has priority if enabled to drive these registers
            //don't store the private key generated in sw accessible register if it's going to keyvault
            privkey_reg[dword] = hwif_out.ECC_PRIVKEY_IN[11-dword].PRIVKEY_IN.value;
            hwif_in.ECC_PRIVKEY_IN[dword].PRIVKEY_IN.we = (pcr_sign_mode | (kv_privkey_write_en & (kv_privkey_write_offset == dword))) & !zeroize_reg;
            hwif_in.ECC_PRIVKEY_IN[dword].PRIVKEY_IN.next = pcr_sign_mode       ? pcr_signing_data.pcr_ecc_signing_privkey[dword] : 
                                                            kv_privkey_write_en ? kv_privkey_write_data : 
                                                                                  read_reg[11-dword];
            hwif_in.ECC_PRIVKEY_IN[dword].PRIVKEY_IN.hwclr = zeroize_reg | kv_key_data_present_reset | (kv_privkey_error == KV_READ_FAIL);
            hwif_in.ECC_PRIVKEY_IN[dword].PRIVKEY_IN.swwe = ecc_ready_reg & ~kv_key_data_present;
        end 

        for (int dword=0; dword < 12; dword++)begin
            //If keyvault is not enabled, grab the sw value as usual
            hwif_in.ECC_PRIVKEY_OUT[dword].PRIVKEY_OUT.we = (privkey_we_reg & ~(dest_keyvault | kv_seed_data_present)) & !zeroize_reg;
            hwif_in.ECC_PRIVKEY_OUT[dword].PRIVKEY_OUT.next = read_reg[11-dword];
            hwif_in.ECC_PRIVKEY_OUT[dword].PRIVKEY_OUT.hwclr = zeroize_reg;
        end

        for (int dword=0; dword < 12; dword++)begin
            seed_reg[dword] = hwif_out.ECC_SEED[11-dword].SEED.value;
            hwif_in.ECC_SEED[dword].SEED.we = (kv_seed_write_en & (kv_seed_write_offset == dword)) & !zeroize_reg;
            hwif_in.ECC_SEED[dword].SEED.next = kv_seed_write_data;
            hwif_in.ECC_SEED[dword].SEED.hwclr = zeroize_reg | kv_seed_data_present_reset | (kv_seed_error == KV_READ_FAIL);
            hwif_in.ECC_SEED[dword].SEED.swwe  = ecc_ready_reg & ~kv_seed_data_present;
        end

        for (int dword=0; dword < 12; dword++)begin
            nonce_reg[dword] = hwif_out.ECC_NONCE[11-dword].NONCE.value;
            hwif_in.ECC_NONCE[dword].NONCE.hwclr = zeroize_reg;
        end

        for (int dword=0; dword < 12; dword++)begin
            msg_reg[dword] = hwif_out.ECC_MSG[11-dword].MSG.value;
            hwif_in.ECC_MSG[dword].MSG.we = pcr_sign_mode & !zeroize_reg;
            hwif_in.ECC_MSG[dword].MSG.next = pcr_signing_data.pcr_hash[dword];
            hwif_in.ECC_MSG[dword].MSG.hwclr = zeroize_reg;
        end

        for (int dword=0; dword < 12; dword++)begin
            pubkeyx_reg[dword] = hwif_out.ECC_PUBKEY_X[11-dword].PUBKEY_X.value;
            hwif_in.ECC_PUBKEY_X[dword].PUBKEY_X.we = hw_pubkeyx_we & !zeroize_reg;
            hwif_in.ECC_PUBKEY_X[dword].PUBKEY_X.next = read_reg[11-dword];  
            hwif_in.ECC_PUBKEY_X[dword].PUBKEY_X.hwclr = zeroize_reg;
        end

        for (int dword=0; dword < 12; dword++)begin
            pubkeyy_reg[dword] = hwif_out.ECC_PUBKEY_Y[11-dword].PUBKEY_Y.value;
            hwif_in.ECC_PUBKEY_Y[dword].PUBKEY_Y.we = hw_pubkeyy_we & !zeroize_reg;
            hwif_in.ECC_PUBKEY_Y[dword].PUBKEY_Y.next = read_reg[11-dword];
            hwif_in.ECC_PUBKEY_Y[dword].PUBKEY_Y.hwclr = zeroize_reg;
        end

        for (int dword=0; dword < 12; dword++)begin
            r_reg[dword] = hwif_out.ECC_SIGN_R[11-dword].SIGN_R.value;
            hwif_in.ECC_SIGN_R[dword].SIGN_R.we = hw_r_we & !zeroize_reg;
            hwif_in.ECC_SIGN_R[dword].SIGN_R.next = read_reg[11-dword];
            hwif_in.ECC_SIGN_R[dword].SIGN_R.hwclr = zeroize_reg;
        end

        for (int dword=0; dword < 12; dword++)begin
            s_reg[dword] = hwif_out.ECC_SIGN_S[11-dword].SIGN_S.value;
            hwif_in.ECC_SIGN_S[dword].SIGN_S.we = hw_s_we & !zeroize_reg;
            hwif_in.ECC_SIGN_S[dword].SIGN_S.next = read_reg[11-dword];
            hwif_in.ECC_SIGN_S[dword].SIGN_S.hwclr = zeroize_reg;
        end

        for (int dword=0; dword < 12; dword++)begin 
            hwif_in.ECC_VERIFY_R[dword].VERIFY_R.we = hw_verify_r_we & !zeroize_reg;       
            hwif_in.ECC_VERIFY_R[dword].VERIFY_R.next = read_reg[11-dword];
            hwif_in.ECC_VERIFY_R[dword].VERIFY_R.hwclr = zeroize_reg;
        end

        for (int dword=0; dword < 12; dword++)begin
            IV_reg[dword] = hwif_out.ECC_IV[11-dword].IV.value;
            hwif_in.ECC_IV[dword].IV.hwclr = zeroize_reg;
        end

        for (int dword=0; dword < 12; dword++)begin
            hwif_in.ECC_DH_SHARED_KEY[dword].DH_SHARED_KEY.we = (sharedkey_we_reg & ~(dest_keyvault | kv_key_data_present)) & !zeroize_reg;
            hwif_in.ECC_DH_SHARED_KEY[dword].DH_SHARED_KEY.next = read_reg[11-dword];  
            hwif_in.ECC_DH_SHARED_KEY[dword].DH_SHARED_KEY.hwclr = zeroize_reg;
        end
    end

    //transformed msg into modulo q 
    always_ff @(posedge clk or negedge reset_n) 
    begin : reduced_msg
        if (!reset_n)
            msg_reduced_reg <= '0;
        else if (zeroize_reg)
            msg_reduced_reg <= '0;
        else begin
            if (msg_reg >= GROUP_ORDER)
                msg_reduced_reg <= msg_reg - GROUP_ORDER;
            else
                msg_reduced_reg <= msg_reg;
        end
    end
    

    always_comb hwif_in.ECC_CTRL.CTRL.hwclr = |cmd_reg;
    always_comb hwif_in.ECC_CTRL.DH_SHAREDKEY.hwclr = |cmd_reg;
    always_comb hwif_in.ECC_CTRL.PCR_SIGN.hwclr = hwif_out.ECC_CTRL.PCR_SIGN.value;
    
    // TODO add other interrupt hwset signals (errors)
    always_comb hwif_in.intr_block_rf.error_internal_intr_r.error_internal_sts.hwset = error_flag_edge;
    always_comb hwif_in.intr_block_rf.notif_internal_intr_r.notif_cmd_done_sts.hwset = ecc_status_done_p;


    always_comb begin: ecc_kv_ctrl_reg
        //ready when fsm is not busy
        hwif_in.ecc_kv_rd_pkey_status.ERROR.next = kv_privkey_error;
        hwif_in.ecc_kv_rd_seed_status.ERROR.next = kv_seed_error;
        hwif_in.ecc_kv_wr_pkey_status.ERROR.next = kv_write_error;
        //ready when fsm is not busy
        hwif_in.ecc_kv_rd_pkey_status.READY.next = kv_privkey_ready;
        hwif_in.ecc_kv_rd_seed_status.READY.next = kv_seed_ready;
        hwif_in.ecc_kv_wr_pkey_status.READY.next = kv_write_ready;
        //set valid when fsm is done
        hwif_in.ecc_kv_rd_pkey_status.VALID.hwset = kv_privkey_done;
        hwif_in.ecc_kv_rd_seed_status.VALID.hwset = kv_seed_done;
        hwif_in.ecc_kv_wr_pkey_status.VALID.hwset = kv_write_done;
        //clear valid when new request is made
        hwif_in.ecc_kv_rd_pkey_status.VALID.hwclr = kv_privkey_read_ctrl_reg.read_en;
        hwif_in.ecc_kv_rd_seed_status.VALID.hwclr = kv_seed_read_ctrl_reg.read_en;
        hwif_in.ecc_kv_wr_pkey_status.VALID.hwclr = kv_write_ctrl_reg.write_en;
        //clear enable when busy
        hwif_in.ecc_kv_rd_pkey_ctrl.read_en.hwclr = ~kv_privkey_ready;
        hwif_in.ecc_kv_rd_seed_ctrl.read_en.hwclr = ~kv_seed_ready;
        hwif_in.ecc_kv_wr_pkey_ctrl.write_en.hwclr = ~kv_write_ready;
    end

    // Software write-enables to prevent KV reg manipulation mid-operation
    always_comb hwif_in.ecc_kv_rd_pkey_ctrl.read_en.swwe         = !kv_key_data_present && ecc_ready_reg;
    always_comb hwif_in.ecc_kv_rd_pkey_ctrl.read_entry.swwe      = !kv_key_data_present && ecc_ready_reg;
    always_comb hwif_in.ecc_kv_rd_pkey_ctrl.pcr_hash_extend.swwe = !kv_key_data_present && ecc_ready_reg;
    always_comb hwif_in.ecc_kv_rd_pkey_ctrl.rsvd.swwe            = !kv_key_data_present && ecc_ready_reg;

    always_comb hwif_in.ecc_kv_rd_seed_ctrl.read_en.swwe         = !kv_seed_data_present && ecc_ready_reg;
    always_comb hwif_in.ecc_kv_rd_seed_ctrl.read_entry.swwe      = !kv_seed_data_present && ecc_ready_reg;
    always_comb hwif_in.ecc_kv_rd_seed_ctrl.pcr_hash_extend.swwe = !kv_seed_data_present && ecc_ready_reg;
    always_comb hwif_in.ecc_kv_rd_seed_ctrl.rsvd.swwe            = !kv_seed_data_present && ecc_ready_reg;

    // KV write control must be written before ECC core operation begins, even though
    // output isn't written to KV until the end of the operation.
    // Prevent partial-key attacks by blocking register modifications during core execution.
    always_comb hwif_in.ecc_kv_wr_pkey_ctrl.write_en.swwe              = ecc_ready_reg;
    always_comb hwif_in.ecc_kv_wr_pkey_ctrl.write_entry.swwe           = ecc_ready_reg;
    always_comb hwif_in.ecc_kv_wr_pkey_ctrl.hmac_key_dest_valid.swwe   = ecc_ready_reg;
    always_comb hwif_in.ecc_kv_wr_pkey_ctrl.hmac_block_dest_valid.swwe = ecc_ready_reg;
    always_comb hwif_in.ecc_kv_wr_pkey_ctrl.mldsa_seed_dest_valid.swwe = ecc_ready_reg;
    always_comb hwif_in.ecc_kv_wr_pkey_ctrl.ecc_pkey_dest_valid.swwe   = ecc_ready_reg;
    always_comb hwif_in.ecc_kv_wr_pkey_ctrl.ecc_seed_dest_valid.swwe   = ecc_ready_reg;
    always_comb hwif_in.ecc_kv_wr_pkey_ctrl.aes_key_dest_valid.swwe    = ecc_ready_reg;
    always_comb hwif_in.ecc_kv_wr_pkey_ctrl.mlkem_seed_dest_valid.swwe = ecc_ready_reg;
    always_comb hwif_in.ecc_kv_wr_pkey_ctrl.mlkem_msg_dest_valid.swwe  = ecc_ready_reg;
    always_comb hwif_in.ecc_kv_wr_pkey_ctrl.dma_data_dest_valid.swwe   = ecc_ready_reg;
    always_comb hwif_in.ecc_kv_wr_pkey_ctrl.rsvd.swwe                  = ecc_ready_reg;

    //keyvault control reg macros for assigning to struct
    `CALIPTRA_KV_READ_CTRL_REG2STRUCT(kv_privkey_read_ctrl_reg, ecc_kv_rd_pkey_ctrl)
    `CALIPTRA_KV_READ_CTRL_REG2STRUCT(kv_seed_read_ctrl_reg, ecc_kv_rd_seed_ctrl)
    `CALIPTRA_KV_WRITE_CTRL_REG2STRUCT(kv_write_ctrl_reg, ecc_kv_wr_pkey_ctrl)

    //Detect keyvault data coming in to lock api registers and protect outputs
    always_comb kv_seed_data_present_set = kv_seed_read_ctrl_reg.read_en;
    always_comb kv_seed_data_present_reset = kv_seed_data_present & ecc_status_done_p;
    
    always_comb kv_key_data_present_set = kv_privkey_read_ctrl_reg.read_en;
    always_comb kv_key_data_present_reset = kv_key_data_present & ecc_status_done_p;

    always_comb pcr_sign_mode = hwif_out.ECC_CTRL.PCR_SIGN.value;

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
        else if(zeroize_reg) begin
            scalar_G_reg <= '0;
            scalar_PK_reg <= '0;
        end
        else begin
            if (!scalar_G_sel)
                scalar_G_reg <= hmac_drbg_result;
            else if (hw_scalar_G_we)
                scalar_G_reg <= read_reg;
            
            if (hw_scalar_PK_we)
                scalar_PK_reg <= read_reg;
        end
    end

    // Set the write enable flag for different register based on sequencer output of "DSA_UOP_RD_CORE"
    // to read them from data memory inside ecc_arith_unit
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
        hw_pk_chk_we = 0;
        hw_sharedkey_we = 0;
        if ((prog_instr.opcode == DSA_UOP_RD_CORE) & (cycle_cnt == 0)) begin
            unique case (prog_instr.reg_id)
                PRIVKEY_ID      : hw_privkey_we = 1;
                PUBKEYX_ID      : hw_pubkeyx_we = 1;
                PUBKEYY_ID      : hw_pubkeyy_we = 1;
                R_ID            : hw_r_we = 1;
                S_ID            : hw_s_we = 1;
                SCALAR_G_ID     : hw_scalar_G_we = 1;
                SCALAR_PK_ID    : hw_scalar_PK_we = 1;
                VERIFY_R_ID     : hw_verify_r_we = 1;
                PK_VALID_ID     : hw_pk_chk_we = 1;
                DH_SHAREDKEY_ID : hw_sharedkey_we = 1;
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
                        hw_pk_chk_we = 0;
                        hw_sharedkey_we = 0;
                    end
            endcase
        end
    end // wr_en_signals

    
    // set the write register value based on sequencer output of "DSA_UOP_WR_CORE"
    // to write into data memory inside ecc_arith_unit
    always_comb 
    begin : write_to_pm_core
        write_reg = '0;
        if (prog_instr.opcode == DSA_UOP_WR_CORE) begin
            unique case (prog_instr.reg_id)
                CONST_ZERO_ID         : write_reg = {zero_pad, ZERO_CONST};
                CONST_ONE_ID          : write_reg = {zero_pad, ONE_CONST};
                CONST_E_a_MONT_ID     : write_reg = {zero_pad, E_a_MONT};
                CONST_E_b_MONT_ID     : write_reg = {zero_pad, E_b_MONT};
                CONST_E_3b_MONT_ID    : write_reg = {zero_pad, E_3b_MONT};
                CONST_ONE_p_MONT_ID   : write_reg = {zero_pad, ONE_p_MONT};
                CONST_R2_p_MONT_ID    : write_reg = {zero_pad, R2_p_MONT};
                CONST_G_X_MONT_ID     : write_reg = {zero_pad, G_X_MONT};
                CONST_G_Y_MONT_ID     : write_reg = {zero_pad, G_Y_MONT};
                CONST_R2_q_MONT_ID    : write_reg = {zero_pad, R2_q_MONT};
                CONST_ONE_q_MONT_ID   : write_reg = {zero_pad, ONE_q_MONT};
                MSG_ID                : write_reg = {zero_pad, msg_reduced_reg};
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
        else if (prog_instr.opcode == DSA_UOP_WR_SCALAR) begin
            unique case (prog_instr.reg_id)
                SCALAR_PK_ID          : write_reg = (REG_SIZE+RND_SIZE)'(scalar_PK_reg << RND_SIZE);
                SCALAR_G_ID           : write_reg = (REG_SIZE+RND_SIZE)'(scalar_G_reg << RND_SIZE);
                SCALAR_ID             : write_reg = scalar_out_reg; // SCA
                default               : write_reg = '0;
            endcase
        end
    end // write_to_pm_core

    // Set the input scalar for scalar_blinding module
    always_ff @(posedge clk or negedge reset_n) 
    begin : scalar_sca_ctrl
        if(!reset_n) begin
            scalar_in_reg <= '0;
        end
        else if(zeroize_reg) begin
            scalar_in_reg <= '0;
        end
        else begin
            if (prog_instr.opcode == DSA_UOP_SCALAR_SCA) begin
                scalar_in_reg <= scalar_G_reg;
            end
        end
    end // scalar_sca_ctrl

    assign hmac_busy = ~hmac_ready;
    assign subcomponent_busy = pm_busy_o | hmac_busy | scalar_sca_busy_o;


    //----------------------------------------------------------------
    // ERROR detection
    //
    // bound check for different input/output registers.
    //----------------------------------------------------------------   
    always_ff @(posedge clk or negedge reset_n) 
    begin : pk_chk
        if(!reset_n) begin
            pk_chk_reg <= '0;
        end
        else if(zeroize_reg) begin
            pk_chk_reg <= '0;
        end
        else begin
            if (hw_pk_chk_we) begin
                pk_chk_reg <= read_reg;
            end
        end
    end // pk_chk

    always_ff @(posedge clk or negedge reset_n) 
    begin : error_detection
        if(!reset_n)
            error_flag_reg <= 1'b0;
        else if(zeroize_reg)
            error_flag_reg <= 1'b0;
        else if (error_flag)
            error_flag_reg <= 1'b1;
    end // error_detection
    
    assign error_flag_edge = error_flag & (!error_flag_reg);

    assign privkey_input_outofrange = signing_process & ((privkey_reg == 0) | (privkey_reg >= GROUP_ORDER));
    assign r_output_outofrange      = signing_process & (hw_r_we & ((read_reg == 0) | (read_reg >= GROUP_ORDER)));
    assign s_output_outofrange      = signing_process & (hw_s_we & ((read_reg == 0) | (read_reg >= GROUP_ORDER)));

    assign r_input_outofrange       = verifying_process & ((r_reg == 0) | (r_reg >= GROUP_ORDER));
    assign s_input_outofrange       = verifying_process & ((s_reg == 0) | (s_reg >= GROUP_ORDER));
    assign pubkeyx_input_outofrange = (verifying_process | sharedkey_process) & (pubkeyx_reg >= PRIME);
    assign pubkeyy_input_outofrange = (verifying_process | sharedkey_process) & (pubkeyy_reg >= PRIME);
    assign pubkey_input_invalid     = (verifying_process | sharedkey_process) & (pk_chk_reg != 0);

    assign pcr_sign_input_invalid   = ((cmd_reg == KEYGEN) | (cmd_reg == VERIFY) | (cmd_reg == SHARED_KEY)) & pcr_sign_mode;

    assign privkey_output_outofrange = keygen_process & (hw_privkey_we & ((read_reg == 0) | (read_reg >= GROUP_ORDER)));
    assign pubkeyx_output_outofrange = keygen_process & (hw_pubkeyx_we & (read_reg >= PRIME));
    assign pubkeyy_output_outofrange = keygen_process & (hw_pubkeyy_we & (read_reg >= PRIME));

    assign sharedkey_outofrange = sharedkey_process & (hw_sharedkey_we & (read_reg >= PRIME));

    assign error_flag = privkey_input_outofrange | r_output_outofrange | s_output_outofrange | 
                        r_input_outofrange | s_input_outofrange | pubkeyx_input_outofrange | pubkeyy_input_outofrange | 
                        pubkey_input_invalid | pcr_sign_input_invalid |
                        privkey_output_outofrange | pubkeyx_output_outofrange | pubkeyy_output_outofrange |
                        sharedkey_outofrange;

    //----------------------------------------------------------------
    // ECDSA_FSM_flow
    //
    // This FSM starts with the keyfen/signing/verifying command to 
    // perform different operations.
    // Active low and async reset.
    //----------------------------------------------------------------
    always_ff @(posedge clk or negedge reset_n) 
    begin : ECDSA_FSM
        if(!reset_n) begin
            prog_cntr           <= ECC_RESET;
            cycle_cnt           <= '0;
            pm_cmd_reg          <= '0;
            ecc_valid_reg       <= 0;
            scalar_G_sel        <= 0;
            hmac_mode           <= '0;
            hmac_init           <= 0;
            scalar_sca_en       <= 0;
            keygen_process      <= 0;
            signing_process     <= 0;
            verifying_process   <= 0;
            sharedkey_process   <= 0;
        end
        else if(zeroize_reg) begin
            prog_cntr           <= ECC_RESET;
            cycle_cnt           <= '0;
            pm_cmd_reg          <= '0;
            ecc_valid_reg       <= 0;
            scalar_G_sel        <= 0;
            hmac_mode           <= '0;
            hmac_init           <= 0;
            scalar_sca_en       <= 0;
            keygen_process      <= 0;
            signing_process     <= 0;
            verifying_process   <= 0;
            sharedkey_process   <= 0;
        end
        else if (error_flag | error_flag_reg) begin
            prog_cntr           <= ECC_NOP;
            cycle_cnt           <= '0;
            pm_cmd_reg          <= '0;
            ecc_valid_reg       <= 0;
            scalar_G_sel        <= 0;
            hmac_mode           <= '0;
            hmac_init           <= 0;
            scalar_sca_en       <= 0;
            keygen_process      <= 0;
            signing_process     <= 0;
            verifying_process   <= 0;
            sharedkey_process   <= 0;
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
                unique case (prog_cntr)
                    ECC_NOP : begin 
                        keygen_process      <= 0;
                        signing_process     <= 0;
                        verifying_process   <= 0;
                        sharedkey_process   <= 0;
                        // Waiting for new valid command 
                        unique case (cmd_reg)
                            KEYGEN : begin  // keygen
                                prog_cntr <= DSA_KG_S;
                                ecc_valid_reg <= 0;
                                scalar_G_sel <= 0;
                                hmac_mode <= 2'b00;
                                keygen_process <= 1;
                            end   

                            SIGN : begin  // signing
                                prog_cntr <= DSA_SGN_S;
                                ecc_valid_reg <= 0;
                                scalar_G_sel <= 0;
                                hmac_mode <= 2'b01;
                                signing_process <= 1;
                            end                                   

                            VERIFY : begin  // verifying
                                prog_cntr <= DSA_VER_S;
                                ecc_valid_reg <= 0;
                                scalar_G_sel <= 1;
                                verifying_process <= 1;
                            end

                            SHARED_KEY : begin  // DH shared_key
                                prog_cntr <= DH_SHARED_S;
                                ecc_valid_reg <= 0;
                                scalar_G_sel <= 1;
                                hmac_mode <= 2'b10;
                                sharedkey_process <= 1;
                            end

                            default : begin
                                prog_cntr <= ECC_NOP;
                                scalar_G_sel <= 0;
                            end
                        endcase
                        pm_cmd_reg  <= '0;
                        hmac_init   <= 0;
                    end                

                    DSA_KG_E : begin // end of keygen
                        prog_cntr <= ECC_NOP;
                        ecc_valid_reg <= 1;
                    end

                    DSA_SGN_E : begin // end of signing
                        prog_cntr <= ECC_NOP;
                        ecc_valid_reg <= 1;
                    end

                    DSA_VER_E : begin // end of verifying
                        prog_cntr <= ECC_NOP;
                        ecc_valid_reg <= 1;
                    end

                    DH_SHARED_E: begin // end of DH shared key
                        prog_cntr <= ECC_NOP;
                        ecc_valid_reg <= 1;
                    end
                    
                    ECC_RESET,
                    DSA_KG_S,
                    DSA_SGN_S,
                    DSA_VER_S,
                    DH_SHARED_S : begin
                        prog_cntr       <= prog_cntr + 1;
                        pm_cmd_reg      <= prog_instr.opcode.pm_cmd;
                        hmac_init       <= prog_instr.opcode.hmac_drbg_en;
                        scalar_sca_en   <= prog_instr.opcode.sca_en;
                    end

                    default : begin
                        prog_cntr       <= prog_cntr + 1;
                        pm_cmd_reg      <= prog_instr.opcode.pm_cmd;
                        hmac_init       <= prog_instr.opcode.hmac_drbg_en;
                        scalar_sca_en   <= prog_instr.opcode.sca_en;
                    end
                endcase
            end
        end
    end // ECDSA_FSM

    // Generate a pulse to trig the interupt after finishing the operation
    always_ff @(posedge clk or negedge reset_n)
        if (!reset_n)
            ecc_status_done_d <= 1'b0;
        else if (zeroize_reg)
            ecc_status_done_d <= 1'b0;
        else
            ecc_status_done_d <= hwif_in.ECC_STATUS.VALID.next;
    always_comb ecc_status_done_p = hwif_in.ECC_STATUS.VALID.next && !ecc_status_done_d;

    // Set the ready/busy flag of ECC
    assign dsa_busy = (prog_cntr == ECC_NOP)? 1'b0 : 1'b1;
    always_comb ecc_ready_reg = !(dsa_busy | pm_busy_o);
    
    //Key Vault Control Modules
    always_comb begin
        kv_privkey_read_metrics.ocp_lock_in_progress = ocp_lock_in_progress;
        kv_privkey_read_metrics.kv_read_dest         = KV_NUM_READ'(1<<KV_DEST_IDX_ECC_PKEY);
        kv_privkey_read_metrics.kv_key_entry         = kv_privkey_read_ctrl_reg.read_entry;
    end

    //Read PRIVKEY
    kv_read_client #(
        .DATA_WIDTH(REG_SIZE),
        .PAD(0)
    )
    ecc_privkey_kv_read
    (
        .clk(clk),
        .rst_b(reset_n),
        .zeroize(zeroize_reg),

        //client control register
        .read_ctrl_reg(kv_privkey_read_ctrl_reg),
        .read_metrics(kv_privkey_read_metrics),

        //interface with kv
        .kv_read(kv_read[0]),
        .kv_resp(kv_rd_resp[0]),

        //interface with client
        .write_en(kv_privkey_write_en),
        .write_offset(kv_privkey_write_offset),
        .write_data(kv_privkey_write_data),

        .error_code(kv_privkey_error),
        .kv_ready(kv_privkey_ready),
        .read_done(kv_privkey_done)
    );

    //Read SEED
    always_comb begin
        kv_seed_read_metrics.ocp_lock_in_progress = ocp_lock_in_progress;
        kv_seed_read_metrics.kv_read_dest         = KV_NUM_READ'(1<<KV_DEST_IDX_ECC_SEED);
        kv_seed_read_metrics.kv_key_entry         = kv_seed_read_ctrl_reg.read_entry;
    end

    kv_read_client #(
        .DATA_WIDTH(REG_SIZE),
        .PAD(0)
    )
    ecc_seed_kv_read
    (
        .clk(clk),
        .rst_b(reset_n),
        .zeroize(zeroize_reg),

        //client control register
        .read_ctrl_reg(kv_seed_read_ctrl_reg),
        .read_metrics(kv_seed_read_metrics),

        //interface with kv
        .kv_read(kv_read[1]),
        .kv_resp(kv_rd_resp[1]),

        //interface with client
        .write_en(kv_seed_write_en),
        .write_offset(kv_seed_write_offset),
        .write_data(kv_seed_write_data),

        .error_code(kv_seed_error),
        .kv_ready(kv_seed_ready),
        .read_done(kv_seed_done)
    );

    //Write to keyvault
    always_comb begin
        kv_write_metrics.ocp_lock_in_progress = ocp_lock_in_progress;
        kv_write_metrics.kv_data0_present     = kv_seed_data_present;
        kv_write_metrics.kv_data0_entry       = kv_seed_read_ctrl_reg.read_entry; // FIXME latch this at start-time
        kv_write_metrics.kv_data1_present     = kv_key_data_present;
        kv_write_metrics.kv_data1_entry       = kv_privkey_read_ctrl_reg.read_entry; // FIXME latch this at start-time
        kv_write_metrics.kv_write_src         = KV_NUM_WRITE'(1 << KV_WRITE_IDX_ECC);
        kv_write_metrics.kv_write_entry       = kv_write_ctrl_reg.write_entry;
        kv_write_metrics.aes_decrypt_ecb_op   = 1'b0;
    end

    kv_write_client #(
        .DATA_WIDTH(REG_SIZE)
    )
    ecc_privkey_kv_write
    (
        .clk(clk),
        .rst_b(reset_n),
        .zeroize(zeroize_reg),

        //client control register
        .write_ctrl_reg(kv_write_ctrl_reg),
        .num_dwords(REG_NUM_DWORDS[4:0]),
        .write_metrics(kv_write_metrics),

        //interface with kv
        .kv_write(kv_write),
        .kv_resp(kv_wr_resp),

        //interface with client
        .dest_keyvault(dest_keyvault),
        .dest_data_avail(secretkey_we),
        .dest_data(kv_reg),

        .error_code(kv_write_error),
        .kv_ready(kv_write_ready),
        .dest_done(kv_write_done)
    );

always_comb busy_o = ~ecc_ready_reg | ~kv_write_ready | ~kv_seed_ready | ~kv_privkey_ready;
    `CALIPTRA_ASSERT_MUTEX(ERR_ECC_PRIVKEY_WE_MUTEX, {hw_privkey_we, privkey_we_reg}, clk, !reset_n)
    `CALIPTRA_ASSERT_MUTEX(ERR_ECC_SHAREDKEY_WE_MUTEX, {hw_sharedkey_we , sharedkey_we_reg}, clk, !reset_n)

//keyvault signals should be stable during engine operation
//Assertions get disabled during reset or when the engine is idle
`CALIPTRA_ASSERT_STABLE(ERR_ECC_PRIVKEY_RD_CTRL_NOT_STABLE, kv_privkey_read_ctrl_reg, clk, (!reset_n || ecc_ready_reg) )
`CALIPTRA_ASSERT_STABLE(ERR_ECC_SEED_RD_CTRL_NOT_STABLE, kv_seed_read_ctrl_reg, clk, (!reset_n || ecc_ready_reg) )
//write happens while engine is not idle, so hwclr triggers the writen en to de-assert
//instead confirming that entry and dest valid fields are stable
//`CALIPTRA_ASSERT_STABLE(ERR_ECC_WR_CTRL_NOT_STABLE, kv_write_ctrl_reg, clk, (!reset_n || ecc_ready_reg) )
`CALIPTRA_ASSERT_STABLE(ERR_ECC_WR_CTRL_ENTRY_NOT_STABLE, kv_write_ctrl_reg.write_entry, clk, (!reset_n || ecc_ready_reg) )
`CALIPTRA_ASSERT_STABLE(ERR_ECC_WR_CTRL_DEST_NOT_STABLE, kv_write_ctrl_reg.write_dest_vld, clk, (!reset_n || ecc_ready_reg) )

`CALIPTRA_ASSERT_STABLE(ERR_ECC_PRIVKEY_NOT_STABLE, privkey_reg, clk, (!reset_n || ecc_ready_reg) )
`CALIPTRA_ASSERT_STABLE(ERR_ECC_SEED_NOT_STABLE, seed_reg, clk, (!reset_n || ecc_ready_reg) )

endmodule
