// -------------------------------------------------
// Contact: contact@lubis-eda.com
// Author: Tobias Ludwig, Michael Schwarz
// -------------------------------------------------
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
module fv_ecc_dsa_ctrl_m
    import ecc_params_pkg::*;
    import ecc_dsa_uop_pkg::*;
    import ecc_reg_pkg::*;
    import kv_defines_pkg::*;
    (
    // Clock and reset.
    input logic           clk,
    input logic           reset_n,
    input logic          cptra_pwrgood,
    // Reg ports.
    input ecc_reg__out_t hwif_out,
    input ecc_reg__in_t hwif_in,    //output

    // KV interface
    input kv_read_t [1:0] kv_read,  //output
    input kv_write_t kv_write,      //output
    input kv_rd_resp_t [1:0] kv_rd_resp,
    input kv_wr_resp_t kv_wr_resp,

    //PCR Signing
    input pcr_signing_t pcr_signing_data,

    // Interrupts (from ecc_reg)
    input logic error_intr,         //output
    input logic notif_intr,         //output
    input logic debugUnlock_or_scan_mode_switch
    );

    localparam CYC_CNT = 4; // Equivalent to cycle count in DUT

 default clocking default_clk @(posedge clk); endclocking
   

    ////////////////////////////////////////////
    // Helper logic used for defining zeroize
    ////////////////////////////////////////////

    logic fv_zeroize;

    always_comb begin: logic_zeroize
        fv_zeroize = hwif_out.ECC_CTRL.ZEROIZE.value || debugUnlock_or_scan_mode_switch;
    end

    ////////////////////////////////////////////
    // Helper logic used in disabling the proofs
    // once the error is set in the design 
    // then fv_error_set stays asserted until reset_n or zeroize
    ////////////////////////////////////////////

    logic fv_error_set, fv_error;
        always_ff @(posedge clk, negedge reset_n) begin
            if(!reset_n) begin
                fv_error_set <= 0;
            end
            else if(fv_zeroize) begin
                fv_error_set <= 0;
            end
            else begin
                if(ecc_dsa_ctrl.error_flag) begin
                    fv_error_set <= 1;
                end
            end
        end
    

    ////////////////////////////////////////////
    // Helper logic for write_reg look up

    logic [(REG_SIZE+RND_SIZE)-1 : 0] fv_write_reg;
    logic [DSA_OPR_ADDR_WIDTH-1:0] fv_reg_id;

    assign fv_reg_id = ecc_dsa_ctrl.prog_instr.reg_id;

      always_comb begin: fv_write_reg_logic
        fv_write_reg = '0;
        if(ecc_dsa_ctrl.prog_instr.opcode == DSA_UOP_WR_CORE) begin
            unique casez (fv_reg_id)
                CONST_ZERO_ID         : fv_write_reg = {ecc_dsa_ctrl.zero_pad, ZERO_CONST};
                CONST_ONE_ID          : fv_write_reg = {ecc_dsa_ctrl.zero_pad, ONE_CONST};
                CONST_E_a_MONT_ID     : fv_write_reg = {ecc_dsa_ctrl.zero_pad, E_a_MONT};
                CONST_E_b_MONT_ID     : fv_write_reg = {ecc_dsa_ctrl.zero_pad, E_b_MONT};
                CONST_E_3b_MONT_ID    : fv_write_reg = {ecc_dsa_ctrl.zero_pad, E_3b_MONT};
                CONST_ONE_p_MONT_ID   : fv_write_reg = {ecc_dsa_ctrl.zero_pad, ONE_p_MONT};
                CONST_R2_p_MONT_ID    : fv_write_reg = {ecc_dsa_ctrl.zero_pad, R2_p_MONT};
                CONST_G_X_MONT_ID     : fv_write_reg = {ecc_dsa_ctrl.zero_pad, G_X_MONT};
                CONST_G_Y_MONT_ID     : fv_write_reg = {ecc_dsa_ctrl.zero_pad, G_Y_MONT};
                CONST_R2_q_MONT_ID    : fv_write_reg = {ecc_dsa_ctrl.zero_pad, R2_q_MONT};
                CONST_ONE_q_MONT_ID   : fv_write_reg = {ecc_dsa_ctrl.zero_pad, ONE_q_MONT};
                MSG_ID                : fv_write_reg = {ecc_dsa_ctrl.zero_pad, ecc_dsa_ctrl.msg_reduced_reg};
                PRIVKEY_ID            : fv_write_reg = {ecc_dsa_ctrl.zero_pad, ecc_dsa_ctrl.privkey_reg};
                PUBKEYX_ID            : fv_write_reg = {ecc_dsa_ctrl.zero_pad, ecc_dsa_ctrl.pubkeyx_reg};
                PUBKEYY_ID            : fv_write_reg = {ecc_dsa_ctrl.zero_pad, ecc_dsa_ctrl.pubkeyy_reg};
                R_ID                  : fv_write_reg = {ecc_dsa_ctrl.zero_pad, ecc_dsa_ctrl.r_reg};
                S_ID                  : fv_write_reg = {ecc_dsa_ctrl.zero_pad, ecc_dsa_ctrl.s_reg};
                SCALAR_G_ID           : fv_write_reg = {ecc_dsa_ctrl.zero_pad, ecc_dsa_ctrl.scalar_G_reg};
                LAMBDA_ID             : fv_write_reg = {ecc_dsa_ctrl.zero_pad, ecc_dsa_ctrl.lambda_reg};
                MASKING_ID            : fv_write_reg = {ecc_dsa_ctrl.zero_pad, ecc_dsa_ctrl.masking_rnd_reg};
                default               : fv_write_reg = '0;
            endcase
        end
            else if(ecc_dsa_ctrl.prog_instr.opcode == DSA_UOP_WR_SCALAR) begin
                unique casez (fv_reg_id)
                    SCALAR_G_ID           : fv_write_reg = (ecc_dsa_ctrl.scalar_G_reg << RND_SIZE);
                    SCALAR_PK_ID          : fv_write_reg = (ecc_dsa_ctrl.scalar_PK_reg << RND_SIZE);
                    SCALAR_ID             : fv_write_reg = ecc_dsa_ctrl.scalar_out_reg; // SCA 
                    default               : fv_write_reg = '0;
            endcase
            end

        end


    ////////////////////////////////////////////
    // Helper logic for read_reg look up

        logic [DSA_PROG_ADDR_W-1 : 0] fv_prog_cntr_reg;
        logic fv_hw_privkey_we;
        logic fv_hw_pubkeyx_we;
        logic fv_hw_pubkeyy_we;
        logic fv_hw_r_we;
        logic fv_hw_s_we;
        logic fv_hw_scalar_G_we ;
        logic fv_hw_scalar_PK_we;
        logic fv_hw_verify_r_we;
        logic fv_hw_pk_chk_we;

          always_ff @(posedge clk) begin
              fv_prog_cntr_reg <= ecc_dsa_ctrl.prog_cntr;
          end

          always_comb begin: wr_en_logic
              fv_hw_privkey_we = 0;
              fv_hw_pubkeyx_we = 0;
              fv_hw_pubkeyy_we = 0;
              fv_hw_r_we = 0;
              fv_hw_s_we = 0;
              fv_hw_scalar_G_we = 0;
              fv_hw_scalar_PK_we = 0;
              fv_hw_verify_r_we = 0;
              fv_hw_pk_chk_we = 0;
              if (ecc_dsa_ctrl.prog_instr.opcode == DSA_UOP_RD_CORE && fv_prog_cntr_reg!= ecc_dsa_ctrl.prog_cntr) begin
                  unique casez (fv_reg_id)
                      PRIVKEY_ID      : fv_hw_privkey_we = 1;
                      PUBKEYX_ID      : fv_hw_pubkeyx_we = 1;
                      PUBKEYY_ID      : fv_hw_pubkeyy_we = 1;
                      R_ID            : fv_hw_r_we = 1;
                      S_ID            : fv_hw_s_we = 1;
                      SCALAR_G_ID     : fv_hw_scalar_G_we = 1;
                      SCALAR_PK_ID    : fv_hw_scalar_PK_we = 1;
                      VERIFY_R_ID     : fv_hw_verify_r_we = 1;
                      PK_VALID_ID     : fv_hw_pk_chk_we = 1;
                      default         : 
                          begin 
                              fv_hw_privkey_we = 0;
                              fv_hw_pubkeyx_we = 0;
                              fv_hw_pubkeyy_we = 0;
                              fv_hw_r_we = 0;
                              fv_hw_s_we = 0;
                              fv_hw_scalar_G_we = 0;
                              fv_hw_scalar_PK_we = 0;
                              fv_hw_verify_r_we = 0;
                              fv_hw_pk_chk_we = 0;
                          end
                  endcase
              end
          end

        sequence reset_sequence;
          (!reset_n || fv_zeroize) ##1 reset_n && !fv_zeroize;
        endsequence 


    ////////////////////////////////////////////
    // reset property, when reset all the o/p //
    // are zero                               //
    ////////////////////////////////////////////

        property reset_p;
            $past(!reset_n || fv_zeroize) 
            |->

            ecc_dsa_ctrl.prog_cntr == DSA_RESET &&
            ecc_dsa_ctrl.cycle_cnt           == '0 &&
            ecc_dsa_ctrl.pm_cmd_reg          == '0 &&
            hwif_in.ECC_STATUS.VALID.next    == '0 &&
            ecc_dsa_ctrl.scalar_G_sel        == '0 &&
            ecc_dsa_ctrl.hmac_mode           == '0 &&
            ecc_dsa_ctrl.hmac_init           == '0 &&
            ecc_dsa_ctrl.scalar_sca_en       == '0 &&
            ecc_dsa_ctrl.keygen_process      == '0 &&
            ecc_dsa_ctrl.signing_process     == '0 &&
            ecc_dsa_ctrl.scalar_G_reg        == '0 &&
            ecc_dsa_ctrl.scalar_PK_reg       == '0 &&
            ecc_dsa_ctrl.pk_chk_reg          == '0 &&
            ecc_dsa_ctrl.kv_reg              == '0 &&
            ecc_dsa_ctrl.scalar_in_reg       == '0 &&
            ecc_dsa_ctrl.verifying_process   == '0 &&
            ecc_dsa_ctrl.kv_read_data_present == '0;
        endproperty

        reset_a : assert property(reset_p);


    ////////////////////////////////////////////
    // zeroize property, when set the resp. o/p //
    // are zero                               //
    ////////////////////////////////////////////


        property zeroize_p(word);
            (fv_zeroize)
            |->
            hwif_in.ECC_PRIVKEY_IN[word].PRIVKEY_IN.hwclr &&
            hwif_in.ECC_PRIVKEY_OUT[word].PRIVKEY_OUT.hwclr &&
            hwif_in.ECC_NONCE[word].NONCE.hwclr &&
            hwif_in.ECC_MSG[word].MSG.hwclr &&
            hwif_in.ECC_PUBKEY_X[word].PUBKEY_X.hwclr &&
            hwif_in.ECC_PUBKEY_Y[word].PUBKEY_Y.hwclr &&
            hwif_in.ECC_SIGN_R[word].SIGN_R.hwclr &&
            hwif_in.ECC_SIGN_S[word].SIGN_S.hwclr &&
            hwif_in.ECC_VERIFY_R[word].VERIFY_R.hwclr &&
            hwif_in.ECC_IV[word].IV.hwclr &&
            hwif_in.ECC_SEED[word].SEED.hwclr ;
         endproperty
   

         property no_zeroize_p(word);
            !(fv_zeroize)
            |->
            ! hwif_in.ECC_PRIVKEY_IN[word].PRIVKEY_IN.hwclr &&
            ! hwif_in.ECC_PRIVKEY_OUT[word].PRIVKEY_OUT.hwclr &&
            ! hwif_in.ECC_NONCE[word].NONCE.hwclr &&
            ! hwif_in.ECC_MSG[word].MSG.hwclr &&
            ! hwif_in.ECC_PUBKEY_X[word].PUBKEY_X.hwclr &&
            ! hwif_in.ECC_PUBKEY_Y[word].PUBKEY_Y.hwclr &&
            ! hwif_in.ECC_SIGN_R[word].SIGN_R.hwclr &&
            ! hwif_in.ECC_VERIFY_R[word].VERIFY_R.hwclr &&
            ! hwif_in.ECC_IV[word].IV.hwclr;
            endproperty


        // seed clr when there isn't any zeroize depends on the keyvault read status
         property no_zeroize_seed_clr_p(word);
            !(fv_zeroize)
            |->
            hwif_in.ECC_SEED[word].SEED.hwclr == (ecc_dsa_ctrl.privkey_out_we && ecc_dsa_ctrl.kv_read_data_present);
        endproperty

        for(genvar i=0 ;i< REG_NUM_DWORDS;i++) begin
                no_zeroize_a: assert property(no_zeroize_p(i));
                zeroize_a: assert property(zeroize_p(i));
                no_zeroize_seed_clr_a: assert property(disable iff(fv_error_set)no_zeroize_seed_clr_p(i));
        end




    // Store constant values once the reset or zeorize triggered.
    

        property store_const_after_reset_p;
            ecc_dsa_ctrl.prog_cntr == DSA_RESET
            |->
            ##CYC_CNT ecc_dsa_ctrl.prog_cntr == 1 
            ##CYC_CNT ecc_dsa_ctrl.prog_cntr == 2
            ##CYC_CNT ecc_dsa_ctrl.prog_cntr == 3
            ##CYC_CNT ecc_dsa_ctrl.prog_cntr == 4
            ##CYC_CNT ecc_dsa_ctrl.prog_cntr == 5
            ##CYC_CNT ecc_dsa_ctrl.prog_cntr == 6
            ##CYC_CNT ecc_dsa_ctrl.prog_cntr == 7
            ##CYC_CNT ecc_dsa_ctrl.prog_cntr == 8
            ##CYC_CNT ecc_dsa_ctrl.prog_cntr == 9
            ##CYC_CNT ecc_dsa_ctrl.prog_cntr == 10
            ##CYC_CNT ecc_dsa_ctrl.prog_cntr == 11;    
        endproperty
         store_const_after_reset_a: assert property(disable iff(!reset_n || fv_zeroize || fv_error_set)store_const_after_reset_p);


        property store_const_end_p;
            (ecc_dsa_ctrl.prog_cntr == 11) [*CYC_CNT] 
            |=>
             ecc_dsa_ctrl.prog_cntr == DSA_NOP;    
        endproperty

         store_const_end_a: assert property(disable iff(!reset_n || fv_zeroize || fv_error_set)store_const_end_p);


        // Before start of operations these constants are stored and stays stable until unless reset or zeroize
        property stable_const_mem_p;
            ecc_dsa_ctrl.prog_cntr >= DSA_NOP
            |->
            $stable(ecc_dsa_ctrl.ecc_arith_unit_i.ram_tdp_file_i.mem[0]) &&
            $stable(ecc_dsa_ctrl.ecc_arith_unit_i.ram_tdp_file_i.mem[1]) &&
            $stable(ecc_dsa_ctrl.ecc_arith_unit_i.ram_tdp_file_i.mem[2]) &&
            $stable(ecc_dsa_ctrl.ecc_arith_unit_i.ram_tdp_file_i.mem[3]) &&
            $stable(ecc_dsa_ctrl.ecc_arith_unit_i.ram_tdp_file_i.mem[4]) &&
            $stable(ecc_dsa_ctrl.ecc_arith_unit_i.ram_tdp_file_i.mem[5]) &&
            $stable(ecc_dsa_ctrl.ecc_arith_unit_i.ram_tdp_file_i.mem[6]) &&
            $stable(ecc_dsa_ctrl.ecc_arith_unit_i.ram_tdp_file_i.mem[7]) &&
            $stable(ecc_dsa_ctrl.ecc_arith_unit_i.ram_tdp_file_i.mem[28]) &&
            $stable(ecc_dsa_ctrl.ecc_arith_unit_i.ram_tdp_file_i.mem[29]);
        endproperty
        stable_const_mem_a: assert property(disable iff(!reset_n || fv_zeroize || fv_error_set)stable_const_mem_p);


/////////////////////////////////////////////////////////////////////////////////////
// ---------------------------------BEGIN----------------------------------------- //
// Checking the counter integrity that the sequence is performed one after another //
/////////////////////////////////////////////////////////////////////////////////////

    logic  [DSA_PROG_ADDR_W-1 : 0]   counter_const_a, counter_const_b;
    logic triggered_counter_const_a,triggered_counter_const_b;


        counter_const_a_assume: assume property(disable iff(!reset_n || fv_zeroize) (counter_const_a >=0) && (counter_const_a <=DSA_NOP) && $stable(counter_const_a));
        counter_const_b_assume: assume property(disable iff(!reset_n || fv_zeroize) (counter_const_b <=DSA_NOP) && (counter_const_b > counter_const_a) && $stable(counter_const_b));
        

        always_ff @(posedge clk, negedge reset_n) begin
            if(!reset_n ||fv_zeroize ) begin
                triggered_counter_const_a <= 0;
                triggered_counter_const_b <= 0;
            end
            else begin

                if(ecc_dsa_ctrl.prog_cntr==counter_const_a)
                    triggered_counter_const_a <=1;
                if (ecc_dsa_ctrl.prog_cntr==counter_const_b)
                    triggered_counter_const_b <= 1;
            end
        end


        property counter_const_liveness_p(trigered);
            ecc_dsa_ctrl.prog_cntr == DSA_RESET &&
            !(ecc_dsa_ctrl.error_flag_edge) &&
            !(ecc_dsa_ctrl.subcomponent_busy)
            |->
            s_eventually(trigered);
        endproperty

         counter_const_a_liveness_a: assert property(disable iff(!reset_n || fv_zeroize|| fv_error_set)counter_const_liveness_p(triggered_counter_const_a));
         counter_const_b_liveness_a: assert property(disable iff(!reset_n || fv_zeroize|| fv_error_set) counter_const_liveness_p(triggered_counter_const_b));


         property order_check_p(triggered_a,triggered_b);
           triggered_b
           |=>
           $past(triggered_a);
        endproperty
        counter_integrity_const_a: assert property(disable iff(!reset_n || fv_zeroize || fv_error_set) order_check_p(triggered_counter_const_a,triggered_counter_const_b));
    



/////////////////////////////////////////////////////////////////////////////////////
// ------------------------------------END---------------------------------------- //
/////////////////////////////////////////////////////////////////////////////////////


`ifdef REDUCED_PM_CTRL

    // This property works on the reduced version of the pm_ctrl
        property keygen_sequence_p;
            hwif_out.ECC_CTRL.CTRL.value == KEYGEN &&
            ecc_dsa_ctrl.prog_cntr == DSA_NOP &&
            !(ecc_dsa_ctrl.error_flag_edge) &&
            !(ecc_dsa_ctrl.subcomponent_busy)
            |=>
            ecc_dsa_ctrl.prog_cntr == DSA_KG_S    
            ##4 ecc_dsa_ctrl.prog_cntr ==        DSA_KG_S+ 1
            ##2 ecc_dsa_ctrl.prog_cntr ==        DSA_KG_S+ 2    
            ##4 ecc_dsa_ctrl.prog_cntr ==        DSA_KG_S+ 3    
            ##4 ecc_dsa_ctrl.prog_cntr ==        DSA_KG_S+ 4    
            ##4 ecc_dsa_ctrl.prog_cntr ==        DSA_KG_S+ 5    
            ##2 ecc_dsa_ctrl.prog_cntr ==        DSA_KG_S+ 6    
            ##4 ecc_dsa_ctrl.prog_cntr ==        DSA_KG_S+ 7    
            ##4 ecc_dsa_ctrl.prog_cntr ==        DSA_KG_S+ 8    
            ##4 ecc_dsa_ctrl.prog_cntr ==       DSA_KG_S+ 9    
            ##26 ecc_dsa_ctrl.prog_cntr ==        DSA_KG_S+ 10   
            ##4 ecc_dsa_ctrl.prog_cntr ==        DSA_KG_S+ 11   
            ##4 ecc_dsa_ctrl.prog_cntr ==        DSA_KG_S+ 12           
            ;
        endproperty

        keygen_sequence_a: assert property(disable iff(!reset_n || fv_zeroize || fv_error_set)keygen_sequence_p);
  `endif    


        // Proves the liveliness that once the cmd is triggered eventually it would have a valid
            property sequence_valid_p(cmd);
                hwif_out.ECC_CTRL.CTRL.value == cmd &&
                ecc_dsa_ctrl.prog_cntr == DSA_NOP &&
                !(ecc_dsa_ctrl.error_flag_edge) &&
                !(ecc_dsa_ctrl.subcomponent_busy)
                |->
                s_eventually(hwif_in.ECC_STATUS.VALID.next);
            endproperty

         keygen_sequence_valid_a: assert property(disable iff(!reset_n || fv_zeroize || fv_error_set)sequence_valid_p(KEYGEN));
         signing_sequence_valid_a: assert property(disable iff(!reset_n || fv_zeroize || fv_error_set)sequence_valid_p(SIGN));
         verify_sequence_valid_a:  assert property(disable iff(!reset_n || fv_zeroize || fv_error_set)sequence_valid_p(VERIFY));

         
         // At the last step of the cmd sequence, the valid signal should be asserted
         property valid_set_end_seq_p(end_st);
            ecc_dsa_ctrl.prog_cntr == end_st
            ##1 ecc_dsa_ctrl.prog_cntr != fv_prog_cntr_reg
            |->
            hwif_in.ECC_STATUS.VALID.next;
        endproperty
         keygen_valid_a: assert property(disable iff(!reset_n || fv_zeroize || fv_error_set)valid_set_end_seq_p(DSA_KG_E));
         signing_valid_a: assert property(disable iff(!reset_n || fv_zeroize || fv_error_set)valid_set_end_seq_p(DSA_SGN_E));
         verify_valid_a:  assert property(disable iff(!reset_n || fv_zeroize || fv_error_set)valid_set_end_seq_p(DSA_VER_E));


        //If the prog_cntr isn't in last step of the sequences and the DSA_NOP then valid should be deasserted
         property no_valid_p;
            (ecc_dsa_ctrl.prog_cntr != DSA_KG_E &&
            ecc_dsa_ctrl.prog_cntr != DSA_SGN_E &&
            ecc_dsa_ctrl.prog_cntr != DSA_VER_E &&
            ecc_dsa_ctrl.prog_cntr != DSA_NOP)   //Review: After the completion of seq. if no new input is set then the valid stays
            |=>
            !hwif_in.ECC_STATUS.VALID.next;
        endproperty
        no_valid_a:  assert property(disable iff(!reset_n || fv_zeroize || fv_error_set)no_valid_p);

        // TODO: ready and valid together
        
/////////////////////////////////////////////////////////////////////////////////////
// ---------------------------------BEGIN----------------------------------------- //
// Checking the counter integrity that the sequence is performed one after another //
/////////////////////////////////////////////////////////////////////////////////////

    logic  [DSA_PROG_ADDR_W-1 : 0]   counter_keygen_a, counter_keygen_b;
    logic  triggered_counter_keygen_a,triggered_counter_keygen_b;


        counter_keygen_a_assume: assume property(disable iff(!reset_n || fv_zeroize) (counter_keygen_a >=DSA_KG_S) && (counter_keygen_a <=DSA_KG_E) && $stable(counter_keygen_a));
        counter_keygen_b_assume: assume property(disable iff(!reset_n || fv_zeroize) (counter_keygen_b <=DSA_KG_E) && (counter_keygen_b > counter_keygen_a) && $stable(counter_keygen_b));
        
       
        always_ff @(posedge clk, negedge reset_n) begin
            if(!reset_n ||fv_zeroize ) begin
                triggered_counter_keygen_a <= 0;
                triggered_counter_keygen_b <= 0;
            end
            else begin

                if(ecc_dsa_ctrl.prog_cntr==counter_keygen_a)
                    triggered_counter_keygen_a <=1;
                if (ecc_dsa_ctrl.prog_cntr==counter_keygen_b)
                    triggered_counter_keygen_b <= 1;
            end
        end

        property counter_liveness_p(cmd,trigered);
            hwif_out.ECC_CTRL.CTRL.value == cmd &&
            ecc_dsa_ctrl.prog_cntr == DSA_NOP &&
            !(ecc_dsa_ctrl.error_flag_edge) &&
            !(ecc_dsa_ctrl.subcomponent_busy)
            |->
            s_eventually(trigered);
            endproperty

        counter_keygen_a_liveness_a: assert property(disable iff(!reset_n || fv_zeroize || fv_error_set)counter_liveness_p(KEYGEN,triggered_counter_keygen_a));
        counter_keygen_b_liveness_a: assert property(disable iff(!reset_n || fv_zeroize || fv_error_set) counter_liveness_p(KEYGEN,triggered_counter_keygen_b));

        counter_keygen_integrity_a: assert property(disable iff(!reset_n || fv_zeroize || fv_error_set) order_check_p(triggered_counter_keygen_a,triggered_counter_keygen_b));
    



/////////////////////////////////////////////////////////////////////////////////////
// ------------------------------------END---------------------------------------- //
/////////////////////////////////////////////////////////////////////////////////////

        
`ifdef REDUCED_PM_CTRL
       // This property works on the reduced version of the pm_ctrl
        property signing_sequence_p;
            hwif_out.ECC_CTRL.CTRL.value == SIGN &&
            ecc_dsa_ctrl.prog_cntr == DSA_NOP &&
            !(ecc_dsa_ctrl.error_flag_edge) &&
            !(ecc_dsa_ctrl.subcomponent_busy)
            |=>
            ecc_dsa_ctrl.prog_cntr == DSA_SGN_S      
            ##4 ecc_dsa_ctrl.prog_cntr == DSA_SGN_S+ 1   
            ##4 ecc_dsa_ctrl.prog_cntr == DSA_SGN_S+ 2   
            ##4 ecc_dsa_ctrl.prog_cntr == DSA_SGN_S+ 3   
            ##2 ecc_dsa_ctrl.prog_cntr == DSA_SGN_S+ 4   
            ##4 ecc_dsa_ctrl.prog_cntr == DSA_SGN_S+ 5   
            ##4 ecc_dsa_ctrl.prog_cntr == DSA_SGN_S+ 6   
            ##2 ecc_dsa_ctrl.prog_cntr == DSA_SGN_S+ 7   
            ##4 ecc_dsa_ctrl.prog_cntr == DSA_SGN_S+ 8   
            ##4 ecc_dsa_ctrl.prog_cntr == DSA_SGN_S+ 9   
            ##4 ecc_dsa_ctrl.prog_cntr == DSA_SGN_S+ 10  
            ##4 ecc_dsa_ctrl.prog_cntr == DSA_SGN_S+ 11  
            ##39 ecc_dsa_ctrl.prog_cntr ==  DSA_SGN_S+ 12 
            ##4 ecc_dsa_ctrl.prog_cntr == DSA_SGN_S+ 13  
            ##4 ecc_dsa_ctrl.prog_cntr == DSA_SGN_S+ 14  
            ;
        endproperty

        signing_sequence_a:  assert property(disable iff(!reset_n || fv_zeroize || ecc_dsa_ctrl.error_flag_edge)signing_sequence_p);
`endif

    


       
/////////////////////////////////////////////////////////////////////////////////////
// ---------------------------------BEGIN----------------------------------------- //
// Checking the counter integrity that the sequence is performed one after another //
/////////////////////////////////////////////////////////////////////////////////////

    logic  [DSA_PROG_ADDR_W-1 : 0]   counter_sign_a, counter_sign_b;
    logic  triggered_counter_sign_a,triggered_counter_sign_b;


        counter_sign_a_assume: assume property(disable iff(!reset_n || fv_zeroize) (counter_sign_a >=DSA_SGN_S) && (counter_sign_a <=DSA_SGN_E) && $stable(counter_sign_a));
        counter_sign_b_assume: assume property(disable iff(!reset_n || fv_zeroize) (counter_sign_b <=DSA_SGN_E) && (counter_sign_b > counter_sign_a) && $stable(counter_sign_b));
        
        always_ff @(posedge clk, negedge reset_n) begin
            if(!reset_n || fv_zeroize ) begin
                triggered_counter_sign_a <= 0;
                triggered_counter_sign_b <= 0;
            end
            else begin

                if(ecc_dsa_ctrl.prog_cntr==counter_sign_a)
                    triggered_counter_sign_a <=1;
                if (ecc_dsa_ctrl.prog_cntr==counter_sign_b)
                    triggered_counter_sign_b <= 1;
            end
        end

       
    counter_sign_a_liveness_a: assert property(disable iff(!reset_n || fv_zeroize || fv_error_set)counter_liveness_p(SIGN,triggered_counter_sign_a));
    counter_sign_b_liveness_a: assert property(disable iff(!reset_n || fv_zeroize|| fv_error_set) counter_liveness_p(SIGN,triggered_counter_sign_b));

    counter_integrity_sign_a: assert property(disable iff(!reset_n || fv_zeroize|| fv_error_set) order_check_p(triggered_counter_sign_a,triggered_counter_sign_b));
    



/////////////////////////////////////////////////////////////////////////////////////
// ------------------------------------END---------------------------------------- //
/////////////////////////////////////////////////////////////////////////////////////

   `ifdef REDUCED_PM_CTRL
       // This property works on the reduced version of the pm_ctrl      
        property verify_sequence_p;
            hwif_out.ECC_CTRL.CTRL.value == VERIFY &&
            ecc_dsa_ctrl.prog_cntr == DSA_NOP &&
            !(ecc_dsa_ctrl.error_flag_edge) &&
            !(ecc_dsa_ctrl.subcomponent_busy)
            |=>
            ecc_dsa_ctrl.prog_cntr == DSA_VER_S      
            ##4 ecc_dsa_ctrl.prog_cntr == DSA_VER_S+ 1   
            ##4 ecc_dsa_ctrl.prog_cntr == DSA_VER_S+ 2   
            ##4 ecc_dsa_ctrl.prog_cntr == DSA_VER_S+ 3   
            ##4 ecc_dsa_ctrl.prog_cntr == DSA_VER_S+ 4   
            ##42 ecc_dsa_ctrl.prog_cntr == DSA_VER_S+ 5   
            ##4 ecc_dsa_ctrl.prog_cntr == DSA_VER_S+ 6   
            ##4 ecc_dsa_ctrl.prog_cntr == DSA_VER_S+ 7   
            ##4 ecc_dsa_ctrl.prog_cntr == DSA_VER_S+ 8   
            ##4 ecc_dsa_ctrl.prog_cntr == DSA_VER_S+ 9   
            ##4 ecc_dsa_ctrl.prog_cntr == DSA_VER_S+ 10  
            ##4 ecc_dsa_ctrl.prog_cntr == DSA_VER_S+ 11  
            ##14 ecc_dsa_ctrl.prog_cntr == DSA_VER_S+ 12 
            ##4 ecc_dsa_ctrl.prog_cntr == DSA_VER_S+ 13  
            ##4 ecc_dsa_ctrl.prog_cntr == DSA_VER_S+ 14  
            ##4 ecc_dsa_ctrl.prog_cntr == DSA_VER_S+ 15  
            ##4 ecc_dsa_ctrl.prog_cntr == DSA_VER_S+ 16
            ##18 ecc_dsa_ctrl.prog_cntr == DSA_VER_S+ 17  
            ##4 ecc_dsa_ctrl.prog_cntr == DSA_VER_S+ 18  
            ##4 ecc_dsa_ctrl.prog_cntr == DSA_VER_S+ 19  
            ##4 ecc_dsa_ctrl.prog_cntr == DSA_VER_S+ 20  
            ##4 ecc_dsa_ctrl.prog_cntr == DSA_VER_S+ 21  
            ##34 ecc_dsa_ctrl.prog_cntr == DSA_VER_S+ 22
            ##4 ecc_dsa_ctrl.prog_cntr == DSA_VER_S+ 23  
            ;  
        endproperty

        verify_sequence_a:  assert property(disable iff(!reset_n || fv_zeroize || fv_error_set)verify_sequence_p);
`endif

   
/////////////////////////////////////////////////////////////////////////////////////
// ---------------------------------BEGIN----------------------------------------- //
// Checking the counter integrity that the sequence is performed one after another //
/////////////////////////////////////////////////////////////////////////////////////

    logic  [DSA_PROG_ADDR_W-1 : 0]   counter_verify_a, counter_verify_b;
    logic  triggered_counter_verify_a,triggered_counter_verify_b;


        counter_verify_a_assume: assume property(disable iff(!reset_n || fv_zeroize) (counter_verify_a >=DSA_SGN_S) && (counter_verify_a <=DSA_SGN_E) && $stable(counter_verify_a));
        counter_verify_b_assume: assume property(disable iff(!reset_n || fv_zeroize) (counter_verify_b <=DSA_SGN_E) && (counter_verify_b > counter_verify_a) && $stable(counter_verify_b));
        
        always_ff @(posedge clk, negedge reset_n) begin
            if(!reset_n ||fv_zeroize ) begin
                triggered_counter_verify_a <= 0;
                triggered_counter_verify_b <= 0;
            end
            else begin

                if(ecc_dsa_ctrl.prog_cntr==counter_verify_a)
                    triggered_counter_verify_a <=1;
                if (ecc_dsa_ctrl.prog_cntr==counter_verify_b)
                    triggered_counter_verify_b <= 1;
            end
        end

       
        counter_verify_a_liveness_a: assert property(disable iff(!reset_n || fv_zeroize || fv_error_set)counter_liveness_p(VERIFY,triggered_counter_verify_a));
        counter_verify_b_liveness_a: assert property(disable iff(!reset_n || fv_zeroize || fv_error_set) counter_liveness_p(VERIFY,triggered_counter_verify_b));

        counter_integrity_verify_a: assert property(disable iff(!reset_n || fv_zeroize || fv_error_set) order_check_p(triggered_counter_verify_a,triggered_counter_verify_b));
    



/////////////////////////////////////////////////////////////////////////////////////
// ------------------------------------END---------------------------------------- //
/////////////////////////////////////////////////////////////////////////////////////






    //---------------------------------------------------------------------//
    //                          Primary output                             //
    //---------------------------------------------------------------------//


        //Primary outputs connect to primary inputs
        property output_directconnection_input_p;
            hwif_in.reset_b == reset_n &&
            hwif_in.hard_reset_b == cptra_pwrgood &&
            hwif_in.ECC_NAME[0].NAME.next == ECC_CORE_NAME[31 : 0] &&
            hwif_in.ECC_NAME[1].NAME.next == ECC_CORE_NAME[63 : 32] &&
            hwif_in.ECC_VERSION[0].VERSION.next == ECC_CORE_VERSION[31 : 0] &&
            hwif_in.ECC_VERSION[1].VERSION.next == ECC_CORE_VERSION[63 : 32] &&
            error_intr == hwif_out.intr_block_rf.error_global_intr_r.intr &&
            notif_intr == hwif_out.intr_block_rf.notif_global_intr_r.intr &&
            hwif_in.ECC_CTRL.CTRL.hwclr == |hwif_out.ECC_CTRL.CTRL.value &&
            hwif_in.ECC_CTRL.PCR_SIGN.hwclr == hwif_out.ECC_CTRL.PCR_SIGN.value;
        endproperty

        output_directconnection_input_a: assert property(output_directconnection_input_p);


        // Primary outputs connected to the submodule outputs, here it is read_reg
        property output_connectedto_submodules_p(word);
            hwif_in.ECC_PRIVKEY_OUT[word].PRIVKEY_OUT.next == ecc_dsa_ctrl.read_reg[(REG_NUM_DWORDS-1)- word]&&
            hwif_in.ECC_SEED[word].SEED.next == ecc_dsa_ctrl.kv_seed_write_data &&
            hwif_in.ECC_MSG[word].MSG.next == pcr_signing_data.pcr_hash[word] &&
            hwif_in.ECC_PUBKEY_Y[word].PUBKEY_Y.next == ecc_dsa_ctrl.read_reg[(REG_NUM_DWORDS-1)- word] &&
            hwif_in.ECC_SIGN_R[word].SIGN_R.next == ecc_dsa_ctrl.read_reg[(REG_NUM_DWORDS-1)- word] &&
            hwif_in.ECC_SIGN_S[word].SIGN_S.next == ecc_dsa_ctrl.read_reg[(REG_NUM_DWORDS-1)- word] &&
            hwif_in.ECC_VERIFY_R[word].VERIFY_R.next == ecc_dsa_ctrl.read_reg[(REG_NUM_DWORDS-1)- word] &&
            hwif_in.ECC_PUBKEY_X[word].PUBKEY_X.next == ecc_dsa_ctrl.read_reg[(REG_NUM_DWORDS-1)- word];
        endproperty
         for(genvar i=0;i< REG_NUM_DWORDS;i++) begin
            output_connectedto_submodules_a: assert property(output_connectedto_submodules_p(i));
        end


        // If pcr sign is set then msg we and privkey_in we should be ! zeroize and privkey_in should take data from pcr_Signing
        property pcr_sign_mode_p(word);
            hwif_out.ECC_CTRL.PCR_SIGN.value 
            |->
            hwif_in.ECC_MSG[word].MSG.we == !(fv_zeroize) &&
            hwif_in.ECC_PRIVKEY_IN[word].PRIVKEY_IN.next == pcr_signing_data.pcr_signing_privkey[word] &&
            hwif_in.ECC_PRIVKEY_IN[word].PRIVKEY_IN.we == !(fv_zeroize)
            ;
        endproperty

        for(genvar i=0;i< REG_NUM_DWORDS;i++) begin
            pcr_sign_mode_a: assert property(pcr_sign_mode_p(i));
        end


        // If pcr sign isn't enabled then for msg no we and privkey_in is dependent on keyvault write_en
        property no_pcr_sign_mode_p(word);
            !hwif_out.ECC_CTRL.PCR_SIGN.value
             |->
            !hwif_in.ECC_MSG[word].MSG.we  &&
            hwif_in.ECC_PRIVKEY_IN[word].PRIVKEY_IN.next ==  (ecc_dsa_ctrl.kv_privkey_write_en ?  ecc_dsa_ctrl.kv_privkey_write_data :  ecc_dsa_ctrl.read_reg[(REG_NUM_DWORDS-1)-word] )&&
            hwif_in.ECC_PRIVKEY_IN[word].PRIVKEY_IN.we == ((ecc_dsa_ctrl.kv_privkey_write_en & (ecc_dsa_ctrl.kv_privkey_write_offset == word)) & !(fv_zeroize))
            ;
        endproperty
        for(genvar i=0;i< REG_NUM_DWORDS;i++) begin
            no_pcr_sign_mode_a: assert property(no_pcr_sign_mode_p(i));
        end


        //If privkey_out i.e reading from the reg after the privkey computation and 
        //if the seed is not rom the keyvault then privkey_out we is equal to !zeroize
        property privkey_out_we_p(word);
             ecc_dsa_ctrl.privkey_out_we &&
            !(ecc_dsa_ctrl.dest_keyvault | ecc_dsa_ctrl.kv_read_data_present)
            |->
            hwif_in.ECC_PRIVKEY_OUT[word].PRIVKEY_OUT.we == !(fv_zeroize);
        endproperty
         for(genvar i=0;i< REG_NUM_DWORDS;i++) begin
            privkey_out_we_a: assert property(disable iff(fv_error_set) privkey_out_we_p(i));
        end


        //If no privkey_out or keyvault is choose as desitination then prvkey_out we is deasserted
         property no_privkey_out_we_p(word);
            (!ecc_dsa_ctrl.privkey_out_we ||
            (ecc_dsa_ctrl.dest_keyvault | ecc_dsa_ctrl.kv_read_data_present))
            |->
            !hwif_in.ECC_PRIVKEY_OUT[word].PRIVKEY_OUT.we ;
        endproperty
         for(genvar i=0;i< REG_NUM_DWORDS;i++) begin
            no_privkey_out_we_a: assert property(no_privkey_out_we_p(i));
        end

        
        // if keyvault write is enabled and offset is equal to each word the seed we is equal to !zeroize
        property seed_we_p(word);
            (ecc_dsa_ctrl.kv_seed_write_en && 
            (ecc_dsa_ctrl.kv_seed_write_offset == word))
            |->
            hwif_in.ECC_SEED[word].SEED.we == !(fv_zeroize);
        endproperty
         for(genvar i=0;i< REG_NUM_DWORDS;i++) begin
            seed_we_a: assert property(seed_we_p(i));
        end


        // if keyvault write is not enabled and offset is not equal to each word then seed we is deasserted
         property no_seed_we_p(word);
            (!ecc_dsa_ctrl.kv_seed_write_en || 
            (ecc_dsa_ctrl.kv_seed_write_offset != word))
            |->
            !hwif_in.ECC_SEED[word].SEED.we;
        endproperty
         for(genvar i=0;i< REG_NUM_DWORDS;i++) begin
            no_seed_we_a: assert property(no_seed_we_p(i));
        end


        // Rest we are triggered with rd_core opcode and cycle_cnt=0
        property rd_core_we_p(word);
            hwif_in.ECC_PUBKEY_X[word].PUBKEY_X.we == (fv_hw_pubkeyx_we & !(fv_zeroize)) &&
            hwif_in.ECC_PUBKEY_Y[word].PUBKEY_Y.we == (fv_hw_pubkeyy_we & !(fv_zeroize)) &&
            hwif_in.ECC_SIGN_S[word].SIGN_S.we     == (fv_hw_s_we & !(fv_zeroize)) &&
            hwif_in.ECC_VERIFY_R[word].VERIFY_R.we == (fv_hw_verify_r_we & !(fv_zeroize)) &&
            hwif_in.ECC_SIGN_R[word].SIGN_R.we   == (fv_hw_r_we & !(fv_zeroize));
        endproperty
         for(genvar i=0;i< REG_NUM_DWORDS;i++) begin
            rd_core_we_a: assert property(disable iff(fv_error_set)rd_core_we_p(i));
        end


        // keyvault privkey read ctrl reg is connected to primary input kv_rd_pkey_ctrl
        property kv_privkey_read_ctrl_reg_p;
            ecc_dsa_ctrl.kv_privkey_read_ctrl_reg.rsvd == '0 &&
            ecc_dsa_ctrl.kv_privkey_read_ctrl_reg.pcr_hash_extend == hwif_out.ecc_kv_rd_pkey_ctrl.pcr_hash_extend.value &&
            ecc_dsa_ctrl.kv_privkey_read_ctrl_reg.read_entry == hwif_out.ecc_kv_rd_pkey_ctrl.read_entry.value &&
            ecc_dsa_ctrl.kv_privkey_read_ctrl_reg.read_en == hwif_out.ecc_kv_rd_pkey_ctrl.read_en.value;
        endproperty

        kv_privkey_read_ctrl_reg_a: assert property(kv_privkey_read_ctrl_reg_p);


        // keyvault seed read ctrl reg is connected to primary input kv_rd_seed_ctrl
        property kv_seed_read_ctrl_reg_p;
            ecc_dsa_ctrl.kv_seed_read_ctrl_reg.rsvd == '0 &&
            ecc_dsa_ctrl.kv_seed_read_ctrl_reg.pcr_hash_extend == hwif_out.ecc_kv_rd_seed_ctrl.pcr_hash_extend.value &&
            ecc_dsa_ctrl.kv_seed_read_ctrl_reg.read_entry == hwif_out.ecc_kv_rd_seed_ctrl.read_entry.value &&
            ecc_dsa_ctrl.kv_seed_read_ctrl_reg.read_en == hwif_out.ecc_kv_rd_seed_ctrl.read_en.value;
        endproperty

        kv_seed_read_ctrl_reg_a: assert property(kv_seed_read_ctrl_reg_p);


    //  keyvault write ctrl reg is connected to primary input kv_wr_pkey_ctrl
        property kv_write_ctrl_reg_p;
            ecc_dsa_ctrl.kv_write_ctrl_reg.rsvd == '0 &&
            ecc_dsa_ctrl.kv_write_ctrl_reg.write_dest_vld[0] == hwif_out.ecc_kv_wr_pkey_ctrl.hmac_key_dest_valid.value &&
            ecc_dsa_ctrl.kv_write_ctrl_reg.write_dest_vld[1] == hwif_out.ecc_kv_wr_pkey_ctrl.hmac_block_dest_valid.value &&
            ecc_dsa_ctrl.kv_write_ctrl_reg.write_dest_vld[2] == hwif_out.ecc_kv_wr_pkey_ctrl.sha_block_dest_valid.value &&
            ecc_dsa_ctrl.kv_write_ctrl_reg.write_dest_vld[3] == hwif_out.ecc_kv_wr_pkey_ctrl.ecc_pkey_dest_valid.value &&
            ecc_dsa_ctrl.kv_write_ctrl_reg.write_dest_vld[4] == hwif_out.ecc_kv_wr_pkey_ctrl.ecc_seed_dest_valid.value &&
            ecc_dsa_ctrl.kv_write_ctrl_reg.write_entry == hwif_out.ecc_kv_wr_pkey_ctrl.write_entry.value &&
            ecc_dsa_ctrl.kv_write_ctrl_reg.write_en == hwif_out.ecc_kv_wr_pkey_ctrl.write_en.value;
        endproperty

        kv_write_ctrl_reg_a: assert property(kv_write_ctrl_reg_p);


    // kv_read data present stays asserted until privkey is generated if read_en of kv is set
        property kv_read_data_present_p;
            ecc_dsa_ctrl.kv_seed_read_ctrl_reg.read_en
            |=>
            ecc_dsa_ctrl.kv_read_data_present until_with ecc_dsa_ctrl.privkey_out_we;
        endproperty
        kv_read_data_present_a: assert property(disable iff(!reset_n || fv_zeroize) kv_read_data_present_p);


     // Once kv_read_data_present is set then it deasserts if privkey is ready to be read and no new read_en
         property no_kv_read_data_present_p;
            ecc_dsa_ctrl.kv_read_data_present &&
            ecc_dsa_ctrl.privkey_out_we &&
            !ecc_dsa_ctrl.kv_seed_read_ctrl_reg.read_en //Review: Fails because if read_en is continously high then it won't be deasserted.
            |=>
            !ecc_dsa_ctrl.kv_read_data_present;
        endproperty
        no_kv_read_data_present_a: assert property(disable iff(!reset_n || fv_zeroize) no_kv_read_data_present_p);


    // If privkey is ready to read and keyvault is choosen as destination then kv_reg will have the privkey
       property kv_reg_p;
            ecc_dsa_ctrl.privkey_out_we &&
            (ecc_dsa_ctrl.dest_keyvault | ecc_dsa_ctrl.kv_read_data_present)
            |=>
            ecc_dsa_ctrl.kv_reg == $past(ecc_dsa_ctrl.read_reg);
        endproperty

    kv_reg_a: assert property(disable iff(!reset_n || fv_zeroize)kv_reg_p);


    // kv_reg stays stable if privkey isn't ready or kv is not choosen as dest.
     property stable_kv_reg_p;
            !ecc_dsa_ctrl.privkey_out_we ||
            !(ecc_dsa_ctrl.dest_keyvault | ecc_dsa_ctrl.kv_read_data_present)
            |=>
            ecc_dsa_ctrl.kv_reg == $past(ecc_dsa_ctrl.kv_reg);
        endproperty

    stable_kv_reg_a: assert property(disable iff(!reset_n || fv_zeroize)stable_kv_reg_p);



    // Primary outputs directly connected to kv(submodule) outputs
    property primaryout_connected_to_kvout_p;
         hwif_in.ecc_kv_rd_pkey_status.ERROR.next == ecc_dsa_ctrl.kv_privkey_error &&
        hwif_in.ecc_kv_rd_seed_status.ERROR.next == ecc_dsa_ctrl.kv_seed_error &&
        hwif_in.ecc_kv_wr_pkey_status.ERROR.next == ecc_dsa_ctrl.kv_write_error &&
        //ready when fsm is not busy
        hwif_in.ecc_kv_rd_pkey_status.READY.next == ecc_dsa_ctrl.kv_privkey_ready &&
        hwif_in.ecc_kv_rd_seed_status.READY.next == ecc_dsa_ctrl.kv_seed_ready &&
        hwif_in.ecc_kv_wr_pkey_status.READY.next == ecc_dsa_ctrl.kv_write_ready &&
        //set valid when fsm is done
        hwif_in.ecc_kv_rd_pkey_status.VALID.hwset == ecc_dsa_ctrl.kv_privkey_done &&
        hwif_in.ecc_kv_rd_seed_status.VALID.hwset == ecc_dsa_ctrl.kv_seed_done &&
        hwif_in.ecc_kv_wr_pkey_status.VALID.hwset == ecc_dsa_ctrl.kv_write_done &&
        //clear valid when new request is made
        hwif_in.ecc_kv_rd_pkey_status.VALID.hwclr == hwif_out.ecc_kv_rd_pkey_ctrl.read_en.value &&
        hwif_in.ecc_kv_rd_seed_status.VALID.hwclr == hwif_out.ecc_kv_rd_seed_ctrl.read_en.value &&
        hwif_in.ecc_kv_wr_pkey_status.VALID.hwclr == hwif_out.ecc_kv_wr_pkey_ctrl.write_en.value &&
        //clear enable when busy
        hwif_in.ecc_kv_rd_pkey_ctrl.read_en.hwclr == !ecc_dsa_ctrl.kv_privkey_ready &&
        hwif_in.ecc_kv_rd_seed_ctrl.read_en.hwclr == !ecc_dsa_ctrl.kv_seed_ready &&
        hwif_in.ecc_kv_wr_pkey_ctrl.write_en.hwclr == !ecc_dsa_ctrl.kv_write_ready; 

    endproperty

    primaryout_connected_to_kvout_a: assert property(primaryout_connected_to_kvout_p);


    // If pm_ctrl is not busy and prog_cntr is equal to DSA_NOP then ecc_ready to accept cmds
    property ready_p;
        !ecc_dsa_ctrl.pm_busy_o &&
        ecc_dsa_ctrl.prog_cntr == DSA_NOP
        |->
        hwif_in.ECC_STATUS.READY.next &&
        hwif_in.ecc_ready;
    endproperty

    ready_a: assert property(disable iff(!reset_n || fv_zeroize)ready_p);


    // If pm_ctrl is busy or prog_cntr is in cmd execution or memory write steps then ecc isn't ready
    property no_ready_p;
        ecc_dsa_ctrl.pm_busy_o ||
        ecc_dsa_ctrl.prog_cntr != DSA_NOP 
        |->
        !hwif_in.ECC_STATUS.READY.next &&
        !hwif_in.ecc_ready;
    endproperty

    no_ready_a: assert property(disable iff(!reset_n || fv_zeroize)no_ready_p);



    //-------------------------------------------------------//
    // Notif interrupt and error sequences                   //
    //-------------------------------------------------------//


    logic [REG_NUM_DWORDS-1 : 0][RADIX-1:0] privkey_reg;
    for(genvar i=0;i< REG_NUM_DWORDS;i++) begin
        assign privkey_reg[i] = hwif_out.ECC_PRIVKEY_IN[(REG_NUM_DWORDS-1)-i].PRIVKEY_IN.value;
    end

    // During sign subroutine if input privkey is zero or >= Group_order or while writing 
    // the outputs s and r are equal to zero error is triggered
        property error_sign_p;
            ((ecc_dsa_ctrl.prog_cntr <= DSA_SGN_E) &&
            (ecc_dsa_ctrl.prog_cntr >= DSA_SGN_S)) &&
            (((privkey_reg == '0) | (privkey_reg >= GROUP_ORDER)) ||
            (fv_hw_s_we &&(ecc_dsa_ctrl.read_reg==0)) ||
            (fv_hw_r_we &&(ecc_dsa_ctrl.read_reg==0)))
            |=>
            hwif_in.intr_block_rf.error_internal_intr_r.error_internal_sts.hwset;
        endproperty

        error_sign_a: assert property(disable iff(!reset_n || fv_zeroize) error_sign_p);

    
    // If keygen subroutine is the cmd then input cannot have pcr_sign, this results in error
        property error_keygen_p;
            (ecc_dsa_ctrl.cmd_reg== KEYGEN) && 
            hwif_out.ECC_CTRL.PCR_SIGN.value
            |=>
            hwif_in.intr_block_rf.error_internal_intr_r.error_internal_sts.hwset;
        endproperty

        error_keygen_a: assert property(disable iff(!reset_n || fv_zeroize) error_keygen_p);


    // During verifying subroutine if r and s inputs are equal to zero or greater than group order or 
    // the pubkey is greater than prime or
    // If the cmd is just set as verify after reset then pcr_sign cannot be set along this results in error
        property error_verify_p;
            (((ecc_dsa_ctrl.prog_cntr <= DSA_VER_E) && 
            (ecc_dsa_ctrl.prog_cntr >= DSA_VER_S)) &&
                (((ecc_dsa_ctrl.r_reg == 0) ||
                (ecc_dsa_ctrl.r_reg >= GROUP_ORDER)) ||
                ((ecc_dsa_ctrl.s_reg == 0) ||
                (ecc_dsa_ctrl.s_reg >= GROUP_ORDER)) ||
                (ecc_dsa_ctrl.pubkeyx_reg >= PRIME) ||
                (ecc_dsa_ctrl.pubkeyy_reg >= PRIME))) ||
            ((ecc_dsa_ctrl.cmd_reg==VERIFY) & hwif_out.ECC_CTRL.PCR_SIGN.value) 
            |=>
            hwif_in.intr_block_rf.error_internal_intr_r.error_internal_sts.hwset;
        endproperty

        error_verify_a: assert property(disable iff(!reset_n || fv_zeroize) error_verify_p);


        // Once valid signal is set then interrupt is triggered as a pulse
        property notif_interrupt_p;
            $rose(hwif_in.ECC_STATUS.VALID.next)
            |->
            hwif_in.intr_block_rf.notif_internal_intr_r.notif_cmd_done_sts.hwset
            ##1
            !hwif_in.intr_block_rf.notif_internal_intr_r.notif_cmd_done_sts.hwset;
        endproperty
        notif_interrupt_a: assert property(disable iff(!reset_n || fv_zeroize)notif_interrupt_p);


        // If pm_ctrl busy or sca_blinding modules are busy or if hmac is not ready then subcomponent_busy is asserted
        property subcomponent_busy_p;
            ecc_dsa_ctrl.pm_busy_o ||
            ecc_dsa_ctrl.scalar_sca_busy_o ||
            !ecc_dsa_ctrl.hmac_ready
            |->
            ecc_dsa_ctrl.subcomponent_busy;
        endproperty

        subcomponent_busy_a: assert property(disable iff(!reset_n || fv_zeroize) subcomponent_busy_p);


        // If none of the subcomponents are busy then subcomponent_busy is deasserted
        property no_subcomponent_busy_p;
            !ecc_dsa_ctrl.pm_busy_o &&
            !ecc_dsa_ctrl.scalar_sca_busy_o &&
            ecc_dsa_ctrl.hmac_ready
            |->
            !ecc_dsa_ctrl.subcomponent_busy;
        endproperty

        no_subcomponent_busy_a: assert property(disable iff(!reset_n || fv_zeroize) no_subcomponent_busy_p);
    


//-------------------------------------------------------------------------//
//                          HMAC_Interface
//-------------------------------------------------------------------------//

        //If hmac_drbg is enabled from seq then if no error flag and cyc_cnt=3 hmac_init is triggered until the 
        // prog_cntr advances
        property hmac_init_p;
            ecc_dsa_ctrl.prog_instr.opcode.hmac_drbg_en && 
            (ecc_dsa_ctrl.prog_cntr == fv_prog_cntr_reg) && //represents CYC=2
            !ecc_dsa_ctrl.error_flag_edge 
           ##1 (ecc_dsa_ctrl.prog_cntr != fv_prog_cntr_reg) // represents CYC=3
            |->
            ecc_dsa_ctrl.hmac_init s_until_with (ecc_dsa_ctrl.prog_cntr != fv_prog_cntr_reg);
        endproperty

        hmac_init_a: assert property(disable iff(!reset_n ||fv_zeroize)hmac_init_p);

        // If hmac_drbg en is set and the cntr is stable then hmac_init isn't set
         property no_hmac_init_less3cyc_p;
            ecc_dsa_ctrl.prog_instr.opcode.hmac_drbg_en && 
            (ecc_dsa_ctrl.prog_cntr == fv_prog_cntr_reg) &&
            !ecc_dsa_ctrl.error_flag_edge 
           ##1 (ecc_dsa_ctrl.prog_cntr == fv_prog_cntr_reg)
            |->
            !ecc_dsa_ctrl.hmac_init;
        endproperty

        no_hmac_init_less3cyc_a: assert property(disable iff(!reset_n ||fv_zeroize)no_hmac_init_less3cyc_p);


        // If subcomponent busy or prog_cntr is DSA_NOP or there isn't hmac_drbg_en then no hmac_init
        property no_hmac_init_p;
            (!ecc_dsa_ctrl.prog_instr.opcode.hmac_drbg_en && 
            (ecc_dsa_ctrl.prog_cntr != fv_prog_cntr_reg)) ||
            ecc_dsa_ctrl.error_flag_edge ||
            (ecc_dsa_ctrl.prog_cntr == DSA_NOP) ||
            (ecc_dsa_ctrl.subcomponent_busy)   
            |=>
            !ecc_dsa_ctrl.hmac_init ;
        endproperty

        no_hmac_init_a: assert property(disable iff(!reset_n ||fv_zeroize)no_hmac_init_p);


        // If sign subroutine is set the no subcomponent busy then hmac_mode is set
        property hmac_mode_p;
            (hwif_out.ECC_CTRL.CTRL.value == SIGN &&
            ecc_dsa_ctrl.prog_cntr == DSA_NOP ) &&
            !ecc_dsa_ctrl.subcomponent_busy 
            |=>
            ecc_dsa_ctrl.hmac_mode;
        endproperty
        
        hmac_mode_a: assert property(disable iff(!reset_n ||fv_zeroize || fv_error_set)hmac_mode_p);

        // Once hmac_mode is stays stable until keygen subroutine triggers
        property continue_hmac_mode_p;
            ecc_dsa_ctrl.hmac_mode
            |->
            (ecc_dsa_ctrl.hmac_mode until ecc_dsa_ctrl.keygen_process);  //no ovelapping condition and intial tick both cannot be occured
        endproperty
        continue_hmac_mode_a: assert property(disable iff(!reset_n ||fv_zeroize || fv_error_set)continue_hmac_mode_p);


        //If keygen subroutine is set then no hmac_mode
         property no_hmac_mode_p;
            (hwif_out.ECC_CTRL.CTRL.value == KEYGEN &&
            ecc_dsa_ctrl.prog_cntr == DSA_NOP ) &&
            !ecc_dsa_ctrl.subcomponent_busy 
            |=>
            !ecc_dsa_ctrl.hmac_mode;
        endproperty
        
        no_hmac_mode_a: assert property(disable iff(!reset_n ||fv_zeroize || fv_error_set)no_hmac_mode_p);

        // Once hmac_mode deasserted stays stable until new sign subroutine is triggered
        property continue_no_hmac_mode_p;
            !ecc_dsa_ctrl.hmac_mode
            |->
            (!ecc_dsa_ctrl.hmac_mode until ecc_dsa_ctrl.signing_process);
        endproperty
        continue_no_hmac_mode_a: assert property(disable iff(!reset_n ||fv_zeroize || fv_error_set)continue_no_hmac_mode_p);



        // Hmac inputs directly connected to the primary inputs
        property hmac_input_reg_p(word);
            ecc_dsa_ctrl.privkey_reg[word] == hwif_out.ECC_PRIVKEY_IN[(REG_NUM_DWORDS-1)-word].PRIVKEY_IN.value &&
            ecc_dsa_ctrl.seed_reg[word] == hwif_out.ECC_SEED[(REG_NUM_DWORDS-1)-word].SEED.value &&
            ecc_dsa_ctrl.nonce_reg[word] == hwif_out.ECC_NONCE[(REG_NUM_DWORDS-1)-word].NONCE.value &&
            ecc_dsa_ctrl.msg_reg[word] == hwif_out.ECC_MSG[(REG_NUM_DWORDS-1)-word].MSG.value &&
            ecc_dsa_ctrl.IV_reg[word] == hwif_out.ECC_IV[(REG_NUM_DWORDS-1)-word].IV.value;
        endproperty
         for(genvar i=0;i< REG_NUM_DWORDS;i++) begin
            hmac_input_reg_a: assert property(hmac_input_reg_p(i));
        end




//-------------------------------------------------------------------------//
//                          Scalar_blinding
//-------------------------------------------------------------------------//

        //If sca_en is enabled from seq then if no error flag and cyc_cnt=3 scalar_en is triggered until the 
        // prog_cntr advances
        property scalar_en_p;
            ecc_dsa_ctrl.prog_instr.opcode.sca_en && 
            (ecc_dsa_ctrl.prog_cntr == fv_prog_cntr_reg) &&
            !ecc_dsa_ctrl.error_flag_edge 
           ##1 (ecc_dsa_ctrl.prog_cntr != fv_prog_cntr_reg)
            |->
            ecc_dsa_ctrl.scalar_sca_en s_until_with (ecc_dsa_ctrl.prog_cntr != fv_prog_cntr_reg);
        endproperty

        scalar_en_a: assert property(disable iff(!reset_n ||fv_zeroize)scalar_en_p);



        // If sca_en is set and the cntr is stable then scalar_en isn't set
        property no_scalar_en_less3cyc_p;
            ecc_dsa_ctrl.prog_instr.opcode.sca_en && 
            (ecc_dsa_ctrl.prog_cntr == fv_prog_cntr_reg) &&
            !ecc_dsa_ctrl.error_flag_edge 
           ##1 (ecc_dsa_ctrl.prog_cntr == fv_prog_cntr_reg)
            |->
            !ecc_dsa_ctrl.scalar_sca_en;
        endproperty
        no_scalar_en_less3cyc_a: assert property(disable iff(!reset_n ||fv_zeroize)no_scalar_en_less3cyc_p);



        // If subcomponent busy or prog_cntr is DSA_NOP or there isn't sca_en then no scalar_en
        property no_scalar_en_p;
            (!ecc_dsa_ctrl.prog_instr.opcode.sca_en  && 
            (ecc_dsa_ctrl.prog_cntr != fv_prog_cntr_reg)) ||
            ecc_dsa_ctrl.error_flag_edge ||
            (ecc_dsa_ctrl.prog_cntr == DSA_NOP) ||
            (ecc_dsa_ctrl.subcomponent_busy)   
            |=>
            !ecc_dsa_ctrl.scalar_sca_en;
        endproperty
        no_scalar_en_a: assert property(disable iff(!reset_n ||fv_zeroize)no_scalar_en_p);


        // Input for scalar_blinding is from scalar_g_reg
        property scalar_in_reg_p;
            ecc_dsa_ctrl.prog_instr.opcode.sca_en &&
            !ecc_dsa_ctrl.verifying_process
            |=>
            ecc_dsa_ctrl.scalar_in_reg == $past(ecc_dsa_ctrl.scalar_G_reg);
        endproperty

        scalar_in_reg_a: assert property(disable iff(!reset_n ||fv_zeroize)scalar_in_reg_p);


        // Input stays stable if sca not enabled or in verifying process
        property stable_scalar_in_reg_p;
            !ecc_dsa_ctrl.prog_instr.opcode.sca_en ||
            ecc_dsa_ctrl.verifying_process
            |=>
            ecc_dsa_ctrl.scalar_in_reg == $past(ecc_dsa_ctrl.scalar_in_reg);
        endproperty

        stable_scalar_in_reg_a: assert property(disable iff(!reset_n ||fv_zeroize)stable_scalar_in_reg_p);

//-------------------------------------------------------------------------//
//                          Arithmetic unit
//-------------------------------------------------------------------------//

    // If no error and prog_cntr is not equal to DSA_NOP and none of the subcomponents are busy and cyc cnt ==3 then
    // pm_ctrl cmd is equal to dsa_seq opcode pm_cmd
    property pm_cmd_reg_p;
        !ecc_dsa_ctrl.error_flag_edge &&
        (ecc_dsa_ctrl.prog_cntr!= DSA_NOP) &&
        (!ecc_dsa_ctrl.subcomponent_busy) &&
        (ecc_dsa_ctrl.cycle_cnt==3) 
          |=>
        ecc_dsa_ctrl.pm_cmd_reg == $past(ecc_dsa_ctrl.prog_instr.opcode.pm_cmd);
    endproperty
        pm_cmd_reg_a: assert property(disable iff(!reset_n ||fv_zeroize)pm_cmd_reg_p);


        // If error is triggered or prog_cntr is equal to DSA_NOP or subcomponents are busy then pm_cmd ==0 
        property no_pm_cmd_reg_p;
             ecc_dsa_ctrl.error_flag_edge ||
            (ecc_dsa_ctrl.prog_cntr == DSA_NOP) ||
            (ecc_dsa_ctrl.subcomponent_busy) 
            |=>
            ecc_dsa_ctrl.pm_cmd_reg =='0;
        endproperty

        no_pm_cmd_reg_a: assert property(disable iff(!reset_n ||fv_zeroize)no_pm_cmd_reg_p);


    // If cmd is acceptable but cyc cnt is less than 3 then  pm_cmd stays stable
    property pm_cmd_when_cyc3less_p;
        !ecc_dsa_ctrl.error_flag_edge &&
        (ecc_dsa_ctrl.prog_cntr!= DSA_NOP) &&
        (!ecc_dsa_ctrl.subcomponent_busy) &&
        (ecc_dsa_ctrl.cycle_cnt < (CYC_CNT-1)) 
         |=>
        ecc_dsa_ctrl.pm_cmd_reg == $past(ecc_dsa_ctrl.pm_cmd_reg);
    endproperty

    pm_cmd_when_cyc3less_a: assert property(disable iff(!reset_n ||fv_zeroize)pm_cmd_when_cyc3less_p);


//-------------------------------------------------------------------------//
//                          Address Liveliness
//-------------------------------------------------------------------------//


    property wr_core_addr_eventually_in_memory_p;
    logic [DSA_OPR_ADDR_WIDTH-1 : 0] temp;
        ecc_dsa_ctrl.prog_instr.opcode == DSA_UOP_WR_CORE
        ##0 (1'b1, temp = ecc_dsa_ctrl.prog_instr.mem_addr)
        |->
        s_eventually(ecc_dsa_ctrl.ecc_arith_unit_i.ram_tdp_file_i.addrb == temp);
    endproperty

    wr_core_addr_eventually_in_memory_a: assert property(disable iff(!reset_n ||fv_zeroize)wr_core_addr_eventually_in_memory_p);





  //-------------------------------------------------------------------------//
  //                          write_reg to the core
  //-------------------------------------------------------------------------//

    

    property write_reg_p;
        ecc_dsa_ctrl.prog_instr.opcode == DSA_UOP_WR_CORE
        |->
        ecc_dsa_ctrl.write_reg == fv_write_reg;
    endproperty
    write_reg_a: assert property(write_reg_p);

    property write_reg_no_cmd_p;
        ecc_dsa_ctrl.prog_instr.opcode != DSA_UOP_WR_CORE &&
        ecc_dsa_ctrl.prog_instr.opcode != DSA_UOP_WR_SCALAR
        |->
        ecc_dsa_ctrl.write_reg == '0;
    endproperty
    write_reg_no_cmd_a:assert property(write_reg_no_cmd_p);

     property write_reg_sca_p;
        ecc_dsa_ctrl.prog_instr.opcode == DSA_UOP_WR_SCALAR
        |->
        ecc_dsa_ctrl.write_reg == fv_write_reg;
    endproperty
    write_reg_sca_a:assert property(write_reg_sca_p);

  //-------------------------------------------------------------------------//
  //                          read_reg from the core
  //-------------------------------------------------------------------------//
  

    property we_p;
        ecc_dsa_ctrl.prog_instr.opcode == DSA_UOP_RD_CORE && 
        ecc_dsa_ctrl.prog_cntr !=fv_prog_cntr_reg
        |->
        ecc_dsa_ctrl.hw_privkey_we     == fv_hw_privkey_we &&
        ecc_dsa_ctrl.hw_pubkeyx_we     == fv_hw_pubkeyx_we &&
        ecc_dsa_ctrl.hw_pubkeyy_we     == fv_hw_pubkeyy_we &&
        ecc_dsa_ctrl.hw_r_we           == fv_hw_r_we &&
        ecc_dsa_ctrl.hw_s_we           == fv_hw_s_we &&
        ecc_dsa_ctrl.hw_scalar_G_we    == fv_hw_scalar_G_we &&
        ecc_dsa_ctrl.hw_scalar_PK_we   == fv_hw_scalar_PK_we &&
        ecc_dsa_ctrl.hw_verify_r_we    == fv_hw_verify_r_we &&
        ecc_dsa_ctrl.hw_pk_chk_we      == fv_hw_pk_chk_we;
    endproperty

    we_a: assert property(disable iff (fv_error_set)we_p);

    property no_rd_we_p;
        (ecc_dsa_ctrl.prog_instr.opcode != DSA_UOP_RD_CORE) || 
        ecc_dsa_ctrl.prog_cntr ==fv_prog_cntr_reg
        |->
        ecc_dsa_ctrl.hw_privkey_we     == 0 &&
        ecc_dsa_ctrl.hw_pubkeyx_we     == 0 &&
        ecc_dsa_ctrl.hw_pubkeyy_we     == 0 &&
        ecc_dsa_ctrl.hw_r_we           == 0 &&
        ecc_dsa_ctrl.hw_s_we           == 0 &&
        ecc_dsa_ctrl.hw_scalar_G_we    == 0 &&
        ecc_dsa_ctrl.hw_scalar_PK_we   == 0 &&
        ecc_dsa_ctrl.hw_verify_r_we    == 0 &&
        ecc_dsa_ctrl.hw_pk_chk_we      == 0;
    endproperty
    no_rd_we_a: assert property(no_rd_we_p);


    property read_reg_r_p;
        fv_hw_r_we 
        |->
        (ecc_dsa_ctrl.read_reg != '0) &&
        (ecc_dsa_ctrl.read_reg < 384'hffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973);
    endproperty
    read_reg_r_a: assert property(disable iff(!reset_n || fv_zeroize || fv_error_set) read_reg_r_p);


    property read_reg_s_p;
        fv_hw_s_we 
        |->
        ecc_dsa_ctrl.read_reg != '0 &&
        ecc_dsa_ctrl.read_reg < 384'hffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973;
    endproperty
    read_reg_s_a: assert property(disable iff(!reset_n || fv_zeroize || fv_error_set) read_reg_s_p);


    property read_reg_ver_r_p;
        fv_hw_verify_r_we 
        |->
        ecc_dsa_ctrl.read_reg != '0 &&
        ecc_dsa_ctrl.read_reg < 384'hffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973;
    endproperty
    read_reg_ver_r_a: assert property(disable iff(!reset_n || fv_zeroize || fv_error_set) read_reg_ver_r_p);


    //-----------------------------------------------------------//
    // scalar_G_reg and scalar_G_sel
    //-----------------------------------------------------------//
    

        property hmac_drbg_in_scalar_G_reg_p;
            (ecc_dsa_ctrl.prog_cntr < DSA_VER_S) 
            |=>
            ecc_dsa_ctrl.scalar_G_reg == $past(ecc_dsa_ctrl.hmac_drbg_result) &&
            (ecc_dsa_ctrl.scalar_G_reg < 384'hffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973)
            ;
        endproperty

        hmac_drbg_in_scalar_G_reg_a: assert property(disable iff(!reset_n || fv_zeroize || fv_error_set) hmac_drbg_in_scalar_G_reg_p);


         property read_reg_scalar_G_reg_p;
            (ecc_dsa_ctrl.prog_cntr >= DSA_VER_S) &&
            fv_hw_scalar_G_we
            |=>
            ecc_dsa_ctrl.scalar_G_reg == $past(ecc_dsa_ctrl.read_reg)&&
            (ecc_dsa_ctrl.scalar_G_reg < 384'hffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973) &&
            (ecc_dsa_ctrl.scalar_G_reg >'0);
        endproperty

        read_reg_scalar_G_reg_a: assert property(disable iff(!reset_n || fv_zeroize || fv_error_set) read_reg_scalar_G_reg_p);

        property no_read_reg_scalar_G_reg_p;
            (ecc_dsa_ctrl.prog_cntr >= DSA_VER_S) &&
            !fv_hw_scalar_G_we
            |=>
            ecc_dsa_ctrl.scalar_G_reg == $past(ecc_dsa_ctrl.scalar_G_reg);
        endproperty

        no_read_reg_scalar_G_reg_a: assert property(disable iff(!reset_n || fv_zeroize || fv_error_set) no_read_reg_scalar_G_reg_p);

       


       //------------------------------------------------//
       // scalar_Pk_reg
       //------------------------------------------------//


       property we_scalar_pk_reg_p;
            fv_hw_scalar_PK_we
            |=>
            ecc_dsa_ctrl.scalar_PK_reg ==  $past(ecc_dsa_ctrl.read_reg) && 
            (ecc_dsa_ctrl.scalar_PK_reg < 384'hffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973) &&
            (ecc_dsa_ctrl.scalar_PK_reg >'0);
        endproperty

        we_scalar_pk_reg_a: assert property(disable iff(!reset_n || fv_zeroize || fv_error_set)we_scalar_pk_reg_p);

        property no_we_scalar_pk_reg_p;
            !fv_hw_scalar_PK_we
            |=>
            ecc_dsa_ctrl.scalar_PK_reg ==  $past(ecc_dsa_ctrl.scalar_PK_reg);
        endproperty

        no_we_scalar_pk_reg_a: assert property(disable iff(!reset_n || fv_zeroize || fv_error_set)no_we_scalar_pk_reg_p);

 
     //------------------------------------------------//
       // pk_chk_reg
       //------------------------------------------------//

       property pk_chk_reg_p;
        fv_hw_pk_chk_we
        |=>
        ecc_dsa_ctrl.pk_chk_reg == $past(ecc_dsa_ctrl.read_reg);
    endproperty
    pk_chk_reg_a: assert property(disable iff(!reset_n || fv_zeroize || fv_error_set)pk_chk_reg_p);

      property no_pk_chk_reg_p;
        !fv_hw_pk_chk_we
        |=>
        ecc_dsa_ctrl.pk_chk_reg == $past(ecc_dsa_ctrl.pk_chk_reg);
    endproperty
    no_pk_chk_reg_a: assert property(disable iff(!reset_n || fv_zeroize)no_pk_chk_reg_p);

endmodule


bind ecc_dsa_ctrl fv_ecc_dsa_ctrl_m fv_ecc_dsa_ctrl (
        .clk(clk),
        .reset_n(reset_n),
        .cptra_pwrgood(cptra_pwrgood),

        .hwif_out(hwif_out),
        .hwif_in(hwif_in),

        .kv_read(kv_read),
        .kv_rd_resp(kv_rd_resp),
        .kv_write(kv_write),
        .kv_wr_resp(kv_wr_resp),
        .pcr_signing_data(pcr_signing_data),
        
        .error_intr(error_intr),
        .notif_intr(notif_intr),
        .debugUnlock_or_scan_mode_switch(debugUnlock_or_scan_mode_switch)
    );