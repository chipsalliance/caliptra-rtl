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
module fv_ecc_pm_ctrl_abstract
    import ecc_pm_uop_pkg::*;
    #(
    parameter REG_SIZE      = 384,
    parameter RND_SIZE      = 192,
    parameter INSTR_SIZE    = 24,
    parameter MULT_DLY      = 38,
    parameter ADD_DLY       = 1,
    parameter Secp384_MONT_COUNT = 384,
    parameter Secp384_SCA_MONT_COUNT = 576
    )
    (
    // Clock and reset.
    input  wire           clk,
    input  wire           rst_n,


    // from arith_unit
    input  wire  [2  :   0]                 ecc_cmd_i,
    input  wire                             sca_en_i,
    input  wire                             digit_i,
    input pm_instr_struct_t                instr_o,
    input logic                            req_digit_o,
    input wire                             busy_o
);

    ///////////////////////////////////////////////////////////////////
    // All the sequences latency from start to end
    // The function dly, has the arguments as no. of mult, no. of add+sub
    // no. of store operations, rest operations in the sequence
    ///////////////////////////////////////////////////////////////////

    localparam CHK_DLY = dly(6,6,3,3,4);
    localparam PM_INT_G_DLY = dly(3,3,0,0,0);
    localparam PM_INT_DLY = dly(0,0,3,3,4);
    localparam PA_DLY = dly(17,17,23,23,0);
    localparam PD_DLY = dly(17,17,23,23,4);
    localparam CONV_VER0_P1_DLY = dly(4,4,0,0,4);
    localparam INV_DLY = dly(519,519,1,1,0);
    localparam SIGN0_DLY = dly(7,7,5,5,4);
    localparam INVQ_DLY = dly(519,519,1,1,4);
    localparam SIGN1_DLY = dly(3,3,1,1,4);
    localparam VER0_P0_DLY = dly(3,3,0,0,4);
    localparam VER_ST_DLY = dly(0,0,3,3,0);
    localparam PM_INT_PK_DLY = dly(2,2,1,1,0);
    localparam VER_PA_DLY = dly(17,17,24,24,0);

    localparam PIP_DLY = 3; // The pipeline delay from having the data in instr_o from prog_instr





    //////////////////////////////////////////
    //Delay computation                     //
    //////////////////////////////////////////

     function logic [24:0] dly(input logic[11:0] num_mul,input logic[11:0] st_mul,input logic[11:0] num_add_sub,input logic[11:0] st_add_sub,input logic[11:0] rest);
         logic [24:0] fv_total_mult_dly;
         logic [24:0] fv_total_add_sub_dly;
         fv_total_mult_dly = (num_mul*(MULT_DLY+2))+(st_mul);
         fv_total_add_sub_dly = (num_add_sub*(ADD_DLY+2))+(st_add_sub);
         return(fv_total_mult_dly+fv_total_add_sub_dly+rest-1);
     endfunction




 default clocking default_clk @(posedge clk); endclocking

        sequence reset_sequence;
          !rst_n ##1 rst_n;
        endsequence 


    ////////////////////////////////////////////
    // reset property, when reset out and reg //
    // are zero                               //
    ////////////////////////////////////////////

        property reset_p;
            $past(!rst_n)  
            |->
            ecc_pm_ctrl.prog_cntr == NOP &&
            ecc_pm_ctrl.mont_cntr   <= '0 &&
            ecc_pm_ctrl.stall_cntr  <= '0 &&
            ecc_pm_ctrl.stalled     <= '0 &&
            ecc_pm_ctrl.mont_ladder <= '0 &&
            ecc_pm_ctrl.ecc_cmd_reg <= '0 &&
            instr_o == '0 &&
            req_digit_o == '0 &&
            busy_o == 0;
        endproperty

        reset_a : assert property(reset_p);


        //--------------------------------//
        // Unabstracted counter properties//
        //-------------------------------//

        // Validates once the check public key cmd is set then the sequence is triggered and finally ends in NOP
        property check_point_p(delay);
            ecc_cmd_i == CHK_PK_CMD &&
            ecc_pm_ctrl.prog_cntr == NOP
            |=>
            ecc_pm_ctrl.prog_cntr == CHK_PK_S 
            ##delay ecc_pm_ctrl.prog_cntr == CHK_PK_E 
            ##1 ecc_pm_ctrl.prog_cntr == NOP; 
        endproperty
        check_point_a: assert property(disable iff(!rst_n) check_point_p(CHK_DLY));


        // validates once the cmd is set initally it would traverse through PM_INIT_G_S and PM_INIT_S
         property pm_init_g_s_to_pm_init_s_p(cmd,delay);
            ecc_cmd_i == cmd &&
            ecc_pm_ctrl.prog_cntr == NOP
            |=>
            ecc_pm_ctrl.prog_cntr == PM_INIT_G_S   &&     // Initialise R1 with G
            ecc_pm_ctrl.mont_cntr == $past((sca_en_i)?  ecc_pm_ctrl.Secp384_SCA_MONT_COUNT : ecc_pm_ctrl.Secp384_MONT_COUNT)
            ##delay ecc_pm_ctrl.prog_cntr == PM_INIT_G_E
            ##1 ecc_pm_ctrl.prog_cntr == PM_INIT_S;      // Initialise R0 with (0:1:0) 
        endproperty
        keygen_stage0_a: assert property(disable iff(!rst_n) pm_init_g_s_to_pm_init_s_p(KEYGEN_CMD,PM_INT_G_DLY));
        signing_stage0_a: assert property(disable iff(!rst_n) pm_init_g_s_to_pm_init_s_p(SIGN_CMD,PM_INT_G_DLY));
        
        // validates if cmd sequence is ongoing then it would traverse from PM_INIT_S till PA_S
        property pm_init_s_to_pa_s_p(cmd,delay);
            ecc_pm_ctrl.ecc_cmd_reg == cmd &&
            ecc_pm_ctrl.prog_cntr == PM_INIT_S
            |->
            ##delay ecc_pm_ctrl.prog_cntr == PM_INIT_E
            ##1 ecc_pm_ctrl.prog_cntr == PA_S &&
            ecc_pm_ctrl.mont_cntr == $past(ecc_pm_ctrl.mont_cntr)-1;           // Point add
        endproperty
        keygen_stage1_a: assert property(disable iff(!rst_n) pm_init_s_to_pa_s_p(KEYGEN_CMD,PM_INT_DLY));
        signing_stage1_a: assert property(disable iff(!rst_n) pm_init_s_to_pa_s_p(SIGN_CMD,PM_INT_DLY));
        verify_part1_stage1_a: assert property(disable iff(!rst_n) pm_init_s_to_pa_s_p(VER_PART1_CMD,PM_INT_DLY));
        verify_part2_stage1_a: assert property(disable iff(!rst_n) pm_init_s_to_pa_s_p(VER_PART2_CMD,PM_INT_DLY));



        //validates if cmd sequence is ongoing then it would traverse from PA_S to PD_S
        property pa_s_to_pd_s_p(cmd,delay);
            ecc_pm_ctrl.ecc_cmd_reg == cmd &&
            ecc_pm_ctrl.prog_cntr == PA_S
            |->
            ##delay ecc_pm_ctrl.prog_cntr == PA_E 
            ##1 ecc_pm_ctrl.prog_cntr == PD_S; 
        endproperty
        keygen_stage1_1_a: assert property(disable iff(!rst_n) pa_s_to_pd_s_p(KEYGEN_CMD,PA_DLY));
        signing_stage1_1_a:  assert property(disable iff(!rst_n) pa_s_to_pd_s_p(SIGN_CMD,PA_DLY));
        verify_part1_stage1_1_a: assert property(disable iff(!rst_n) pa_s_to_pd_s_p(VER_PART1_CMD,PA_DLY));
        verify_part2_stage1_1_a: assert property(disable iff(!rst_n) pa_s_to_pd_s_p(VER_PART2_CMD,PA_DLY));



        //validates if cmd sequence is ongoing then it would traverse from PD_S to PD_E
         property pd_s_to_pd_e_p(cmd,delay);
            ecc_pm_ctrl.ecc_cmd_reg == cmd &&
            ecc_pm_ctrl.prog_cntr == PD_S 
            |->
            ##delay ecc_pm_ctrl.prog_cntr == PD_E; 
        endproperty
         keygen_stage2_1_a: assert property(disable iff(!rst_n) pd_s_to_pd_e_p(KEYGEN_CMD,PD_DLY));
         signing_stage2_1_a: assert property(disable iff(!rst_n) pd_s_to_pd_e_p(SIGN_CMD,PD_DLY));
         verify_part1_stage2_1_a: assert property(disable iff(!rst_n) pd_s_to_pd_e_p(VER_PART1_CMD,PD_DLY));
         verify_part2_stage2_1_a: assert property(disable iff(!rst_n) pd_s_to_pd_e_p(VER_PART2_CMD,PD_DLY));


        //validates if cmd sequence is ongoing then it would traverse from PD_E to INV_S when the mont_cntr is zero
        property pd_e_to_invs_p(cmd);
            ecc_pm_ctrl.ecc_cmd_reg == cmd &&
            ecc_pm_ctrl.prog_cntr == PD_E &&
            ecc_pm_ctrl.mont_cntr == 0
            |->
            ##1 ecc_pm_ctrl.prog_cntr == INV_S; 
        endproperty
        keygen_stage2_a: assert property(disable iff(!rst_n) pd_e_to_invs_p(KEYGEN_CMD));
        signing_stage2_a: assert property(disable iff(!rst_n) pd_e_to_invs_p(SIGN_CMD));

        // validates if cmd sequence is ongoing then it would traverse from PD_E to PA_S when the mont_cntr is not zero
        property pd_e_to_pa_s_p(cmd);
            ecc_pm_ctrl.ecc_cmd_reg == cmd &&
            ecc_pm_ctrl.prog_cntr == PD_E &&
            ecc_pm_ctrl.mont_cntr != 0
            |->
            ##1 ecc_pm_ctrl.prog_cntr == PA_S &&
            ecc_pm_ctrl.mont_cntr == $past(ecc_pm_ctrl.mont_cntr)-1; 
        endproperty
        keygen_stage2_loop_a: assert property(disable iff(!rst_n) pd_e_to_pa_s_p(KEYGEN_CMD));
        signing_stage2_loop_a: assert property(disable iff(!rst_n) pd_e_to_pa_s_p(SIGN_CMD));
        verify_part1_stage2_loop_a: assert property(disable iff(!rst_n) pd_e_to_pa_s_p(VER_PART1_CMD));
        verify_part2_stage2_loop_a: assert property(disable iff(!rst_n) pd_e_to_pa_s_p(VER_PART2_CMD));

    //validates if cmd sequence is ongoing then it would traverse from INV_E to CONV_S
         property inve_to_convs_p(cmd);
            ecc_pm_ctrl.ecc_cmd_reg == cmd &&
            ecc_pm_ctrl.prog_cntr == INV_E[*(MULT_DLY+2)]      //[*3] for mult delay 1
             |->
            ##1 ecc_pm_ctrl.prog_cntr == CONV_S; 
        endproperty
        keygen_stage3_a: assert property(disable iff(!rst_n) inve_to_convs_p(KEYGEN_CMD));
        signing_stage3_a: assert property(disable iff(!rst_n) inve_to_convs_p(SIGN_CMD));
        verify_part2_stage3_2_a: assert property(disable iff(!rst_n) inve_to_convs_p(VER_PART2_CMD));
         
    //validates if cmd sequence is ongoing then it would traverse from INV_S to INV_E
         property invs_to_inve_p(cmd,delay);
            ecc_pm_ctrl.ecc_cmd_reg == cmd &&
            ecc_pm_ctrl.prog_cntr == INV_S      //[*3] for mult delay 1
             |->
            ##delay ecc_pm_ctrl.prog_cntr == INV_E; 
        endproperty
        keygen_stage3_1_a: assert property(disable iff(!rst_n) invs_to_inve_p(KEYGEN_CMD,INV_DLY));
        signing_stage3_1_a: assert property(disable iff(!rst_n) invs_to_inve_p(SIGN_CMD,INV_DLY));
        verify_part2_stage3_1_a: assert property(disable iff(!rst_n) invs_to_inve_p(VER_PART2_CMD,INV_DLY));


    //validates if cmd sequence is ongoing then it would traverse from CONV_S to NOP
        property convs_to_nop(cmd,delay);
            ecc_pm_ctrl.ecc_cmd_reg == cmd &&
            ecc_pm_ctrl.prog_cntr == CONV_S
            |->
           ##delay ecc_pm_ctrl.prog_cntr == CONV_E //##19 mult delay 1
            ##1 ecc_pm_ctrl.prog_cntr == NOP;
        endproperty
        keygen_stage4_a: assert property(disable iff(!rst_n) convs_to_nop(KEYGEN_CMD,CONV_VER0_P1_DLY));
        verify_part2_stage4_a: assert property(disable iff(!rst_n) convs_to_nop(VER_PART2_CMD,CONV_VER0_P1_DLY));



/////////////////////////////////////////////////////////////////////////////////////
// ---------------------------------BEGIN----------------------------------------- //
// Checking the counter integrity that the sequence is performed one after another //
/////////////////////////////////////////////////////////////////////////////////////

    logic  [PROG_ADDR_W-1  : 0] counter_keygen_a;
    logic  [PROG_ADDR_W-1  : 0] counter_keygen_b;
    logic trigger_counter_keygen_a_reg;
    logic trigger_counter_keygen_b_reg; 
    logic triggered_counter_keygen_a;
    logic triggered_counter_keygen_b;

        counter_nonreachable_values: assume property (disable iff(!rst_n)counter_nonreachable_values_p);
        property counter_nonreachable_values_p;
            counter_keygen_a != PM_INIT_G_E+1 && counter_keygen_b != PM_INIT_G_E+1 &&
            counter_keygen_a != PM_INIT_E+1 && counter_keygen_b != PM_INIT_E+1 &&
            counter_keygen_a != INV_E+1 && counter_keygen_b != INV_E+1 &&
            counter_keygen_a != PA_E+1 && counter_keygen_b != PA_E+1 &&
            counter_keygen_a != PD_E+1 && counter_keygen_b != PD_E+1 &&
            counter_keygen_a != INV_E+1 && counter_keygen_b != INV_E+1;
        endproperty

        counter_keygen_a_assume: assume property(disable iff(!rst_n) (counter_keygen_a >=PM_INIT_G_S) && (counter_keygen_a <=CONV_E) && $stable(counter_keygen_a));
        counter_keygen_b_assume: assume property(disable iff(!rst_n) (counter_keygen_b <=CONV_E) && (counter_keygen_b > counter_keygen_a) && $stable(counter_keygen_b));
        
        assign trigger_counter_keygen_a_reg = (ecc_pm_ctrl.prog_cntr==counter_keygen_a);
        assign trigger_counter_keygen_b_reg = (ecc_pm_ctrl.prog_cntr==counter_keygen_b);
        always_ff @(posedge clk, negedge rst_n) begin
            if(!rst_n) begin
                triggered_counter_keygen_a <= '0;
                triggered_counter_keygen_b <= '0;
            end
            else begin
                if(ecc_pm_ctrl.ecc_cmd_reg==KEYGEN_CMD) begin
                    if(trigger_counter_keygen_a_reg) begin
                        triggered_counter_keygen_a <= 1;
                    end
                    if(trigger_counter_keygen_b_reg) begin
                        triggered_counter_keygen_b <= 1;
                    end
                end
            end
        end

        property liveness_p(cmd,trigered);
            ecc_cmd_i == cmd &&
            ecc_pm_ctrl.prog_cntr == NOP
            |->
            s_eventually(trigered);
        endproperty
    counter_keygen_a_liveness_a: assert property(disable iff(!rst_n) liveness_p(KEYGEN_CMD,triggered_counter_keygen_a));
    counter_keygen_b_liveness_a: assert property(disable iff(!rst_n) liveness_p(KEYGEN_CMD,triggered_counter_keygen_b));

    //property  to order_check
         property order_check_p(triggered_a,triggered_b);
           triggered_b
           |=>
           $past(triggered_a);
        endproperty
    keygen_order_check_a: assert property(disable iff(!rst_n) order_check_p(triggered_counter_keygen_a,triggered_counter_keygen_b));
    
/////////////////////////////////////////////////////////////////////////////////////
// ------------------------------------END---------------------------------------- //
/////////////////////////////////////////////////////////////////////////////////////

        //------------------------------------//
        // Signing staging
        //------------------------------------//


        //validates if signing sequence is ongoing then it would traverse from CONV_S  till INVq_S
         property signing_stage3_2_p(delay1,delay2);
            ecc_pm_ctrl.ecc_cmd_reg == SIGN_CMD &&
            ecc_pm_ctrl.prog_cntr == CONV_S  
            |->
            ##delay1 ecc_pm_ctrl.prog_cntr == CONV_E           // conversion to affine r compute done
            ##1 ecc_pm_ctrl.prog_cntr == SIGN0_S           // (d + r (privKey-d)),((h-d) + r.d) 
            ##delay2 ecc_pm_ctrl.prog_cntr == SIGN0_E
            ##1 ecc_pm_ctrl.prog_cntr == INVq_S;            // k inverse ##52 mult delay 1
        endproperty
        signing_stage3_2_a: assert property(disable iff(!rst_n) signing_stage3_2_p(CONV_VER0_P1_DLY,SIGN0_DLY));


         //validates if signing sequence is ongoing then it would traverse from INVq_S  till INVq_E
         property signing_stage4_1_p(delay);
            ecc_pm_ctrl.ecc_cmd_reg == SIGN_CMD &&
            ecc_pm_ctrl.prog_cntr == INVq_S 
            |->
            ##delay ecc_pm_ctrl.prog_cntr == INVq_E;            
           endproperty
        signing_stage4_1_a: assert property(disable iff(!rst_n) signing_stage4_1_p(INVQ_DLY));


        //validates if signing sequence is ongoing then it would traverse from INVq_E till NOP
         property signing_stage4_p(delay);
            ecc_pm_ctrl.ecc_cmd_reg == SIGN_CMD &&
            ecc_pm_ctrl.prog_cntr == INVq_E
            |->
            ##1 ecc_pm_ctrl.prog_cntr == SIGN1_S           // final value s [k^-1((h-d) + r (privKey-d))] + [k^-1(d + r.d)] mod q
            ##delay ecc_pm_ctrl.prog_cntr == SIGN1_E
            ##1 ecc_pm_ctrl.prog_cntr == NOP ;              // ##20 mult delay 1
        endproperty
        signing_stage4_a: assert property(disable iff(!rst_n) signing_stage4_p(SIGN1_DLY));



/////////////////////////////////////////////////////////////////////////////////////
// ---------------------------------BEGIN----------------------------------------- //
// Checking the counter integrity that the sequence is performed one after another //
/////////////////////////////////////////////////////////////////////////////////////

    logic  [PROG_ADDR_W-1  : 0] counter_sign_a; 
    logic  [PROG_ADDR_W-1  : 0] counter_sign_b;
    logic trigger_counter_sign_a_reg;
    logic trigger_counter_sign_b_reg;
    logic triggered_counter_sign_a;
    logic triggered_counter_sign_b;

        counter_nonreachable_values_in_sign: assume property (disable iff(!rst_n)counter_nonreachable_values_in_sign_p);
        property counter_nonreachable_values_in_sign_p;
            counter_sign_a != PM_INIT_G_E+1 && counter_sign_b != PM_INIT_G_E+1 &&
            counter_sign_a != PM_INIT_E+1 && counter_sign_b != PM_INIT_E+1 &&
            counter_sign_a != INV_E+1 && counter_sign_b != INV_E+1 &&
            counter_sign_a != PA_E+1 && counter_sign_b != PA_E+1 &&
            counter_sign_a != PD_E+1 && counter_sign_b != PD_E+1 &&
            counter_sign_a != INV_E+1 && counter_sign_b != INV_E+1 &&
            counter_sign_a != CONV_E+1 && counter_sign_b != CONV_E+1 &&
            counter_sign_a != SIGN0_E+1 && counter_sign_b != SIGN0_E+1 &&
            counter_sign_a != INVq_E+1 && counter_sign_b != INVq_E+1 
            ;
        endproperty

        counter_sign_a_assume: assume property(disable iff(!rst_n) (counter_sign_a >=PM_INIT_G_S) && (counter_sign_a <=SIGN1_E) && $stable(counter_sign_a));
        counter_sign_b_assume: assume property(disable iff(!rst_n) (counter_sign_b <=SIGN1_E) && (counter_sign_b > counter_sign_a) && $stable(counter_sign_b));
        
        assign trigger_counter_sign_a_reg = (ecc_pm_ctrl.prog_cntr==counter_sign_a);
        assign trigger_counter_sign_b_reg = (ecc_pm_ctrl.prog_cntr==counter_sign_b);
        always_ff @(posedge clk, negedge rst_n) begin
            if(!rst_n) begin
                triggered_counter_sign_a <= '0;
                triggered_counter_sign_b <= '0;
            end
            else begin
                if(ecc_pm_ctrl.ecc_cmd_reg==SIGN_CMD) begin
                    if(trigger_counter_sign_a_reg) begin
                        triggered_counter_sign_a <= 1;
                    end
                    if(trigger_counter_sign_b_reg) begin
                        triggered_counter_sign_b <= 1;
                    end
                end
            end
        end

    counter_sign_a_liveness_a: assert property(disable iff(!rst_n) liveness_p(SIGN_CMD,triggered_counter_sign_a));

    counter_sign_b_liveness_a: assert property(disable iff(!rst_n) liveness_p(SIGN_CMD,triggered_counter_sign_b));

    order_check_sign_a: assert property(disable iff(!rst_n) order_check_p(triggered_counter_sign_a,triggered_counter_sign_b));
    



/////////////////////////////////////////////////////////////////////////////////////
// ------------------------------------END---------------------------------------- //
/////////////////////////////////////////////////////////////////////////////////////


        //--------------------------------------//
        // Verifying staging
        //-------------------------------------//

        //Validates once the VER_PART0_CMD is triggered then it would traverse itll INVq_S
         property verify_part0_stage0_p(delay);
            ecc_cmd_i == VER_PART0_CMD &&
            ecc_pm_ctrl.prog_cntr == NOP
            |=>
            ecc_pm_ctrl.prog_cntr == VER0_P0_S         //convert h,r,s inputs to mont
            ##delay ecc_pm_ctrl.prog_cntr == VER0_P0_E
            ##1 ecc_pm_ctrl.prog_cntr == INVq_S;         // compute s inverse         //##16 mult delay 1   
        endproperty
        verify_part0_stage0_a: assert property(disable iff(!rst_n) verify_part0_stage0_p(VER0_P0_DLY));


        //validates if the verify part0 is ongoing then it would traverse from INVq_s to INVq_E
        property verify_part0_stage1_1_p(delay);
            ecc_pm_ctrl.ecc_cmd_reg == VER_PART0_CMD &&
            ecc_pm_ctrl.prog_cntr == INVq_S
            |->
            ##delay ecc_pm_ctrl.prog_cntr == INVq_E;
         endproperty
        verify_part0_stage1_1_a: assert property(disable iff(!rst_n) verify_part0_stage1_1_p(INVQ_DLY));


        //validates if the verify part0 is ongoing then finally it would end in NOP
         property verify_part0_stage1_p(delay);
            ecc_pm_ctrl.ecc_cmd_reg == VER_PART0_CMD &&
            ecc_pm_ctrl.prog_cntr == INVq_E
            |->
            ##1 ecc_pm_ctrl.prog_cntr == VER0_P1_S      // compute h*s_inv and r*s_inv
            ##delay ecc_pm_ctrl.prog_cntr == VER0_P1_E
            ##1 ecc_pm_ctrl.prog_cntr == NOP;          // ##20 mult delay 1
         endproperty
        verify_part0_stage1_a: assert property(disable iff(!rst_n) verify_part0_stage1_p(CONV_VER0_P1_DLY));



/////////////////////////////////////////////////////////////////////////////////////
// ---------------------------------BEGIN----------------------------------------- //
// Checking the counter integrity that the sequence is performed one after another //
/////////////////////////////////////////////////////////////////////////////////////

    logic  [PROG_ADDR_W-1  : 0] counter_ver_p0_a; 
    logic  [PROG_ADDR_W-1  : 0] counter_ver_p0_b;
    logic  [PROG_ADDR_W-1  : 0] counter_ver_p0_c;
    logic  [PROG_ADDR_W-1  : 0] counter_ver_p0_a_1; 
    logic  [PROG_ADDR_W-1  : 0] counter_ver_p0_b_1;
    logic  [PROG_ADDR_W-1  : 0] counter_ver_p0_c_1;
    logic trigger_counter_ver_p0_a_reg;
    logic trigger_counter_ver_p0_b_reg;
    logic trigger_counter_ver_p0_c_reg; 
    logic trigger_counter_ver_p0_a_1_reg;
    logic trigger_counter_ver_p0_b_1_reg;
    logic trigger_counter_ver_p0_c_1_reg;
    logic triggered_counter_ver_p0_a;
    logic triggered_counter_ver_p0_b;
    logic triggered_counter_ver_p0_c;
    logic triggered_counter_ver_p0_a_1;
    logic triggered_counter_ver_p0_b_1;
    logic triggered_counter_ver_p0_c_1;

        
       
        counter_ver_p0_a_assume: assume property(disable iff(!rst_n) (counter_ver_p0_a <=VER0_P0_E) && (counter_ver_p0_a >=VER0_P0_S) && $stable(counter_ver_p0_a));
        counter_ver_p0_a_1_assume: assume property(disable iff(!rst_n) (counter_ver_p0_a_1 <=VER0_P0_E) && (counter_ver_p0_a_1 > counter_ver_p0_a) && $stable(counter_ver_p0_a_1));
        counter_ver_p0_b_assume: assume property(disable iff(!rst_n) (counter_ver_p0_b >=INVq_S) && (counter_ver_p0_b <=INVq_E) && $stable(counter_ver_p0_b));
        counter_ver_p0_b_1_assume: assume property(disable iff(!rst_n) (counter_ver_p0_b_1 >counter_ver_p0_b) && (counter_ver_p0_b_1 <=INVq_E) && $stable(counter_ver_p0_b_1));
        counter_ver_p0_c_assume: assume property(disable iff(!rst_n) (counter_ver_p0_c <=VER0_P1_E) && ((counter_ver_p0_c >=VER0_P1_S)) && $stable(counter_ver_p0_c));
        counter_ver_p0_c_1_assume: assume property(disable iff(!rst_n) (counter_ver_p0_c_1 <=VER0_P1_E) && ((counter_ver_p0_c_1 > counter_ver_p0_c)) && $stable(counter_ver_p0_c_1));
        
        assign trigger_counter_ver_p0_a_reg = (ecc_pm_ctrl.prog_cntr==counter_ver_p0_a);
        assign trigger_counter_ver_p0_b_reg = (ecc_pm_ctrl.prog_cntr==counter_ver_p0_b);
        assign trigger_counter_ver_p0_c_reg = (ecc_pm_ctrl.prog_cntr==counter_ver_p0_c);
        assign trigger_counter_ver_p0_a_1_reg = (ecc_pm_ctrl.prog_cntr==counter_ver_p0_a_1);
        assign trigger_counter_ver_p0_b_1_reg = (ecc_pm_ctrl.prog_cntr==counter_ver_p0_b_1);
        assign trigger_counter_ver_p0_c_1_reg = (ecc_pm_ctrl.prog_cntr==counter_ver_p0_c_1);

        always_ff @(posedge clk, negedge rst_n) begin
            if(!rst_n) begin
                triggered_counter_ver_p0_a <= '0;
                triggered_counter_ver_p0_b <= '0;
                triggered_counter_ver_p0_c <= '0;
                triggered_counter_ver_p0_a_1 <= '0;
                triggered_counter_ver_p0_b_1 <= '0;
                triggered_counter_ver_p0_c_1 <= '0;
            end
            else begin
                if(ecc_pm_ctrl.ecc_cmd_reg==VER_PART0_CMD) begin
                    if(trigger_counter_ver_p0_a_reg) begin
                        triggered_counter_ver_p0_a <= 1;
                    end
                    if(trigger_counter_ver_p0_b_reg) begin
                        triggered_counter_ver_p0_b <= 1;
                    end
                    if(trigger_counter_ver_p0_c_reg) begin
                        triggered_counter_ver_p0_c <= 1;
                    end
                    if(trigger_counter_ver_p0_a_1_reg) begin
                        triggered_counter_ver_p0_a_1 <= 1;
                    end
                    if(trigger_counter_ver_p0_b_1_reg) begin
                        triggered_counter_ver_p0_b_1 <= 1;
                    end
                    if(trigger_counter_ver_p0_c_1_reg) begin
                        triggered_counter_ver_p0_c_1 <= 1;
                    end
                end
            end
        end

     
    counter_ver_p0_a_liveness_a: assert property(disable iff(!rst_n) liveness_p(VER_PART0_CMD,triggered_counter_ver_p0_a));

    counter_ver_p0_b_liveness_a: assert property(disable iff(!rst_n) liveness_p(VER_PART0_CMD,triggered_counter_ver_p0_b));

    counter_ver_p0_c_liveness_a: assert property(disable iff(!rst_n) liveness_p(VER_PART0_CMD,triggered_counter_ver_p0_c));

    counter_intrnl_ver0_p0_s_a: assert property(disable iff(!rst_n) order_check_p(triggered_counter_ver_p0_a,triggered_counter_ver_p0_a_1));
   
    counter_staging0_ver_p0_a: assert property(disable iff(!rst_n) order_check_p((triggered_counter_ver_p0_a & triggered_counter_ver_p0_a_1 & triggered_counter_ver_p0_b),triggered_counter_ver_p0_b_1));
    
    counter_staging1_ver_p0_a: assert property(disable iff(!rst_n) order_check_p((triggered_counter_ver_p0_a & triggered_counter_ver_p0_b & triggered_counter_ver_p0_c & triggered_counter_ver_p0_a_1 & triggered_counter_ver_p0_b_1),triggered_counter_ver_p0_c_1));
    
     


/////////////////////////////////////////////////////////////////////////////////////
// ------------------------------------END---------------------------------------- //
/////////////////////////////////////////////////////////////////////////////////////




        //validates once the verify part1 is set initally it would traverse through PM_INIT_G_S and PM_INIT_S
        property verify_part1_stage0_p(delay);
            ecc_cmd_i == VER_PART1_CMD &&
            ecc_pm_ctrl.prog_cntr == NOP
            |=>
            ecc_pm_ctrl.prog_cntr == PM_INIT_G_S &&      // Initialise R1 with G
            ecc_pm_ctrl.mont_cntr == ecc_pm_ctrl.Secp384_MONT_COUNT
            ##delay ecc_pm_ctrl.prog_cntr == PM_INIT_G_E
            ##1 ecc_pm_ctrl.prog_cntr == PM_INIT_S;      // Initialise R0 with (0:1:0)
        endproperty
        verify_part1_stage0_a: assert property(disable iff(!rst_n) verify_part1_stage0_p(PM_INT_G_DLY));


        //validates if verify part1 sequence is ongoing then it would traverse from PD_E to NOP when the mont_cntr is zero
         property verify_part1_stage2_p;
            ecc_pm_ctrl.ecc_cmd_reg == VER_PART1_CMD &&
            ecc_pm_ctrl.prog_cntr == PD_E &&
            ecc_pm_ctrl.mont_cntr == 0
            |->
            ##1 ecc_pm_ctrl.prog_cntr == NOP;           //(h*s^-1)*G
        endproperty
        verify_part1_stage2_a: assert property(disable iff(!rst_n) verify_part1_stage2_p);


/////////////////////////////////////////////////////////////////////////////////////
// ---------------------------------BEGIN----------------------------------------- //
// Checking the counter integrity that the sequence is performed one after another //
/////////////////////////////////////////////////////////////////////////////////////

    logic  [PROG_ADDR_W-1  : 0] counter_ver_p1_a; 
    logic  [PROG_ADDR_W-1  : 0] counter_ver_p1_b;
    logic trigger_counter_ver_p1_a_reg;
    logic trigger_counter_ver_p1_b_reg; 
    logic triggered_counter_ver_p1_a;
    logic triggered_counter_ver_p1_b;

        counter_nonreachable_values_in_ver_p1: assume property (disable iff(!rst_n)counter_nonreachable_values_in_ver_p1_p);
        property counter_nonreachable_values_in_ver_p1_p;
            counter_ver_p1_a != PM_INIT_G_E+1 && counter_ver_p1_b != PM_INIT_G_E+1 &&
            counter_ver_p1_a != PM_INIT_E+1 && counter_ver_p1_b != PM_INIT_E+1 &&
            counter_ver_p1_a != INV_E+1 && counter_ver_p1_b != INV_E+1 &&
            counter_ver_p1_a != PA_E+1 && counter_ver_p1_b != PA_E+1;
      
        endproperty

        counter_ver_p1_a_assume: assume property(disable iff(!rst_n) (counter_ver_p1_a >=PM_INIT_G_S) && (counter_ver_p1_a <=PD_E) && $stable(counter_ver_p1_a));
        counter_ver_p1_b_assume: assume property(disable iff(!rst_n) (counter_ver_p1_b <=PD_E) && (counter_ver_p1_b > counter_ver_p1_a) && $stable(counter_ver_p1_b));
        
        assign trigger_counter_ver_p1_a_reg = (ecc_pm_ctrl.prog_cntr==counter_ver_p1_a);
        assign trigger_counter_ver_p1_b_reg = (ecc_pm_ctrl.prog_cntr==counter_ver_p1_b);
        always_ff @(posedge clk, negedge rst_n) begin
            if(!rst_n) begin
                triggered_counter_ver_p1_a <= '0;
                triggered_counter_ver_p1_b <= '0;
            end
            else begin
              if (ecc_pm_ctrl.ecc_cmd_reg == VER_PART1_CMD) begin
                if(trigger_counter_ver_p1_a_reg) begin
                    triggered_counter_ver_p1_a <= 1;
                end
                if(trigger_counter_ver_p1_b_reg) begin
                    triggered_counter_ver_p1_b <= 1;
                end
              end
            end
        end

    counter_ver_p1_a_liveness_a: assert property(disable iff(!rst_n) liveness_p(VER_PART1_CMD,triggered_counter_ver_p1_a));

    counter_ver_p1_b_liveness_a: assert property(disable iff(!rst_n) liveness_p(VER_PART1_CMD,triggered_counter_ver_p1_b));

    counter_order_check_ver_p1_a: assert property(disable iff(!rst_n) order_check_p(triggered_counter_ver_p1_a,triggered_counter_ver_p1_b));
    



/////////////////////////////////////////////////////////////////////////////////////
// ------------------------------------END---------------------------------------- //
/////////////////////////////////////////////////////////////////////////////////////


        // validates once the verify part2 is set initally it would traverse through VER1_ST_S and PM_INIT_S
         property verify_part2_stage0_p(delay1,delay2);
            ecc_cmd_i == VER_PART2_CMD &&
            ecc_pm_ctrl.prog_cntr == NOP
            |=>
            ecc_pm_ctrl.prog_cntr == VER1_ST_S         //store (h*s^-1)*G  in P1 address
            ##delay1 ecc_pm_ctrl.prog_cntr == VER1_ST_E
            ##1 ecc_pm_ctrl.prog_cntr == PM_INIT_PK_S   // Pubkey in R1
            ##delay2 ecc_pm_ctrl.prog_cntr == PM_INIT_PK_E
            ##1 ecc_pm_ctrl.prog_cntr == PM_INIT_S;      // Initialise R0 with (0:1:0)    ##12 mult delay 1                 
        endproperty
        verify_part2_stage0_a: assert property(disable iff(!rst_n) verify_part2_stage0_p(VER_ST_DLY,PM_INT_PK_DLY));


    //validates if verify part2 sequence is ongoing then it would traverse from PD_E to VER2_PA_S when the mont_cntr is zero
         property verify_part2_stage2_p;
            ecc_pm_ctrl.ecc_cmd_reg == VER_PART2_CMD &&
            ecc_pm_ctrl.prog_cntr == PD_E &&
             ecc_pm_ctrl.mont_cntr == 0
            |->
            ##1 ecc_pm_ctrl.prog_cntr == VER2_PA_S  ;    // add (h*s_inv)*G, (r*s_inv)*PK)
        endproperty
        verify_part2_stage2_a: assert property(disable iff(!rst_n) verify_part2_stage2_p);



    //validates if verify part2 sequence is ongoing then it would traverse from VER2_PA_S till INV_S
        property verify_part2_stage3_p(delay);
            ecc_pm_ctrl.ecc_cmd_reg == VER_PART2_CMD &&
            ecc_pm_ctrl.prog_cntr == VER2_PA_S
            |->
            ##delay ecc_pm_ctrl.prog_cntr == VER2_PA_E
            ##1 ecc_pm_ctrl.prog_cntr == INV_S ;         // Inv z coordinate
            endproperty
        verify_part2_stage3_a: assert property(disable iff(!rst_n) verify_part2_stage3_p(VER_PA_DLY));


/////////////////////////////////////////////////////////////////////////////////////
// ---------------------------------BEGIN----------------------------------------- //
// Checking the counter integrity that the sequence is performed one after another //
/////////////////////////////////////////////////////////////////////////////////////

    logic  [PROG_ADDR_W-1  : 0] counter_ver_p2_a;
    logic  [PROG_ADDR_W-1  : 0] counter_ver_p2_b;
    logic  [PROG_ADDR_W-1  : 0] counter_ver_p2_c;
    logic  [PROG_ADDR_W-1  : 0] counter_ver_p2_d;
    logic  [PROG_ADDR_W-1  : 0] counter_ver_p2_a_1;
    logic  [PROG_ADDR_W-1  : 0] counter_ver_p2_b_1;
    logic  [PROG_ADDR_W-1  : 0] counter_ver_p2_c_1;
    logic  [PROG_ADDR_W-1  : 0] counter_ver_p2_d_1;
    logic trigger_counter_ver_p2_a_1_reg;
    logic trigger_counter_ver_p2_b_1_reg;
    logic trigger_counter_ver_p2_c_1_reg;
    logic trigger_counter_ver_p2_d_1_reg; 
    logic triggered_counter_ver_p2_a_1;
    logic triggered_counter_ver_p2_b_1;
    logic triggered_counter_ver_p2_c_1;
    logic triggered_counter_ver_p2_d_1;
    logic trigger_counter_ver_p2_a_reg;
    logic trigger_counter_ver_p2_b_reg;
    logic trigger_counter_ver_p2_c_reg;
    logic trigger_counter_ver_p2_d_reg; 
    logic triggered_counter_ver_p2_a;
    logic triggered_counter_ver_p2_b;
    logic triggered_counter_ver_p2_c;
    logic triggered_counter_ver_p2_d;

        counter_nonreachable_values_in_ver_p2: assume property (disable iff(!rst_n)counter_nonreachable_values_in_ver_p2_p);
        property counter_nonreachable_values_in_ver_p2_p;
           
            counter_ver_p2_a != VER1_ST_E+1 && counter_ver_p2_a_1 != VER1_ST_E+1 &&
            counter_ver_p2_b != PM_INIT_E+1 && counter_ver_p2_b_1 != PM_INIT_E+1 &&
            counter_ver_p2_b != PA_E+1 && counter_ver_p2_b_1 != PA_E+1 && 
            counter_ver_p2_d!= INV_E+1 && counter_ver_p2_d_1!= INV_E+1
            ;
        endproperty

        counter_ver_p2_a_assume: assume property(disable iff(!rst_n) (counter_ver_p2_a >=VER1_ST_S) && (counter_ver_p2_a <=PM_INIT_PK_E) && $stable(counter_ver_p2_a));
        counter_ver_p2_a_1_assume: assume property(disable iff(!rst_n) (counter_ver_p2_a_1 > counter_ver_p2_a) && (counter_ver_p2_a_1 <=PM_INIT_PK_E) && $stable(counter_ver_p2_a_1));

        counter_ver_p2_b_assume: assume property(disable iff(!rst_n) (counter_ver_p2_b <=PD_E) && (counter_ver_p2_b >= PM_INIT_S) && $stable(counter_ver_p2_b));
        counter_ver_p2_b_1_assume: assume property(disable iff(!rst_n) (counter_ver_p2_b_1 <=PD_E) && (counter_ver_p2_b_1 > counter_ver_p2_b) && $stable(counter_ver_p2_b_1));
        
        counter_ver_p2_c_assume: assume property(disable iff(!rst_n) (counter_ver_p2_c >=VER2_PA_S) && (counter_ver_p2_c <=VER2_PA_E) && $stable(counter_ver_p2_c));
        counter_ver_p2_c_1_assume: assume property(disable iff(!rst_n) (counter_ver_p2_c_1 >counter_ver_p2_c) && (counter_ver_p2_c_1 <=VER2_PA_E) && $stable(counter_ver_p2_c_1));
        
        counter_ver_p2_d_assume: assume property(disable iff(!rst_n) (counter_ver_p2_d <=CONV_E) && (counter_ver_p2_d >= INV_S) && $stable(counter_ver_p2_d));
        counter_ver_p2_d_1_assume: assume property(disable iff(!rst_n) (counter_ver_p2_d_1 <=CONV_E) && (counter_ver_p2_d_1 >  counter_ver_p2_d) && $stable(counter_ver_p2_d_1));
         
        assign trigger_counter_ver_p2_a_reg = (ecc_pm_ctrl.prog_cntr==counter_ver_p2_a);
        assign trigger_counter_ver_p2_b_reg = (ecc_pm_ctrl.prog_cntr==counter_ver_p2_b);

        assign trigger_counter_ver_p2_c_reg = (ecc_pm_ctrl.prog_cntr==counter_ver_p2_c);
        assign trigger_counter_ver_p2_d_reg = (ecc_pm_ctrl.prog_cntr==counter_ver_p2_d);

        assign trigger_counter_ver_p2_a_1_reg = (ecc_pm_ctrl.prog_cntr==counter_ver_p2_a_1);
        assign trigger_counter_ver_p2_b_1_reg = (ecc_pm_ctrl.prog_cntr==counter_ver_p2_b_1);

        assign trigger_counter_ver_p2_c_1_reg = (ecc_pm_ctrl.prog_cntr==counter_ver_p2_c_1);
        assign trigger_counter_ver_p2_d_1_reg = (ecc_pm_ctrl.prog_cntr==counter_ver_p2_d_1);

        always_ff @(posedge clk, negedge rst_n) begin
            if(!rst_n) begin
                triggered_counter_ver_p2_a <= '0;
                triggered_counter_ver_p2_b <= '0;
                triggered_counter_ver_p2_c <= '0;
                triggered_counter_ver_p2_d <= '0;
                triggered_counter_ver_p2_a_1 <= '0;
                triggered_counter_ver_p2_b_1 <= '0;
                triggered_counter_ver_p2_c_1 <= '0;
                triggered_counter_ver_p2_d_1 <= '0;
            end
            else begin
                if(ecc_pm_ctrl.ecc_cmd_reg == VER_PART2_CMD) begin
                    if(trigger_counter_ver_p2_a_reg) begin
                        triggered_counter_ver_p2_a <= 1;
                    end
                    if(trigger_counter_ver_p2_b_reg) begin
                        triggered_counter_ver_p2_b <= 1;
                    end
                    if(trigger_counter_ver_p2_c_reg) begin
                        triggered_counter_ver_p2_c <= 1;
                    end
                    if(trigger_counter_ver_p2_d_reg) begin
                        triggered_counter_ver_p2_d <= 1;
                    end
                    if(trigger_counter_ver_p2_a_1_reg) begin
                        triggered_counter_ver_p2_a_1 <= 1;
                    end
                    if(trigger_counter_ver_p2_b_1_reg) begin
                        triggered_counter_ver_p2_b_1 <= 1;
                    end
                    if(trigger_counter_ver_p2_c_1_reg) begin
                        triggered_counter_ver_p2_c_1 <= 1;
                    end
                    if(trigger_counter_ver_p2_d_1_reg) begin
                        triggered_counter_ver_p2_d_1 <= 1;
                    end
                end
            end
        end


    counter_ver_p2_a_liveness_a: assert property(disable iff(!rst_n) liveness_p(VER_PART2_CMD,triggered_counter_ver_p2_a));

 
    counter_ver_p2_b_liveness_a: assert property(disable iff(!rst_n) liveness_p(VER_PART2_CMD,triggered_counter_ver_p2_b));

    counter_ver_p2_c_liveness_a: assert property(disable iff(!rst_n) liveness_p(VER_PART2_CMD,triggered_counter_ver_p2_c));

    counter_ver_p2_d_liveness_a: assert property(disable iff(!rst_n) liveness_p(VER_PART2_CMD,triggered_counter_ver_p2_d));

    counter_intrnl_ver_p2_a: assert property(disable iff(!rst_n) order_check_p(triggered_counter_ver_p2_a,triggered_counter_ver_p2_a_1));
    
    counter_staging0_ver_p2_a: assert property(disable iff(!rst_n) order_check_p((triggered_counter_ver_p2_a & triggered_counter_ver_p2_a_1 & triggered_counter_ver_p2_b),triggered_counter_ver_p2_b_1));
    
    counter_staging1_ver_p2_a: assert property(disable iff(!rst_n) order_check_p((triggered_counter_ver_p2_a & triggered_counter_ver_p2_b & triggered_counter_ver_p2_c & triggered_counter_ver_p2_a_1 & triggered_counter_ver_p2_b_1), triggered_counter_ver_p2_c_1));

    counter_staging2_ver_p2_a: assert property(disable iff(!rst_n) order_check_p((triggered_counter_ver_p2_a & triggered_counter_ver_p2_b & triggered_counter_ver_p2_c & triggered_counter_ver_p2_d & triggered_counter_ver_p2_a_1 & triggered_counter_ver_p2_b_1 & triggered_counter_ver_p2_c_1),triggered_counter_ver_p2_d_1));
    


/////////////////////////////////////////////////////////////////////////////////////
// ------------------------------------END---------------------------------------- //
/////////////////////////////////////////////////////////////////////////////////////




    //If the prog_cntr is not NOP then the pm_ctrl is busy
        property busy_p;
            ecc_pm_ctrl.prog_cntr != NOP
            |->
            busy_o;
        endproperty
        busy_a: assert property(disable iff(!rst_n) busy_p);

    //If the prog_cntr is NOP then the pm_ctrl is not busy
        property no_busy_p;
            (ecc_pm_ctrl.prog_cntr == NOP)
            |->
            !busy_o;
        endproperty
        no_busy_a: assert property(disable iff(!rst_n) no_busy_p);
        

    //req_digit_o is set only when the mont_cntr is not zero in PD_E step or the very first rotation i.e in PM_INIT_E
        property req_digit_p;
            (ecc_pm_ctrl.prog_cntr == PD_E && ecc_pm_ctrl.mont_cntr!=0) ||
            (ecc_pm_ctrl.prog_cntr == PM_INIT_E)
            |=>
            req_digit_o;
        endproperty
        req_digit_a: assert property(disable iff(!rst_n) req_digit_p);


    //req_digit_o is zero  when the mont_cntr is  zero in PD_E step or it is not the very first rotation i.e in PM_INIT_E
         property no_req_digit_p;
            !(ecc_pm_ctrl.prog_cntr == PD_E && ecc_pm_ctrl.mont_cntr!=0) &&
            !(ecc_pm_ctrl.prog_cntr == PM_INIT_E)
            |=>
            !req_digit_o;
        endproperty
        no_req_digit_a: assert property(disable iff(!rst_n) no_req_digit_p);


    //req_digit_o trigger mont_cntr times
        property mont_multiples_req_digit_o_p(cmd,count);
            $rose(ecc_pm_ctrl.ecc_cmd_reg == cmd)
            |->
            strong((req_digit_o && (ecc_pm_ctrl.prog_cntr==PA_S))[->count] ##1( ecc_pm_ctrl.mont_cntr==0)) ;
        endproperty
        keygen_mont_multiples_req_digit_o_a:assert property(disable iff(!rst_n) mont_multiples_req_digit_o_p(KEYGEN_CMD,Secp384_SCA_MONT_COUNT));
        signing_mont_multiples_req_digit_o_a:assert property(disable iff(!rst_n) mont_multiples_req_digit_o_p(SIGN_CMD,Secp384_SCA_MONT_COUNT));
        ver_p1_mont_multiples_req_digit_o_a:assert property(disable iff(!rst_n) mont_multiples_req_digit_o_p(VER_PART1_CMD,Secp384_MONT_COUNT));
        ver_p2_mont_multiples_req_digit_o_a:assert property(disable iff(!rst_n) mont_multiples_req_digit_o_p(VER_PART2_CMD,Secp384_MONT_COUNT));
        
        
    //when output of pm_sequencer instruction is add it would be on primary output after 3 cycles and stays stable for the delay time +2
        property opcode_add_p;
            ecc_pm_ctrl.prog_instr.opcode.add_en 
            |->
            ##PIP_DLY
            instr_o.opcode == $past(ecc_pm_ctrl.prog_instr.opcode,3) 
            ##1 instr_o.opcode ==$past(instr_o.opcode)[*(ADD_DLY+1)];
        endproperty
        opcode_add_a: assert property(disable iff(!rst_n) opcode_add_p);

   
    //when output of pm_sequencer instruction is multiplication it would be on primary output after 3 cycles and stays stable for the delay time +2
        property opcode_mul_p;
            ecc_pm_ctrl.prog_instr.opcode.mult_en
            |->
            ##PIP_DLY
            instr_o.opcode == $past(ecc_pm_ctrl.prog_instr.opcode,3)
            ##1 instr_o.opcode ==$past(instr_o.opcode)[*(MULT_DLY+1)];
        endproperty
        opcode_mul_a: assert property(disable iff(!rst_n) opcode_mul_p);


    //-----------------------------------------//   
    //      Helper logic for stall
    //-----------------------------------------//   

    logic fv_stall;
    logic fv_stall_dly;
    logic fv_stall_pulse;
    logic [6:0] fv_dly_cntr;

        always_ff @(posedge clk, negedge rst_n) begin
            if(!rst_n) begin
                fv_stall <= 0;
                fv_dly_cntr <= 0;
                fv_stall_dly <= 0;
            end
            else begin
                if(ecc_pm_ctrl.prog_instr.opcode.add_en || 
            ecc_pm_ctrl.prog_instr.opcode.mult_en) begin
                fv_stall <= 1;
            end
            if(ecc_pm_ctrl.prog_instr.opcode.add_en)begin
                fv_dly_cntr <= ADD_DLY+1;
            end
            if(ecc_pm_ctrl.prog_instr.opcode.mult_en) begin
                fv_dly_cntr <= MULT_DLY+1; 
            end
            if(fv_dly_cntr>0) begin
                fv_dly_cntr <= fv_dly_cntr - 7'h1; 
            end
            if(fv_dly_cntr == 0 && fv_stall==1) begin
                fv_stall <= 0;
            end
            fv_stall_dly <= fv_stall;
            end
        end
    assign fv_stall_pulse = fv_stall & ~fv_stall_dly;

//When the add or mult are set then the next cycle output of pm_seq instruction is stored so it not lost during 
//the exceution of add ormult and the next instr_o would be stored value 
        property opcode_no_compute_p;
            logic[5:0] next_opcode;  
            fv_stall_pulse 
            ##0 (1'b1, next_opcode = ecc_pm_ctrl.prog_instr.opcode)
            ##1 !fv_stall[->1]        
            |->
            ##2
            instr_o.opcode == next_opcode;
        endproperty

        opcode_no_compute_a: assert property (disable iff(!rst_n)opcode_no_compute_p);



//Helper function for choosing address
function logic[5:0] xor_choose(input logic digit, input logic[5:0] addr);
    return({addr[5:3],digit^addr[2],addr[1:0]});
endfunction


//Constraint on digit_i stability,proven on the top
stable_digit_during_ladder: assume property(disable iff(!rst_n) ((ecc_pm_ctrl.prog_cntr <= PD_E) &&
            (ecc_pm_ctrl.prog_cntr >= PA_S)) |-> $stable(digit_i));


logic[5:0] fv_compute_addra;
logic[5:0] fv_compute_addrb;
//Helper logic for storing the computed address
    always_comb begin:operands_addr
        if((ecc_pm_ctrl.prog_cntr <= PD_E) && (ecc_pm_ctrl.prog_cntr >= PA_S) && ecc_pm_ctrl.prog_instr.opa_addr[5:3]==3'b001)
            fv_compute_addra = xor_choose(digit_i,ecc_pm_ctrl.prog_instr.opa_addr);
        else
            fv_compute_addra = ecc_pm_ctrl.prog_instr.opa_addr;

        if((ecc_pm_ctrl.prog_cntr <= PD_E) && (ecc_pm_ctrl.prog_cntr >= PA_S) && ecc_pm_ctrl.prog_instr.opb_addr[5:3]==3'b001)
            fv_compute_addrb = xor_choose(digit_i,ecc_pm_ctrl.prog_instr.opb_addr);
        else
            fv_compute_addrb = ecc_pm_ctrl.prog_instr.opb_addr;
    end



//when output of pm_sequencer instruction is add and the addresses are not R0 then 
//it would be on primary output after 3 cycles and stays stable for the delay time +2
      property addr_when_add_sub_p;
            logic[5:0] addra,addrb;
            ecc_pm_ctrl.prog_instr.opcode.add_en 
            ##0 (1'b1, addra = (fv_compute_addra))  
            ##0 (1'b1, addrb = (fv_compute_addrb))         
            |->
            ##PIP_DLY
            (instr_o.opa_addr == addra &&
            instr_o.opb_addr == addrb)[*(ADD_DLY+2)]
             ;
        endproperty

         addr_when_add_sub_a: assert property (disable iff(!rst_n)addr_when_add_sub_p);


//when output of pm_sequencer instruction is multiplication and the addresses it  
//would be on primary output after 3 cycles and stays stable for the delay time +2
        property addr_when_mult_p;
            logic[5:0] addra,addrb;
            ecc_pm_ctrl.prog_instr.opcode.mult_en 
            ##0 (1'b1, addra = (fv_compute_addra))  
            ##0 (1'b1, addrb = (fv_compute_addrb)) 
            |->
            ##PIP_DLY
            (instr_o.opa_addr == addra &&
            instr_o.opb_addr == addrb)[*(MULT_DLY+2)] 
             ;
        endproperty

         addr_when_mult_a: assert property (disable iff(!rst_n)addr_when_mult_p);



//When the add or mult are set then the next cycle output of pm_seq instruction is 
//stored so it not lost during the exceution of add ormult and the next instr_o would be stored value 
    property addr_when_no_cmd_p;
            logic[5:0] addra,addrb;
            
            fv_stall_pulse 
            ##0 (1'b1, addra = (fv_compute_addra))  
            ##0 (1'b1, addrb = (fv_compute_addrb)) 
            ##1 !fv_stall[->1]       
            |->
            ##2
            (instr_o.opa_addr == addra &&
            instr_o.opb_addr == addrb)
             ;
        endproperty

         addr_when_no_cmd_a: assert property (disable iff(!rst_n)addr_when_no_cmd_p);




    property instr_o_when_cmds_2cycls_p;
        ecc_pm_ctrl.prog_instr.opcode.add_en || 
        ecc_pm_ctrl.prog_instr.opcode.mult_en
        |=>
         (instr_o.opa_addr == $past(instr_o.opa_addr) &&
         instr_o.opb_addr == $past(instr_o.opb_addr)) &&
         instr_o.opcode == $past(instr_o.opcode);
    endproperty
    instr_o_when_cmds_2cycls_a: assert property(disable iff(!rst_n) instr_o_when_cmds_2cycls_p);


     property instr_o_when_no_cmds_2cycls_p;
        !fv_stall && 
        ecc_pm_ctrl.prog_instr.opcode!=UOP_NOP
         |=>
         (instr_o.opa_addr == $past(instr_o.opa_addr) &&
         instr_o.opb_addr == $past(instr_o.opb_addr)) &&
         instr_o.opcode == $past(instr_o.opcode);
    endproperty
    instr_o_when_no_cmds_2cycls_a: assert property(disable iff(!rst_n) instr_o_when_no_cmds_2cycls_p);

    

      property prog_cntr_stable_p;
        fv_stall &&
        (fv_dly_cntr > 1)
        |=>
        ecc_pm_ctrl.prog_cntr == $past(ecc_pm_ctrl.prog_cntr);
      endproperty

      prog_cntr_stable_a: assert property(disable iff(!rst_n) prog_cntr_stable_p);



        property prog_cntr_change_p;
        (fv_stall & (fv_dly_cntr <= 1))
        |=>
        ecc_pm_ctrl.prog_cntr != $past(ecc_pm_ctrl.prog_cntr);
      endproperty

      prog_cntr_change_a: assert property(disable iff(!rst_n) prog_cntr_change_p);


       property prog_cntr_change_1_p;
        !fv_stall &&
        ecc_pm_ctrl.prog_cntr !=NOP
        |=>
        fv_stall ||
        ecc_pm_ctrl.prog_cntr != $past(ecc_pm_ctrl.prog_cntr);
      endproperty

      prog_cntr_change_1_a: assert property(disable iff(!rst_n) prog_cntr_change_1_p);


        property no_cmd_prog_nop_p;
            ecc_pm_ctrl.prog_cntr == NOP &&
            ecc_cmd_i != KEYGEN_CMD &&
            ecc_cmd_i != SIGN_CMD &&
            ecc_cmd_i != VER_PART0_CMD &&
            ecc_cmd_i != VER_PART1_CMD &&
            ecc_cmd_i != VER_PART2_CMD &&
            ecc_cmd_i != CHK_PK_CMD
            |=>
            ecc_pm_ctrl.prog_cntr == NOP;
        endproperty

        no_cmd_prog_nop_a: assert property(disable iff(!rst_n) no_cmd_prog_nop_p);



endmodule

bind ecc_pm_ctrl fv_ecc_pm_ctrl_abstract #(
        .REG_SIZE(REG_SIZE),
        .RND_SIZE(RND_SIZE),
        .INSTR_SIZE(INSTRUCTION_LENGTH),
        .MULT_DLY(ecc_pm_ctrl.MULT_DELAY),
        .ADD_DLY(ecc_pm_ctrl.ADD_DELAY),
        .Secp384_MONT_COUNT(ecc_pm_ctrl.Secp384_MONT_COUNT),
        .Secp384_SCA_MONT_COUNT(ecc_pm_ctrl.Secp384_SCA_MONT_COUNT)
        )
        fv_ecc_pm_ctrl_abstract_inst(
        .clk(clk),
        .rst_n(reset_n && !zeroize),
        .ecc_cmd_i(ecc_cmd_i),
        .sca_en_i(sca_en_i),
        .digit_i(digit_i),
        .instr_o(instr_o),
        .req_digit_o(req_digit_o),
        .busy_o(busy_o)
    );