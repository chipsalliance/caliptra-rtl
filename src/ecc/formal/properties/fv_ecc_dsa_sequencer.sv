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
module fv_ecc_dsa_sequencer 
    import ecc_pm_uop_pkg::*;
    import ecc_dsa_uop_pkg::*;
    #(
    parameter ADDR_WIDTH = 8,
    parameter DATA_WIDTH = 32
    )
    (      
    input  wire                      clk,
    input  wire                      rst_n,
    input  wire                      ena,
    input  wire  [ADDR_WIDTH-1 : 0]  addra,
    input logic [DATA_WIDTH-1 : 0]  douta
    );

    ///////////////////////////////////////////////
    // Helper logic for driving the addra, these assertions
    // are used only at block level
    ///////////////////////////////////////////////

    logic [ADDR_WIDTH-1 : 0] fv_cntr_const,fv_cntr_kgn,fv_cntr_sgn,fv_cntr_ver;
    logic fv_const_set, fv_kgn_set,fv_sgn_set,fv_ver_set;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if(!rst_n) begin
            fv_cntr_const <= '0;
            fv_cntr_kgn <= '0;
            fv_cntr_sgn <= '0;
            fv_cntr_ver <= '0;
            fv_const_set <= 0;
            fv_kgn_set <= 0;
            fv_sgn_set <= 0;
            fv_ver_set <= 0;
        end
        else begin
            if(addra ==0) begin
                fv_ver_set <= 0;
                fv_const_set <=1;
                fv_cntr_const <= addra+1;
            end
            else if(fv_const_set) begin
            fv_cntr_const <= fv_cntr_const+1;
            end
             if(addra ==DSA_KG_S) begin
                fv_const_set <=0;
                fv_kgn_set <= 1;
                fv_cntr_kgn <= addra+1;
             end
            else if(fv_kgn_set) begin
            fv_cntr_kgn <= fv_cntr_kgn+1;
            end
             if(addra == DSA_SGN_S) begin
                fv_kgn_set  <=0;
                fv_sgn_set <= 1;
                fv_cntr_sgn <= addra +1;
             end
             else if(fv_sgn_set) begin
            fv_cntr_sgn <= fv_cntr_sgn+1;
            end
             if(addra == DSA_VER_S) begin
                fv_sgn_set  <=0;
                fv_ver_set <= 1;
                fv_cntr_ver <= addra +1;
             end
             else if(fv_ver_set) begin
            fv_cntr_ver <= fv_cntr_ver+1;
            end 


        end
    end

    cntr_assume: assume property(disable iff(!rst_n) fv_const_set |-> addra == fv_cntr_const);
    cntr_assume_kgn: assume property(disable iff(!rst_n) fv_kgn_set |-> addra == fv_cntr_kgn);
    cntr_assume_sgn: assume property(disable iff(!rst_n) fv_sgn_set |-> addra == fv_cntr_sgn);
    cntr_assume_ver: assume property(disable iff(!rst_n) fv_ver_set |-> addra == fv_cntr_ver);
    always_enable: assume property(disable iff(!rst_n) ena == 1'b1);

    default clocking default_clk @(posedge clk); endclocking


        sequence reset_sequence;
          !rst_n ##1 rst_n;
        endsequence


    ////////////////////////////////////////////
    // reset property, when reset out a and b //
    // are zero                               //
    ////////////////////////////////////////////

        property reset_p;
         $past(!rst_n)  
        |->
        douta == '0;
        endproperty

        reset_a : assert property(reset_p);


    //If the addra input has illegal addresses then the output douta should be zero
        property illegal_addr_p;
            ((addra > DSA_NOP) && (addra < DSA_KG_S)) ||
            ((addra > DSA_KG_E) && (addra < DSA_SGN_S)) ||
            ((addra > DSA_SGN_E) && (addra < DSA_VER_S)) ||
            (addra > DSA_VER_E)
            |=>
            douta == '0;
        endproperty
        illegal_addr_a : assert property(disable iff(!rst_n) illegal_addr_p);



    //Checks the sequence where some constant values are written into the memory
        property const_p;
            addra == 0
            |->
            ##1 douta == {DSA_UOP_NOP,       NOP_ID,                  UOP_OPR_DONTCARE}         //no operation
            ##1 douta == {DSA_UOP_WR_CORE,   CONST_ZERO_ID,           UOP_OPR_CONST_ZERO}       // write to the memory addr zero with value zero
            ##1 douta == {DSA_UOP_WR_CORE,   CONST_ONE_ID,            UOP_OPR_CONST_ONE}        // write to the memory addr one with value one
            ##1 douta == {DSA_UOP_WR_CORE,   CONST_E_a_MONT_ID,       UOP_OPR_CONST_E_a}        // write to the memory addr two with value mont_a
            ##1 douta == {DSA_UOP_WR_CORE,   CONST_E_3b_MONT_ID,      UOP_OPR_CONST_E_3b}       // write to the memory addr three with value mont_3b
            ##1 douta == {DSA_UOP_WR_CORE,   CONST_ONE_p_MONT_ID,     UOP_OPR_CONST_ONE_MONT}   // write to the memory addr four with value const_one in mont for mod p
            ##1 douta == {DSA_UOP_WR_CORE,   CONST_R2_p_MONT_ID,      UOP_OPR_CONST_R2_p}       // write to the memory addr five with value R2 in mont domain mod p, used for converting normal domain to mont domain
            ##1 douta == {DSA_UOP_WR_CORE,   CONST_G_X_MONT_ID,       UOP_OPR_CONST_GX_MONT}    // write to the memory addr six with value Gx in mont domain
            ##1 douta == {DSA_UOP_WR_CORE,   CONST_G_Y_MONT_ID,       UOP_OPR_CONST_GY_MONT}    // write to the memory addr seven with value Gy in mont domain
            ##1 douta == {DSA_UOP_WR_CORE,   CONST_R2_q_MONT_ID,      UOP_OPR_CONST_R2_q}       // write to the memory addr 29 with value R2 in mont domain mod q, used for converting normal domain to mont domain
            ##1 douta == {DSA_UOP_WR_CORE,   CONST_ONE_q_MONT_ID,     UOP_OPR_CONST_ONE_q_MONT} //// write to the memory addr 28 with value const_one in mont for mod p
            ##1 douta == {DSA_UOP_NOP,       NOP_ID,                  UOP_OPR_DONTCARE};
        endproperty


        const_a: assert property (disable iff(!rst_n) const_p);


        // Checks the sequence of operations for the keygen operation
        property keygen_p;
            addra == DSA_KG_S
            |->
            ##1 douta <= {DSA_UOP_HMAC_DRBG,     NOP_ID,             UOP_OPR_DONTCARE}       // Input seed for lamda, scalar, privkey genration
            ##1 douta <= {DSA_UOP_NOP,           NOP_ID,             UOP_OPR_DONTCARE}
            ##1 douta <= {DSA_UOP_WR_CORE,       SCALAR_G_ID,        UOP_OPR_SCALAR_G}      // Writing scalar here it is privkey to the memory
            ##1 douta <= {DSA_UOP_RD_CORE,       PRIVKEY_ID,         UOP_OPR_SCALAR_G}      // Read the generated privkey, used for out
            ##1 douta <= {DSA_UOP_SCALAR_SCA,    SCALAR_G_ID,        UOP_OPR_DONTCARE}      // passing the generated scalar to scalar blinding as input
            ##1 douta <= {DSA_UOP_NOP,           NOP_ID,             UOP_OPR_DONTCARE}  
            ##1 douta <= {DSA_UOP_WR_SCALAR,     SCALAR_ID,          UOP_OPR_DONTCARE}      // the scalar blinded privkey is used as a secret key
            ##1 douta <= {DSA_UOP_WR_CORE,       LAMBDA_ID,          UOP_OPR_LAMBDA}        // lamda generated by hmac_drbg is stored into memory
            ##1 douta <= {DSA_UOP_KEYGEN,        NOP_ID,             UOP_OPR_DONTCARE}      // keygen cmd triggered in pm_ctrl to generate pub key
            ##1 douta <= {DSA_UOP_NOP,           NOP_ID,             UOP_OPR_DONTCARE}
            ##1 douta <= {DSA_UOP_RD_CORE,       PUBKEYX_ID,         UOP_OPR_Qx_AFFN}       // reading the generated pubkey x and y from memory 
            ##1 douta <= {DSA_UOP_RD_CORE,       PUBKEYY_ID,         UOP_OPR_Qy_AFFN}
            ##1 douta <= {DSA_UOP_NOP,           NOP_ID,             UOP_OPR_DONTCARE};
        endproperty

        keygen_a: assert property (disable iff(!rst_n) keygen_p);
            

        // Checks the sequence of operations for the signing operation
        property sign_p;
            addra == DSA_SGN_S
            |->
            ##1 douta == {DSA_UOP_WR_CORE,       MSG_ID,             UOP_OPR_HASH_MSG}      //Input hash msg
            ##1 douta == {DSA_UOP_WR_CORE,       PRIVKEY_ID,         UOP_OPR_PRIVKEY}       //Input priv key
            ##1 douta == {DSA_UOP_HMAC_DRBG,     NOP_ID,             UOP_OPR_DONTCARE}      // Feed in h and pk for k genration
            ##1 douta == {DSA_UOP_NOP,           NOP_ID,             UOP_OPR_DONTCARE}
            ##1 douta == {DSA_UOP_WR_CORE,       SCALAR_G_ID,        UOP_OPR_SCALAR_G}      // write to memory with the generated k
            ##1 douta == {DSA_UOP_SCALAR_SCA,    SCALAR_G_ID,        UOP_OPR_DONTCARE}      // enable the scalar blinding with k as input
            ##1 douta == {DSA_UOP_NOP,           NOP_ID,             UOP_OPR_DONTCARE}
            ##1 douta == {DSA_UOP_WR_SCALAR,     SCALAR_ID,          UOP_OPR_DONTCARE}      // the randmoised k is written to the secret key in pm ctrl
            ##1 douta == {DSA_UOP_WR_CORE,       LAMBDA_ID,          UOP_OPR_LAMBDA}        // lamda generated by hmac_drbg is stored into memory
            ##1 douta == {DSA_UOP_WR_CORE,       MASKING_ID,         UOP_OPR_MASKING}       // mask value generated by hmac_drbg is stored into the memory
            ##1 douta == {DSA_UOP_SIGN,          NOP_ID,             UOP_OPR_DONTCARE}      // signing cmd is passed to the pm_ctrl
            ##1 douta == {DSA_UOP_NOP,           NOP_ID,             UOP_OPR_DONTCARE}
            ##1 douta == {DSA_UOP_RD_CORE,       R_ID,               UOP_OPR_SIGN_R}        // read the generated r from the memory
            ##1 douta == {DSA_UOP_RD_CORE,       S_ID,               UOP_OPR_SIGN_S}        // read the generated s from the memory
            ##1 douta == {DSA_UOP_NOP,           NOP_ID,             UOP_OPR_DONTCARE};
        endproperty

        sign_a: assert property(disable iff(!rst_n) sign_p);



        // Checks the sequence of operations for the verifying operation
        property verify_p;
            addra == DSA_VER_S
            |->
            ##1 douta == {DSA_UOP_WR_CORE,        CONST_E_b_MONT_ID,  UOP_OPR_CONST_E_b}        // writing to the memory const b, which is in mont domain
            ##1 douta == {DSA_UOP_WR_CORE,        PUBKEYX_ID,         UOP_OPR_Qx_AFFN}          // writing to the memory input pubkey
            ##1 douta == {DSA_UOP_WR_CORE,        PUBKEYY_ID,         UOP_OPR_Qy_AFFN}
            ##1 douta == {DSA_UOP_PK_CHK,         NOP_ID,             UOP_OPR_DONTCARE}         // Cmd to pm ctrl to check if the pubkey is on the curve
            ##1 douta == {DSA_UOP_NOP,            NOP_ID,             UOP_OPR_DONTCARE}
            ##1 douta == {DSA_UOP_RD_CORE,        PK_VALID_ID,        UOP_OPR_PK_VALID}         // Reading the result from memory if the pubkey is valid point on the curve
            ##1 douta == {DSA_UOP_WR_CORE,        MSG_ID,             UOP_OPR_HASH_MSG}         // writing to the memory input hash msg
            ##1 douta == {DSA_UOP_WR_CORE,        R_ID,               UOP_OPR_SIGN_R}           // writing to the memory input r
            ##1 douta == {DSA_UOP_WR_CORE,        S_ID,               UOP_OPR_SIGN_S}           // writing to the memory input s
            ##1 douta == {DSA_UOP_WR_CORE,        CONST_ONE_ID,       UOP_OPR_LAMBDA}           // writing to the memory for lamda as value 1
            ##1 douta == {DSA_UOP_VERIFY0,        NOP_ID,             UOP_OPR_DONTCARE}         // verify0_cmd triggered in pm ctrl
            ##1 douta == {DSA_UOP_NOP,            NOP_ID,             UOP_OPR_DONTCARE}
            ##1 douta == {DSA_UOP_RD_CORE,        SCALAR_G_ID,        UOP_OPR_SCALAR_G}         // reading from memory (h*s_inv) value in normal domain
            ##1 douta == {DSA_UOP_RD_CORE,        SCALAR_PK_ID,       UOP_OPR_SCALAR_PK}        // reading from memory (r*s_inv) value in normal domain
            ##1 douta == {DSA_UOP_WR_SCALAR,      SCALAR_G_ID,        UOP_OPR_DONTCARE}         // (h*s_inv) value shifted by RND_SIZE and provided to pm as secret key 
            ##1 douta == {DSA_UOP_VERIFY1,        NOP_ID,             UOP_OPR_DONTCARE}         // verify1_cmd passed to pm_ctrl, result in R0_x,y,z
            ##1 douta == {DSA_UOP_NOP,            NOP_ID,             UOP_OPR_DONTCARE}
            ##1 douta == {DSA_UOP_WR_CORE,        PUBKEYX_ID,         UOP_OPR_Qx_AFFN}          // writing into memory the pubkey again
            ##1 douta == {DSA_UOP_WR_CORE,        PUBKEYY_ID,         UOP_OPR_Qy_AFFN}
            ##1 douta == {DSA_UOP_WR_SCALAR,      SCALAR_PK_ID,       UOP_OPR_DONTCARE}         // (r*s_inv) value shifted by RND_SIZE and provided to pm as secret key
            ##1 douta == {DSA_UOP_VERIFY2,        NOP_ID,             UOP_OPR_DONTCARE}
            ##1 douta == {DSA_UOP_NOP,            NOP_ID,             UOP_OPR_DONTCARE}
            ##1 douta == {DSA_UOP_RD_CORE,        VERIFY_R_ID,        UOP_OPR_Qx_AFFN}          //Computed r' in normal domain read back from memory
            ##1 douta == {DSA_UOP_NOP,            NOP_ID,             UOP_OPR_DONTCARE};
        endproperty
            
        verify_a: assert property(disable iff(!rst_n) verify_p);



//If the first field is DSA_UOP_NOP, the next fields should be NOP_ID and UOP_OPR_DONTCARE, respectively.

    property when_nop_both_id_addr_0_p;
        douta[19:12] == DSA_UOP_NOP 
        |->
        douta[11:0]== {NOP_ID,UOP_OPR_DONTCARE};
    endproperty

when_nop_both_id_addr_0_a: assert property(disable iff(!rst_n) when_nop_both_id_addr_0_p);


//If the first field is DSA_UOP_WR_CORE, the next fields should include a valid ID and ADDRESS, respectively.

     property when_wr_both_id_addr_not_0_p;
        douta[19:12] == DSA_UOP_WR_CORE 
        |->
        douta[11:0] == {CONST_ZERO_ID, UOP_OPR_CONST_ZERO} ||
        douta[11:0]  == {CONST_ONE_ID,            UOP_OPR_CONST_ONE} ||
        douta[11:0]  == {CONST_E_a_MONT_ID,       UOP_OPR_CONST_E_a} ||
        douta[11:0]  == {CONST_E_3b_MONT_ID,      UOP_OPR_CONST_E_3b} ||
        douta[11:0]  == {CONST_ONE_p_MONT_ID,     UOP_OPR_CONST_ONE_MONT} ||
        douta[11:0]  == {CONST_R2_p_MONT_ID,      UOP_OPR_CONST_R2_p} ||
        douta[11:0]  == {CONST_G_X_MONT_ID,       UOP_OPR_CONST_GX_MONT} ||
        douta[11:0]  == {CONST_G_Y_MONT_ID,       UOP_OPR_CONST_GY_MONT} ||
        douta[11:0]  == {CONST_R2_q_MONT_ID,      UOP_OPR_CONST_R2_q} ||
        douta[11:0]  == {CONST_ONE_q_MONT_ID,     UOP_OPR_CONST_ONE_q_MONT} ||
        douta[11:0]  == {SCALAR_G_ID,        UOP_OPR_SCALAR_G} ||
        douta[11:0]  == {LAMBDA_ID,          UOP_OPR_LAMBDA} ||
        douta[11:0]  == {MSG_ID,             UOP_OPR_HASH_MSG} ||
        douta[11:0]  == {PRIVKEY_ID,         UOP_OPR_PRIVKEY} ||
        douta[11:0]  == {MASKING_ID,         UOP_OPR_MASKING} ||
        douta[11:0]  == {CONST_E_b_MONT_ID,  UOP_OPR_CONST_E_b} ||
        douta[11:0]  == {R_ID,               UOP_OPR_SIGN_R} ||
        douta[11:0]  == {S_ID,               UOP_OPR_SIGN_S} ||
        douta[11:0]  == {CONST_ONE_ID,       UOP_OPR_LAMBDA} ||
        douta[11:0]  == {PUBKEYX_ID,         UOP_OPR_Qx_AFFN} ||
        douta[11:0]  == {PUBKEYY_ID,         UOP_OPR_Qy_AFFN};
    endproperty

when_wr_both_id_addr_not_0_a: assert property(disable iff(!rst_n) when_wr_both_id_addr_not_0_p);


//If the first field is DSA_UOP_HMAC_DRBG, the next fields should be NOP_ID and UOP_OPR_DONTCARE, respectively.
 property when_drbg_both_id_addr_0_p;
        douta[19:12] == DSA_UOP_HMAC_DRBG 
        |->
        douta[11:0] == {NOP_ID,UOP_OPR_DONTCARE};
    endproperty

when_drbg_both_id_addr_0_a: assert property(disable iff(!rst_n) when_drbg_both_id_addr_0_p);

//If the first field is DSA_UOP_SCALAR_SCA, the next fields should be SCALAR_G_ID and UOP_OPR_DONTCARE, respectively.
 property when_scalar_both_id_addr_p;
        douta[19:12] == DSA_UOP_SCALAR_SCA 
        |->
        douta[11:0] == {SCALAR_G_ID,UOP_OPR_DONTCARE};
    endproperty

when_scalar_both_id_addr_a: assert property(disable iff(!rst_n) when_scalar_both_id_addr_p);

//If the first field is DSA_UOP_WR_SCALAR, the next fields should be SCALAR_ID/ SCALAR_G_ID/ SCALAR_G_ID and UOP_OPR_DONTCARE, respectively.
 property when_wr_scalar_both_id_addr_p;
        douta[19:12] == DSA_UOP_WR_SCALAR 
        |->
        (douta[11:6] == SCALAR_G_ID ||
        douta[11:6] == SCALAR_ID ||
         douta[11:6] == SCALAR_PK_ID ) &&
        douta[5:0] == UOP_OPR_DONTCARE;
    endproperty

when_wr_scalar_both_id_addr_a: assert property(disable iff(!rst_n) when_wr_scalar_both_id_addr_p);



//If the first field is DSA_UOP_KEYGEN/ DSA_UOP_KEYGEN/ DSA_UOP_VERIFY0-2, the next fields should be NOP_ID and UOP_OPR_DONTCARE, respectively.

 property when_commands_both_id_addr_0_p;
        douta[19:12] == DSA_UOP_KEYGEN ||
        douta[19:12] == DSA_UOP_SIGN ||
        douta[19:12] == DSA_UOP_VERIFY0 ||
        douta[19:12] == DSA_UOP_VERIFY1 ||
        douta[19:12] == DSA_UOP_VERIFY2
        |->
        douta[11:0] == {NOP_ID,UOP_OPR_DONTCARE};
    endproperty

when_commands_both_id_addr_0_a: assert property(disable iff(!rst_n) when_commands_both_id_addr_0_p);

//o	If the first field is DSA_UOP_RD_CORE, the next fields should include a valid ID and ADDRESS, respectively.

 property when_rd_both_id_addr_not_0_p;
        douta[19:12] == DSA_UOP_RD_CORE 
        |->
        douta[11:0] ==  {PRIVKEY_ID,         UOP_OPR_SCALAR_G} ||
        douta[11:0] ==   {PUBKEYX_ID,         UOP_OPR_Qx_AFFN} ||
        douta[11:0] ==   {PUBKEYY_ID,         UOP_OPR_Qy_AFFN} ||
        douta[11:0] ==   {R_ID,               UOP_OPR_SIGN_R} ||
        douta[11:0] ==   {S_ID,               UOP_OPR_SIGN_S} ||
        douta[11:0] ==   {PK_VALID_ID,        UOP_OPR_PK_VALID} ||
        douta[11:0] ==   {SCALAR_G_ID,        UOP_OPR_SCALAR_G} ||
        douta[11:0] ==   {SCALAR_PK_ID,       UOP_OPR_SCALAR_PK} ||
        douta[11:0] ==   {VERIFY_R_ID,        UOP_OPR_Qx_AFFN};
    endproperty

when_rd_both_id_addr_not_0_a: assert property(disable iff(!rst_n) when_rd_both_id_addr_not_0_p);


endmodule


bind ecc_dsa_sequencer fv_ecc_dsa_sequencer  
    #(.ADDR_WIDTH(ADDR_WIDTH),
        .DATA_WIDTH(DATA_WIDTH)
        )
        fv_ecc_dsa_sequencer_inst(
        .clk(clka),
        .rst_n(reset_n && !zeroize),
        .ena(ena),
        .addra(addra),
        .douta(douta)
    );
