    
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
module fv_ecc_pm_sequencer 
    import ecc_pm_uop_pkg::*;
    #(
    parameter ADDR_WIDTH = 10,
    parameter DATA_WIDTH = 32
    )
    (      
    input  wire                      clk,
    input  wire                      rst_n,
    input  wire                      ena,
    input  wire  [ADDR_WIDTH-1 : 0]  addra,
    input logic [DATA_WIDTH-1 : 0]  douta
    );

logic [ADDR_WIDTH-1 : 0] fv_cntr_pminitg;
logic [ADDR_WIDTH-1 : 0] fv_cntr_pminit;
logic [ADDR_WIDTH-1 : 0] fv_cntr_pa;
logic [ADDR_WIDTH-1 : 0] fv_cntr_pd;
logic [ADDR_WIDTH-1 : 0] fv_cntr_inv;
logic [ADDR_WIDTH-1 : 0] fv_cntr_conv;
logic [ADDR_WIDTH-1 : 0] fv_cntr_sign0;
logic [ADDR_WIDTH-1 : 0] fv_cntr_invq;
logic [ADDR_WIDTH-1 : 0] fv_cntr_sign1;
logic [ADDR_WIDTH-1 : 0] fv_cntr_chkpk;
logic [ADDR_WIDTH-1 : 0] fv_cntr_ver0p0;
logic [ADDR_WIDTH-1 : 0] fv_cntr_ver0p1;
logic [ADDR_WIDTH-1 : 0] fv_cntr_ver1st;
logic [ADDR_WIDTH-1 : 0] fv_cntr_pminitpk;
logic [ADDR_WIDTH-1 : 0] fv_cntr_ver2pa;

logic fv_set_pminitg;
logic fv_set_pminit;
logic fv_set_pa;
logic fv_set_pd;
logic fv_set_inv;
logic fv_set_conv;
logic fv_set_sign0;
logic fv_set_invq;
logic fv_set_sign1;
logic fv_set_chkpk;
logic fv_set_ver0p0;
logic fv_set_ver0p1;
logic fv_set_ver1st;
logic fv_set_pminitpk;
logic fv_set_ver2pa;

always_ff @(posedge clk or negedge rst_n) begin
    if(!rst_n) begin
        fv_set_pminitg    <= '0;
        fv_set_pminit     <= '0;
        fv_set_pa         <= '0;
        fv_set_pd         <= '0;
        fv_set_inv        <= '0;
        fv_set_conv       <= '0;
        fv_set_sign0      <= '0;
        fv_set_invq       <= '0;
        fv_set_sign1      <= '0;
        fv_set_chkpk      <= '0;
        fv_set_ver0p0     <= '0;
        fv_set_ver0p1     <= '0;
        fv_set_ver1st     <= '0;
        fv_set_pminitpk   <= '0;
        fv_set_ver2pa     <= '0;
        fv_cntr_pminitg   <= '0;
        fv_cntr_pminit    <= '0;
        fv_cntr_pa        <= '0;
        fv_cntr_pd        <= '0;
        fv_cntr_inv       <= '0;
        fv_cntr_conv      <= '0;
        fv_cntr_sign0     <= '0;
        fv_cntr_invq      <= '0;
        fv_cntr_sign1     <= '0;
        fv_cntr_chkpk     <= '0;
        fv_cntr_ver0p0    <= '0;
        fv_cntr_ver0p1    <= '0;
        fv_cntr_ver1st    <= '0;
        fv_cntr_pminitpk  <= '0;
        fv_cntr_ver2pa    <= '0;
    end
    else begin
        if(addra == PM_INIT_G_S) begin
                fv_set_pminitg <= 1;
                fv_set_ver2pa <=0;
                fv_cntr_pminitg <= addra+1;
            end
            else if(fv_set_pminitg) begin
            fv_cntr_pminitg <= fv_cntr_pminitg+1;
            end
        if(addra == PM_INIT_S) begin
                fv_set_pminitg <= 0;
                fv_set_pminit <=1;
                fv_cntr_pminit <= addra+1;
            end
            else if(fv_set_pminit) begin
            fv_cntr_pminit <= fv_cntr_pminit+1;
            end
        if(addra == PA_S) begin
                fv_set_pminit <= 0;
                fv_set_pa <=1;
                fv_cntr_pa <= addra+1;
            end
            else if(fv_set_pa) begin
            fv_cntr_pa <= fv_cntr_pa+1;
            end
        if(addra == PD_S) begin
                fv_set_pa <= 0;
                fv_set_pd <=1;
                fv_cntr_pd <= addra+1;
            end
            else if(fv_set_pd) begin
            fv_cntr_pd <= fv_cntr_pd+1;
            end
         if(addra == INV_S) begin
                fv_set_pd <= 0;
                fv_set_inv <=1;
                fv_cntr_inv <= addra+1;
            end
            else if(fv_set_inv) begin
            fv_cntr_inv <= fv_cntr_inv+1;
            end
        if(addra == CONV_S) begin
                fv_set_inv <= 0;
                fv_set_conv <=1;
                fv_cntr_conv <= addra+1;
            end
            else if(fv_set_conv) begin
            fv_cntr_conv <= fv_cntr_conv+1;
            end
        if(addra == SIGN0_S) begin
                fv_set_conv <= 0;
                fv_set_sign0 <=1;
                fv_cntr_sign0 <= addra+1;
            end
            else if(fv_set_sign0) begin
            fv_cntr_sign0 <= fv_cntr_sign0+1;
            end
        if(addra == INVq_S) begin
                fv_set_sign0 <= 0;
                fv_set_invq <=1;
                fv_cntr_invq <= addra+1;
            end
            else if(fv_set_invq) begin
            fv_cntr_invq <= fv_cntr_invq+1;
            end
        if(addra == SIGN1_S) begin
                fv_set_invq <= 0;
                fv_set_sign1 <=1;
                fv_cntr_sign1 <= addra+1;
            end
            else if(fv_set_sign1) begin
            fv_cntr_sign1 <= fv_cntr_sign1+1;
            end
        if(addra == CHK_PK_S) begin
                fv_set_sign1 <= 0;
                fv_set_chkpk <=1;
                fv_cntr_chkpk <= addra+1;
            end
            else if(fv_set_chkpk) begin
            fv_cntr_chkpk <= fv_cntr_chkpk+1;
            end
         if(addra == VER0_P0_S) begin
                fv_set_chkpk <= 0;
                fv_set_ver0p0 <=1;
                fv_cntr_ver0p0 <= addra+1;
            end
            else if(fv_set_ver0p0) begin
            fv_cntr_ver0p0 <= fv_cntr_ver0p0+1;
            end
        if(addra == VER0_P1_S) begin
                fv_set_ver0p0 <= 0;
                fv_set_ver0p1 <=1;
                fv_cntr_ver0p1 <= addra+1;
            end
            else if(fv_set_ver0p1) begin
            fv_cntr_ver0p1 <= fv_cntr_ver0p1+1;
            end
        if(addra == VER1_ST_S) begin
                fv_set_ver0p1 <= 0;
                fv_set_ver1st <=1;
                fv_cntr_ver1st <= addra+1;
            end
            else if(fv_set_ver1st) begin
            fv_cntr_ver1st <= fv_cntr_ver1st+1;
            end
        if(addra == PM_INIT_PK_S) begin
                fv_set_pminitpk <= 1;
                fv_set_ver1st <=0;
                fv_cntr_pminitpk <= addra+1;
            end
            else if(fv_set_pminitpk) begin
            fv_cntr_pminitpk <= fv_cntr_pminitpk+1;
            end
        if(addra == VER2_PA_S) begin
                fv_set_ver2pa <= 1;
                fv_set_pminitpk <=0;
                fv_cntr_ver2pa <= addra+1;
            end
            else if(fv_set_ver2pa) begin
            fv_cntr_ver2pa <= fv_cntr_ver2pa+1;
            end
    end
end

property assign_addra(set,cntr);
    set
    |->
    addra == cntr;
endproperty

cntr_assume_pminitg :assume property(assign_addra(fv_set_pminitg ,fv_cntr_pminitg ));
cntr_assume_pminit  :assume property(assign_addra(fv_set_pminit  ,fv_cntr_pminit  ));
cntr_assume_pa      :assume property(assign_addra(fv_set_pa      ,fv_cntr_pa      ));
cntr_assume_pd      :assume property(assign_addra(fv_set_pd      ,fv_cntr_pd      ));
cntr_assume_inv     :assume property(assign_addra(fv_set_inv     ,fv_cntr_inv     ));
cntr_assume_conv    :assume property(assign_addra(fv_set_conv    ,fv_cntr_conv    ));
cntr_assume_sign0   :assume property(assign_addra(fv_set_sign0   ,fv_cntr_sign0   ));
cntr_assume_invq    :assume property(assign_addra(fv_set_invq    ,fv_cntr_invq    ));
cntr_assume_sign1   :assume property(assign_addra(fv_set_sign1   ,fv_cntr_sign1   ));
cntr_assume_chkpk   :assume property(assign_addra(fv_set_chkpk   ,fv_cntr_chkpk   ));
cntr_assume_ver0p0  :assume property(assign_addra(fv_set_ver0p0  ,fv_cntr_ver0p0  ));
cntr_assume_ver0p1  :assume property(assign_addra(fv_set_ver0p1  ,fv_cntr_ver0p1  ));
cntr_assume_ver1st  :assume property(assign_addra(fv_set_ver1st  ,fv_cntr_ver1st  ));
cntr_assume_pminitpk:assume property(assign_addra(fv_set_pminitpk,fv_cntr_pminitpk));
cntr_assume_ver2pa  :assume property(assign_addra(fv_set_ver2pa  ,fv_cntr_ver2pa  ));

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


////////////////////////////////////////////
// Illegal address should result in zero  //
////////////////////////////////////////////

    property illicit_addra_p;
       ((addra >1) && (addra < PM_INIT_G_S))||
       ((addra >PM_INIT_G_E) && (addra < PM_INIT_S))||
       ((addra >PM_INIT_E) && (addra < PA_S))||
       ((addra >PA_E) && (addra < PD_S))||
       ((addra >PD_E) && (addra < INV_S))||
       ((addra >INV_E) && (addra < CONV_S))||
       ((addra >CONV_E) && (addra < SIGN0_S))||
       ((addra >SIGN0_E) && (addra < INVq_S))||
       ((addra >INVq_E) && (addra < SIGN1_S))||
       ((addra >SIGN1_E) && (addra < CHK_PK_S))||
       ((addra >CHK_PK_E) && (addra < VER0_P0_S))||
       ((addra >VER0_P0_E) && (addra < VER0_P1_S))||
       ((addra >VER0_P1_E) && (addra < VER1_ST_S))||
       ((addra >VER1_ST_E) && (addra < PM_INIT_PK_S))||
       ((addra >PM_INIT_PK_E) && (addra < VER2_PA_S))||
       (addra > VER2_PA_E)
       |=>
       douta =='0;
    endproperty


    illicit_addra_a : assert property(disable iff(!rst_n) illicit_addra_p);

       

////////////////////////////////////////////
// Initial two steps dout is zero         //
//                                        //
////////////////////////////////////////////
     property initial_p;
        addra == NOP ||
        addra == 1
        |=>

        douta == '0;
    endproperty 

    initial_a : assert property(disable iff(!rst_n) initial_p);

////////////////////////////////////////////
// Base point randamization and storing   //
//  in R1                                 //
////////////////////////////////////////////


    property pm_init_G_p;
        addra == PM_INIT_G_S

        |->

        ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_LAMBDA,            UOP_OPR_CONST_R2_p}   // R1_Z = mm(Lambda, R2)        λ conversion to montgomery domain
        ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,          UOP_OPR_R1_Z}         //                                storing  λ in the projective coordinate R1_Z
        ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_CONST_GX_MONT,     UOP_OPR_R1_Z}         // R1_X = mm(GX_MONT, R0_Z)     𝑋=𝐺𝑥×λ
        ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,          UOP_OPR_R1_X}
        ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_CONST_GY_MONT,     UOP_OPR_R1_Z}         // R1_Y = mm(GY_MONT, R0_Z)     𝑌=𝐺𝑦×λ
        ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,          UOP_OPR_R1_Y};
    endproperty

    pm_init_G_a: assert property (disable iff(!rst_n) pm_init_G_p);            


////////////////////////////////////////////
// Initialize R0 with Zero                //
//                                        //
////////////////////////////////////////////


    property pm_init_S_p;
        addra == PM_INIT_S

        |->

        ##1 douta == {UOP_DO_ADD_p,   UOP_OPR_CONST_ZERO,        UOP_OPR_CONST_ZERO}  // R0_X = 0
        ##1 douta == {UOP_ST_ADD_p,   UOP_OPR_R0_X,              UOP_OPR_DONTCARE}
        ##1 douta == {UOP_DO_ADD_p,   UOP_OPR_CONST_ONE_MONT,    UOP_OPR_CONST_ZERO}  // initialised with one_mont R0_y = 384'h100000000ffffffffffffffff0000000100000000 
        ##1 douta == {UOP_ST_ADD_p,   UOP_OPR_R0_Y,              UOP_OPR_DONTCARE}
        ##1 douta == {UOP_DO_ADD_p,   UOP_OPR_CONST_ZERO,        UOP_OPR_CONST_ZERO}  // R0_Z = 0
        ##1 douta == {UOP_ST_ADD_p,   UOP_OPR_R0_Z,              UOP_OPR_DONTCARE}
        ##1 douta == {UOP_NOP,        UOP_OPR_DONTCARE,          UOP_OPR_DONTCARE}
        ##1 douta == {UOP_NOP,        UOP_OPR_DONTCARE,          UOP_OPR_DONTCARE}
        ##1 douta == {UOP_NOP,        UOP_OPR_DONTCARE,          UOP_OPR_DONTCARE}
        ##1 douta == {UOP_NOP,        UOP_OPR_DONTCARE,          UOP_OPR_DONTCARE};
    endproperty


     pm_init_S_a: assert property (disable iff(!rst_n) pm_init_S_p);





/////////////////////////////////////////////
// t0 =A,t1 =B,t2 =C,t3 =D,t4 =E,t5 =F     //
// X1 = R0_x ,X2 = R1_x, after step 15 X3 = R1_x
// Y1 = R0_y ,Y2 = R1_y, after step  Y3 = R1_x
// Z1 = R0_z ,Z2 = R1_z, after step 19 Z3 = R1_z
// 
////////////////////////////////////////////
    property point_add_p;
       addra == PA_S

        |=>
        
       douta == {UOP_DO_MUL_p,   UOP_OPR_R0_X,       UOP_OPR_R1_X}  // t0 <- X1.X2
    ##1  douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_R0_Y,       UOP_OPR_R1_Y}  // t1 <- Y1.Y2
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_B}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_R0_Z,       UOP_OPR_R1_Z}  // t2 <- Z1.Z2
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_C}
    ##1 douta == {UOP_DO_ADD_p,   UOP_OPR_R0_X,       UOP_OPR_R0_Y}  // t3 <- X1+Y1
    ##1 douta == {UOP_ST_ADD_p,   UOP_OPR_D,          UOP_OPR_DONTCARE}
    ##1 douta == {UOP_DO_ADD_p,   UOP_OPR_R1_X,       UOP_OPR_R1_Y}  // t4 <- X2+Y2
    ##1 douta == {UOP_ST_ADD_p,   UOP_OPR_E,          UOP_OPR_DONTCARE}
    ##1  douta == {UOP_DO_MUL_p,   UOP_OPR_D,          UOP_OPR_E}     // t3 <- t3.t4
    ##1  douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_D}
    ##1  douta == {UOP_DO_ADD_p,   UOP_OPR_A,          UOP_OPR_B}     //t4 <- t0+t1
    ##1  douta == {UOP_ST_ADD_p,   UOP_OPR_E,          UOP_OPR_DONTCARE}
    ##1  douta == {UOP_DO_SUB_p,   UOP_OPR_D,          UOP_OPR_E}     // t3 <- t3 - t4
    ##1  douta == {UOP_ST_ADD_p,   UOP_OPR_D,          UOP_OPR_DONTCARE}
    ##1  douta == {UOP_DO_ADD_p,   UOP_OPR_R0_X,       UOP_OPR_R0_Z}  // t4 <- X1+Z1
    ##1  douta == {UOP_ST_ADD_p,   UOP_OPR_E,          UOP_OPR_DONTCARE}
    ##1  douta == {UOP_DO_ADD_p,   UOP_OPR_R1_X,       UOP_OPR_R1_Z}  // t5 <- X2 + Z2
    ##1  douta == {UOP_ST_ADD_p,   UOP_OPR_F,          UOP_OPR_DONTCARE}
    ##1  douta == {UOP_DO_MUL_p,   UOP_OPR_E,          UOP_OPR_F}     //t4 <- t4.t5
    ##1  douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_E}
    ##1  douta == {UOP_DO_ADD_p,   UOP_OPR_A,          UOP_OPR_C}     // t5 <- t0+t2
    ##1  douta == {UOP_ST_ADD_p,   UOP_OPR_F,          UOP_OPR_DONTCARE}
    ##1  douta == {UOP_DO_SUB_p,   UOP_OPR_E,          UOP_OPR_F}     // t4 <- t4 - t5
    ##1  douta == {UOP_ST_ADD_p,   UOP_OPR_E,          UOP_OPR_DONTCARE}
    ##1  douta == {UOP_DO_ADD_p,   UOP_OPR_R0_Y,       UOP_OPR_R0_Z}  // t5 <- Y1+Z1
    ##1  douta == {UOP_ST_ADD_p,   UOP_OPR_F,          UOP_OPR_DONTCARE}
    ##1  douta == {UOP_DO_ADD_p,   UOP_OPR_R1_Y,       UOP_OPR_R1_Z}  // X3 <- Y2 +Z2
    ##1  douta == {UOP_ST_ADD_p,   UOP_OPR_R1_X,       UOP_OPR_DONTCARE}        
    ##1  douta == {UOP_DO_MUL_p,   UOP_OPR_F,          UOP_OPR_R1_X}  // t5 <- t5.X3
    ##1  douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_F}
    ##1  douta == {UOP_DO_ADD_p,   UOP_OPR_B,          UOP_OPR_C}     // X3 <- t1 +t2
    ##1  douta == {UOP_ST_ADD_p,   UOP_OPR_R1_X,       UOP_OPR_DONTCARE}
    ##1  douta == {UOP_DO_SUB_p,   UOP_OPR_F,          UOP_OPR_R1_X}  // t5 <- t5-X3
    ##1  douta == {UOP_ST_ADD_p,   UOP_OPR_F,          UOP_OPR_DONTCARE}    
    ##1  douta == {UOP_DO_MUL_p,   UOP_OPR_CONST_E_a,  UOP_OPR_E}     // Z3 <- a.t4
    ##1  douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_R1_Z}
    ##1  douta == {UOP_DO_MUL_p,   UOP_OPR_CONST_E_3b, UOP_OPR_C}     // X3 <-3b.t2
    ##1  douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_R1_X}
    ##1  douta == {UOP_DO_ADD_p,   UOP_OPR_R1_X,       UOP_OPR_R1_Z}  // Z3 <- X3 + Z3
    ##1  douta == {UOP_ST_ADD_p,   UOP_OPR_R1_Z,       UOP_OPR_DONTCARE}
    ##1  douta == {UOP_DO_SUB_p,   UOP_OPR_B,          UOP_OPR_R1_Z}  // X3 <- t1-Z3
    ##1  douta == {UOP_ST_ADD_p,   UOP_OPR_R1_X,       UOP_OPR_DONTCARE}
    ##1  douta == {UOP_DO_ADD_p,   UOP_OPR_B,          UOP_OPR_R1_Z}  // Z3 <- t1+Z3
    ##1  douta == {UOP_ST_ADD_p,   UOP_OPR_R1_Z,       UOP_OPR_DONTCARE}
    ##1  douta == {UOP_DO_MUL_p,   UOP_OPR_R1_X,       UOP_OPR_R1_Z}  // Y3 <- X3.Z3
    ##1  douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_R1_Y}
    ##1  douta == {UOP_DO_ADD_p,   UOP_OPR_A,          UOP_OPR_A}     // t1 <- t0+t0
    ##1  douta == {UOP_ST_ADD_p,   UOP_OPR_B,          UOP_OPR_DONTCARE}
    ##1  douta == {UOP_DO_ADD_p,   UOP_OPR_B,          UOP_OPR_A}     // t1 <- t1+t0
    ##1  douta == {UOP_ST_ADD_p,   UOP_OPR_B,          UOP_OPR_DONTCARE}
    ##1  douta == {UOP_DO_MUL_p,   UOP_OPR_CONST_E_a,  UOP_OPR_C}     // t2 <- a.t2
    ##1  douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_C}
    ##1  douta == {UOP_DO_MUL_p,   UOP_OPR_CONST_E_3b, UOP_OPR_E}     // t4 <- 3b.t4
    ##1  douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_E}
    ##1  douta == {UOP_DO_ADD_p,   UOP_OPR_B,          UOP_OPR_C}     // t1<-t1+t2
    ##1  douta == {UOP_ST_ADD_p,   UOP_OPR_B,          UOP_OPR_DONTCARE}
    ##1  douta == {UOP_DO_SUB_p,   UOP_OPR_A,          UOP_OPR_C}     // t2<-t0-t2
    ##1  douta == {UOP_ST_ADD_p,   UOP_OPR_C,          UOP_OPR_DONTCARE}            
    ##1  douta == {UOP_DO_MUL_p,   UOP_OPR_CONST_E_a,  UOP_OPR_C}     // t2<- a.t2
    ##1  douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_C}
    ##1  douta == {UOP_DO_ADD_p,   UOP_OPR_E,          UOP_OPR_C}     // t4<-t4+t2
    ##1  douta == {UOP_ST_ADD_p,   UOP_OPR_E,          UOP_OPR_DONTCARE}
    ##1  douta == {UOP_DO_MUL_p,   UOP_OPR_B,          UOP_OPR_E}     // t0 <- t1.t4
    ##1  douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A}            
    ##1  douta == {UOP_DO_ADD_p,   UOP_OPR_R1_Y,       UOP_OPR_A}     // Y3 <- Y3+t0
    ##1  douta == {UOP_ST_ADD_p,   UOP_OPR_R1_Y,       UOP_OPR_DONTCARE}
    ##1  douta == {UOP_DO_MUL_p,   UOP_OPR_F,          UOP_OPR_E}     // t0<-t5.t4
    ##1  douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A}
    ##1  douta == {UOP_DO_MUL_p,   UOP_OPR_D,          UOP_OPR_R1_X}  // X3 <- t3.X3
    ##1  douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_R1_X}            
    ##1  douta == {UOP_DO_SUB_p,   UOP_OPR_R1_X,       UOP_OPR_A}     // X3 <- X3-t0
    ##1  douta == {UOP_ST_ADD_p,   UOP_OPR_R1_X,       UOP_OPR_DONTCARE}
    ##1  douta == {UOP_DO_MUL_p,   UOP_OPR_D,          UOP_OPR_B}     // t0 <- t3.t1
    ##1  douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A}
    ##1  douta == {UOP_DO_MUL_p,   UOP_OPR_F,          UOP_OPR_R1_Z}  //Z3 <- t5.Z3
    ##1  douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_R1_Z}            
    ##1  douta == {UOP_DO_ADD_p,   UOP_OPR_R1_Z,       UOP_OPR_A}     // Z3 <- Z3 + t0
    ##1  douta == {UOP_ST_ADD_p,   UOP_OPR_R1_Z,       UOP_OPR_DONTCARE}
    ##1  addra == PD_S;
endproperty

point_add_a: assert property(disable iff(!rst_n) point_add_p);




    property point_dbl_p;

       addra == PD_S

        |=>
        
       douta == {UOP_DO_MUL_p,   UOP_OPR_R0_X,       UOP_OPR_R0_X}  // t0 <- X1.X2
    ##1  douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_R0_Y,       UOP_OPR_R0_Y}  // t1 <- Y1.Y2
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_B}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_R0_Z,       UOP_OPR_R0_Z}  // t2 <- Z1.Z2
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_C}
    ##1 douta == {UOP_DO_ADD_p,   UOP_OPR_R0_X,       UOP_OPR_R0_Y}  // t3 <- X1+Y1
    ##1 douta == {UOP_ST_ADD_p,   UOP_OPR_D,          UOP_OPR_DONTCARE}
    ##1 douta == {UOP_DO_ADD_p,   UOP_OPR_R0_X,       UOP_OPR_R0_Y}  // t4 <- X2+Y2
    ##1 douta == {UOP_ST_ADD_p,   UOP_OPR_E,          UOP_OPR_DONTCARE}
    ##1  douta == {UOP_DO_MUL_p,   UOP_OPR_D,          UOP_OPR_E}     // t3 <- t3.t4
    ##1  douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_D}
    ##1  douta == {UOP_DO_ADD_p,   UOP_OPR_A,          UOP_OPR_B}     //t4 <- t0+t1
    ##1  douta == {UOP_ST_ADD_p,   UOP_OPR_E,          UOP_OPR_DONTCARE}
    ##1  douta == {UOP_DO_SUB_p,   UOP_OPR_D,          UOP_OPR_E}     // t3 <- t3 - t4
    ##1  douta == {UOP_ST_ADD_p,   UOP_OPR_D,          UOP_OPR_DONTCARE}
    ##1  douta == {UOP_DO_ADD_p,   UOP_OPR_R0_X,       UOP_OPR_R0_Z}  // t4 <- X1+Z1
    ##1  douta == {UOP_ST_ADD_p,   UOP_OPR_E,          UOP_OPR_DONTCARE}
    ##1  douta == {UOP_DO_ADD_p,   UOP_OPR_R0_X,       UOP_OPR_R0_Z}  // t5 <- X2 + Z2
    ##1  douta == {UOP_ST_ADD_p,   UOP_OPR_F,          UOP_OPR_DONTCARE}
    ##1  douta == {UOP_DO_MUL_p,   UOP_OPR_E,          UOP_OPR_F}     //t4 <- t4.t5
    ##1  douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_E}
    ##1  douta == {UOP_DO_ADD_p,   UOP_OPR_A,          UOP_OPR_C}     // t5 <- t0+t2
    ##1  douta == {UOP_ST_ADD_p,   UOP_OPR_F,          UOP_OPR_DONTCARE}
    ##1  douta == {UOP_DO_SUB_p,   UOP_OPR_E,          UOP_OPR_F}     // t4 <- t4 - t5
    ##1  douta == {UOP_ST_ADD_p,   UOP_OPR_E,          UOP_OPR_DONTCARE}
    ##1  douta == {UOP_DO_ADD_p,   UOP_OPR_R0_Y,       UOP_OPR_R0_Z}  // t5 <- Y1+Z1
    ##1  douta == {UOP_ST_ADD_p,   UOP_OPR_F,          UOP_OPR_DONTCARE}
    ##1  douta == {UOP_DO_ADD_p,   UOP_OPR_R0_Y,       UOP_OPR_R0_Z}  // X3 <- Y2 +Z2
    ##1  douta == {UOP_ST_ADD_p,   UOP_OPR_R0_X,       UOP_OPR_DONTCARE}        
    ##1  douta == {UOP_DO_MUL_p,   UOP_OPR_F,          UOP_OPR_R0_X}  // t5 <- t5.X3
    ##1  douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_F}
    ##1  douta == {UOP_DO_ADD_p,   UOP_OPR_B,          UOP_OPR_C}     // X3 <- t1 +t2
    ##1  douta == {UOP_ST_ADD_p,   UOP_OPR_R0_X,       UOP_OPR_DONTCARE}
    ##1  douta == {UOP_DO_SUB_p,   UOP_OPR_F,          UOP_OPR_R0_X}  // t5 <- t5-X3
    ##1  douta == {UOP_ST_ADD_p,   UOP_OPR_F,          UOP_OPR_DONTCARE}    
    ##1  douta == {UOP_DO_MUL_p,   UOP_OPR_CONST_E_a,  UOP_OPR_E}     // Z3 <- a.t4
    ##1  douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_R0_Z}
    ##1  douta == {UOP_DO_MUL_p,   UOP_OPR_CONST_E_3b, UOP_OPR_C}     // X3 <-3b.t2
    ##1  douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_R0_X}
    ##1  douta == {UOP_DO_ADD_p,   UOP_OPR_R0_X,       UOP_OPR_R0_Z}  // Z3 <- X3 + Z3
    ##1  douta == {UOP_ST_ADD_p,   UOP_OPR_R0_Z,       UOP_OPR_DONTCARE}
    ##1  douta == {UOP_DO_SUB_p,   UOP_OPR_B,          UOP_OPR_R0_Z}  // X3 <- t1-Z3
    ##1  douta == {UOP_ST_ADD_p,   UOP_OPR_R0_X,       UOP_OPR_DONTCARE}
    ##1  douta == {UOP_DO_ADD_p,   UOP_OPR_B,          UOP_OPR_R0_Z}  // Z3 <- t1+Z3
    ##1  douta == {UOP_ST_ADD_p,   UOP_OPR_R0_Z,       UOP_OPR_DONTCARE}
    ##1  douta == {UOP_DO_MUL_p,   UOP_OPR_R0_X,       UOP_OPR_R0_Z}  // Y3 <- X3.Z3
    ##1  douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_R0_Y}
    ##1  douta == {UOP_DO_ADD_p,   UOP_OPR_A,          UOP_OPR_A}     // t1 <- t0+t0
    ##1  douta == {UOP_ST_ADD_p,   UOP_OPR_B,          UOP_OPR_DONTCARE}
    ##1  douta == {UOP_DO_ADD_p,   UOP_OPR_B,          UOP_OPR_A}     // t1 <- t1+t0
    ##1  douta == {UOP_ST_ADD_p,   UOP_OPR_B,          UOP_OPR_DONTCARE}
    ##1  douta == {UOP_DO_MUL_p,   UOP_OPR_CONST_E_a,  UOP_OPR_C}     // t2 <- a.t2
    ##1  douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_C}
    ##1  douta == {UOP_DO_MUL_p,   UOP_OPR_CONST_E_3b, UOP_OPR_E}     // t4 <- 3b.t4
    ##1  douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_E}
    ##1  douta == {UOP_DO_ADD_p,   UOP_OPR_B,          UOP_OPR_C}     // t1<-t1+t2
    ##1  douta == {UOP_ST_ADD_p,   UOP_OPR_B,          UOP_OPR_DONTCARE}
    ##1  douta == {UOP_DO_SUB_p,   UOP_OPR_A,          UOP_OPR_C}     // t2<-t0-t2
    ##1  douta == {UOP_ST_ADD_p,   UOP_OPR_C,          UOP_OPR_DONTCARE}            
    ##1  douta == {UOP_DO_MUL_p,   UOP_OPR_CONST_E_a,  UOP_OPR_C}     // t2<- a.t2
    ##1  douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_C}
    ##1  douta == {UOP_DO_ADD_p,   UOP_OPR_E,          UOP_OPR_C}     // t4<-t4+t2
    ##1  douta == {UOP_ST_ADD_p,   UOP_OPR_E,          UOP_OPR_DONTCARE}
    ##1  douta == {UOP_DO_MUL_p,   UOP_OPR_B,          UOP_OPR_E}     // t0 <- t1.t4
    ##1  douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A}            
    ##1  douta == {UOP_DO_ADD_p,   UOP_OPR_R0_Y,       UOP_OPR_A}     // Y3 <- Y3+t0
    ##1  douta == {UOP_ST_ADD_p,   UOP_OPR_R0_Y,       UOP_OPR_DONTCARE}
    ##1  douta == {UOP_DO_MUL_p,   UOP_OPR_F,          UOP_OPR_E}     // t0<-t5.t4
    ##1  douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A}
    ##1  douta == {UOP_DO_MUL_p,   UOP_OPR_D,          UOP_OPR_R0_X}  // X3 <- t3.X3
    ##1  douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_R0_X}            
    ##1  douta == {UOP_DO_SUB_p,   UOP_OPR_R0_X,       UOP_OPR_A}     // X3 <- X3-t0
    ##1  douta == {UOP_ST_ADD_p,   UOP_OPR_R0_X,       UOP_OPR_DONTCARE}
    ##1  douta == {UOP_DO_MUL_p,   UOP_OPR_D,          UOP_OPR_B}     // t0 <- t3.t1
    ##1  douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A}
    ##1  douta == {UOP_DO_MUL_p,   UOP_OPR_F,          UOP_OPR_R0_Z}  //Z3 <- t5.Z3
    ##1  douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_R0_Z}            
    ##1  douta == {UOP_DO_ADD_p,   UOP_OPR_R0_Z,       UOP_OPR_A}     // Z3 <- Z3 + t0
    ##1  douta == {UOP_ST_ADD_p,   UOP_OPR_R0_Z,       UOP_OPR_DONTCARE}
    ##1 douta == {UOP_NOP,        UOP_OPR_DONTCARE,          UOP_OPR_DONTCARE}
    ##1 douta == {UOP_NOP,        UOP_OPR_DONTCARE,          UOP_OPR_DONTCARE}
    ##1 douta == {UOP_NOP,        UOP_OPR_DONTCARE,          UOP_OPR_DONTCARE}
    ##1 douta == {UOP_NOP,        UOP_OPR_DONTCARE,          UOP_OPR_DONTCARE};
endproperty

point_dbl_a: assert property(disable iff(!rst_n) point_dbl_p);






property conv_p;
    addra == CONV_S

    |->

    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_INV_OUT,    UOP_OPR_R0_Y}          // y_MONT = fp_mult(Z_inv, Y_MONT, p) .     Y = Y/Z (Ref: sec 2 Montgomery curves and their arithmetic The case of large characteristic fields Craig Costello · Benjamin Smith)
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_Qy_MONT}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_INV_OUT,    UOP_OPR_R0_X}          // x_MONT = fp_mult(Z_inv, X_MONT, p)       X = X/Z
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_Qx_MONT}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_CONST_ONE,  UOP_OPR_Qy_MONT}       // y_affine = fp_mult(y_MONT, 1, p)         conversion from mont domain to normal
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_Qy_AFFN}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_CONST_ONE,  UOP_OPR_Qx_MONT}       // y_affine = fp_mult(y_MONT, 1, p)         conversion from mont domain to normal
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_Qx_AFFN}
    ##1 douta == {UOP_NOP,        UOP_OPR_DONTCARE,   UOP_OPR_DONTCARE}
    ##1 douta == {UOP_NOP,        UOP_OPR_DONTCARE,   UOP_OPR_DONTCARE}
    ##1 douta == {UOP_NOP,        UOP_OPR_DONTCARE,   UOP_OPR_DONTCARE}
    ##1 douta == {UOP_NOP,        UOP_OPR_DONTCARE,   UOP_OPR_DONTCARE};
endproperty

conv_a: assert property(disable iff(!rst_n) conv_p);

////////////////////////////////////////////////////////////////
// s = [k^-1((h-d) + r (privKey-d))] + [k^-1(d + r.d)] mod n  //
//                                                            //
////////////////////////////////////////////////////////////////


property sign0_p;
    addra == SIGN0_S

    |->

    ##1 douta == {UOP_DO_ADD_q,   UOP_OPR_CONST_ZERO, UOP_OPR_Qx_AFFN}       // R = Qx_AFFN
    ##1 douta == {UOP_ST_ADD_q,   UOP_OPR_SIGN_R,     UOP_OPR_DONTCARE}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_SIGN_R,     UOP_OPR_CONST_R2_q}   // E = mm(R, R2) % q           r conversion to montgomery domain
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_E}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_SCALAR_G,   UOP_OPR_CONST_R2_q}    // k_MONT = mm(k, R2) % q     k conversion to montgomery domain
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_INV_IN}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_PRIVKEY,    UOP_OPR_CONST_R2_q}    // A = mm(privKey, R2) % q    privkey conversion to montgomery domain
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_HASH_MSG,   UOP_OPR_CONST_R2_q}    // B = mm(h, R2) % q          hash msg conversion to montgomery domain
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_B}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_MASKING,    UOP_OPR_CONST_R2_q}    // D = mm(masking_d, R2) % q  d conversion to montgomery domain
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_D}
    ##1 douta == {UOP_DO_SUB_q,   UOP_OPR_A,          UOP_OPR_D}            // A = (A - D) % q             (privkey-d)
    ##1 douta == {UOP_ST_ADD_q,   UOP_OPR_A,          UOP_OPR_DONTCARE}
    ##1 douta == {UOP_DO_SUB_q,   UOP_OPR_B,          UOP_OPR_D}             // B = (B - D) % q            (h-d)
    ##1 douta == {UOP_ST_ADD_q,   UOP_OPR_B,          UOP_OPR_DONTCARE}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A,          UOP_OPR_E}             // C = mm(A, E) % q           r(privkey-d)
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_C}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_D,          UOP_OPR_E}             // F = mm(D, E) % q           r.d
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_F}
    ##1 douta == {UOP_DO_ADD_q,   UOP_OPR_D,          UOP_OPR_C}             // C = (C + D) % q            (d + r (privKey-d))
    ##1 douta == {UOP_ST_ADD_q,   UOP_OPR_C,          UOP_OPR_DONTCARE}
    ##1 douta == {UOP_DO_ADD_q,   UOP_OPR_B,          UOP_OPR_F}             // D = (B + F) % q             ((h-d) + r.d)
    ##1 douta == {UOP_ST_ADD_q,   UOP_OPR_D,          UOP_OPR_DONTCARE};
endproperty



sign0_a: assert property(disable iff(!rst_n) sign0_p);


property sign1_p;
    addra ==  SIGN1_S

    |->

     ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_INV_OUT,    UOP_OPR_C}           // C = fp_mult(C, k_inv, q)      C = k^-1.((h-d) + r (privKey-d))
     ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_C}
     ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_INV_OUT,    UOP_OPR_D}           // D = fp_mult(D, k_inv, q)      D = k^-1.(d + r.d)
     ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_D}
     ##1 douta == {UOP_DO_ADD_q,   UOP_OPR_C,          UOP_OPR_D}           // B = C + D % q                 B = (C+D) mod n
     ##1 douta == {UOP_ST_ADD_q,   UOP_OPR_B,          UOP_OPR_DONTCARE}
     ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_CONST_ONE,  UOP_OPR_B}          // B = fp_mult(B, 1, q)          conversion from montgomery to normal domain
     ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_SIGN_S}
     ##1 douta == {UOP_NOP,        UOP_OPR_DONTCARE,   UOP_OPR_DONTCARE}
     ##1 douta == {UOP_NOP,        UOP_OPR_DONTCARE,   UOP_OPR_DONTCARE}
     ##1 douta == {UOP_NOP,        UOP_OPR_DONTCARE,   UOP_OPR_DONTCARE}
     ##1 douta == {UOP_NOP,        UOP_OPR_DONTCARE,   UOP_OPR_DONTCARE};
endproperty

sign1_a: assert property(disable iff(!rst_n) sign1_p);


// Inputs pubKey,h(hash msg),r(respective r part in signature),s(respective s part in signature)
// s1 = s^-1 mod q
// R' = (h* s1)*G + (r*s1)*pubKey
// r' = R'x mod q
//
// Verify part0 to convert inputs to the mont domain




property verify0_p0_p;
    addra == VER0_P0_S

    |->

    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_HASH_MSG,   UOP_OPR_CONST_R2_q}    // A = mm(h, R2) % q        conversion of hash msg to mont domain
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_SIGN_R,     UOP_OPR_CONST_R2_q}    // B = mm(R, R2) % q        conversion of r to mont domain
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_B}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_SIGN_S,     UOP_OPR_CONST_R2_q}    // INV_IN = mm(S, R2) % q   conversion of s to mont domain
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_INV_IN}
    ##1 douta == {UOP_NOP,        UOP_OPR_DONTCARE,   UOP_OPR_DONTCARE}
    ##1 douta == {UOP_NOP,        UOP_OPR_DONTCARE,   UOP_OPR_DONTCARE}
    ##1 douta == {UOP_NOP,        UOP_OPR_DONTCARE,   UOP_OPR_DONTCARE}
    ##1 douta == {UOP_NOP,        UOP_OPR_DONTCARE,   UOP_OPR_DONTCARE};
endproperty

verify0_p0_a: assert property(disable iff(!rst_n)verify0_p0_p);



// verify part1 use the generated s^-1 for the intermediate computations and convert them 
// into normal domain so in next step they could be used in the point multiplication.


property verify0_p1_p;
    addra == VER0_P1_S

    |->

    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_INV_OUT,    UOP_OPR_A}             // A = mm(h, S_INV) % q    h*s^-1 mod q 
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_CONST_ONE,  UOP_OPR_A}             // hs1 = mm(A, 1) % q      conversion from mont domain to normal domain
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_SCALAR_G}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_INV_OUT,    UOP_OPR_B}             // B = mm(r, S_INV) % q    r*s^-1 mod q  
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_B}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_CONST_ONE,  UOP_OPR_B}             // rs1 = mm(B, 1) % q      conversion from mont domain to normal domain
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_SCALAR_PK}
    ##1 douta == {UOP_NOP,        UOP_OPR_DONTCARE,   UOP_OPR_DONTCARE}
    ##1 douta == {UOP_NOP,        UOP_OPR_DONTCARE,   UOP_OPR_DONTCARE}
    ##1 douta == {UOP_NOP,        UOP_OPR_DONTCARE,   UOP_OPR_DONTCARE}
    ##1 douta == {UOP_NOP,        UOP_OPR_DONTCARE,   UOP_OPR_DONTCARE};
endproperty

verify0_p1_a: assert property(disable iff(!rst_n)verify0_p1_p);


//verify1 (h*s^-1)*G

property verify1_st_p;
    addra == VER1_ST_S

    |->

    ##1 douta == {UOP_DO_ADD_p,   UOP_OPR_R0_X,       UOP_OPR_CONST_ZERO}     // computed results stored in R0, in the previous seq
    ##1 douta == {UOP_ST_ADD_p,   UOP_OPR_P1_X_MONT,  UOP_OPR_DONTCARE}
    ##1 douta == {UOP_DO_ADD_p,   UOP_OPR_R0_Y,       UOP_OPR_CONST_ZERO}
    ##1 douta == {UOP_ST_ADD_p,   UOP_OPR_P1_Y_MONT,  UOP_OPR_DONTCARE}
    ##1 douta == {UOP_DO_ADD_p,   UOP_OPR_R0_Z,       UOP_OPR_CONST_ZERO}
    ##1 douta == {UOP_ST_ADD_p,   UOP_OPR_P1_Z_MONT,  UOP_OPR_DONTCARE};

endproperty

verify1_st_a: assert property(disable iff(!rst_n)verify1_st_p);


// verify2 Initialise with PubKey(PK) for (r*s^-1)*PK computation
// It is stored R1, but R1_z is initialised with one_mont 



property verify2_init_pk_p;

    addra == PM_INIT_PK_S

    |->

    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_Qx_AFFN,           UOP_OPR_CONST_R2_p}     //Through DSA seq pubkey is stored to QX and QY prior to start of this seq
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,          UOP_OPR_R1_X}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_Qy_AFFN,           UOP_OPR_CONST_R2_p}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,          UOP_OPR_R1_Y}
    ##1 douta == {UOP_DO_ADD_p,   UOP_OPR_CONST_ONE_MONT,    UOP_OPR_CONST_ZERO}   // 
    ##1 douta == {UOP_ST_ADD_p,   UOP_OPR_R1_Z,              UOP_OPR_DONTCARE};
endproperty

verify2_init_pk_a: assert property (disable iff(!rst_n) verify2_init_pk_p);



 //VER2 point addtion of PA((h*s_inv)*G, (r*s_inv)*PK)
 // t0 =A,t1 =B,t2 =C,t3 =D,t4 =E,t5 =F     //
 // X1 = R0_x ,X2 = P1_x, after step 15 X3 = R0_x
 // Y1 = R0_y ,Y2 = P1_y, after step  Y3 = R0_x
 // Z1 = R0_z ,Z2 = P1_z, after step 19 Z3 = R0_z

 property verify2_pointadd_p;

    addra == VER2_PA_S
    |->

    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_R0_X,       UOP_OPR_P1_X_MONT}  // A = fp_mult(P0.X, P1.X, p)      t0 <- X1.X2
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_R0_Y,       UOP_OPR_P1_Y_MONT}  // B = fp_mult(P0.Y, P1.Y, p)      t1 <- Y1.Y2
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_B}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_R0_Z,       UOP_OPR_P1_Z_MONT}  // C = fp_mult(P0.Z, P1.Z, p)      t2 <- Z1.Z2
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_C}
    ##1 douta == {UOP_DO_ADD_p,   UOP_OPR_R0_X,       UOP_OPR_R0_Y}      // D = (P0.X + P0.Y) % p            t3 <- X1+Y1
    ##1 douta == {UOP_ST_ADD_p,   UOP_OPR_D,          UOP_OPR_DONTCARE}
    ##1 douta == {UOP_DO_ADD_p,   UOP_OPR_P1_X_MONT,  UOP_OPR_P1_Y_MONT}  // E = (P1.X + P1.Y) % p           t4 <- X2+Y2
    ##1 douta == {UOP_ST_ADD_p,   UOP_OPR_E,          UOP_OPR_DONTCARE}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_D,          UOP_OPR_E}         // D = fp_mult(D, E, p)             t3 <- t3.t4
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_D}
    ##1 douta == {UOP_DO_ADD_p,   UOP_OPR_A,          UOP_OPR_B}         // E = (A + B) % p                  t4 <- t0+t1
    ##1 douta == {UOP_ST_ADD_p,   UOP_OPR_E,          UOP_OPR_DONTCARE}
    ##1 douta == {UOP_DO_SUB_p,   UOP_OPR_D,          UOP_OPR_E}        // D = (D - E) % p                   t3 <- t3 - t4
    ##1 douta == {UOP_ST_ADD_p,   UOP_OPR_D,          UOP_OPR_DONTCARE}
    ##1 douta == {UOP_DO_ADD_p,   UOP_OPR_R0_X,       UOP_OPR_R0_Z}      // E = (P0.X + P0.Z) % p            t4 <- X1+Z1
    ##1 douta == {UOP_ST_ADD_p,   UOP_OPR_E,          UOP_OPR_DONTCARE}
    ##1 douta == {UOP_DO_ADD_p,   UOP_OPR_P1_X_MONT,  UOP_OPR_P1_Z_MONT}  // F = (P1.X + P1.Z) % p           t5 <- X2 + Z2
    ##1 douta == {UOP_ST_ADD_p,   UOP_OPR_F,          UOP_OPR_DONTCARE}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_E,          UOP_OPR_F}         // E = fp_mult(E, F, p)             t4 <- t4.t5
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_E}
    ##1 douta == {UOP_DO_ADD_p,   UOP_OPR_A,          UOP_OPR_C}         // F = (A + C) % p                  t5 <- t0+t2
    ##1 douta == {UOP_ST_ADD_p,   UOP_OPR_F,          UOP_OPR_DONTCARE}
    ##1 douta == {UOP_DO_SUB_p,   UOP_OPR_E,          UOP_OPR_F}         // E = (E - F) % p                  t4 <- t4 - t5
    ##1 douta == {UOP_ST_ADD_p,   UOP_OPR_E,          UOP_OPR_DONTCARE}
    ##1 douta == {UOP_DO_ADD_p,   UOP_OPR_R0_Y,       UOP_OPR_R0_Z}     // F = (P0.Y + P0.Z) % p             t5 <- Y1+Z1
    ##1 douta == {UOP_ST_ADD_p,   UOP_OPR_F,          UOP_OPR_DONTCARE}
    ##1 douta == {UOP_DO_ADD_p,   UOP_OPR_P1_Y_MONT,  UOP_OPR_P1_Z_MONT}  // X3 = (P1.Y + P1.Z) % p          X3 <- Y2 +Z2
    ##1 douta == {UOP_ST_ADD_p,   UOP_OPR_R0_X,       UOP_OPR_DONTCARE}       
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_F,          UOP_OPR_R0_X}      // F = fp_mult(F, X3, p)            t5 <- t5.X3
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_F}
    ##1 douta == {UOP_DO_ADD_p,   UOP_OPR_B,          UOP_OPR_C}         // X3 = (B + C) % p                 X3 <- t1 +t2
    ##1 douta == {UOP_ST_ADD_p,   UOP_OPR_R0_X,       UOP_OPR_DONTCARE}
    ##1 douta == {UOP_DO_SUB_p,   UOP_OPR_F,          UOP_OPR_R0_X}      // F = (F - X3) % p                t5 <- t5-X3
    ##1 douta == {UOP_ST_ADD_p,   UOP_OPR_F,          UOP_OPR_DONTCARE}   
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_CONST_E_a,  UOP_OPR_E}         // Z3 = fp_mult(ECC.a, E, p)        Z3 <- a.t4
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_R0_Z}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_CONST_E_3b, UOP_OPR_C}         // X3 = fp_mult(ECC.3b, C, p)       X3 <-3b.t2
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_R0_X}
    ##1 douta == {UOP_DO_ADD_p,   UOP_OPR_R0_X,       UOP_OPR_R0_Z}      // Z3 = (X3 + Z3) % p               Z3 <- X3 + Z3
    ##1 douta == {UOP_ST_ADD_p,   UOP_OPR_R0_Z,       UOP_OPR_DONTCARE}
    ##1 douta == {UOP_DO_SUB_p,   UOP_OPR_B,          UOP_OPR_R0_Z}      // X3 = (B - Z3) % p                X3 <- t1-Z3
    ##1 douta == {UOP_ST_ADD_p,   UOP_OPR_R0_X,       UOP_OPR_DONTCARE}
    ##1 douta == {UOP_DO_ADD_p,   UOP_OPR_B,          UOP_OPR_R0_Z}      // Z3 = (B + Z3) % p                Z3 <- t1+Z3
    ##1 douta == {UOP_ST_ADD_p,   UOP_OPR_R0_Z,       UOP_OPR_DONTCARE}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_R0_X,       UOP_OPR_R0_Z}      // Y3 = fp_mult(X3, Z3, p)          Y3 <- X3.Z3
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_R0_Y}
    ##1 douta == {UOP_DO_ADD_p,   UOP_OPR_A,          UOP_OPR_A}         // B = (A + A) % p                  t1 <- t0+t0
    ##1 douta == {UOP_ST_ADD_p,   UOP_OPR_B,          UOP_OPR_DONTCARE}
    ##1 douta == {UOP_DO_ADD_p,   UOP_OPR_B,          UOP_OPR_A}         // B = (B + A) % p                  t1 <- t1+t0
    ##1 douta == {UOP_ST_ADD_p,   UOP_OPR_B,          UOP_OPR_DONTCARE}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_CONST_E_a,  UOP_OPR_C}         // C = fp_mult(ECC.a, C, p)         t2 <- a.t2
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_C}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_CONST_E_3b, UOP_OPR_E}         // E = fp_mult(ECC.3b, E, p)        t4 <- 3b.t4
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_E}
    ##1 douta == {UOP_DO_ADD_p,   UOP_OPR_B,          UOP_OPR_C}         // B = (B + C) % p                  t1<-t1+t2
    ##1 douta == {UOP_ST_ADD_p,   UOP_OPR_B,          UOP_OPR_DONTCARE}
    ##1 douta == {UOP_DO_SUB_p,   UOP_OPR_A,          UOP_OPR_C}          // C = (A - C) % p                 t2<-t0-t2
    ##1 douta == {UOP_ST_ADD_p,   UOP_OPR_C,          UOP_OPR_DONTCARE}            
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_CONST_E_a,  UOP_OPR_C}          // C = fp_mult(ECC.a, C, p)        t2<- a.t2
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_C}
    ##1 douta == {UOP_DO_ADD_p,   UOP_OPR_E,          UOP_OPR_C}          // E = (E + C) % p                 t4<-t4+t2
    ##1 douta == {UOP_ST_ADD_p,   UOP_OPR_E,          UOP_OPR_DONTCARE}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_B,          UOP_OPR_E}          // A = fp_mult(B, E, p)            t0 <- t1.t4
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A}            
    ##1 douta == {UOP_DO_ADD_p,   UOP_OPR_R0_Y,       UOP_OPR_A}          // Y3 = (Y3 + A) % p               Y3 <- Y3+t0
    ##1 douta == {UOP_ST_ADD_p,   UOP_OPR_R0_Y,       UOP_OPR_DONTCARE}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_F,          UOP_OPR_E}          // A = fp_mult(F, E, p)            t0<-t5.t4
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_D,          UOP_OPR_R0_X}       // X3 = fp_mult(D, X3, p)          X3 <- t3.X3
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_R0_X}            
    ##1 douta == {UOP_DO_SUB_p,   UOP_OPR_R0_X,       UOP_OPR_A}          // X3 = (X3 - A) % p               X3 <- X3-t0
    ##1 douta == {UOP_ST_ADD_p,   UOP_OPR_R0_X,       UOP_OPR_DONTCARE}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_D,          UOP_OPR_B}          // A = fp_mult(D, B, p)            t0 <- t3.t1
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_F,          UOP_OPR_R0_Z}       // Z3 = fp_mult(F, Z3, p)          Z3 <- t5.Z3
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_R0_Z}            
    ##1 douta == {UOP_DO_ADD_p,   UOP_OPR_R0_Z,       UOP_OPR_A}          // Z3 = (Z3 + A) % p               Z3 <- Z3 + t0
    ##1 douta == {UOP_ST_ADD_p,   UOP_OPR_R0_Z,       UOP_OPR_DONTCARE}
    ##1 douta == {UOP_DO_ADD_p,   UOP_OPR_R0_Z,       UOP_OPR_CONST_ZERO} // Zinv_IN = P1_Z                    
    ##1 douta == {UOP_ST_ADD_p,   UOP_OPR_INV_IN,     UOP_OPR_DONTCARE};
endproperty

verify2_pointadd_a: assert property (disable iff(!rst_n) verify2_pointadd_p);





property inv_modp_p;
    addra == INV_S

    |->
    ##1 douta == {UOP_DO_ADD_p,   UOP_OPR_CONST_ZERO, UOP_OPR_CONST_ONE_MONT}    // precompute[0] = UOP_OPR_CONST_ONE_MONT % p
    ##1 douta == {UOP_ST_ADD_p,   UOP_OPR_INV_PRE0,   UOP_OPR_DONTCARE}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_INV_IN,     UOP_OPR_INV_PRE0}    // precompute[1] = fp_mult(Z, precompute[0], p)
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_INV_PRE1}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_INV_IN,     UOP_OPR_INV_PRE1}    // precompute[2] = fp_mult(Z, precompute[1], p)
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_INV_PRE2}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_INV_IN,     UOP_OPR_INV_PRE2}    // precompute[3] = fp_mult(Z, precompute[2], p)
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_INV_PRE3}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_INV_IN,     UOP_OPR_INV_PRE3}    // precompute[4] = fp_mult(Z, precompute[3], p)
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_INV_PRE4}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_INV_IN,     UOP_OPR_INV_PRE4}    // precompute[5] = fp_mult(Z, precompute[4], p)
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_INV_PRE5}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_INV_IN,     UOP_OPR_INV_PRE5}    // precompute[6] = fp_mult(Z, precompute[5], p)
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_INV_PRE6}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_INV_IN,     UOP_OPR_INV_PRE6}    // precompute[7] = fp_mult(Z, precompute[6], p)
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_INV_PRE0,   UOP_OPR_INV_PRE0}    // a_inv = fp_mult(precompute[0], precompute[0], p)
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV}       // a_inv = fp_mult(a_inv, a_inv, p)   //why these two additional steps ?
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,      UOP_OPR_A_INV}       // a_inv = fp_mult(a_inv, a_inv, p)
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}

    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE3}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE0}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE0}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE0}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE0}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE0}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE0}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE0}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE0}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE0}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE0}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE0}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE0}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE0}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE0}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE0}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE0}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE0}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE0}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE0}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE0}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE0}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE3}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_p, UOP_OPR_A_INV, UOP_OPR_INV_PRE5}
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,   UOP_OPR_INV_OUT};
endproperty
   

inv_modp_a: assert property (disable iff(!rst_n) inv_modp_p);




property inv_modq_p;
    addra == INVq_S

    |->

    ##1 douta == {UOP_DO_ADD_q,   UOP_OPR_CONST_ZERO, UOP_OPR_CONST_ONE_q_MONT}    // precompute[0] = UOP_OPR_CONST_ONE_q_MONT % q
    ##1 douta == {UOP_ST_ADD_q,   UOP_OPR_INV_PRE0,   UOP_OPR_DONTCARE}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_INV_IN,     UOP_OPR_INV_PRE0}    // precompute[1] = fp_mult(Z, precompute[0], q)
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_INV_PRE1}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_INV_IN,     UOP_OPR_INV_PRE1}    // precompute[2] = fp_mult(Z, precompute[1], q)
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_INV_PRE2}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_INV_IN,     UOP_OPR_INV_PRE2}    // precompute[3] = fp_mult(Z, precompute[2], q)
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_INV_PRE3}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_INV_IN,     UOP_OPR_INV_PRE3}    // precompute[4] = fp_mult(Z, precompute[3], q)
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_INV_PRE4}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_INV_IN,     UOP_OPR_INV_PRE4}    // precompute[5] = fp_mult(Z, precompute[4], q)
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_INV_PRE5}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_INV_IN,     UOP_OPR_INV_PRE5}    // precompute[6] = fp_mult(Z, precompute[5], q)
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_INV_PRE6}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_INV_IN,     UOP_OPR_INV_PRE6}    // precompute[7] = fp_mult(Z, precompute[6], q)
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_INV_PRE0,   UOP_OPR_INV_PRE0}    // a_inv = fp_mult(precompute[0], precompute[0], q)
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV}       // a_inv = fp_mult(a_inv, a_inv, q)
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,      UOP_OPR_A_INV}       // a_inv = fp_mult(a_inv, a_inv, q)
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
     
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE6}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE1}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE6}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE6}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE1}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE5}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE1}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE5}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE4}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE0}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE3}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE2}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE0}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE6}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE1}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE3}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE3}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE5}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE5}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE3}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE0}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE0}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE6}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE4}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE0}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE6}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE6}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE6}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE2}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE2}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE2}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE1}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE3}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE0}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE2}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE4}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE7}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE3}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE6}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE5}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE6}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE6}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE3}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE5}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE4}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE0}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE6}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE2}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE6}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE5}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE3}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE1}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE4}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE6}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE1}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE2}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE2}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE4}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE5}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE6}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q,   UOP_OPR_A_INV,   UOP_OPR_A_INV}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_A_INV}
    ##1 douta == {UOP_DO_MUL_q, UOP_OPR_A_INV, UOP_OPR_INV_PRE1}
    ##1 douta == {UOP_ST_MUL_q,   UOP_OPR_DONTCARE,   UOP_OPR_INV_OUT};
endproperty

inv_modq_a: assert property(disable iff(!rst_n) inv_modq_p);



//seq to check the provided pubKey is on the curve or not.
property chk_pk_p;
    addra == CHK_PK_S

    |->

    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_Qy_AFFN,   UOP_OPR_CONST_R2_p}  // A = mm(Qy, R2) % p     conversion of pubkey y to mont domain
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,  UOP_OPR_A}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_A,         UOP_OPR_A}           // A = A*A % p            y^2
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,  UOP_OPR_A}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_Qx_AFFN,   UOP_OPR_CONST_R2_p}  // B = mm(Qx, R2) % p     conversion of pubkey x to mont domain
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,  UOP_OPR_B}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_B,         UOP_OPR_B}           // C = B*B % p            x^2
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,  UOP_OPR_C}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_C,         UOP_OPR_B}           // C = C*B % p            x^3
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,  UOP_OPR_C}
    ##1 douta == {UOP_DO_MUL_p,   UOP_OPR_CONST_E_a, UOP_OPR_B}           // D = ECC.a*B % p        a.x
    ##1 douta == {UOP_ST_MUL_p,   UOP_OPR_DONTCARE,  UOP_OPR_D}
    ##1 douta == {UOP_DO_ADD_p,   UOP_OPR_C,         UOP_OPR_D}           // C = C + D % p          x^3 + a.x
    ##1 douta == {UOP_ST_ADD_p,   UOP_OPR_C,         UOP_OPR_DONTCARE}
    ##1 douta == {UOP_DO_ADD_p,   UOP_OPR_C,         UOP_OPR_CONST_E_b}   // C = C + ECC.b % p      x^3 + a.x + b
    ##1 douta == {UOP_ST_ADD_p,   UOP_OPR_C,         UOP_OPR_DONTCARE}
    ##1 douta == {UOP_DO_SUB_p,   UOP_OPR_A,         UOP_OPR_C}           // PK_valid = A - C % p   y^2 - (x^3 + a.x + b) should be equal to zero if the key is on the curve
    ##1 douta == {UOP_ST_ADD_p,   UOP_OPR_PK_VALID,  UOP_OPR_DONTCARE}
    ##1 douta == {UOP_NOP,        UOP_OPR_DONTCARE,  UOP_OPR_DONTCARE}
    ##1 douta == {UOP_NOP,        UOP_OPR_DONTCARE,  UOP_OPR_DONTCARE}
    ##1 douta == {UOP_NOP,        UOP_OPR_DONTCARE,  UOP_OPR_DONTCARE}
    ##1 douta == {UOP_NOP,        UOP_OPR_DONTCARE,  UOP_OPR_DONTCARE};
endproperty

chk_pk_a: assert property(disable iff(!rst_n) chk_pk_p);



// When storing both the address should not be the same
property store_not_same_addr_p;
    douta[17] ||
    douta[16]
    |->
    douta[11:6]!= douta[5:0];
endproperty

store_not_same_addr_a: assert property(disable iff(!rst_n) store_not_same_addr_p);

//	If it starts with UOP_NOP, the next both fields should be UOP_OPR_DONTCARE
property when_nop_both_addr_0_p;
    douta[17:12] == UOP_NOP 
    |->
    douta[11:0]== {UOP_OPR_DONTCARE,UOP_OPR_DONTCARE};
endproperty

when_nop_both_addr_0_a: assert property(disable iff(!rst_n) when_nop_both_addr_0_p);

//If it starts with UOP_ST_ADD_p/UOP_ST_ADD_q, the last field should be UOP_OPR_DONTCARE.

property when_add_addrb_0_p;
    (douta[17:12] == UOP_ST_ADD_p) ||
    (douta[17:12] == UOP_ST_ADD_q)
    |->
    douta[5:0]== UOP_OPR_DONTCARE;
endproperty

when_add_addrb_0_a: assert property(disable iff(!rst_n) when_add_addrb_0_p);


//o	If it starts with UOP_ST_MUL_p/UOP_ST_MUL_q the middle field should be UOP_OPR_DONTCARE

property when_mult_addra_0_p;
    (douta[17:12] == UOP_ST_MUL_p) ||
    (douta[17:12] == UOP_ST_MUL_q)
    |->
    douta[11:6]== UOP_OPR_DONTCARE;
endproperty

when_mult_addra_0_a: assert property(disable iff(!rst_n) when_mult_addra_0_p);

//If it starts with UOP_DO_MUL_p/UOP_DO_MUL_q/ UOP_DO_ADD_p/ UOP_DO_ADD_q/ UOP_DO_SUB_p/UOP_DO_SUB_q, 
//the next both fields shouldn’t be UOP_OPR_DONTCARE.


property when_do_add_mul_sub_addr_not_zero_p;
    ((douta[17:12] == UOP_DO_MUL_p) ||
    (douta[17:12] == UOP_DO_MUL_q) ||
    (douta[17:12] == UOP_DO_ADD_q) ||
    (douta[17:12] == UOP_DO_ADD_p) ||
    (douta[17:12] == UOP_DO_SUB_p) ||
    (douta[17:12] == UOP_DO_SUB_q))  &&
    $past(addra) != PM_INIT_S &&
    $past(addra) != PM_INIT_S+ 4 //Next field after opcode is const_zero i.e both the fields are zero so excluded
    |->
    douta[11:0] != {UOP_OPR_DONTCARE,UOP_OPR_DONTCARE};
endproperty

when_do_add_mul_sub_addr_not_zero_a: assert property(disable iff(!rst_n) when_do_add_mul_sub_addr_not_zero_p);


endmodule



bind ecc_pm_sequencer fv_ecc_pm_sequencer  
    #(.ADDR_WIDTH(ADDR_WIDTH),
        .DATA_WIDTH(DATA_WIDTH)
        )
        fv_ecc_pm_sequencer_inst(
        .clk(clka),
        .rst_n(reset_n && !zeroize),
        .ena(ena),
        .addra(addra),
        .douta(douta)
    );
