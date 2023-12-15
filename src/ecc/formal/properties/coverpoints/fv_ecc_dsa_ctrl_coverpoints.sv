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
module fv_ecc_dsa_ctrl_coverpoints(
    input logic clk,
    input logic reset_n,
    input logic zeroize
);

 
    default clocking default_clk @(posedge clk); endclocking

 //cover zeroize
    cover_zeroize: cover property(disable iff(!reset_n) ecc_dsa_ctrl.zeroize_reg );

//cover seed_reg

    cover_seed_reg_max: cover property(disable iff(!reset_n || zeroize) ecc_dsa_ctrl.seed_reg == 384'hFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF);
    cover_seed_reg_zero: cover property(disable iff(!reset_n || zeroize) ecc_dsa_ctrl.seed_reg =='0);

//cover nonce_reg


    cover_nonce_reg_max: cover property(disable iff(!reset_n || zeroize) ecc_dsa_ctrl.nonce_reg== 384'hFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF);
    cover_nonce_reg_zero: cover property(disable iff(!reset_n || zeroize) ecc_dsa_ctrl.nonce_reg =='0);

//cover msg_reg

    cover_msg_reg_max: cover property(disable iff(!reset_n || zeroize)  ecc_dsa_ctrl.msg_reg == 384'hFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF);
    cover_msg_reg_zero: cover property(disable iff(!reset_n || zeroize) ecc_dsa_ctrl.msg_reg =='0);


//cover privkey_reg

    cover_privkey_reg_less_grp_order: cover property(disable iff(!reset_n || zeroize)  ecc_dsa_ctrl.privkey_reg < 384'hffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973);
    cover_privkey_reg_grt_zero: cover property(disable iff(!reset_n || zeroize) ecc_dsa_ctrl.privkey_reg >'0);

//cover scalar_G_reg

    cover_scalar_G_reg_less_grp_order: cover property(disable iff(!reset_n || zeroize)  ecc_dsa_ctrl.scalar_G_reg < 384'hffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973);
    cover_scalar_G_reg_grt_zero: cover property(disable iff(!reset_n || zeroize) ecc_dsa_ctrl.scalar_G_reg >'0);
    cover_scalar_G_reg_grp_order_1: cover property(disable iff(!reset_n || zeroize)  ecc_dsa_ctrl.scalar_G_reg == 384'hffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52972);
    cover_scalar_G_reg_1: cover property(disable iff(!reset_n || zeroize) ecc_dsa_ctrl.scalar_G_reg == 1);

//cover scalar_PK_reg

    cover_scalar_PK_reg_less_grp_order: cover property(disable iff(!reset_n || zeroize)  ecc_dsa_ctrl.scalar_PK_reg < 384'hffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973);
    cover_scalar_PK_reg_grt_zero: cover property(disable iff(!reset_n || zeroize) ecc_dsa_ctrl.scalar_PK_reg >'0);
    cover_scalar_PK_reg_grp_order_1: cover property(disable iff(!reset_n || zeroize)  ecc_dsa_ctrl.scalar_PK_reg == 384'hffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52972);
    cover_scalar_PK_reg_1: cover property(disable iff(!reset_n || zeroize) ecc_dsa_ctrl.scalar_PK_reg == 1);

//cover r_reg

    cover_r_reg_less_grp_order: cover property(disable iff(!reset_n || zeroize)  ecc_dsa_ctrl.r_reg < 384'hffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973);
    cover_r_reg_grt_zero: cover property(disable iff(!reset_n || zeroize) ecc_dsa_ctrl.r_reg >'0);
    cover_r_reg_grp_order_1: cover property(disable iff(!reset_n || zeroize)  ecc_dsa_ctrl.r_reg == 384'hffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52972);
    cover_r_reg_1: cover property(disable iff(!reset_n || zeroize) ecc_dsa_ctrl.r_reg == 1);

//cover s_reg
    cover_s_reg_less_grp_order: cover property(disable iff(!reset_n || zeroize)  ecc_dsa_ctrl.s_reg < 384'hffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973);
    cover_s_reg_grt_zero: cover property(disable iff(!reset_n || zeroize) ecc_dsa_ctrl.s_reg >'0);
    cover_s_reg_grp_order_1: cover property(disable iff(!reset_n || zeroize)  ecc_dsa_ctrl.s_reg == 384'hffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52972);
    cover_s_reg_1: cover property(disable iff(!reset_n || zeroize) ecc_dsa_ctrl.s_reg == 1);


//cover IV_reg
    cover_IV_reg_less_grp_order: cover property(disable iff(!reset_n || zeroize)  ecc_dsa_ctrl.IV_reg < 384'hffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973);
    cover_IV_reg_grt_zero: cover property(disable iff(!reset_n || zeroize) ecc_dsa_ctrl.IV_reg >'0);
    cover_IV_reg_grp_order_1: cover property(disable iff(!reset_n || zeroize)  ecc_dsa_ctrl.IV_reg == 384'hffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52972);
    cover_IV_reg_1: cover property(disable iff(!reset_n || zeroize) ecc_dsa_ctrl.IV_reg == 1);

//cover pubkeyx_reg
    cover_pubkeyx_reg_less_prime: cover property(disable iff(!reset_n || zeroize)  ecc_dsa_ctrl.pubkeyx_reg < 384'hfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff);
    cover_pubkeyx_reg_zero: cover property(disable iff(!reset_n || zeroize) ecc_dsa_ctrl.pubkeyx_reg =='0);
    cover_pubkeyx_reg_prime_1: cover property(disable iff(!reset_n || zeroize)  ecc_dsa_ctrl.pubkeyx_reg == 384'hfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000fffffffe);
    cover_pubkeyx_reg_grt_prime: cover property(disable iff(!reset_n || zeroize) ecc_dsa_ctrl.pubkeyx_reg > 384'hfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff);

//cover pubkeyy_reg
    cover_pubkeyy_reg_less_prime: cover property(disable iff(!reset_n || zeroize)  ecc_dsa_ctrl.pubkeyy_reg < 384'hfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff);
    cover_pubkeyy_reg_zero: cover property(disable iff(!reset_n || zeroize) ecc_dsa_ctrl.pubkeyy_reg =='0);
    cover_pubkeyy_reg_prime_1: cover property(disable iff(!reset_n || zeroize)  ecc_dsa_ctrl.pubkeyy_reg == 384'hfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000fffffffe);
    cover_pubkeyy_reg_grt_prime: cover property(disable iff(!reset_n || zeroize) ecc_dsa_ctrl.pubkeyy_reg > 384'hfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff);


//cover scalar_out_reg
    cover_scalar_out_reg_eq_1: cover property(disable iff(!reset_n || zeroize) ecc_dsa_ctrl.scalar_out_reg==1);
    cover_scalar_out_reg_grp_order_1: cover property(disable iff(!reset_n || zeroize) ecc_dsa_ctrl.scalar_out_reg==384'hffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52972);
    cover_scalar_out_reg_grp_mult: cover property(disable iff(!reset_n || zeroize) ecc_dsa_ctrl.scalar_out_reg==(1+((2**192)-1)*384'hffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973) );
    cover_scalar_out_reg_grp_order_mult_1: cover property(disable iff(!reset_n || zeroize) ecc_dsa_ctrl.scalar_out_reg==(384'hffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52972 +((2**192)-1)*384'hffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973) );



//cover lambda_reg

    cover_lambda_reg_max: cover property(disable iff(!reset_n || zeroize)  ecc_dsa_ctrl.lambda_reg == 384'hFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF);
    cover_lambda_reg_zero: cover property(disable iff(!reset_n || zeroize) ecc_dsa_ctrl.lambda_reg =='0);



//cover masking_rnd_reg

    cover_masking_rnd_reg_max: cover property(disable iff(!reset_n || zeroize)  ecc_dsa_ctrl.masking_rnd_reg == 384'hFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF);
    cover_masking_rnd_reg_zero: cover property(disable iff(!reset_n || zeroize) ecc_dsa_ctrl.masking_rnd_reg =='0);





endmodule

bind ecc_dsa_ctrl fv_ecc_dsa_ctrl_coverpoints fv_ecc_dsa_ctrl_coverpoints_inst (
    .clk(clk),
    .reset_n(reset_n),
    .zeroize(ecc_dsa_ctrl.zeroize_reg)
);