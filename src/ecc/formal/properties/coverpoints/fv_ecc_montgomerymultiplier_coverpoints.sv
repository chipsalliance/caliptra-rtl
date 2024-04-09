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
module fv_ecc_montgomerymultiplier_coverpoints_m(
    input logic clk,
    input logic reset_n,
    input logic zeroize
);
    
    default clocking default_clk @(posedge clk); endclocking

//Cover zeroize: 
    cover_zeroize: cover property(disable iff(!reset_n) ecc_montgomerymultiplier.zeroize );
    cover_prime_p: cover property(disable iff(!reset_n || zeroize) (ecc_montgomerymultiplier.n_i==384'hfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff));
    cover_group_order: cover property(disable iff(!reset_n || zeroize)(ecc_montgomerymultiplier.n_i==384'hffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973));
    cover_n_prime_i_prime_mu : cover property(disable iff(!reset_n|| zeroize) ecc_montgomerymultiplier.n_prime_i == 48'h100000001);
    cover_n_prime_i_group_order_mu : cover property(disable iff(!reset_n|| zeroize) ecc_montgomerymultiplier.n_prime_i == 48'h6089e88fdc45);
    cover_opa_i_0 : cover property(disable iff(!reset_n|| zeroize) (ecc_montgomerymultiplier.opa_i == '0)&&(ecc_montgomerymultiplier.opb_i == '0 || ecc_montgomerymultiplier.opb_i == (ecc_montgomerymultiplier.n_i-1)) );
    cover_opa_i_prime_minus_1 : cover property(disable iff(!reset_n|| zeroize) (ecc_montgomerymultiplier.opa_i == (ecc_montgomerymultiplier.n_i-1))&&(ecc_montgomerymultiplier.opb_i == '0 || ecc_montgomerymultiplier.opb_i == (ecc_montgomerymultiplier.n_i-1)) );
    cover_opb_i_0 : cover property(disable iff(!reset_n|| zeroize) (ecc_montgomerymultiplier.opb_i == '0)&&(ecc_montgomerymultiplier.opa_i == '0 || ecc_montgomerymultiplier.opa_i == (ecc_montgomerymultiplier.n_i-1)) );
    cover_opb_i_prime_minus_1 : cover property(disable iff(!reset_n|| zeroize) (ecc_montgomerymultiplier.opb_i == (ecc_montgomerymultiplier.n_i-1))&&(ecc_montgomerymultiplier.opa_i == '0 || ecc_montgomerymultiplier.opa_i == (ecc_montgomerymultiplier.n_i-1)) );
    cover_sub_b_o_zero: cover property(disable iff(!reset_n || zeroize) ecc_montgomerymultiplier.ready_o && ecc_montgomerymultiplier.sub_b_o[2*(ecc_montgomerymultiplier.PE_UNITS+1)]==0);
    cover_sub_b_o_one: cover property(disable iff(!reset_n || zeroize) ecc_montgomerymultiplier.ready_o && ecc_montgomerymultiplier.sub_b_o[2*(ecc_montgomerymultiplier.PE_UNITS+1)]== 1);
    cover_p_sub_internal: cover property (disable iff(!reset_n || zeroize) !$past(!reset_n || zeroize) && ecc_montgomerymultiplier.ready_o && (ecc_montgomerymultiplier.p_subtracted_internal == ( ecc_montgomerymultiplier.p_internal - ecc_montgomerymultiplier.n_i)));
    


endmodule

bind ecc_montgomerymultiplier fv_ecc_montgomerymultiplier_coverpoints_m fv_ecc_montgomerymultiplier_coverpoints(
    .clk(clk),
    .reset_n(reset_n),
    .zeroize(zeroize)
);