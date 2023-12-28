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
module fv_add_sub_alter_coverpoints_m(
    input logic clk,
    input logic reset_n,
    input logic zeroize
);
    
    default clocking default_clk @(posedge clk); endclocking

    //Cover zeroize: 
    cover_zeroize: cover property(disable iff(!reset_n) ecc_add_sub_mod_alter.zeroize );

    cover_prime_p: cover property(disable iff(!reset_n) (ecc_add_sub_mod_alter.prime_i==384'hfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff));
    cover_prime_q: cover property(disable iff(!reset_n)(ecc_add_sub_mod_alter.prime_i==384'hffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973));
    cover_add_en: cover property(disable iff(!reset_n) ecc_add_sub_mod_alter.add_en_i==1);
    cover_add_disable: cover property(disable iff(!reset_n) ecc_add_sub_mod_alter.add_en_i==0);
    cover_r0_0: cover property(disable iff(!reset_n || zeroize) ecc_add_sub_mod_alter.r0=='0);
    cover_r0_1: cover property(disable iff(!reset_n || zeroize) ecc_add_sub_mod_alter.r0=='1);
    cover_r0_greater_prime: cover property(disable iff(!reset_n || zeroize) ecc_add_sub_mod_alter.r0 > ecc_add_sub_mod_alter.prime_i);


endmodule

bind ecc_add_sub_mod_alter fv_add_sub_alter_coverpoints_m fv_add_sub_alter_coverpoints(
    .clk(clk),
    .reset_n(reset_n),
    .zeroize(zeroize)
);
