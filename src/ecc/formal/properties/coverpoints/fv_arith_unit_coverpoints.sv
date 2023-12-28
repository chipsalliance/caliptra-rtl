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
module fv_ecc_arith_unit_coverpoints_m(
    input logic clk,
    input logic reset_n,
    input logic zeroize
);
    
    default clocking default_clk @(posedge clk); endclocking

    //Cover zeroize: 
    cover_zeroize: cover property(disable iff(!reset_n) ecc_arith_unit.zeroize );

    //cover wea
    cover_wea: cover property(disable iff(!reset_n) (
                ecc_arith_unit.ecc_instr_s.opcode.add_en 
            ##3 
                ecc_arith_unit.ram_tdp_file_i.wea));

    //cover web
    cover_wem: cover property(disable iff(!reset_n) 
                ecc_arith_unit.ecc_instr_s.opcode.mult_en 
            ##41 
                ecc_arith_unit.web_mux_s);

    //cover req_digit when keygen cmd
    cover_req_digit_keygen: cover property(disable iff(!reset_n) 
                ecc_arith_unit.ecc_cmd_i== 3'b001 //KEYGEN_CMD 
            ##1 
                ecc_arith_unit.req_digit[->576]);

    //cover req_digit when signing cmd
    cover_req_digit_signing: cover property(disable iff(!reset_n) 
                ecc_arith_unit.ecc_cmd_i==3'b010 //SIGN_CMD 
            ##1 
                ecc_arith_unit.req_digit[->576]);

    
    //cover wr_op_sel_i when ecc_cmd_i is received
    cover_wr_op_sel_i: cover property(disable iff(!reset_n) 
                (ecc_arith_unit.ecc_cmd_i!=3'b0 && !ecc_arith_unit.wr_op_sel_i));

    //cover wr_en_i when ecc_cmd_i is received
    cover_wr_en_i: cover property(disable iff(!reset_n || zeroize) 
                (ecc_arith_unit.ecc_cmd_i!=3'b0 && !ecc_arith_unit.wr_en_i));

    //cover sca_en_i
    cover_sca_en_always: cover property(disable iff(!reset_n || zeroize)
                ecc_arith_unit.sca_en_i ==1);

    //cover digit_in be the MSB bit of secret key
    cover_digit_in_msb_secret_key: cover property(disable iff(!reset_n || zeroize)
                ecc_arith_unit.req_digit 
                ##1 
                ecc_arith_unit.digit_in == $past(ecc_arith_unit.secret_key[(ecc_arith_unit.REG_SIZE+ecc_arith_unit.RND_SIZE)-1]));

    //cover secret key is shifted with req_digit
    cover_req_digit_secret_key: cover property(disable iff(!reset_n || zeroize) 
                ecc_arith_unit.req_digit 
              ##1 
                ecc_arith_unit.secret_key == $past({ecc_arith_unit.secret_key[(ecc_arith_unit.REG_SIZE+ecc_arith_unit.RND_SIZE)-2 : 0], ecc_arith_unit.secret_key[(ecc_arith_unit.REG_SIZE+ecc_arith_unit.RND_SIZE)-1]}));


endmodule

bind ecc_arith_unit fv_ecc_arith_unit_coverpoints_m fv_ecc_arith_unit_coverpoints(
    .clk(clk),
    .reset_n(reset_n),
    .zeroize(zeroize)
);