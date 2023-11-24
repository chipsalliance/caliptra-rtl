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
module fv_ecc_arith_unit 
    #(
    parameter                  REG_SIZE     = 384,
    parameter                  RND_SIZE     = 192,
    parameter                  RADIX        = 32,
    parameter                  ADDR_WIDTH   = 6,
    parameter [REG_SIZE-1 : 0] p_prime      = 384'hfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff,
    parameter [RADIX-1    : 0] p_mu         = 32'h00000001,
    parameter [REG_SIZE-1 : 0] q_grouporder = 384'hffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973,
    parameter [RADIX-1    : 0] q_mu         = 32'he88fdc45
    )
    (
    // Clock and reset.
    input wire           clk,
    input wire           rst_n,
    

    // DATA PORT
    input  wire [2 : 0]                     ecc_cmd_i,
    input  wire                             sca_en_i,
    input  wire [ADDR_WIDTH-1 : 0]          addr_i,
    input  wire                             wr_op_sel_i,
    input  wire                             wr_en_i,
    input  wire                             rd_reg_i,
    input  wire [(REG_SIZE+RND_SIZE)-1 : 0] data_i,
    input wire [REG_SIZE-1: 0]             data_o,
    input wire                             busy_o
    );


    default clocking default_clk @(posedge clk); endclocking

no_busy_assume: assume property($past(!rst_n) |-> !ecc_arith_unit.ecc_busy_s); // used only when pm_ctrl is blackboxed
    sequence reset_sequence;
      !rst_n ##1 rst_n;
    endsequence


////////////////////////////////////////////
// reset property, when reset data_o      //
// are zero                               //
////////////////////////////////////////////


    property reset_p;
    $past(!rst_n) 
    |->
    busy_o == '0 && //open wire when black boxed
    data_o == '0 &&
    ecc_arith_unit.reg_dinb_r  == '0 &&
    ecc_arith_unit.reg_addr_r  == '0 &&
    ecc_arith_unit.reg_web_r   == 0  &&
    ecc_arith_unit.secret_key  == '0;
    endproperty

    reset_a : assert property(reset_p);


////////////////////////////////////////////
// if read reg enabled then data_o has    //
// the mem out of b                       //
////////////////////////////////////////////

    property dout_p;
    rd_reg_i
    |=>
    data_o == $past(ecc_arith_unit.opb_s);
    endproperty
    dout_a: assert property(disable iff(!rst_n) dout_p);

    property no_dout_p;
    !rd_reg_i
    |=>
    data_o == '0;
    endproperty
    no_dout_a: assert property(disable iff(!rst_n) no_dout_p);
        

////////////////////////////////////////////
// If busy then the mux determines inputs //
// for the ram                            //
////////////////////////////////////////////


    property busy_mux;
    ecc_arith_unit.ecc_busy_s
    |->
    ecc_arith_unit.addrb_mux_s == ecc_arith_unit.ecc_instr_s.opb_addr &&
    ecc_arith_unit.web_mux_s == ecc_arith_unit.ecc_instr_s.opcode.mult_we &&
    ecc_arith_unit.dinb_mux_s ==ecc_arith_unit.mult_res_s;
    endproperty

    busy_mux_a: assert property(disable iff(!rst_n) busy_mux);


//If not busy then ram addrb takes addr_i
    property not_busy_addr_mux_p;
    !ecc_arith_unit.ecc_busy_s
    |->
    ecc_arith_unit.addrb_mux_s == ecc_arith_unit.reg_addr_r;

    endproperty
    not_busy_addr_mux_a: assert property(disable iff(!rst_n) not_busy_addr_mux_p);



//If not busy and the previous cycle there isn't wr_op_sel then web takes wr_en_i
    property not_busy_web_mux_p;
        !wr_op_sel_i
        ##1 !ecc_arith_unit.ecc_busy_s
        |->
        ecc_arith_unit.web_mux_s == $past(wr_en_i);
    endproperty
    not_busy_web_mux_a: assert property(disable iff(!rst_n) not_busy_web_mux_p);



//if not busy and in the previous clcok tick there is wr_en_i and no wr_op_sel then dinb takes data_i
    property not_busy_dinb_mux_p;
        wr_en_i &&
        !wr_op_sel_i
        ##1 !ecc_arith_unit.ecc_busy_s
        |->
        ecc_arith_unit.dinb_mux_s == REG_SIZE'($past(data_i));

    endproperty
    not_busy_dinb_mux_a: assert property(disable iff(!rst_n) not_busy_dinb_mux_p);


//If mod_q_sel is set then the prime should be selected as group order
    property prime_selection_as_q_p;
        ecc_arith_unit.ecc_instr_s.opcode.mod_q_sel
        |->
        ecc_arith_unit.adder_prime == q_grouporder &&
        ecc_arith_unit.mult_mu == q_mu;
    endproperty
    prime_selection_as_q_a: assert property(disable iff(!rst_n)prime_selection_as_q_p);

//If mod_q_sel is not set then the prime should be selected as the p (prime)
     property prime_selection_as_p_p;
        !ecc_arith_unit.ecc_instr_s.opcode.mod_q_sel
        |->
        ecc_arith_unit.adder_prime == p_prime &&
        ecc_arith_unit.mult_mu == p_mu;
    endproperty
    prime_selection_as_p_a: assert property(disable iff(!rst_n)prime_selection_as_p_p);

//If req_digit is set and no wr_en then the secret_key should be shifted
    property req_digit_p;
        ecc_arith_unit.req_digit &&
        !wr_en_i
        |=>
        ecc_arith_unit.secret_key == ($past({ecc_arith_unit.secret_key[(REG_SIZE+RND_SIZE)-2 : 0], ecc_arith_unit.secret_key[(REG_SIZE+RND_SIZE)-1]}));
    endproperty
    req_digit_a: assert property(disable iff(!rst_n)req_digit_p);


//If req_digit isn't set then and no wr_En then the secret_key should hold the previous value
    property no_req_digit_p;
        !ecc_arith_unit.req_digit &&
        !wr_en_i
        |=>
         ecc_arith_unit.secret_key == $past( ecc_arith_unit.secret_key);
    endproperty
    no_req_digit_a: assert property(disable iff(!rst_n) no_req_digit_p);


//If wr_en is set and the wr_op_Sel is set then secret_key should take the value of 
//data_i and reg_dinb_r should hold the previous value
    property wr_en_op_sel_p;
        wr_en_i &&
        wr_op_sel_i 
        |=>
        ecc_arith_unit.secret_key == $past(data_i)&&
        ecc_arith_unit.reg_dinb_r == $past(ecc_arith_unit.reg_dinb_r);
    endproperty
    wr_en_op_sel_a: assert property(disable iff(!rst_n)wr_en_op_sel_p);


//If wr_en is set and the wr_op_Sel isn't set then secret_key shouldhold the previous value 
//and reg_dinb_r should take  the data_i
    property wr_en_no_op_sel_p;
        wr_en_i &&
        !wr_op_sel_i 
        |=>
        ecc_arith_unit.secret_key == $past( ecc_arith_unit.secret_key) &&
        ecc_arith_unit.reg_dinb_r ==  $past(data_i[REG_SIZE-1 : 0]);
    endproperty
    wr_en_no_op_sel_a: assert property(disable iff(!rst_n)wr_en_no_op_sel_p);
   

//If no wr_En then reg_dinb_r should hold the previous value
    property no_wr_en_i_p;
        !wr_en_i
        |=>
        ecc_arith_unit.reg_dinb_r == $past(ecc_arith_unit.reg_dinb_r);
    endproperty
    no_wr_en_i_a: assert property(disable iff(!rst_n)no_wr_en_i_p);


//reg_addr_r always takes the addr_i
   // Helper logic for reset reg to use in disable iff
    logic fv_rst_n_reg;
    always_ff @(posedge clk) begin
        fv_rst_n_reg <= rst_n;
    end

    property reg_addr_r_p; 
        ecc_arith_unit.reg_addr_r == $past(addr_i);
    endproperty
    reg_addr_r_a: assert property(disable iff(!rst_n || !fv_rst_n_reg)reg_addr_r_p);


//digit_in is always equal to the MSB bit of the secretkey, which when shifted becomes secret_key[0]
    property digit_in_p;
        ecc_arith_unit.digit_in == ecc_arith_unit.secret_key[0];
    endproperty
    digit_in_a: assert property(disable iff(!rst_n)digit_in_p);
    
endmodule

bind  ecc_arith_unit fv_ecc_arith_unit#(
        .REG_SIZE(REG_SIZE),
        .RND_SIZE(RND_SIZE),
        .RADIX(RADIX),
        .ADDR_WIDTH(ADDR_WIDTH),
        .p_prime(p_prime),
        .p_mu(p_mu),
        .q_grouporder(q_grouporder),
        .q_mu(q_mu)
        )
        fv_ecc_arith_unit_inst (
        .clk(clk),
        .rst_n(reset_n && !zeroize),
        .ecc_cmd_i(ecc_cmd_i),
        .sca_en_i(sca_en_i),
        .addr_i(addr_i),
        .wr_op_sel_i(wr_op_sel_i),

        .wr_en_i(wr_en_i),
        .rd_reg_i(rd_reg_i),
        .data_i(data_i),
        .data_o(data_o),
        .busy_o(busy_o)
        );