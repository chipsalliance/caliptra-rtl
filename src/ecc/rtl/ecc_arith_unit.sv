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
// ecc_arith_unit.sv
// --------
// ECC arithmetic unit to perform point multiplication including 
// data memory, pm sequencer, and field arithmeric
//
//
//======================================================================

module ecc_arith_unit #(
    parameter REG_SIZE      = 384,
    parameter RND_SIZE      = 192,
    parameter RADIX         = 32,
    parameter p_prime       = 384'hfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff,
    parameter p_mu          = 32'h00000001,
    parameter q_grouporder  = 384'hffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973,
    parameter q_mu          = 32'he88fdc45,
    parameter ADD_NUM_ADDS  = 1,
    parameter ADD_BASE_SZ   = 384
    )
    (
    // Clock and reset.
    input wire           clk,
    input wire           reset_n,

    // DATA PORT
    input  wire [2 : 0]                   ecc_cmd_i,
    input  wire [7 : 0]                   addr_i,
    input  wire                           wr_op_sel_i,
    input  wire                           wr_en_i,
    input  wire                           rd_reg_i,
    input  wire [REG_SIZE+RND_SIZE-1 : 0] data_i,
    output wire [REG_SIZE-1: 0]           data_o,
    output wire                           busy_o
    );

    //----------------------------------------------------------------
    // 
    // ECC Control Logic
    // 
    //----------------------------------------------------------------
    logic [REG_SIZE-1 : 0]      opa_s;
    logic [REG_SIZE-1 : 0]      opb_s;
    logic [REG_SIZE-1 : 0]      add_res_s;
    logic [REG_SIZE-1 : 0]      mult_res_s;
    logic                       fau_ready;

    reg                 digit_in; 
    logic [23  :  0]    ecc_instr_s;
    logic               req_digit;
    logic               ecc_busy_s;
    
    ecc_pm_ctrl #(
        .REG_SIZE(REG_SIZE),
        .RND_SIZE(RND_SIZE)
        )
        ecc_pm_ctrl_i(
        .clk(clk),
        .reset_n(reset_n),
        .ecc_cmd_i(ecc_cmd_i),
        .digit_i(digit_in),
        .instr_o(ecc_instr_s),
        .req_digit_o(req_digit),
        .busy_o(ecc_busy_s)
    );

    //----------------------------------------------------------------
    // 
    // Memory interface
    // 
    //----------------------------------------------------------------
    logic [REG_SIZE-1 : 0]      reg_dinb_r;
    logic [REG_SIZE-1 : 0]      reg_dout_r;
    logic [REG_SIZE-1 : 0]      dinb_mux_s;
    logic [7 : 0]               reg_addr_r;
    logic [7 : 0]               addrb_mux_s;
    logic                       reg_web_r;
    logic                       web_mux_s;

    logic [REG_SIZE   : 0]      di_mux;
    logic [REG_SIZE-1 : 0]      d_o;

    ecc_ram_tdp_file #(
        .ADDR_WIDTH(6),
        .DATA_WIDTH(REG_SIZE)
        )
        ram_tdp_file_i(
        .clk(clk),
        .ena(1'b1),
        .wea(ecc_instr_s[17]),
        .addra(ecc_instr_s[13 : 8]),
        .dina(add_res_s),
        .douta(opa_s),
        .enb(1'b1),
        .web(web_mux_s),
        .addrb(addrb_mux_s[5 : 0]),
        .dinb(dinb_mux_s),
        .doutb(opb_s)
    );

    //----------------------------------------------------------------
    // 
    // fau interface
    // 
    //----------------------------------------------------------------
    
    logic                       mod_p_q;
    logic [REG_SIZE-1 : 0]      adder_prime;
    logic [RADIX-1 : 0]         mult_mu;

    assign mod_p_q     = ecc_instr_s[21];  //performing mod_p if (mod_p_q = 0), else mod_q
    assign adder_prime = (mod_p_q)? q_grouporder : p_prime;
    assign mult_mu     = (mod_p_q)? q_mu : p_mu;

    ecc_fau #(
        .REG_SIZE(REG_SIZE),
        .RADIX(RADIX),
        .ADD_NUM_ADDS(ADD_NUM_ADDS),
        .ADD_BASE_SZ(ADD_BASE_SZ)
        )
        ecc_fau_i
        (
        // Clock and reset.
        .clk(clk),
        .reset_n(reset_n),

        // DATA PORT
        .sub_i(ecc_instr_s[18]),
        .red_i(ecc_instr_s[19]),
        .mult_start_i(ecc_instr_s[20]),
        .prime_i(adder_prime),
        .mult_mu_i(mult_mu),
        .opa_i(opa_s),
        .opb_i(opb_s),
        .add_res_o(add_res_s),
        .mult_res_o(mult_res_s),
        .ready_o(fau_ready)
    );


    //----------------------------------------------------------------
    // 
    // Memory mapped register interface
    // 
    //----------------------------------------------------------------
    reg [REG_SIZE+RND_SIZE-1 : 0]         secret_key; 

    always_ff @(posedge clk) begin
        if (!reset_n) begin
            reg_dinb_r      <= 0;
            reg_addr_r      <= 0;
            reg_web_r       <= 0;
            secret_key      <= 0;
            digit_in        <= 0;
            reg_dout_r      <= 0;
        end
        else begin
            if (wr_en_i) begin
                if (wr_op_sel_i == 1'b0) // Write new register
                    reg_dinb_r <= data_i[REG_SIZE-1 : 0];
                else                    // Write new key
                    secret_key <= data_i;
            end

            else if (req_digit) begin
                //Shift digit
                secret_key[REG_SIZE+RND_SIZE-1  : 1]  <= secret_key[REG_SIZE+RND_SIZE-2 : 0];
                secret_key[0]                         <= secret_key[REG_SIZE+RND_SIZE-1];
            end
            //Push key bit to ecc control
            digit_in <= secret_key[0];

            reg_addr_r <= addr_i;
            if (wr_op_sel_i == 1'b0)
                reg_web_r <= wr_en_i;
            
            // Read multiplexer    
            if (rd_reg_i)
                d_o <= opb_s;
            else
                d_o <= 0;
        end
    end

            
    assign addrb_mux_s = ecc_busy_s ? ecc_instr_s[7 : 0] : reg_addr_r;
    assign web_mux_s   = ecc_busy_s ? ecc_instr_s[16]    : reg_web_r;
    assign dinb_mux_s  = ecc_busy_s ? mult_res_s         : reg_dinb_r;
    assign busy_o      = ecc_busy_s;
    assign data_o      = d_o;

endmodule
