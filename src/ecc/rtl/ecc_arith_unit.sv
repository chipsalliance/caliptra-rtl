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
// data memory, point mult (pm) controller, and field arithmeric
// - The module controlol memory acces from outside and pm controller
// - Secret key is stored in this madule's register instead of data memory,
//   and this module shifts and feeds one bit of secret key to pm controller
//   in each iteration corresponding with pm controller request (req_digit)
//
//
//======================================================================

module ecc_arith_unit 
    import ecc_pm_uop_pkg::*;
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
    input wire           reset_n,
    input wire           zeroize,

    // DATA PORT
    input  wire [3 : 0]                     ecc_cmd_i,
    input  wire [ADDR_WIDTH-1 : 0]          addr_i,
    input  wire                             wr_op_sel_i,
    input  wire                             wr_en_i,
    input  wire                             rd_reg_i,
    input  wire [(REG_SIZE+RND_SIZE)-1 : 0] data_i,
    output wire [REG_SIZE-1: 0]             data_o,
    output wire                             busy_o
    );
    
    //----------------------------------------------------------------
    // Registers including update variables and write enable.
    //----------------------------------------------------------------
    
    logic [REG_SIZE-1 : 0]      opa_s;
    logic [REG_SIZE-1 : 0]      opb_s;
    logic [REG_SIZE-1 : 0]      add_res_s;
    logic [REG_SIZE-1 : 0]      mult_res_s;

    reg                 digit_in;
    reg                 digit_pk_in;
    reg                 digit_neg_in;
    reg                 digit_pk_neg_in;
    reg [3 : 0]         ecc_cmd_q;
    logic               req_digit;
    logic               ecc_busy_s;
    logic               mult_ready_s;
    logic               mult_start_s;
    logic               mult_accept_s;

    pm_instr_struct_t                   ecc_instr_s;
    logic [REG_SIZE-1 : 0]              reg_dinb_r;
    logic [REG_SIZE-1 : 0]              dinb_mux_s;
    logic [OPR_ADDR_WIDTH-1 : 0]        addra_mux_s;
    logic [OPR_ADDR_WIDTH-1 : 0]        reg_addr_r;
    logic [OPR_ADDR_WIDTH-1 : 0]        addrb_mux_s;
    logic                               reg_web_r;
    logic                               web_mux_s;
    logic                               mult_addr_hold_valid;
    logic [OPR_ADDR_WIDTH-1 : 0]        mult_opa_addr;
    logic [OPR_ADDR_WIDTH-1 : 0]        mult_opb_addr;
    logic                               mult_red_en_hold;
    logic [REG_SIZE-1 : 0]              mult_prime_hold;
    logic [RADIX-1 : 0]                 mult_mu_hold;

    logic [REG_SIZE-1 : 0]              d_o;

    logic                               mod_p_q;
    logic [REG_SIZE-1 : 0]              adder_prime;
    logic [REG_SIZE-1 : 0]              mult_prime_mux_s;
    logic [RADIX-1 : 0]                 mult_mu;
    logic [RADIX-1 : 0]                 mult_mu_mux_s;
    logic                               mult_red_en_mux_s;

    reg [(REG_SIZE+RND_SIZE)-1 : 0]     secret_key;
    reg [(REG_SIZE+RND_SIZE)-1 : 0]     secret_key_pk;
    logic                               jsf_active;
    logic [REG_SIZE : 0]                jsf_digit_g;
    logic [REG_SIZE : 0]                jsf_digit_pk;
    logic [REG_SIZE : 0]                jsf_digit_g_neg;
    logic [REG_SIZE : 0]                jsf_digit_pk_neg;

    function automatic [(4*(REG_SIZE+1))-1 : 0] jsf_recode(
        input logic [REG_SIZE-1 : 0] scalar_g,
        input logic [REG_SIZE-1 : 0] scalar_pk
    );
        logic [REG_SIZE+1 : 0] g_work;
        logic [REG_SIZE+1 : 0] pk_work;
        logic [REG_SIZE : 0] g_nonzero;
        logic [REG_SIZE : 0] pk_nonzero;
        logic [REG_SIZE : 0] g_neg;
        logic [REG_SIZE : 0] pk_neg;
        logic g_use_digit;
        logic pk_use_digit;
        logic g_use_neg;
        logic pk_use_neg;
        int unsigned idx;
        begin
            g_work = {{2{1'b0}}, scalar_g};
            pk_work = {{2{1'b0}}, scalar_pk};
            g_nonzero = '0;
            pk_nonzero = '0;
            g_neg = '0;
            pk_neg = '0;
            for (idx = 0; idx < REG_SIZE+1; idx++) begin
                g_use_digit = g_work[0];
                pk_use_digit = pk_work[0];
                g_use_neg = g_use_digit & (&g_work[1:0]);
                pk_use_neg = pk_use_digit & (&pk_work[1:0]);

                if (g_use_digit & !g_use_neg & (g_work[2:0] == 3'b011) & (pk_work[1:0] == 2'b10)) begin
                    g_use_neg = 1'b1;
                end
                if (pk_use_digit & !pk_use_neg & (pk_work[2:0] == 3'b011) & (g_work[1:0] == 2'b10)) begin
                    pk_use_neg = 1'b1;
                end

                g_nonzero[idx] = g_use_digit;
                pk_nonzero[idx] = pk_use_digit;
                g_neg[idx] = g_use_neg;
                pk_neg[idx] = pk_use_neg;

                if (g_use_digit) begin
                    g_work = g_use_neg ? (g_work + {{(REG_SIZE+1){1'b0}}, 1'b1}) :
                                         (g_work - {{(REG_SIZE+1){1'b0}}, 1'b1});
                end
                if (pk_use_digit) begin
                    pk_work = pk_use_neg ? (pk_work + {{(REG_SIZE+1){1'b0}}, 1'b1}) :
                                           (pk_work - {{(REG_SIZE+1){1'b0}}, 1'b1});
                end
                g_work = {1'b0, g_work[REG_SIZE+1 : 1]};
                pk_work = {1'b0, pk_work[REG_SIZE+1 : 1]};
            end
            jsf_recode = {g_nonzero, g_neg, pk_nonzero, pk_neg};
        end
    endfunction

    //----------------------------------------------------------------
    // 
    // ECC Control Logic
    // 
    //----------------------------------------------------------------
    
    ecc_pm_ctrl #(
        .REG_SIZE(REG_SIZE),
        .RND_SIZE(RND_SIZE),
        .INSTR_SIZE(INSTRUCTION_LENGTH)
        )
        ecc_pm_ctrl_i(
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .ecc_cmd_i(ecc_cmd_i),
        .digit_i(digit_in),
        .digit_pk_i(digit_pk_in),
        .digit_neg_i(digit_neg_in),
        .digit_pk_neg_i(digit_pk_neg_in),
        .instr_o(ecc_instr_s),
        .req_digit_o(req_digit),
        .mult_ready_i(mult_ready_s),
        .mult_start_i(mult_start_s),
        .busy_o(ecc_busy_s)
    );

    //----------------------------------------------------------------
    // 
    // Memory interface
    // 
    //----------------------------------------------------------------
    ecc_ram_tdp_file #(
        .ADDR_WIDTH(OPR_ADDR_WIDTH),
        .DATA_WIDTH(REG_SIZE)
        )
        ram_tdp_file_i(
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .ena(1'b1),
        .wea(ecc_instr_s.opcode.add_we),
        .addra(addra_mux_s),
        .dina(add_res_s),
        .douta(opa_s),
        .enb(1'b1),
        .web(web_mux_s),
        .addrb(addrb_mux_s),
        .dinb(dinb_mux_s),
        .doutb(opb_s)
    );

    //----------------------------------------------------------------
    // 
    // fau interface
    // 
    //----------------------------------------------------------------

    assign mod_p_q     = ecc_instr_s.opcode.mod_q_sel;  //performing mod_p if (mod_p_q = 0), else mod_q
    assign adder_prime = (mod_p_q)? q_grouporder : p_prime;
    assign mult_mu     = (mod_p_q)? q_mu : p_mu;
    assign mult_red_en_mux_s = (ecc_busy_s & mult_addr_hold_valid) ? mult_red_en_hold : ecc_instr_s.opcode.red_en;
    assign mult_prime_mux_s  = (ecc_busy_s & mult_addr_hold_valid) ? mult_prime_hold  : adder_prime;
    assign mult_mu_mux_s     = (ecc_busy_s & mult_addr_hold_valid) ? mult_mu_hold     : mult_mu;

    ecc_fau #(
        .REG_SIZE(REG_SIZE),
        .RADIX(RADIX)
        )
        ecc_fau_i
        (
        // Clock and reset.
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),

        // DATA PORT
        .add_en_i(ecc_instr_s.opcode.add_en),
        .sub_i(ecc_instr_s.opcode.sub_sel),
        .mult_en_i(ecc_instr_s.opcode.mult_en),
        .reduce_i(mult_red_en_mux_s),
        .prime_i(adder_prime),
        .mult_prime_i(mult_prime_mux_s),
        .mult_mu_i(mult_mu_mux_s),
        .opa_i(opa_s),
        .opb_i(opb_s),
        .add_res_o(add_res_s),
        .mult_res_o(mult_res_s),
        .mult_start_o(mult_start_s),
        .mult_accept_o(mult_accept_s),
        .mult_ready_o(mult_ready_s)
    );


    //----------------------------------------------------------------
    // 
    // Register updates
    // 
    //----------------------------------------------------------------
    always_ff @(posedge clk or negedge reset_n) 
    begin :reg_update
        if (!reset_n) begin
            reg_dinb_r      <= '0;
            reg_addr_r      <= '0;
            reg_web_r       <= 0;
            secret_key      <= '0;
            secret_key_pk   <= '0;
            d_o             <= '0;
            jsf_active      <= 1'b0;
            jsf_digit_g     <= '0;
            jsf_digit_pk    <= '0;
            jsf_digit_g_neg <= '0;
            jsf_digit_pk_neg <= '0;
            ecc_cmd_q       <= '0;
            mult_addr_hold_valid <= 1'b0;
            mult_opa_addr <= '0;
            mult_opb_addr <= '0;
            mult_red_en_hold <= 1'b0;
            mult_prime_hold <= '0;
            mult_mu_hold <= '0;
        end
        else if (zeroize) begin
            reg_dinb_r      <= '0;
            reg_addr_r      <= '0;
            reg_web_r       <= 0;
            secret_key      <= '0;
            secret_key_pk   <= '0;
            d_o             <= '0;
            jsf_active      <= 1'b0;
            jsf_digit_g     <= '0;
            jsf_digit_pk    <= '0;
            jsf_digit_g_neg <= '0;
            jsf_digit_pk_neg <= '0;
            ecc_cmd_q       <= '0;
            mult_addr_hold_valid <= 1'b0;
            mult_opa_addr <= '0;
            mult_opb_addr <= '0;
            mult_red_en_hold <= 1'b0;
            mult_prime_hold <= '0;
            mult_mu_hold <= '0;
        end
        else begin
            mult_addr_hold_valid <= ecc_busy_s & ecc_instr_s.opcode.mult_en;
            if (ecc_busy_s & ecc_instr_s.opcode.mult_en) begin
                mult_opa_addr <= ecc_instr_s.opa_addr;
                mult_opb_addr <= ecc_instr_s.opb_addr;
                mult_red_en_hold <= ecc_instr_s.opcode.red_en;
                mult_prime_hold <= adder_prime;
                mult_mu_hold <= mult_mu;
            end

            ecc_cmd_q <= ecc_cmd_i;

            if ((ecc_cmd_i == VER_PART2_CMD) && (ecc_cmd_q != VER_PART2_CMD)) begin
                {jsf_digit_g, jsf_digit_g_neg, jsf_digit_pk, jsf_digit_pk_neg} <= jsf_recode(secret_key[(REG_SIZE+RND_SIZE)-1 -: REG_SIZE],
                                                                                              secret_key_pk[(REG_SIZE+RND_SIZE)-1 -: REG_SIZE]);
                jsf_active <= 1'b1;
            end
            else if ((ecc_cmd_i != VER_PART2_CMD) && (|ecc_cmd_i)) begin
                jsf_active <= 1'b0;
            end

            if (wr_en_i) begin
                if (wr_op_sel_i == 1'b0) // Write new register
                    reg_dinb_r <= data_i[REG_SIZE-1 : 0];
                else if (addr_i == UOP_OPR_SCALAR_PK)
                    secret_key_pk <= data_i;
                else                    // Write new key
                    secret_key <= data_i;
            end
            else if (req_digit) begin
                //Shift secret_key to the left
                secret_key  <= {secret_key[(REG_SIZE+RND_SIZE)-2 : 0], secret_key[(REG_SIZE+RND_SIZE)-1]};
                secret_key_pk <= {secret_key_pk[(REG_SIZE+RND_SIZE)-2 : 0], secret_key_pk[(REG_SIZE+RND_SIZE)-1]};
                jsf_digit_g <= {jsf_digit_g[REG_SIZE-1 : 0], jsf_digit_g[REG_SIZE]};
                jsf_digit_pk <= {jsf_digit_pk[REG_SIZE-1 : 0], jsf_digit_pk[REG_SIZE]};
                jsf_digit_g_neg <= {jsf_digit_g_neg[REG_SIZE-1 : 0], jsf_digit_g_neg[REG_SIZE]};
                jsf_digit_pk_neg <= {jsf_digit_pk_neg[REG_SIZE-1 : 0], jsf_digit_pk_neg[REG_SIZE]};
            end

            reg_addr_r <= addr_i;
            if (wr_op_sel_i == 1'b0)
                reg_web_r <= wr_en_i;
            else
                reg_web_r <= '0;
            
            // Read multiplexer    
            if (rd_reg_i)
                d_o <= opb_s;
            else
                d_o <= '0;
        end
    end // reg_update

    //Push key bit to ecc pm control
    assign digit_in = jsf_active ? jsf_digit_g[0] : secret_key[0];
    assign digit_pk_in = jsf_active ? jsf_digit_pk[0] : secret_key_pk[0];
    assign digit_neg_in = jsf_active & jsf_digit_g_neg[0];
    assign digit_pk_neg_in = jsf_active & jsf_digit_pk_neg[0];

    assign addra_mux_s = (ecc_busy_s & mult_addr_hold_valid & !ecc_instr_s.opcode.add_we) ? mult_opa_addr :
                         ecc_instr_s.opa_addr;
    assign addrb_mux_s = (ecc_busy_s & mult_addr_hold_valid & !ecc_instr_s.opcode.mult_we) ? mult_opb_addr :
                         (ecc_busy_s ? ecc_instr_s.opb_addr : reg_addr_r);
    assign web_mux_s   = ecc_busy_s ? ecc_instr_s.opcode.mult_we    : reg_web_r;
    assign dinb_mux_s  = ecc_busy_s ? mult_res_s                    : reg_dinb_r;
    assign busy_o      = ecc_busy_s;
    assign data_o      = d_o;

endmodule
