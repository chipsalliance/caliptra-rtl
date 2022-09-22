//======================================================================
//
// ecc_arith_unit.sv
// --------
// 
//
//
// Author: Mojtaba Bisheh-Niasar
//======================================================================

module ecc_arith_unit #(
    parameter REG_SIZE      = 384,
    parameter PRIME         = 384'hfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff,
    parameter ADD_NUM_ADDS  = 1,
    parameter ADD_BASE_SZ   = 384
    )
    (
    // Clock and reset.
    input wire           clk,
    input wire           reset_n,

    // DATA PORT
    input  wire [2 : 0]         ecc_cmd_i,
    input  wire [7 : 0]         addr_i,
    input  wire                 wr_input_sel_i,
    input  wire [1 : 0]         wr_op_sel_i,
    input  wire [3 : 0]         wr_word_sel_i,
    input  wire                 wr_en_i,
    input  wire                 rd_reg_i,
    input  wire [1 : 0]         rd_op_sel_i,
    input  wire [3 : 0]         rd_word_sel_i,
    input  wire [31: 0]         data_i,
    output wire [31: 0]         data_o,
    output wire                 busy_o,
    output reg  [8:0]           count_o
    );




    //----------------------------------------------------------------
    // 
    // ECC Control Logic
    // 
    //----------------------------------------------------------------
    wire [REG_SIZE-1 : 0]      opa_s;
    wire [REG_SIZE-1 : 0]      opb_s;
    wire [REG_SIZE-1 : 0]      add_res_s;
    wire [REG_SIZE-1 : 0]      mult_res_s;
    wire                       fau_ready;

    reg                 digit_in; 
    wire [23  :  0]    ecc_instr_s;
    wire               req_digit;
    wire               ecc_busy_s;
    
    ecc_ctrl i_ecc_ctrl(
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
    reg [REG_SIZE-1 : 0]      reg_dinb_r;
    reg [REG_SIZE-1 : 0]      reg_dout_r;
    wire [REG_SIZE-1 : 0]      dinb_mux_s;
    reg [7 : 0]               reg_addr_r;
    wire [7 : 0]               addrb_mux_s;
    reg                       reg_web_r;
    wire                       web_mux_s;

    wire [31 : 0]              di_mux;
    reg [31 : 0]              d_o;

    assign di_mux = (wr_input_sel_i == 0) ? data_i : d_o;

    ram_tdp_file #(
        .ADDR_WIDTH(6),
        .DATA_WIDTH(REG_SIZE)
        )
        i_ram_tdp_file(
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

    fau #(
        .REG_SIZE(REG_SIZE),
        .PRIME(PRIME),
        .ADD_NUM_ADDS(ADD_NUM_ADDS),
        .ADD_BASE_SZ(ADD_BASE_SZ)
        )
        i_fau
        (
        // Clock and reset.
        .clk(clk),
        .reset_n(reset_n),

        // DATA PORT
        .sub_i(ecc_instr_s[18]),
        .red_i(ecc_instr_s[19]),
        .mult_start_i(ecc_instr_s[20]),
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
    reg [REG_SIZE   :0]         secret_key; 

    always @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            reg_dinb_r      <= 0;
            reg_addr_r      <= 0;
            reg_web_r       <= 0;
            secret_key      <= 0;
            digit_in        <= 0;
            reg_dout_r      <= 0;
            count_o         <= 0;
        end
        else begin
            // Write new register
            if (wr_en_i & (wr_op_sel_i == 2'b00)) begin
                case (wr_word_sel_i)
                    4'h0 : begin reg_dinb_r[31  :   0] <= di_mux; end
                    4'h1 : begin reg_dinb_r[63  :  32] <= di_mux; end
                    4'h2 : begin reg_dinb_r[95  :  64] <= di_mux; end
                    4'h3 : begin reg_dinb_r[127 :  96] <= di_mux; end
                    4'h4 : begin reg_dinb_r[159 : 128] <= di_mux; end
                    4'h5 : begin reg_dinb_r[191 : 160] <= di_mux; end
                    4'h6 : begin reg_dinb_r[223 : 192] <= di_mux; end
                    4'h7 : begin reg_dinb_r[255 : 224] <= di_mux; end
                    4'h8 : begin reg_dinb_r[287 : 256] <= di_mux; end
                    4'h9 : begin reg_dinb_r[319 : 288] <= di_mux; end
                    4'hA : begin reg_dinb_r[351 : 320] <= di_mux; end
                    4'hB : begin reg_dinb_r[383 : 352] <= di_mux; end
                    default: begin  end
                endcase
            end

            // Write new key
            if (wr_en_i & (wr_op_sel_i == 2'b01)) begin
                case (wr_word_sel_i)
                    4'h0 : begin secret_key[31  :   0] <= di_mux; end
                    4'h1 : begin secret_key[63  :  32] <= di_mux; end
                    4'h2 : begin secret_key[95  :  64] <= di_mux; end
                    4'h3 : begin secret_key[127 :  96] <= di_mux; end
                    4'h4 : begin secret_key[159 : 128] <= di_mux; end
                    4'h5 : begin secret_key[191 : 160] <= di_mux; end
                    4'h6 : begin secret_key[223 : 192] <= di_mux; end
                    4'h7 : begin secret_key[255 : 224] <= di_mux; end
                    4'h8 : begin secret_key[287 : 256] <= di_mux; end
                    4'h9 : begin secret_key[319 : 288] <= di_mux; end
                    4'hA : begin secret_key[351 : 320] <= di_mux; end
                    4'hB : begin secret_key[383 : 352] <= di_mux; end
                    4'hC : begin secret_key[384]       <= di_mux[0]; end
                    default: begin  end
                endcase
            end
            else if (req_digit) begin
                //Shift digit
                secret_key[REG_SIZE  : 1] <= secret_key[REG_SIZE-1 : 0];
                secret_key[0]             <= secret_key[REG_SIZE];
                
                if (count_o<384)
                    count_o         <= count_o+1;
                else
                    count_o         <= 0;
            end
            //Push key bit to ecc control
            digit_in <= secret_key[REG_SIZE];

            reg_addr_r <= addr_i;
            if (wr_op_sel_i == 2'b00)
                reg_web_r <= wr_en_i & wr_word_sel_i[0] & wr_word_sel_i[1] & (~ wr_word_sel_i[2]) & wr_word_sel_i[3]; // Write after the highest 32-bit word has been written
            
            // Read multiplexer    
            if (rd_reg_i)
                reg_dout_r <= opb_s;
        end
    end

    // Memory mapped register interface
    always @* begin
        case (rd_op_sel_i)
            2'b00 : begin
                case (rd_word_sel_i)
                    4'h0 : begin d_o <= reg_dout_r[31  :   0]; end
                    4'h1 : begin d_o <= reg_dout_r[63  :  32]; end
                    4'h2 : begin d_o <= reg_dout_r[95  :  64]; end
                    4'h3 : begin d_o <= reg_dout_r[127 :  96]; end
                    4'h4 : begin d_o <= reg_dout_r[159 : 128]; end
                    4'h5 : begin d_o <= reg_dout_r[191 : 160]; end
                    4'h6 : begin d_o <= reg_dout_r[223 : 192]; end
                    4'h7 : begin d_o <= reg_dout_r[255 : 224]; end
                    4'h8 : begin d_o <= reg_dout_r[287 : 256]; end
                    4'h9 : begin d_o <= reg_dout_r[319 : 288]; end
                    4'hA : begin d_o <= reg_dout_r[351 : 320]; end
                    4'hB : begin d_o <= reg_dout_r[383 : 352]; end
                    default: begin d_o <= 0; end
                endcase
            end
            
            2'b1 : begin
                case (rd_word_sel_i)
                    4'h0 : begin d_o <= secret_key[31  :   0]; end
                    4'h1 : begin d_o <= secret_key[63  :  32]; end
                    4'h2 : begin d_o <= secret_key[95  :  64]; end
                    4'h3 : begin d_o <= secret_key[127 :  96]; end
                    4'h4 : begin d_o <= secret_key[159 : 128]; end
                    4'h5 : begin d_o <= secret_key[191 : 160]; end
                    4'h6 : begin d_o <= secret_key[223 : 192]; end
                    4'h7 : begin d_o <= secret_key[255 : 224]; end
                    4'h8 : begin d_o <= secret_key[287 : 256]; end
                    4'h9 : begin d_o <= secret_key[319 : 288]; end
                    4'hA : begin d_o <= secret_key[351 : 320]; end
                    4'hB : begin d_o <= secret_key[383 : 352]; end
                    default: begin d_o <= 0; end
                endcase
            end

            default : begin
                d_o <= 0;
            end
        endcase
                    
    end
            
    assign addrb_mux_s = ecc_busy_s ? ecc_instr_s[7 : 0] : reg_addr_r;
    assign web_mux_s   = ecc_busy_s ? ecc_instr_s[16]    : reg_web_r;
    assign dinb_mux_s  = ecc_busy_s ? mult_res_s         : reg_dinb_r;
    assign busy_o      = ecc_busy_s;
    assign data_o      = d_o;

endmodule