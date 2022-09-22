//======================================================================
//
// mm.sv
// --------
// 
//
//
// Author: Mojtaba Bisheh-Niasar
//======================================================================

module mm #(
    parameter REG_SIZE  = 384,
    parameter PE_UNITS  = 5,
    parameter S_NUM     = 13,
    parameter RADIX     = 32
)
(
    // Clock and reset.
    input wire           clk,
    input wire           reset_n,

    // DATA PORT
    input  wire                 start_i,
    input  wire [REG_SIZE-1:0]  opa_i,
    input  wire [REG_SIZE-1:0]  opb_i,
    output wire [REG_SIZE-1:0]  p_o,
    output wire                 ready_o
);

    //----------------------------------------------------------------
    // mm
    //----------------------------------------------------------------
    wire [RADIX-1 : 0] a_array[0:PE_UNITS+1];
    wire [RADIX-1 : 0] b_array[0:PE_UNITS+1];
    wire [RADIX-1 : 0] p_array[0:PE_UNITS+1];
    wire [RADIX-1 : 0] m_array[0:PE_UNITS];
    wire [RADIX   : 0] c_array[0:PE_UNITS+1];
    wire [RADIX-1 : 0] s_array[0:PE_UNITS+1];
    
    reg   [RADIX-1 : 0] t_reg[0:2*PE_UNITS+1];
    
    reg   [REG_SIZE-1 : 0]          a_reg;
    reg   [REG_SIZE+RADIX-1 : 0]    b_reg;  //extended with zero
    wire   [REG_SIZE+RADIX-1 : 0]    p_reg;  //extended with zero
    reg   [3*S_NUM-1 : 0]           push_reg;
    reg                             odd;
    reg   [RADIX-1 : 0]             last_s_reg; 
    
    PE_first #(
        .RADIX(RADIX)
        )
        first_box
        (
        .clk(clk),
        .reset_n(reset_n & ~start_i),
        .a_in(a_array[0]),
        .b_in(b_array[0]),
        .s_in(s_array[0]),
        .odd(odd),

        .a_out(a_array[1]),
        .m_out(m_array[0]),
        .c_out(c_array[0])
        );

    genvar i;
    generate 
        for (i=0; i < PE_UNITS; i=i+1) begin //PE general boxes
            PE #(
                .RADIX(RADIX)
                )
                box_i
                (
                .clk(clk),
                .reset_n(reset_n & ~start_i),
                .a_in(a_array[i+1]),
                .b_in(b_array[i+1]),
                .p_in(p_array[i+1]),
                .m_in(m_array[i]),
                .s_in(s_array[i+1]),
                .c_in(c_array[i]),
                .odd(odd),

                .a_out(a_array[i+2]),
                .m_out(m_array[i+1]),
                .s_out(s_array[i]),
                .c_out(c_array[i+1])
                );
        end
    endgenerate

    PE_final #(
        .RADIX(RADIX)
        )
        final_box
        (
        .clk(clk),
        .reset_n(reset_n & ~start_i),
        .a_in(a_array[PE_UNITS+1]),
        .b_in(b_array[PE_UNITS+1]),
        .p_in(p_array[PE_UNITS+1]),
        .m_in(m_array[PE_UNITS]),
        .s_in(s_array[PE_UNITS+1]),
        .c_in(c_array[PE_UNITS]),
        .odd(odd),

        .s_out(s_array[PE_UNITS]),
        .c_out(c_array[PE_UNITS+1])
        );
        
    assign s_array[PE_UNITS+1] = last_s_reg;
    
    always @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            last_s_reg <= 0;
        else if (start_i)
            last_s_reg <= 0;
        else
            last_s_reg <= c_array[PE_UNITS+1];
    end

    always @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            odd <= 0;
        else if (start_i)
            odd <= 1;
        else
            odd <= ~odd;
    end
        
    always @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            a_reg <= 0;
        else if (start_i)
            a_reg <= opa_i;
        else if (odd) begin
            a_reg[REG_SIZE-RADIX-1 : 0] <= a_reg[REG_SIZE-1 : RADIX];
            a_reg[REG_SIZE-1 : REG_SIZE-RADIX] <= 0; //Shift 
        end 
        else
            a_reg <= a_reg;
    end

    always @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            b_reg <= 0;
        else if (start_i)
            b_reg <= opb_i;
        else
            b_reg <= b_reg;
    end

    assign a_array[0] = a_reg[RADIX-1 : 0];
    assign b_array[0] = b_reg[RADIX-1 : 0];
    assign p_reg = 384'hfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff;
    assign p_array[0] = p_reg[RADIX-1 : 0];

    genvar j;
    generate 
        for (j=1; j < PE_UNITS+2; j=j+1) begin 
            assign b_array[j] = odd ? b_reg[(2*j+1)*RADIX-1 : (2*j)*RADIX] : b_reg[(2*j)*RADIX-1 : (2*j-1)*RADIX];
            assign p_array[j] = odd ? p_reg[(2*j+1)*RADIX-1 : (2*j)*RADIX] : p_reg[(2*j)*RADIX-1 : (2*j-1)*RADIX];
        end
    endgenerate

    genvar t;
    generate 
        for (t=0; t < 2*(PE_UNITS+1); t=t+1) begin
            always @(posedge clk or negedge reset_n) begin
                if (!reset_n)
                    t_reg[t] <= 0;
                else if (push_reg[2*PE_UNITS+1 - t])
                    t_reg[t] <= s_array[t >> 1];
                else
                    t_reg[t] <= t_reg[t];
            end
        end
    endgenerate
    
    genvar k;
    generate 
        for (k=0; k < 2*(PE_UNITS+1); k=k+1) begin
            assign p_o[(k+1)*RADIX-1 : k*RADIX] = t_reg[k];
        end
    endgenerate
        
    always @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            push_reg <= 0;
        else if (start_i)
            push_reg[3*S_NUM-2] <= 1'b1;
        else
            push_reg <= push_reg >> 1;
    end
    
    assign ready_o = (push_reg == 0);

endmodule