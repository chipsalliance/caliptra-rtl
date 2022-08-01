//======================================================================
//
// add_sub_mod.sv
// --------
// from VHDL-SIKE: a speed optimized hardware implementation of the 
//      Supersingular Isogeny Key Encapsulation scheme
//
// Author: Mojtaba Bisheh-Niasar
//======================================================================

module add_sub_mod #(
    parameter REG_SIZE      = 384,
    parameter PRIME         = 384'hfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff,
    parameter NUM_ADDS      = 1,
    parameter BASE_SZ       = 384
    )
    (
    // Clock and reset.
    input wire           clk,
    input wire           reset_n,

    // DATA PORT
    input  wire                 sub_i,
    input  wire                 red_i,
    input  wire  [REG_SIZE-1:0] opa_i,
    input  wire  [REG_SIZE-1:0] opb_i,
    output logic [REG_SIZE-1:0] res_o,
    output wire                 ready_o
);

    localparam L = 30;
    localparam H = 3;   

    logic [BASE_SZ-1 : 0] a_reg_array [0 : NUM_ADDS-1][0 : NUM_ADDS-1];
    logic [BASE_SZ-1 : 0] b_reg_array [0 : NUM_ADDS-1][0 : NUM_ADDS-1];
    logic [BASE_SZ-1 : 0] res1_reg_array [0 : NUM_ADDS-1][0 : NUM_ADDS-1];
    logic [BASE_SZ-1 : 0] res2_reg_array [0 : NUM_ADDS-1][0 : NUM_ADDS-1];
    logic [BASE_SZ-1 : 0] res1_array [0 : NUM_ADDS-1];
    logic [BASE_SZ-1 : 0] res2_array [0 : NUM_ADDS-1];

    logic                 carry1_array       [0 : NUM_ADDS];
    logic                 carry1_reg_array   [0 : NUM_ADDS];
    logic                 carry2_array       [0 : NUM_ADDS];
    logic                 carry2_reg_array   [0 : NUM_ADDS];
    logic                 add_ctrl_reg_array [0 : NUM_ADDS];
    logic                 red_array          [0 : NUM_ADDS];


    logic [BASE_SZ*NUM_ADDS-1 : 0]      full_a;
    logic [BASE_SZ*NUM_ADDS-1 : 0]      full_b;
    logic [BASE_SZ*NUM_ADDS-1 : 0]      full_p;
    logic [BASE_SZ*NUM_ADDS-1 : 0]      full_2p;
    logic [BASE_SZ*NUM_ADDS-1 : 0]      p_in;
    logic [BASE_SZ*NUM_ADDS-1 : 0]      res1_full;
    logic [BASE_SZ*NUM_ADDS-1 : 0]      res1_full_d1;
    logic [BASE_SZ*NUM_ADDS-1 : 0]      res2_full;

    logic neg1_s;
    logic neg2_s;
    logic neg1_r;
    logic zero2_s;

    logic [BASE_SZ*NUM_ADDS-REG_SIZE-1 : 0]    zeros;


    assign zeros = '0;
    assign full_p  = PRIME; //[BASE_SZ*NUM_ADDS-1 : 0];
    assign full_2p = full_p << 1; //{PRIME[BASE_SZ*NUM_ADDS-2 : 0] , 1'b0};
    assign full_a  = {zeros , opa_i[REG_SIZE-1 : 0]};
    assign full_b  = {zeros , opb_i[REG_SIZE-1 : 0]};

    assign carry1_array[0] = 1'b0;
    assign carry2_array[0] = 1'b0;


    always @* begin
        for (int j = 0; j < NUM_ADDS; j++) begin
            case (red_array[j])
                1'b1    : p_in[j*BASE_SZ +: BASE_SZ] = full_p[j*BASE_SZ +: BASE_SZ];
                default : p_in[j*BASE_SZ +: BASE_SZ] = full_2p[j*BASE_SZ +: BASE_SZ];
            endcase
        end
    end

    genvar I;
    generate
        for (I = 0; I < NUM_ADDS; I++) begin
            if (I == 0) begin
                add_sub_gen #(
                    .N(BASE_SZ), 
                    .L(L), 
                    .H(H)
                )
                ADD_SUB_GENERIC_INST_first(
                    .a_i(full_a[BASE_SZ-1 : 0]),
                    .b_i(full_b[BASE_SZ-1 : 0]),
                    .sub_i(sub_i),
                    .c_i(sub_i),
                    .res_o(res1_array[0]),
                    .c_o(carry1_array[1])
                );

                add_sub_gen #(
                    .N(BASE_SZ), 
                    .L(L), 
                    .H(H)
                )
                SUB_ADD_GENERIC_INST_first(
                    .a_i(res1_reg_array[0][0]),
                    .b_i(p_in[BASE_SZ-1 : 0]),
                    .sub_i(~add_ctrl_reg_array[0]), //Inverted sub/add for second cascaded adder
                    .c_i(~add_ctrl_reg_array[0]),
                    .res_o(res2_array[0]),
                    .c_o(carry2_array[1])
                );
            end
            else begin 
                add_sub_gen #(
                    .N(BASE_SZ), 
                    .L(L), 
                    .H(H)
                )
                ADD_SUB_GENERIC_INST_i(
                    .a_i(a_reg_array[I-1][I]),
                    .b_i(b_reg_array[I-1][I]),
                    .sub_i(add_ctrl_reg_array[I-1]),
                    .c_i(carry1_reg_array[I]),
                    .res_o(res1_array[I]),
                    .c_o(carry1_array[I+1])
                );

                add_sub_gen #(
                    .N(BASE_SZ), 
                    .L(L), 
                    .H(H)
                )
                SUB_ADD_GENERIC_INST_i(
                    .a_i(res1_reg_array[I][I]),
                    .b_i(p_in[(I+1)*(BASE_SZ)-1 : (I)*(BASE_SZ)]),
                    .sub_i(~add_ctrl_reg_array[I]),
                    .c_i(carry2_reg_array[I]),
                    .res_o(res2_array[I]),
                    .c_o(carry2_array[I+1])
                    );
            end
        end
    endgenerate
    
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            carry1_reg_array[NUM_ADDS] <= 1'b0;
            carry1_reg_array[0] <= 1'b0;
            carry2_reg_array[NUM_ADDS] <= 1'b0;
            carry2_reg_array[0] <= 1'b0;
            add_ctrl_reg_array[NUM_ADDS] <= 1'b0;
            
            red_array[0] <= 1'b0;
            red_array[NUM_ADDS] <= 1'b0;
            
            res1_full_d1 <= 0;
            neg1_r <= 1'b0;
            
            add_ctrl_reg_array[0] <= 1'b0;
            for (int j = 1; j < NUM_ADDS; j++) begin //Initialize a and b
                a_reg_array[0][j] <= '0;
                b_reg_array[0][j] <= '0;
            end
            res1_reg_array[0][0] <= '0;
            res2_reg_array[0][0] <= '0;
            for (int i = 1; i < NUM_ADDS; i++) begin
                carry1_reg_array[i] <= 1'b0;
                carry2_reg_array[i] <= 1'b0;
                add_ctrl_reg_array[i] <= 1'b0;
                red_array[i] <= 1'b0;
                for (int j = 0; j < NUM_ADDS; j++) begin
                    if (i >= j) begin
                        res1_reg_array[i][j] <= '0;
                        res2_reg_array[i][j] <= '0;
                    end
                    if (i < j) begin
                        a_reg_array[i][j] <= '0;
                        b_reg_array[i][j] <= '0;
                    end
                end
            end
        end
        else begin
            res1_full_d1 <= res1_full;
            neg1_r <= neg1_s;
            carry1_reg_array[NUM_ADDS] <= carry1_array[NUM_ADDS];
            carry2_reg_array[NUM_ADDS] <= carry2_array[NUM_ADDS];
            add_ctrl_reg_array[NUM_ADDS] <= add_ctrl_reg_array[NUM_ADDS-1];
            add_ctrl_reg_array[0] <= sub_i;

            for (int j = 1; j < NUM_ADDS; j++) begin //Initialize a and b
                a_reg_array[0][j] <= full_a[j*BASE_SZ +: BASE_SZ];
                b_reg_array[0][j] <= full_b[j*BASE_SZ +: BASE_SZ];
            end
            res1_reg_array[0][0] <= res1_array[0];
            res2_reg_array[0][0] <= res2_array[0];
            red_array[0] <= red_i;
            red_array[NUM_ADDS] <= red_array[NUM_ADDS-1];

            for (int i = 1; i < NUM_ADDS; i++) begin
                red_array[i] <= red_array[i-1];
                carry1_reg_array[i] <= carry1_array[i];
                carry2_reg_array[i] <= carry2_array[i];
                add_ctrl_reg_array[i] <= add_ctrl_reg_array[i-1];
                for (int j = 0; j < NUM_ADDS; j++) begin
                    if (i == j) begin
                        res1_reg_array[i][j] <= res1_array[i];
                        res2_reg_array[i][j] <= res2_array[i];
                    end
                    else if (i > j) begin
                        res1_reg_array[i][j] <= res1_reg_array[i-1][j];
                        res2_reg_array[i][j] <= res2_reg_array[i-1][j];
                    end
                    if (i < j) begin
                        a_reg_array[i][j] <= a_reg_array[i-1][j];
                        b_reg_array[i][j] <= b_reg_array[i-1][j];            
                    end
                end
            end
        end
    end
   
    always @* begin
        for (int j = 0; j < NUM_ADDS; j++) begin
            res1_full[j*BASE_SZ +: BASE_SZ] <= res1_reg_array[NUM_ADDS-1][j];
            res2_full[j*BASE_SZ +: BASE_SZ] <= res2_reg_array[NUM_ADDS-1][j];
        end
    end
    
    //check here
    assign neg1_s = res1_reg_array[NUM_ADDS-1][NUM_ADDS-1][BASE_SZ-1];
    assign neg2_s = res2_reg_array[NUM_ADDS-1][NUM_ADDS-1][BASE_SZ-1];

    always @* begin
        if (add_ctrl_reg_array[NUM_ADDS] == 0) begin  //A+B-p
            if ((neg2_s == 0) | ((red_array[NUM_ADDS-1] == 1) & (zero2_s == 1))) 
                res_o = res2_full[REG_SIZE-1 : 0];
            else
                res_o = res1_full_d1[REG_SIZE-1 : 0];
        end
        else begin //A-B+p
            if (neg1_r == 1)
                res_o = res2_full[REG_SIZE-1 : 0];
            else
                res_o = res1_full_d1[REG_SIZE-1 : 0];
        end
    end

    always @* begin
        if (res2_full == 0) //if unsigned(res2_full) = 0 then
            zero2_s = 1;
        else
            zero2_s = 0;
    end
    
endmodule