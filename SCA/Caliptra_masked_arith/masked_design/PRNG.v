//======================================================================
//
// PRNG.v
// --------
// This is for 2 randomness
//
//
// Author: Emre Karabulut
//======================================================================

module PRNG #(
    parameter RADIX = 64
)
(
    // DATA PORT
    input  wire [RADIX-1:0]   seed1,
    input  wire [RADIX-1:0]   seed2,
    input  wire    clock,
    input  wire    rst_n,
    input  wire    PRNG_on,

    output reg   [RADIX-1:0] random_number1,
    output reg   [RADIX-1:0] random_number2
);

    parameter IDLE=0,
              RND=1;

    reg state;
    wire [RADIX-1:0] new_random_number1;
    wire [RADIX-1:0] new_random_number2;

    always @(posedge clock or negedge rst_n) begin
        if ( rst_n == 1'b0 )
        begin
            random_number1 <= {RADIX{1'b0}};
            random_number2 <= {RADIX{1'b0}};
            state          <= IDLE;
        end
        else
        begin
            case (state)
                IDLE:
                begin                    
                    if (PRNG_on)
                    begin
                        state          <= RND;
                        random_number1 <= seed1;
                        random_number2 <= seed2;
                    end
                    else
                    begin
                        state          <= IDLE;
                        random_number1 <= {RADIX{1'b0}};
                        random_number2 <= {RADIX{1'b0}};
                    end 
                end
                RND:
                begin
                    random_number1 <= new_random_number1;
                    random_number2 <= new_random_number2;
                    state          <= RND;
                end
            endcase

        end
    end


    xorshift #(.RADIX(RADIX))
    xor1(
        .x(random_number1),
        .random_number(new_random_number1)
    );

    xorshift #(.RADIX(RADIX))
    xor2(
        .x(random_number2),
        .random_number(new_random_number2)
    );

endmodule
