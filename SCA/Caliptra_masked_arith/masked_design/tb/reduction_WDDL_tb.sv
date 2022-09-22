`timescale 1ns / 1ps
//======================================================================
//
// reduction_WDDL_tb.v
// --------
// Test reduction with WDDL circuit
//
//
// Author: Emre Karabulut
//======================================================================

module reduction_WDDL_tb;

    parameter RADIX = 64;

    reg [RADIX-1:0]   seed1;
    reg [RADIX-1:0]   seed2;
    reg    clock;
    reg    rst_n;
    reg    PRNG_on;

    wire   [RADIX-1:0] random_number1;
    wire   [RADIX-1:0] random_number2;

    PRNG#(
        .RADIX(RADIX)
    )
    dut
    (    
        .seed1			(seed1			),
        .seed2			(seed2			),
        .clock			(clock			),
        .rst_n			(rst_n			),
        .PRNG_on		(PRNG_on		),
        .random_number1	(random_number1	),
        .random_number2 (random_number2 )
    );

    reg [25:0]   naive;
    wire   [12:0]  reducted,reducted_WDDL,reducted_WDDL_n;

    reduction dut2
    (
        .naive (naive),
        .reducted(reducted)
    );

    reduction_WDDL dut3
    (
        .naive (naive),
        .reducted(reducted_WDDL),
        .reducted_n(reducted_WDDL_n)
    );

    always
    begin : clock_gen
      #10;
      clock = !clock;
    end 

    initial begin
        clock = 0;
        rst_n = 0;
        seed1 = 0;
        seed2 = 0;
        PRNG_on = 0;
        #40;
        rst_n = 1;
        #40;
        seed1 = 1;
        seed2 = 1;
        #40;
        PRNG_on =1;
    end

    always@(posedge clock or negedge rst_n) begin : reduction_test
        if ( rst_n == 1'b0 )
        begin
            naive <= 0;
        end
        else
        begin
            naive <= random_number1;
            if ((naive%8191) != reducted_WDDL)
                $display("error operator= %d and reducter= %d", (naive%8191), reducted);
        end
      
      
    end

endmodule