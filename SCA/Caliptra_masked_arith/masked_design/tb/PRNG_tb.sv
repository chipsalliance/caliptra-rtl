`timescale 1ns / 1ps
//======================================================================
//
// PRNG_tb.v
// --------
// Author: Emre Karabulut
//======================================================================

module PRNG_tb ();

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

    initial begin
        $monitor("rnd1 = 0x%x and rnd2 = 0x%x",random_number1,random_number2 );
    end


endmodule
