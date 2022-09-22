`timescale 1ns / 1ps
//======================================================================
//
// masked_arith_tb.v
// --------
// Test reduction
//
//
// Author: Emre Karabulut
//======================================================================

module masked_arith_tb;

    parameter RADIX = 13;
    parameter PRNG_on_off = 0;
    parameter CLK_PERIOD = 10;

    reg [RADIX-1:0]   P1; // privKey-share 1
    reg [RADIX-1:0]   P2; // privKey-share 2
    reg [RADIX-1:0]   H1; // message-share 1
    reg [RADIX-1:0]   H2; // message-share 2
    reg [RADIX-1:0]   R;  // the part of signature
    reg [RADIX-1:0]   kInv; // Ephemeral key
    reg    clock;
    reg    rst_n;
    reg    start;

    wire    done;
    wire   [RADIX-1:0] S1; // signature-share 1
    wire   [RADIX-1:0] S2; // signature-share 2

    wire [RADIX-1:0] q;
    assign q = {RADIX{1'b1}};

    reg [12:0] d1;
    reg [12:0] d2;

    masked_arith#(
        .RADIX(RADIX)
    )
    dut
    ( 
        .P1		    (P1	), // privKey-share 1
        .P2		    (P2	), // privKey-share 2
        .H1		    (H1	), // message-share 1
        .H2		    (H2	), // message-share 2
        .R		    (R	),  // the part of signature
        .kInv		(kInv), // Ephemeral key
        .clock		(clock),
        .rst_n		(rst_n),
        .start		(start),
        .done		(done),
        .s1		    (S1	), // signature-share 1
        .s2		    (S2	) // signature-share 2
    );


    always
    begin : clock_gen
      #5;
      clock = !clock;
    end


    task wait_ready;
        begin
            while (done == 0)
            begin
                #CLK_PERIOD;
            end
        end
    endtask

    always@(posedge clock or negedge rst_n) begin : PRNG
        if ( rst_n == 1'b0 )
        begin
            d1 <= 0;
            d2 <= 0;
        end
        else
        begin
            d1 = $urandom_range(0, 8191-1);
            d2 = $urandom_range(0, 8191-1);
        end    
    end
    
    task unprotected (input  [RADIX-1:0]  privKey,
        input  [RADIX-1:0]  r,
        input  [RADIX-1:0]  h,
        input  [RADIX-1:0]  k_inv,
        output [RADIX-1:0]  s );
        reg [RADIX-1:0] PR, PRH;
        reg [2*RADIX-1:0] mult,add,mult2;
        begin
            PR = 0;
            PRH= 0;
            mult= 0;
            mult= privKey * r;
            PR = (mult) % q;
            add = (PR + h);
            PRH = (add) % q;
            mult2= PRH * k_inv;
            s = (mult2) % q;
        end
    endtask

    task splitting_two ( input  [RADIX-1:0]  P,
        input    key_or_message,
        output [RADIX-1:0]  D1,
        output [RADIX-1:0]  D2 );
        reg [RADIX-1:0] d;
        reg [2*RADIX-1:0] PD,QD;
        begin
            if (PRNG_on_off == 0)
                d=5;
            else if (key_or_message==0)
                d=d1;
            else
                d=d2;
            
            PD = P-d;
            QD = (q - d);
            QD = (P + QD) ;

            if (P >= d)
                D1 = PD;
            else
                D1 = QD;

            D2 = d;
        end
    endtask

    task verify_masking (input  [3*RADIX-1:0]  itr);
        reg [RADIX-1:0] k_inv, privKey, h, r, s;
        reg [RADIX:0] s1, s2;
        begin
            k_inv = $urandom_range(0, 8191-1);
            privKey = $urandom_range(0, 8191-1);
            kInv = k_inv;
            r = $urandom_range(0, 8191-1);
            R=r;
            start = 0;
            for (int i=0; i<itr; i++)
            begin
                // k_inv = $urandom_range(0, 8191-1);
                // privKey = $urandom_range(0, 8191-1);
                // kInv = k_inv;
                r = $urandom_range(0, 8191-1);
                R=r;
                h = $urandom_range(0, 8191-1);
                splitting_two (privKey,0,P1,P2);
                #CLK_PERIOD;
                splitting_two (h,1,H1,H2);
                start = 1;
                #CLK_PERIOD;
                start = 0;
                wait_ready();
                s1= S1;
                s2= S2;
                unprotected (privKey, r, h, k_inv, s);
                if (((s1+s2)%q) != s)
                    $display("error prot %d vs unprot %d",((s1+s2)%q), s);
                                
            end
            $display("TEST PASSED");
        end
    endtask



    initial begin
        start = 0;
        clock = 0;
        rst_n = 0;
        #40;
        rst_n = 1;
        #40;
        verify_masking(100000);
        #40;
    end

endmodule