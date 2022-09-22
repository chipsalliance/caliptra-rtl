//======================================================================
//
// masked_arith.v
// --------
// This circuit works on the shares that are split already. This design
// does not perform either splitting or Boolean comparison
//
// Author: Emre Karabulut
//======================================================================

module masked_arith #(
    parameter RADIX = 13
)
(
    // DATA PORT
    input  wire [RADIX-1:0]   P1, // privKey-share 1
    input  wire [RADIX-1:0]   P2, // privKey-share 2
    input  wire [RADIX-1:0]   H1, // message-share 1
    input  wire [RADIX-1:0]   H2, // message-share 2
    input  wire [RADIX-1:0]   R,  // the part of signature
    input  wire [RADIX-1:0]   kInv, // Ephemeral key
    input  wire    clock,
    input  wire    rst_n,
    input  wire    start,

    output reg    done,
    output reg   [RADIX-1:0] s1, // signature-share 1
    output reg   [RADIX-1:0] s2,  // signature-share 2
    output [3*RADIX-1:0]   WDDL_out
);

    parameter IDLE=0,
              PR=1,
              PRH=2,
              S1=3,
              S2=4,
              DONE=5;

    reg [2:0] state;

    //Registers
    reg [RADIX-1:0]   P1_2, H1_2;
    reg [RADIX-1:0]   PR1_2_reg, PRH1_2_reg;
    reg [RADIX-1:0]   PR1_2_reg_n, PRH1_2_reg_n, S1_2_reg_n;


    //Wires
    wire [2*RADIX-1:0] PR1_2, S1_2;
    wire [RADIX:0]     PRH1_2;
    wire [RADIX-1:0]   PR1_2_red, PRH1_2_red, S1_2_red;
    wire [RADIX-1:0]   PR1_2_red_n, PRH1_2_red_n, S1_2_red_n;
    

    assign WDDL_out ={PR1_2_reg_n, PRH1_2_reg_n, S1_2_reg_n}; 

    always @(posedge clock or negedge rst_n) begin
        if ( rst_n == 1'b0 )
        begin
            s1          <= {RADIX{1'b0}};
            s2          <= {RADIX{1'b0}};
            P1_2        <= {RADIX{1'b0}};
            H1_2        <= {RADIX{1'b0}};
            done        <= 1'b0;
            state       <= IDLE;
            PR1_2_reg   <= {RADIX{1'b0}};
            PRH1_2_reg  <= {RADIX{1'b0}};
            PR1_2_reg_n <= {RADIX{1'b0}};
            PRH1_2_reg_n<= {RADIX{1'b0}};
            S1_2_reg_n  <= {RADIX{1'b0}};
        end
        else
        begin
            PR1_2_reg  <= PR1_2_red;
            PRH1_2_reg <= PRH1_2_red;
            PR1_2_reg_n <= PR1_2_red_n;
            PRH1_2_reg_n<= PRH1_2_red_n;            
            case (state)
                IDLE:
                begin
                    s1      <= s1;
                    s2      <= s2;
                    S1_2_reg_n  <= S1_2_reg_n;
                    P1_2    <= P1;
                    H1_2    <= H1;      
                    if (start)
                    begin
                        state   <= PR;
                        done    <= 1'b0;
                    end
                    else
                    begin
                        state   <= IDLE;
                        done    <= 1'b1;
                    end
                end
                PR:
                begin
                    s1      <= s1;
                    s2      <= s2;
                    S1_2_reg_n  <= S1_2_reg_n;
                    P1_2    <= P2;
                    H1_2    <= H1;  
                    done    <= 1'b0;
                    state   <= PRH;
                end                
                PRH:
                begin
                    s1      <= s1;
                    s2      <= s2;
                    S1_2_reg_n  <= S1_2_reg_n;
                    P1_2    <= P2;
                    H1_2    <= H2;  
                    done    <= 1'b0;
                    state   <= S1;
                end                                
                S1:
                begin
                    s1      <= S1_2_red;
                    S1_2_reg_n  <= S1_2_red_n;
                    s2      <= s2;
                    P1_2    <= P2;
                    H1_2    <= H2;  
                    done    <= 1'b0;
                    state   <= S2;
                end                
                S2:
                begin
                    s1      <= s1;
                    s2      <= S1_2_red;
                    S1_2_reg_n  <= S1_2_red_n;
                    P1_2    <= P2;
                    H1_2    <= H2;  
                    done    <= 1'b1;
                    state   <= DONE;
                end
                DONE:
                begin
                    s1      <= s1;
                    s2      <= s2;
                    S1_2_reg_n  <= S1_2_reg_n;
                    P1_2    <= P2;
                    H1_2    <= H2;  
                    done    <= 1'b1;
                    if (start==0)
                        state   <= IDLE;
                    else
                        state   <= DONE;
                end
            endcase

        end
    end


    multiplier #(
        .RADIX(RADIX)
    ) PR_dut (
        .A(P1_2),
        .B(R),
        .P(PR1_2)
    );

    reduction_WDDL red1
    (
        .naive (PR1_2),
        .reducted(PR1_2_red),
        .reducted_n(PR1_2_red_n)
    );

    adder #(
        .RADIX(RADIX)
    ) PRH_dut (
        .A(PR1_2_reg),
        .B(H1_2),
        .P(PRH1_2)
    );

    reduction_WDDL red2
    (
        .naive ({ {12{1'b0}}, PRH1_2 }),
        .reducted(PRH1_2_red),
        .reducted_n(PRH1_2_red_n)
    );

    multiplier #(
        .RADIX(RADIX)
    ) S_1_2_dut (
        .A(PRH1_2_reg),
        .B(kInv),
        .P(S1_2)
    );

    reduction_WDDL red3
    (
        .naive (S1_2),
        .reducted(S1_2_red),
        .reducted_n(S1_2_red_n)
    );



endmodule