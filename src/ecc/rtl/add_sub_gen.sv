//======================================================================
//
// add_sub_gen.sv
// --------
// from VHDL-SIKE: a speed optimized hardware implementation of the 
//      Supersingular Isogeny Key Encapsulation scheme
//
// Author: Mojtaba Bisheh-Niasar
//======================================================================


module add_sub_gen #(
    parameter N = 384,
    parameter L = 30,
    parameter H = 2
    )
    (
    // DATA PORT
    input  wire [N-1 : 0]    a_i,
    input  wire [N-1 : 0]    b_i,
    input  wire              sub_i, //0 = add, 1 = sub
    input  wire              c_i,
    output wire [N-1 : 0]    res_o,
    output wire              c_o
);

    function int log2(int value);
        for (log2 = 0; value > 0; log2=log2+1)
            value = value>>1;
    endfunction

    localparam log2_N = log2(N);

    function int get_max_H (int log2_N, int  H);
        if (H < log2_N)
            return H;
        else
            return log2_N;
    endfunction
    
    localparam max_H = get_max_H(log2_N, H);
    typedef int h_int_arr [0 : max_H];

    function h_int_arr get_H_total (int L, int N, int H);
        h_int_arr res;
        int t;

        res[0] = N;
        for (int i = 0; i < H; i++) begin
            t = res[i] - (res[i] - (2*i+1)*L)/2;
            if (t < res[i])
                res[i+1] = t;
            else
                res[i+1] = res[i];
        end
        return res;
    endfunction
    
    function h_int_arr get_H_start (int L, int H, h_int_arr ht);
        int s;
        h_int_arr res;
        
        res[0] = 0;
        for (int i = 0; i < H; i++) begin
            s = i * L;
            if (ht[i+1] < ht[i])
                res[i+1] = s;
            else
                res[i+1] = ht[i+1];
        end
        return res;
    endfunction
    
    function h_int_arr get_H_finish (int L, int H, h_int_arr ht, h_int_arr hs);
        int f;
        h_int_arr res;

        res[0] = 0;
        for (int i = 0; i < H; i++) begin
            f = ht[i+1] - (ht[i] - ht[i+1]) - hs[i+1];
            if (ht[i+1] < ht[i])
                res[i+1] = f;
            else
                res[i+1] = 0;
        end
        return res;
    endfunction
    
    localparam h_int_arr ht = get_H_total(L, N, max_H);
    localparam h_int_arr hs = get_H_start(L, max_H, ht);
    localparam h_int_arr hf = get_H_finish(L, max_H, ht, hs);
    
    logic [N-1 : 0] a_compact [0 : max_H];
    logic [N-1 : 0] b_compact [0 : max_H];
    logic [N-1 : 0] s_expand  [0 : max_H];

    
    assign a_compact[0] = a_i;
    assign b_compact[0] = (sub_i == 1'b0) ? b_i : ~b_i;
    
    genvar I, J;
    generate
        for (I = 0; I < max_H; I++) begin
            
            localparam pt = ht[I];
            localparam nt = ht[I+1];
            localparam s = hs[I+1];
            localparam f = hf[I+1];
            
            if (s == 0) begin
                assign a_compact[I+1][0] = '0;
                assign b_compact[I+1][0] = '0;
            end
            else begin
                assign a_compact[I+1][hs[I+1]-1 : 0] = a_compact[I][hs[I+1]-1 : 0];
                assign b_compact[I+1][hs[I+1]-1 : 0] = b_compact[I][hs[I+1]-1 : 0];
            end
        
            //genvar J;
            //generate
            for (J = 0; J < hf[I+1]-hf[I+1]-hs[I+1]; J++) begin
                compact compact_inst(
                    .a1(a_compact[I][hs[I+1]+2*J]),
                    .b1(b_compact[I][hs[I+1]+2*J]),
                    .a2(a_compact[I][hs[I+1]+2*J+1]),
                    .b2(b_compact[I][hs[I+1]+2*J+1]),
                    .A_out(a_compact[I+1][hs[I+1]+J]),
                    .B_out(b_compact[I+1][hs[I+1]+J])
                );
            end
            //endgenerate
        
            assign a_compact[I+1][ht[I+1]-1 : ht[I+1]-hf[I+1]] = a_compact[I][ht[I]-1 : ht[I]-hf[I+1]];
            assign b_compact[I+1][ht[I+1]-1 : ht[I+1]-hf[I+1]] = b_compact[I][ht[I]-1 : ht[I]-hf[I+1]];
            
            assign a_compact[I+1][N-1 : ht[I+1]] = '0;
            assign b_compact[I+1][N-1 : ht[I+1]] = '0;
        end
    endgenerate
    
    adder #(
        .N(ht[max_H])
        ) 
        adder_inst(
        .a(a_compact[max_H][ht[max_H]-1 : 0]),
        .b(b_compact[max_H][ht[max_H]-1 : 0]),
        .cin(c_i),
        .s(s_expand[max_H][ht[max_H]-1 : 0]),
        .cout(c_o)
        );

    assign s_expand[max_H][N-1 : ht[max_H]] = '0;
    
    genvar II, JJ;
    generate
        for (II = max_H-1; II >= 0; II--) begin
            localparam int pt = ht[II];
            localparam int nt = ht[II+1];
            localparam int s = hs[II+1];
            localparam int f = hf[II+1];
    
            assign s_expand[II][s-1 : 0] = s_expand[II+1][s-1 : 0];
        
            //genvar JJ;
            //generate
            for (JJ = 0; JJ < nt-f-s; JJ++) begin
                expand expand_inst(
                    .a1(a_compact[II][s+2*JJ]),
                    .b1(b_compact[II][s+2*JJ]),
                    .a2(a_compact[II][s+2*JJ+1]),
                    .b2(b_compact[II][s+2*JJ+1]),
                    .S_in(s_expand[II+1][s+JJ]),
                    .s1(s_expand[II][s+2*JJ]),
                    .s2(s_expand[II][s+2*JJ+1])
                );
            end
            //endgenerate
        
            assign s_expand[II][pt-1 : pt-f] = s_expand[II+1][nt-1 : nt-f];
            
            assign s_expand[II][N-1 : pt] = '0;
        end
    endgenerate

    assign res_o = s_expand[0];
    
endmodule
