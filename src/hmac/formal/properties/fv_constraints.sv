module fv_constraints_m
(
    input logic         clk,
    input logic         rst_n,
    input logic         zeroize,
    input logic         hmac_init,
    input logic         hmac_next,
    input logic [383:0] hmac_key
);

    logic fv_hmac_init_reg;

    default clocking default_clk @(posedge clk); endclocking

   
    always @ (posedge clk or negedge rst_n)
        begin
            if (!rst_n || zeroize)
                fv_hmac_init_reg <= 1'h0;
            else if (hmac_init)
                    fv_hmac_init_reg <= 1'h1;
    end
    

    //////////////////////////
    // Assumptions 1
    // hmac_init and hmac_next 
    // cannot be high at same 
    // time.
    /////
    property hmac_init_and_next_not_high_same;
        !(hmac_init && hmac_next);
    endproperty
    assume_hmac_init_and_next_not_high_same: assume property(disable iff(!rst_n)hmac_init_and_next_not_high_same);

    ///////////////////////////
    // Assumptions 2
    // hmac_init should be high 
    // first then next.
    //////
    property hmac_first_init_then_next;
        !fv_hmac_init_reg
    |->
        !hmac_next;
    endproperty
    assume_hmac_first_init_then_next : assume property(disable iff(!rst_n) hmac_first_init_then_next);

    ///////////////////////////
    // Assumptions 3
    // hmac_key must be stable 
    // from the receiving of the
    // key
    /////
    property hmac_key_stable;
    ##1 $stable(hmac_key) || hmac_init;
    endproperty
    assume_key_stable: assume property(disable iff(!rst_n)hmac_key_stable);

    ///////////////////////////
    // Assumptions 4
    // hmac_init must be high
    // unitl ready is high
    assume_init_not_ready: assume property (disable iff (!rst_n) 
        !hmac_core.ready 
    |-> 
        !hmac_init);

    endmodule

  bind hmac_core fv_constraints_m fv_constraints (
        .clk              (clk             ),
        .rst_n            (reset_n         ),
        .zeroize          (zeroize         ),
        .hmac_init        (init_cmd        ),
        .hmac_next        (next_cmd        ),
        .hmac_key         (key             )
    );


