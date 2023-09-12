module fv_key_stable_top_m
(
    input logic           clk,
    input logic           rst_n
);

    default clocking default_clk @(posedge clk); endclocking

//TODO: hmac top should keep the key stable for signle computation. Check with assertion 
logic [383:0] hmac_key;
logic hmac_init;

assign hmac_key = hmac_ctrl.hmac_inst.core.key;
assign hmac_init = hmac_ctrl.hmac_inst.core.init_cmd;


assert_wip_key_stable: assert property(disable iff(!rst_n)
    hmac_init
    |=>
      ($stable(hmac_key) || hmac_init)
    );


endmodule
  bind hmac_ctrl fv_key_stable_top_m fv_key_stable_top (
        .clk              (clk             ),
        .rst_n            (reset_n         )
    );