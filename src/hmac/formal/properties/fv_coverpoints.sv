module fv_coverpoints_m(
    input logic clk,
    input logic reset_n,
    input logic zeroize
);
    
    default clocking default_clk @(posedge clk); endclocking

     //Cover zeroize: 
     //Assert zeroize input and check the status of all registers. All registers/internal memories should be cleared.
     cover_zeroize: cover property(disable iff(!reset_n) hmac_core.zeroize );
     cover_zeroize_after_next: cover property(disable iff(!reset_n  ) hmac_core.zeroize && hmac_core.ready && hmac_core.next_cmd );
     cover_multiple_next: cover property(disable iff(!reset_n || zeroize ) 
     hmac_core.next_cmd && hmac_core.ready ##1 hmac_core.next_cmd && hmac_core.ready[->1] );

    // Assert init_cmd or next_cmd when HMAC_ready is still low. The engine ignores the new command and continues 
    // to complete the previous command.
     cover_init_and_next_ready_low: cover property(disable iff(!reset_n || zeroize) 
        (hmac_core.init_cmd || 
        hmac_core.next_cmd) &&
        !hmac_core.ready
        );


    // Assert to check if init_cmd then process the key if not process the block message.
     cover_init_IPAD: cover property(disable iff(!reset_n || zeroize) 
        hmac_core.init_cmd 
        ##2
        hmac_core.CTRL_IPAD
        );

     cover_next_OPAD: cover property(disable iff(!reset_n || zeroize) 
        (hmac_core.next_cmd 
        ##2
        hmac_core.CTRL_OPAD
        ));

 endmodule 
bind hmac_core fv_coverpoints_m fv_coverpoints(
  .clk(clk),
  .reset_n(reset_n),
  .zeroize(zeroize)
);