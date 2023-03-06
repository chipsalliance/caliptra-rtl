//
// File: default_reset_gen.sv
//
// Generated from Mentor VIP Configurator (20220406)
// Generated using Mentor VIP Library ( 2022.2 : 04/20/2022:16:06 )
//
module default_reset_gen
(
    output reg  RESET,
    input  reg  CLK_IN
);
    
    initial
    begin
        RESET = 1;
        
        RESET = ~RESET;
        
        repeat ( 2 )
        begin
            @(posedge CLK_IN);
        end
        
        RESET = ~RESET;
    end
    

endmodule: default_reset_gen
