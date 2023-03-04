//
// File: default_clk_gen.sv
//
// Generated from Mentor VIP Configurator (20220406)
// Generated using Mentor VIP Library ( 2022.2 : 04/20/2022:16:06 )
//
module default_clk_gen
(
    output reg  CLK
);
    
    timeunit 1ns;
    timeprecision 1ns;
    
    initial
    begin
        CLK = 0;
        forever
        begin
            #1 CLK = ~CLK;
        end
    end
    

endmodule: default_clk_gen
