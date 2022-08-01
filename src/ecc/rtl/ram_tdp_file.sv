//======================================================================
//
// ram_tdp_file.sv
// --------
// 
//
//
// Author: Mojtaba Bisheh-Niasar
//======================================================================

module ram_tdp_file #(
    parameter ADDR_WIDTH = 10,
    parameter DATA_WIDTH = 32
    )
    (      
    input  wire                      clk,
    
    input  wire                      ena,
    input  wire                      wea,
    input  wire  [ADDR_WIDTH-1 : 0]  addra,
    input  wire  [DATA_WIDTH-1 : 0]  dina,
    output logic [DATA_WIDTH-1 : 0]  douta,

    input  wire                      enb,
    input  wire                      web,
    input  wire  [ADDR_WIDTH-1 : 0]  addrb,
    input  wire  [DATA_WIDTH-1 : 0]  dinb,
    output logic [DATA_WIDTH-1 : 0]  doutb
    );
 
    // Declare the RAM variable
	reg [DATA_WIDTH-1:0] mem[2**ADDR_WIDTH-1:0];

    always_ff @ (posedge clk) begin
        if (ena) begin
            douta <= mem[addra];
            if(wea)
                mem[addra] <= dina;
        end

        if (enb) begin
            doutb <= mem[addrb];
            if(web)
                mem[addrb] <= dinb;
        end
    end

endmodule