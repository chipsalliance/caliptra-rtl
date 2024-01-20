// -------------------------------------------------
// Contact: contact@lubis-eda.com
// Author: Tobias Ludwig, Michael Schwarz
// -------------------------------------------------
// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
module fv_ecc_ram_tdp_file #(
    parameter ADDR_WIDTH = 10,
    parameter DATA_WIDTH = 32
    )
    (      
    input  wire                      clk,
    input  wire                      rst_n,
   
    
    input  wire                      ena,
    input  wire                      wea,
    input  wire  [ADDR_WIDTH-1 : 0]  addra,
    input  wire  [DATA_WIDTH-1 : 0]  dina,
    input logic [DATA_WIDTH-1 : 0]  douta,

    input  wire                      enb,
    input  wire                      web,
    input  wire  [ADDR_WIDTH-1 : 0]  addrb,
    input  wire  [DATA_WIDTH-1 : 0]  dinb,
    input logic [DATA_WIDTH-1 : 0]  doutb
    );
 
      // Declare the RAM variable
     localparam ADDR_LENGTH = 2**ADDR_WIDTH;
    default clocking default_clk @(posedge clk); endclocking


    sequence reset_sequence;
      !rst_n ##1 rst_n;
    endsequence

addr_not_same_write : assume property (disable iff(!rst_n) (ena && wea && enb && web) |-> addra != addrb);


////////////////////////////////////////////
// reset property, when reset out a and b //
// are zero                               //
////////////////////////////////////////////

    property reset_p;
     $past(!rst_n)  
    |->
    douta == '0 &&
    doutb == '0;
    endproperty

    reset_a : assert property(reset_p);


 


///////////////////////////////////////////////
//Symbolic  checking                         // 
///////////////////////////////////////////////
    logic [ADDR_WIDTH-1:0] sym_addr;

    property sym_reset_mem_p;
        $past(!rst_n) 
        |->
        ecc_ram_tdp_file.mem[sym_addr] == '0;
    endproperty
    sym_reset_mem_a: assert property(sym_reset_mem_p);


   ///////////////////////////////////////////////
   // write to the memory with din in the       //
   // address provided considering the addresses//                          
   // a and b  will not be same while writing   // 
   ///////////////////////////////////////////////

    logic [8:0] idx_sym_data_wr_a; 
    logic [8:0] idx_sym_data_wr_b;
   
    idx_sym_wr_a_less_than_384: assume property(disable iff(!rst_n) (idx_sym_data_wr_a<9'd384) && $stable(idx_sym_data_wr_a));
    idx_sym_wr_b_less_than_384: assume property(disable iff(!rst_n) (idx_sym_data_wr_b<9'd384) && $stable(idx_sym_data_wr_b));

  
    property write_p(en,we,addr,dout,din,idx);
     logic [ADDR_WIDTH-1 : 0] store_addr;
     logic [DATA_WIDTH-1: 0]  store_data;
        en &&
        we 
        ##0 (1'b1, store_addr = addr)
        ##0 (1'b1, store_data =  ecc_ram_tdp_file.mem[addr])
        |=>
        dout[idx] == store_data[idx] &&
        (ecc_ram_tdp_file.mem[store_addr][idx]) == $past(din[idx])
        ;
    endproperty
    write_a_a: assert property(disable iff(!rst_n)write_p(ena,wea,addra,douta,dina,idx_sym_data_wr_a));
    write_b_a: assert property(disable iff(!rst_n)write_p(enb,web,addrb,doutb,dinb,idx_sym_data_wr_b));




    ///////////////////////////////////////////////
    // read to the memory with whatever the      //
    // address provided considering the addresses//                          
    // a and b  can be same                      // 
    ///////////////////////////////////////////////
    logic [8:0] idx_sym_data_rd_a;
    logic [8:0] idx_sym_data_rd_b;

     idx_sym_rd_a_less_than_384: assume property(disable iff(!rst_n) (idx_sym_data_rd_a<9'd384) &&  $stable(idx_sym_data_rd_a));
     idx_sym_rd_b_less_than_384:assume property(disable iff(!rst_n) (idx_sym_data_rd_b<9'd384) && $stable(idx_sym_data_rd_b));


     property read_p(en,we,addr,dout,idx);
        logic [DATA_WIDTH-1:0] store_data;
        logic [ADDR_WIDTH-1:0] store_addr;
        en &&
        !we 
        ##0 (1'b1, store_data = ecc_ram_tdp_file.mem[addr] )
        |=>
        dout[idx] == store_data[idx]
        ;
    endproperty
    read_a_a: assert property(disable iff(!rst_n)read_p(ena,wea,addra,douta,idx_sym_data_rd_a));
    read_b_a: assert property(disable iff(!rst_n)read_p(enb,web,addrb,doutb,idx_sym_data_rd_b));




///////////////////////////////////////////////
// No enable, no read and write              // 
///////////////////////////////////////////////
    logic [8:0] idx_sym_nen_a;
    logic [8:0] idx_sym_nen_b;
    logic [8:0] idx_sym_nen_ab;

    idx_sym_nen_a_less_than_384: assume property(disable iff(!rst_n) (idx_sym_nen_a<9'd384) &&  $stable(idx_sym_nen_a));
    idx_sym_nen_b_less_than_384: assume property(disable iff(!rst_n) (idx_sym_nen_b<9'd384) &&  $stable(idx_sym_nen_b));
    idx_sym_nen_ab_less_than_384: assume property(disable iff(!rst_n) (idx_sym_nen_ab<9'd384) && $stable(idx_sym_nen_ab));

    
    property no_enable_p(en,dout,addr,idx);
    logic [DATA_WIDTH-1:0] store_data;
    logic [ADDR_WIDTH-1 : 0] store_addr;
        !en &&
        addra != addrb
        ##0 (1'b1, store_data = ecc_ram_tdp_file.mem[addr] )
        ##0 (1'b1, store_addr = addr)
        |=>
        dout[idx] == $past(dout[idx])  &&
        (ecc_ram_tdp_file.mem[store_addr][idx]) == store_data[idx];
    endproperty

    no_enable_a_a: assert property(disable iff(!rst_n) no_enable_p(ena,douta,addra,idx_sym_nen_a));
    no_enable_b_a: assert property(disable iff(!rst_n) no_enable_p(enb,doutb,addrb,idx_sym_nen_b));


    property no_enable_ab_p;
    logic [DATA_WIDTH-1:0] store_datab,store_dataa;
    logic [ADDR_WIDTH-1 : 0] store_addrb,store_addra;
        !ena &&
        !enb
        ##0 (1'b1, store_dataa = ecc_ram_tdp_file.mem[addra] )
        ##0 (1'b1, store_addra = addra)
        ##0 (1'b1, store_datab = ecc_ram_tdp_file.mem[addrb] )
        ##0 (1'b1, store_addrb = addrb)
        |=>
        douta[idx_sym_nen_ab] == $past(douta[idx_sym_nen_ab])  &&
        (ecc_ram_tdp_file.mem[store_addra][idx_sym_nen_ab]) == store_dataa[idx_sym_nen_ab] &&
        doutb[idx_sym_nen_ab] == $past(doutb[idx_sym_nen_ab]) &&
        (ecc_ram_tdp_file.mem[store_addrb][idx_sym_nen_ab]) == store_datab[idx_sym_nen_ab];
    endproperty

    no_enable_ab_a: assert property(disable iff(!rst_n) no_enable_ab_p);
 
endmodule



bind  ecc_ram_tdp_file fv_ecc_ram_tdp_file #(
        .ADDR_WIDTH(ADDR_WIDTH),
        .DATA_WIDTH(DATA_WIDTH)
        )
        fv_ecc_ram_tdp_file_inst(
        .clk(clk),
        .rst_n(reset_n && !zeroize),
        .ena(ena),
        .wea(wea),
        .addra(addra),
        .dina(dina),
        .douta(douta),
        .enb(enb),
        .web(web),
        .addrb(addrb),
        .dinb(dinb),
        .doutb(doutb)
    );