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

// -------------------------------------------------------------
// AXI TLUL Write Shim
// -------------------------------------------------------------
// Description:
//   Shim to convert AXI protocol writes into TLUL
//
// Limitations:
//   - When multiple ID tracking is enabled, write responses are returned in the
//     same order they are received, regardless of ID.
//
// -------------------------------------------------------------

module axi2tlul_tb ();
    import axi_pkg::*;
    

    //axi_if.w_sub axi_w_sub_if;
    //axi_if.r_sub axi_r_sub_if;
    
    // TLUL signals that connect AXI2TL gasket with TLUL device
    tlul_pkg::tl_h2d_t tl_i;
    tlul_pkg::tl_d2h_t tl_o;

    // Clock and reset
    logic clk;
    logic rst_n;

    localparam ADDR_WIDTH   = 32;
    localparam DATA_WIDTH   = 32;
    localparam USER_WIDTH   = 32;
    localparam ID_WIDTH     = 1;

    // AXI IF connects AXI mgr to AXI2TL
    axi_if #(
        .AW (ADDR_WIDTH),
        .DW (DATA_WIDTH),
        .IW (ID_WIDTH),
        .UW (USER_WIDTH)
    ) axi_sub_if (
        .clk    (clk),
        .rst_n  (rst_n)
    );

    // Memory model interface signals
    logic [ADDR_WIDTH-1:0]  mem_address;
    logic [DATA_WIDTH-1:0]  mem_rdata;
    logic [DATA_WIDTH-1:0]  mem_wdata;
    logic                   mem_write;

    // 100 MHz clock
    initial begin
        clk = 1'b0;
        forever #5 clk = ~clk;
    end
  
    // Reset
    initial begin
        rst_n = 1'b0;
        #10;
        rst_n = 1'b1;
    end

    // Instantiate DUT
    axi2tlul #(
        .AW     (ADDR_WIDTH),
        .DW     (DATA_WIDTH),
        .UW     (DATA_WIDTH),
        .IW     (ID_WIDTH ),
        .EX_EN  (0 ),
        .C_LAT  (0 )
    ) DUT (
        .clk        (clk),
        .rst_n      (rst_n),

        // AXI INF
        .s_axi_r_if (axi_sub_if.r_sub),
        .s_axi_w_if (axi_sub_if.w_sub),

        //TLUL INF
        .tl_i       (tl_o),
        .tl_o       (tl_i) 
    );

    // Instantiate memory model
    // Memory modele instance
    memory_model #(
        .TL_AW  (ADDR_WIDTH),
        .TL_DW  (DATA_WIDTH),
        .TL_AIW (ID_WIDTH),
        .TL_DIW (ID_WIDTH),
        .TL_AUW (USER_WIDTH),
        .TL_DUW (USER_WIDTH),
        .NUM_WORDS (256)
    ) i_mem_model (
        .clk        (clk),
        .rst_n      (rst_n),
        //TLUL INF
        .tl_i       (tl_i   ),
        .tl_o       (tl_o   )
        /*
        .addr       (mem_address),
        .wr_en      (mem_write),
        .wdata      (mem_wdata),
        .rdata      (mem_rdata)
        */
    );

    logic [ADDR_WIDTH-1:0]  addr;
    logic [DATA_WIDTH-1:0]  read_data;
    axi_pkg::axi_resp_e     read_rsp;
    logic [DATA_WIDTH-1:0]  write_data;
    logic [3:0]             wstrb;
    logic [USER_WIDTH-1:0]  user;
    logic [ID_WIDTH-1:0]    id;   

    initial begin
        axi_sub_if.araddr   = '0;
        axi_sub_if.arburst  = '0;
        axi_sub_if.arsize   = '0;
        axi_sub_if.arlen    = '0;
        axi_sub_if.aruser   = '0;
        axi_sub_if.arid     = '0;
        axi_sub_if.arlock   = 0;
        axi_sub_if.arvalid  = 0;
        axi_sub_if.rready   = 0;

        axi_sub_if.awaddr   = '0;
        axi_sub_if.awid     = '0;
        axi_sub_if.awburst  = '0;
        axi_sub_if.awlen    = '0;
        axi_sub_if.awlock   = 0;
        axi_sub_if.awsize   = '0;
        axi_sub_if.awuser   = '0;
        axi_sub_if.awvalid  = 0;
        axi_sub_if.wdata    = '0;
        axi_sub_if.wvalid   = 0;
        axi_sub_if.wlast    = 0;
        axi_sub_if.wstrb    = '0;
        axi_sub_if.bready   = 0;
    end

    
    // Issue AXI transactions via AXI IF
    initial begin

        repeat (5) @(posedge clk);
        addr = 32'h000000FF;
        user = 32'h00000001;
        id = 1'b1;

        $display("Reading location 0x%x", addr);
        axi_sub_if.axi_read_single(addr, user, id, clk, read_data, read_rsp);
        @(posedge clk);
        readVerify(read_data, 32'h000000FC);

        repeat (5) @(posedge clk);
        addr = 32'h000000C0;
        $display("Reading location 0x%x", addr);
        axi_sub_if.axi_read_single(addr, user, id, clk, read_data, read_rsp);
        @(posedge clk);
        readVerify(read_data, 32'h000000C0);

        repeat (5) @(posedge clk);
        addr = 32'h000000cc;
        write_data = 32'h00C0FFEE;
        $display("Writing location 0x%x. Data = 0x%x", addr, write_data);
        axi_sub_if.axi_write_single(addr, user, id, clk, write_data, read_rsp);
        @(posedge clk);
        axi_sub_if.axi_read_single(addr, user, id, clk, read_data, read_rsp);
        @(posedge clk);
        readVerify(read_data, write_data);

        repeat (5) @(posedge clk);
        addr = 32'h000000A0;
        write_data = 32'h0C001DAD;
        $display("Writing location 0x%x. Data = 0x%x", addr, write_data);
        axi_sub_if.axi_write_single(addr, user, id, clk, write_data, read_rsp);
        @(posedge clk);
        axi_sub_if.axi_read_single(addr, user, id, clk, read_data, read_rsp);
        @(posedge clk);
        readVerify(read_data, write_data);
        #100;

        $finish;
    end

    task readVerify (input logic[DATA_WIDTH-1:0] read_data, 
                     input logic[DATA_WIDTH-1:0] expected_data);
        if ((read_rsp == AXI_RESP_OKAY) && (read_data == expected_data)) begin
            $display($time, " TEST PASS - Read Data = 0x%x, Expected Data = 0x%x", read_data, expected_data);
        end
        else begin
            $display($time, " TEST FAIL - Read data does not match expected data. Read Data = 0x%x, Expected Data = 0x%x", read_data, expected_data);
        end
    endtask

endmodule
