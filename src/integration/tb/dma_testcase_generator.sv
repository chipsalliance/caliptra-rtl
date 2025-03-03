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

module dma_testcase_generator (
  input logic preload_dccm_done
  //output logic dma_gen_done
);//dma_if dma_xfer_if);
  import caliptra_top_tb_pkg::*; // provides dma_transfer_randomizer, etc...

  localparam MAX_SIZE_TO_CHECK = 65536;

  // Dynamic array to store test cases
  dma_transfer_randomizer#(MAX_SIZE_TO_CHECK) dma_xfers[];

  //----------------------------------------------------------------
  // main
  //
  // The main test functionality.
  //----------------------------------------------------------------        

  initial begin : main
    int num_iterations;
    int end_addr = `RV_DCCM_EADR;  // Base address for DCCM
    int tc_start_addr;
    int dccm_addr;
    int total_testcase_bytes_to_check = 32'h18000; // FIXME initialize with the value indicating how many DCCM bytes can be used for TC stuffing
    struct packed {
      bit                  src_is_fifo;
      bit                  dst_is_fifo;
      bit                  use_rd_fixed;
      bit                  use_wr_fixed;
      bit                  inject_rand_delays;
      bit                  inject_rst;
      bit                  test_block_size; // Requires accessing the axi_fifo with recovery_data_avail emulation
      dma_transfer_type_e  dma_xfer_type;  // Randomized transfer type
    } type_dword;
    logic [31:0] data;  // Assuming a 39-bit data format

    if (!$value$plusargs("NUM_ITERATIONS=%d", num_iterations)) begin 
      num_iterations = 100; // Default
    end
    
    // Wait for caliptra_top_tb to complete preload_dccm before running slam_dccm_ram
    wait(preload_dccm_done);

    // Test cases cases are stored in DCCM starting from the end address and filling backwards
    // 0x5003_FFFC: num_iterations
    // 0x5003_FFF8: tc #1 xfer_type
    // 0x5003_FFF4: tc #1 xfer_size
    // 0x5003_FFF0: tc #1 payload data #0
    // ...
    // 0x5003_xxxx: tc #1 payload data #(xfer_size-1)
    // 0x5000_xxxx - 4: tc #2 xfer_type
    // ...
    slam_dccm_ram(end_addr - 3, {riscv_ecc32(num_iterations), num_iterations});
    total_testcase_bytes_to_check = total_testcase_bytes_to_check - 4;
    total_testcase_bytes_to_check = total_testcase_bytes_to_check - 16;

    tc_start_addr = end_addr - 7; 
    dccm_addr = tc_start_addr;

    // Resize the dynamic array
    dma_xfers = new[num_iterations];

    $display("    ======================================================");
    $display("    Running %d iterations of rand_test_dma", num_iterations);
    $display("    ======================================================");
        
    // Generate and store test cases
    for (int i = 0; i < num_iterations; i++) begin: gen_dma_tc
      dma_transfer_randomizer#(MAX_SIZE_TO_CHECK) dma_gen = new(total_testcase_bytes_to_check);
      if (!dma_gen.randomize()) begin
        $error("Randomization failed for dma_transfer_generator %d", i);
      end
      else begin
        dma_xfers[i] = dma_gen;

        //dccm_addr = tc_start_addr - (i * ((2 + dma_gen.xfer_size) * 4));  // 1dw = xfer_type, 1dw = xfer_size, xfer_size dws = payload data
        
        // Write DMA transfer_type tp DCCM
        type_dword.src_is_fifo         = dma_gen.src_is_fifo       ;
        type_dword.dst_is_fifo         = dma_gen.dst_is_fifo       ;
        type_dword.use_rd_fixed        = dma_gen.use_rd_fixed      ;
        type_dword.use_wr_fixed        = dma_gen.use_wr_fixed      ;
        type_dword.inject_rand_delays  = dma_gen.inject_rand_delays;
        type_dword.inject_rst          = dma_gen.inject_rst        ;
        type_dword.test_block_size     = dma_gen.test_block_size   ;
        type_dword.dma_xfer_type       = dma_gen.dma_xfer_type     ;
        data = 32'(type_dword);
        $display("dccm_addr = 0x%0x, xfer_type = 0x%0x", dccm_addr, data);
        slam_dccm_ram(dccm_addr, data == 0 ? 0 : {riscv_ecc32(data),data});

        // Write DMA transfer size to DCCM
        dccm_addr = dccm_addr - 4;
        data = dma_gen.xfer_size;
        $display("dccm_addr = 0x%0x, xfer_size = 0x%0x", dccm_addr, data);
        slam_dccm_ram(dccm_addr, data == 0 ? 0 : {riscv_ecc32(data),data});

        // Write DMA src offset to DCCM
        dccm_addr = dccm_addr - 4;
        data = dma_gen.src_offset;
        $display("dccm_addr = 0x%0x, src_offset = 0x%0x", dccm_addr, data);
        slam_dccm_ram(dccm_addr, data == 0 ? 0 : {riscv_ecc32(data),data});

        // Write DMA dst offset to DCCM
        dccm_addr = dccm_addr - 4;
        data = dma_gen.dst_offset;
        $display("dccm_addr = 0x%0x, dst_offset = 0x%0x", dccm_addr, data);
        slam_dccm_ram(dccm_addr, data == 0 ? 0 : {riscv_ecc32(data),data});

        // Write payload data to DCCM
        for (int j = 0; j < dma_gen.xfer_size; j++) begin 
          dccm_addr = dccm_addr - 4;
          data = dma_gen.payload_data[j];
          $display("dccm_addr = 0x%0x, data = 0x%0x", dccm_addr, data);
          slam_dccm_ram(dccm_addr, data == 0 ? 0 : {riscv_ecc32(data), data});
        end
        dma_gen.display(i);
        $display("-------------------------------");

        // After writing the entire transfer, move to a new address for the next transfer
        // Move to the next 4-byte boundary for the next transfer
        dccm_addr = dccm_addr - 4;
      end
      total_testcase_bytes_to_check = total_testcase_bytes_to_check - ((MAX_SIZE_TO_CHECK > dma_gen.xfer_size) ? dma_gen.xfer_size + 16 : 16);
      if (total_testcase_bytes_to_check == 0) begin
          num_iterations = i+1;
          break;
      end
    end

    $display("Writing random generated test cases to DCCM completed.");
    slam_dccm_ram(end_addr - 3, {riscv_ecc32(num_iterations), num_iterations}); // Rewrite in case we had to truncate the num_iterations
    $display("  * Final iteration count of rand_test_dma: %d", num_iterations);
    //dma_gen_done = 1;
  end

  // Task to provide the test cases
  function void get_dma_xfers(dma_transfer_randomizer#(MAX_SIZE_TO_CHECK) t[]);
    t = dma_xfers;
  endfunction
endmodule
