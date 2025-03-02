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

module dma_testcase_generator(
  output logic dma_gen_done
);//dma_if dma_xfer_if);
  `include "dma_transfer_randomizer.sv"

  // Dynamic array to store test cases
  dma_transfer_randomizer dma_xfers[];

  //----------------------------------------------------------------
  // main
  //
  // The main test functionality.
  //----------------------------------------------------------------        

  initial begin : main
    int num_iterations;
    int end_addr = `RV_DCCM_EADR;  // Base address for DCCM
    int addr;
    int tc_start_addr;
    int dccm_addr;
    bit [38:0] data;  // Assuming a 39-bit data format

    if (!$value$plusargs("NUM_ITERATIONS=%d", num_iterations)) begin 
      num_iterations = 100; // Default
    end
    
    // Test cases cases are stored in DCCM starting from the end address and filling backwards
    // 0x5003_FFFC: num_iterations
    // 0x5003_FFF8: tc #1
    // 0x5003_FFF4: tc #2
    // ...
    slam_dccm_ram(end_addr - 3, num_iterations);

    tc_start_addr = end_addr - 7; 
    dccm_addr = tc_start_addr;

    // Resize the dynamic array
    dma_xfers = new[num_iterations];

    $display("    ======================================================");
    $display("    Running %d iterations of rand_test_dma", num_iterations);
    $display("    ======================================================");
        
    // Generate and store test cases
    for (int i = 0; i < num_iterations; i++) begin: gen_dma_tc
      dma_transfer_randomizer dma_gen = new();
      if (!dma_gen.randomize()) begin
        $error("Randomization failed for dma_transfer_generator %d", i);
      end
      else begin
        dma_xfers[i] = dma_gen;
        dccm_addr = tc_start_addr - (i * 8);  // 2dwords are used per test case
        // Convert dma_xfers fields to the expected format if necessary
        //data = {dma_xfers[i].dma_xfer_type, dma_xfers[i].xfer_size}; 
        slam_dccm_ram(dccm_addr, dma_xfers[i].dma_xfer_type);  
        dccm_addr = dccm_addr - 4;
        slam_dccm_ram(dccm_addr, dma_xfers[i].xfer_size);

        //dma_xfers.push_back(dma_gen);
        dma_gen.display(i);
        $display("-------------------------------");
      end
    end

    dma_gen_done = 1;
  end

  // Task to provide the test cases
  function void get_dma_xfers(dma_transfer_randomizer t[]);
    t = dma_xfers;
  endfunction
endmodule