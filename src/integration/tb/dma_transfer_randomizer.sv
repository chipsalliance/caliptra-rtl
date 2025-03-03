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

class dma_transfer_randomizer #(parameter MAX_SIZE_TO_CHECK = 65536);

  // =============================================
  // Class properties
  // =============================================
  rand dma_transfer_type_e  dma_xfer_type;  // Randomized transfer type
       int unsigned         max_checked_xfer_size = 0;  // From the TB, based on space in DCCM
  rand int unsigned         xfer_size;      // Randomized transfer size in dwords
  rand int unsigned         payload_data[]; // Randomized payload data array
  rand int unsigned         src_offset;
  rand int unsigned         dst_offset;
  rand bit                  src_is_fifo;
  rand bit                  dst_is_fifo;
  rand bit                  use_rd_fixed;
  rand bit                  use_wr_fixed;
  rand bit                  inject_rand_delays;
  rand bit                  inject_rst;
  rand bit                  test_block_size; // Requires accessing the axi_fifo with recovery_data_avail emulation

  // =============================================
  // Constraints
  // =============================================
  // sizes
  constraint transfer_size_c {
      xfer_size dist {
          [1:15] :/ 500,
          [16:255] :/ 1000,
          [256:1023] :/ 500,
          [1024:8191] :/ 200,
          [8192:16383] :/ 100,
          [16384:65535] :/ 20,
          [65536:262144] :/ 5
      };
      (xfer_size <= max_checked_xfer_size) || (xfer_size >= MAX_SIZE_TO_CHECK);
      solve dma_xfer_type before xfer_size;
  }
  constraint payload_data_size_c {
      if (xfer_size >= MAX_SIZE_TO_CHECK)
          payload_data.size == 1; // Actual payload will be generated by FIFO auto-mode in the system
      else
          payload_data.size == xfer_size;
      solve xfer_size before payload_data.size;
  }
  
  // access properties
  constraint blk_size_c {
      test_block_size dist { 0 := 2, 1 := 1 };
      test_block_size -> src_is_fifo;
  };
  constraint fifo_access_c {
      !(src_is_fifo && dst_is_fifo);
      src_is_fifo -> use_rd_fixed;
      dst_is_fifo -> use_wr_fixed;
      solve test_block_size before src_is_fifo;
  };
  constraint fixed_access_c {
      use_rd_fixed dist { 0 := 1, 1 := 1 };
      use_wr_fixed dist { 0 := 1, 1 := 1 };
      solve src_is_fifo before use_rd_fixed;
      solve dst_is_fifo before use_wr_fixed;
  };

  // addresses
  constraint src_addr_c {
       src_is_fifo ->  src_offset inside {[0:AXI_FIFO_SIZE_BYTES-1]};
      !src_is_fifo ->  src_offset inside {[0:AXI_SRAM_SIZE_BYTES-1]};
      !src_is_fifo -> (src_offset + xfer_size*4) <= AXI_SRAM_SIZE_BYTES;
      src_offset[1:0] == 2'b0;
  };
  constraint dst_addr_c {
       dst_is_fifo ->  dst_offset inside {[0:AXI_FIFO_SIZE_BYTES-1]};
      !dst_is_fifo ->  dst_offset inside {[0:AXI_SRAM_SIZE_BYTES-1]};
      !dst_is_fifo -> (dst_offset + xfer_size*4) <= AXI_SRAM_SIZE_BYTES;
      dst_offset[1:0] == 2'b0;
  };

  // TB stimulus injection
  constraint inject_c {
      inject_rand_delays dist { 0 := 5, 1 := 1 };
      inject_rst dist { 0 := 25, 1 := 1 };
  };

  // =============================================
  // Constructor
  // =============================================
  function new(int max_checked_size);
      this.max_checked_xfer_size = max_checked_size;
  endfunction

  // =============================================
  // Pre-randomize function
  // =============================================
  function void pre_randomize();
    // Onus is on TB not to request a transfer with size == 0!
    if (max_checked_xfer_size == 0)
        $fatal("max_checked_xfer_size must be provided and non-zero!");
  endfunction

  // =============================================
  // Post-randomize function
  // =============================================
  function void post_randomize();
    //Verify post_randomize() is being called
    $display("post_randomize called with xfer_size = %0d", xfer_size);

    // Report payload_data array size
    if (xfer_size <= MAX_SIZE_TO_CHECK) begin
        $display("payload_data initialized with size: %d", payload_data.size());
    end
    else begin
        $display("payload_data will not be initialized or checked for very large transfer test. Size: %d", payload_data.size());
    end

    // Ensure array is porperly sized
    if ((xfer_size <= MAX_SIZE_TO_CHECK) && (payload_data.size() != xfer_size)) begin
        $error("For xfer_size %d, payload_data.size %d is incorrect!", xfer_size, payload_data.size());
    end

    foreach (payload_data[i]) if (payload_data[i] == 0) $warning("payload_data[%d] is 0!", i);
//    // Populate payload_data array with non-zero random values
//    foreach (payload_data[i]) begin
//      do begin
//        payload_data[i] = $urandom();
//      end while (payload_data[i] == 0); // Ensure non-zero values
//      $display("  Setting payload_data[%0d] = 0x%0x", i, payload_data[i]);
//    end
  endfunction

  // =============================================
  // Display method
  // =============================================
  function void display(int index = -1);
    if (index != -1) begin
      $display("Transfer %0d:", index);
    end
    $display("  Type: %s", dma_xfer_type.name());
    $display("  Size: %0d dwords", xfer_size);
    $display("  Payload Data:");
    foreach (payload_data[i]) begin
      $display("    %0d: %h", i, payload_data[i]);
    end
    $display("  src_is_fifo       : 0x%x", src_is_fifo       );
    $display("  dst_is_fifo       : 0x%x", dst_is_fifo       );
    $display("  src_offset        : 0x%x", src_offset        );
    $display("  dst_offset        : 0x%x", dst_offset        );
    $display("  use_rd_fixed      : 0x%x", use_rd_fixed      );
    $display("  use_wr_fixed      : 0x%x", use_wr_fixed      );
    $display("  inject_rand_delays: 0x%x", inject_rand_delays);
    $display("  inject_rst        : 0x%x", inject_rst        );
    $display("  test_block_size   : 0x%x", test_block_size   );
  endfunction

endclass
