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

class dma_transfer_randomizer;

  // Transfer types enum
  typedef enum {
    AHB2AXI, 
    MBOX2AXI,
    AXI2AXI,
    AXI2MBOX,
    AXI2AHB
  } dma_transfer_type_e;

  // Class properties
  rand dma_transfer_type_e  dma_xfer_type;  // Randomized transfer type
  rand int unsigned         xfer_size;      // Randomized transfer size in dwords

  // Constraints
  constraint transfer_size_c {
    xfer_size inside {[1:2048]};
  }

  // Constructor
  function new();
  endfunction

  // Display method
  function void display(int index = -1);
    if (index != -1) begin
      $display("Transfer %0d:", index);
    end
    $display("  Type: %s", dma_xfer_type.name());
    $display("  Size: %0d dwords", xfer_size);
  endfunction

endclass