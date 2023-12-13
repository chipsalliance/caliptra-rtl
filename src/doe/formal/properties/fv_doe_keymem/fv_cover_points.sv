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

module fv_keymem_coverpoints_m(
    input logic clk,
    input logic reset_n,
    input logic zeroize
);
    
default clocking default_clk @(posedge clk); endclocking

//Cover zeroize
cover_zeroize: cover property(disable iff(!reset_n) doe_key_mem.zeroize );

//Assert zeroize input and check the status of all registers. All registers/internal memories should be cleared.
cover_zeroize_after_next: cover property(disable iff(!reset_n) doe_key_mem.zeroize && doe_key_mem.ready && doe_key_mem.init_cmd);

//Cover that checks multiple init_cmd can be received
cover_multiple_init: cover property(disable iff(!reset_n || zeroize) 
    doe_key_mem.init_cmd && doe_key_mem.ready ##1 doe_key_mem.init_cmd && doe_key_mem.ready[->1] 
);
    
endmodule 

//Connect this coverpoints module with the DUV
bind doe_key_mem fv_keymem_coverpoints_m fv_keymem_coverpoints(
  .clk(clk),
  .reset_n(reset_n),
  .zeroize(zeroize)
);