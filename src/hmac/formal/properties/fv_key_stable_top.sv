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

module fv_key_stable_top_m
(
    input logic           clk,
    input logic           rst_n
);

    default clocking default_clk @(posedge clk); endclocking

//TODO: hmac top should keep the key stable for signle computation. Check with assertion 
logic [383:0] hmac_key;
logic hmac_init;

assign hmac_key = hmac_ctrl.hmac_inst.core.key;
assign hmac_init = hmac_ctrl.hmac_inst.core.init_cmd;


assert_wip_key_stable: assert property(disable iff(!rst_n)
    hmac_init
    |=>
      ($stable(hmac_key) || hmac_init)
    );


endmodule
  bind hmac_ctrl fv_key_stable_top_m fv_key_stable_top (
        .clk              (clk             ),
        .rst_n            (reset_n         )
    );