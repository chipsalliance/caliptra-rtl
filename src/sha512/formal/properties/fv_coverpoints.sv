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

module fv_coverpoints_m(
    input logic clk,
    input logic reset_n
);
    
    default clocking default_clk @(posedge clk); endclocking

    //Cover zeroize: 
    //Assert zeroize input and check the status of all registers. All registers/internal memories should be cleared.
    cover_zeroize: cover property(disable iff(!reset_n) sha512_core.zeroize );
    cover_zeroize_after_next: cover property(disable iff(!reset_n) sha512_core.zeroize && sha512_core.next_cmd );

    //Cover modes:
    //Cover all 4 different modes for SHA512
    cover_mode_224: cover property(disable iff(!reset_n)  sha512_core.mode == 0 && sha512_core.init_cmd  );
    cover_mode_256: cover property(disable iff(!reset_n)  sha512_core.mode == 1 && sha512_core.init_cmd  );
    cover_mode_384: cover property(disable iff(!reset_n)  sha512_core.mode == 2 && sha512_core.init_cmd  );
    cover_mode_512: cover property(disable iff(!reset_n)  sha512_core.mode == 3 && sha512_core.init_cmd  );


endmodule 
bind sha512_core fv_coverpoints_m fv_coverpoints(
  .clk(clk),
  .reset_n(reset_n)
);