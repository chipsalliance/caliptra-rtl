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

package caliptra_top_tb_pkg;

`ifndef VERILATOR
class bitflip_mask_generator #(int MBOX_DATA_AND_ECC_W = 39);

    rand logic [MBOX_DATA_AND_ECC_W-1:0] rand_sram_bitflip_mask;
    logic do_double_bitflip;
    constraint bitflip_c {
        if (do_double_bitflip) {
            $countones(rand_sram_bitflip_mask) == 2;
        } else {
            $countones(rand_sram_bitflip_mask) == 1;
        }
    }

    function new;
        this.rand_sram_bitflip_mask = '0;
        this.do_double_bitflip = 1'b0;
    endfunction

    function logic [MBOX_DATA_AND_ECC_W-1:0] get_mask(bit do_double_bit = 1'b0);
        this.do_double_bitflip = do_double_bit;
        this.randomize();
        return this.rand_sram_bitflip_mask;
    endfunction

endclass
`else
function logic [soc_ifc_pkg::MBOX_DATA_AND_ECC_W-1:0] get_bitflip_mask(bit do_double_bit = 1'b0);
    return 2<<($urandom%(soc_ifc_pkg::MBOX_DATA_AND_ECC_W-2)) | soc_ifc_pkg::MBOX_DATA_AND_ECC_W'(do_double_bit);
endfunction
`endif

endpackage
