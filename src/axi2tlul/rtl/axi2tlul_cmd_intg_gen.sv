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

module axi2tlul_cmd_intg_gen 
    import axi_pkg::*;
    import caliptra_prim_pkg::*;
    import tlul_pkg::*;
    #(
        parameter bit EnableDataIntgGen = 1'b1
    ) (
        input caliptra_prim_mubi_pkg::mubi4_t  instr_type_i,
        input [AXI_AW-1:0]      addr_i,
        input tl_a_op_e         opcode_i,
        input [TL_DBW-1:0]      mask_i,
        input [TL_DW-1:0]       data_i,

        output [H2DCmdIntgWidth-1:0]    cmd_intg,
        output [DataIntgWidth-1:0]      data_intg
    );

    

    logic [H2DCmdMaxWidth-1:0] unused_cmd_payload;
    tl_h2d_cmd_intg_t cmd;

    assign cmd = {  instr_type_i, 
                    addr_i,
                    opcode_i,
                    mask_i    };
    
    caliptra_prim_secded_inv_64_57_enc u_cmd_gen (
        .data_i(H2DCmdMaxWidth'(cmd)),
        .data_o({cmd_intg, unused_cmd_payload})
    );

    logic [TL_DW-1:0] data_final;

    if (EnableDataIntgGen) begin : gen_data_intg
        assign data_final   = data_i;
    
        logic [DataMaxWidth-1:0] unused_data;
        caliptra_prim_secded_inv_39_32_enc u_data_gen (
          .data_i(DataMaxWidth'(data_final)),
          .data_o({data_intg, unused_data})
        );
      end else begin : gen_passthrough_data_intg
        assign data_final   = data_i;
        assign data_intg    = '0;
      end

      `CALIPTRA_ASSERT_INIT(PayMaxWidthCheck_A, $bits(tl_h2d_cmd_intg_t) <= H2DCmdMaxWidth)
                                   
endmodule : axi2tlul_cmd_intg_gen