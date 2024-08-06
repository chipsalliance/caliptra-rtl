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

// NOTE: Side channel integrity check is not usedby Caliptra. Instead AXI_ID will be used to
//          ensure that responses are sent by OTP to appropriate devices only. 
//          This package contains logic used by side channel integrity checks. 

package otp_ctrl_axi_pkg;

    parameter int H2DCmdIntgWidth   = 7;
    parameter int D2HRspIntgWidth   = 7;
    parameter int DataIntgWidth     = 7;
    parameter int DataWidth         = 32;

    typedef enum logic [2:0] {
        PutFullData     = 3'h 0, 
        PutPartialData  = 3'h 1,
        Get             = 3'h 4
    } tl_a_op_e;

    typedef enum logic [2:0] {
        AccessAck       = 3'h 0,
        AccessAckData   = 3'h 1
    } tl_d_op_e;

    // AXI Sub a_user
    typedef struct packed {
        logic [13:0]                        rsvd;
        caliptra_prim_mubi_pkg::mubi4_t     instr_type;
        logic [H2DCmdIntgWidth-1:0]         cmd_intg;
        logic [DataIntgWidth-1:0]           data_intg;
    } axi_a_user_t;

    parameter axi_a_user_t ACI_A_USER_DEFAULT = '{
        rsvd: '0,
        instr_type: caliptra_prim_mubi_pkg::Mubi4False,
        cmd_intg:   {H2DCmdIntgWidth{1'b1}},
        data_intg:  {DataIntgWidth{1'b1}}
    };

    typedef struct packed {
        caliptra_prim_mubi_pkg::mubi4_t     instr_type;
        logic  [axi_pkg::AW-1:0]            addr;

    }

    typedef struct packed {
        caliptra_prim_mubi_pkg::nubi4_t         instr_type;
        logic   [axi_pks::AW-1:0]               addr;
        tl_a_op_e                               opcode;
        logic   [axi_pkg::DW/8-1:0]             strb,
    } axi_h2d_cmd_intg_t;

    //AXI Sub d_user
    typedef struct packed {
        logic [17:0]                   rsvd;
        logic [D2HRspIntgWidth-1:0]    rsp_intg;
        logic [DataIntgWidth-1:0]      data_intg;
    } axi_d_user_t;

    parameter axi_d_user_t AXI_D_USER_DEFAULT = '{
        rsvd: '0,
        instr_type:     {D2HRspIntgWidth{1'b1}},
        data_intg:      {DataIntgWidth{1'b1}}
    };

    typedef struct packed {
        tl_d_op_e                   opcode;
        logic   [xi_pkg::DW-1:0]    size; //TODO - this need to be fixed based on AXI protocol. Placeholder for now
        logic                       error;
    } axi_d2h_rsp_intg_t;

    // extract cmd opcode based on AXI write and strb signal values
    function automatic translate_axi_cmd_to_opcode(logic axi_write, logic [DataWidth/8-1:0] axi_wstrb);
        tl_a_op_e       tl_equiv_opcode;
        if (!axi_write) begin //AXI Read Cmd
            tl_equiv_opcode = Get;
        end
        else begin // AXI Write Cmd
            if (axi_wstrb == 'F) begin // AXI Full Write
                tl_equiv_opcode = PutFullData;
            end
            else begin  // AXI Partial Write
                tl_equiv_opcode = PutPartialData;
            end
        end
        return tl_equiv_opcode;
    endfunction

    // extract rsp/data opcode based on r/W response channels

    // Check for user unsuported values

    // extract variables used for command checking

    // extract variables used for response checking

    // calculate ecc for command checking

    // calculate ecc for data checking

    // return inverted integrity for command payload

    // reutn inverted integrity for data paylod




endpackage
 