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
//======================================================================
//
// ecc_dsa_uop_pkg.sv
// --------
// ECC instructin for the digital signature algorithm (DSA).
//
//
//======================================================================

`ifndef ECC_DSA_UOP_PKG
`define ECC_DSA_UOP_PKG

package ecc_dsa_uop_pkg;


localparam integer DSA_UOP_ADDR_WIDTH       = 9;
localparam integer DSA_OPR_ADDR_WIDTH       = 6;

localparam DSA_PROG_ADDR_W                  = 7; //$clog2(DSA_VER_E+2);
localparam DSA_INSTRUCTION_LENGTH           = DSA_UOP_ADDR_WIDTH + (2*DSA_OPR_ADDR_WIDTH);    // opcode + 2 * operand

typedef enum logic[3 : 0]
{
    no_cmd          = 4'b0000,
    keygen_cmd      = 4'b0001,
    sign_cmd        = 4'b0010,
    verify0_cmd     = 4'b0100,
    verify1_cmd     = 4'b0101,
    verify2_cmd     = 4'b0110,
    pk_chk_cmd      = 4'b0111,
    shared_key_cmd  = 4'b1000
} cmd_t;

typedef struct packed
{
    logic       op_sel;
    logic       wr_en;
    logic       rd_en;
    cmd_t       pm_cmd;
    logic       hmac_drbg_en;
    logic       sca_en;
} opcode_t;

typedef struct packed
{
    opcode_t                            opcode;
    logic [DSA_OPR_ADDR_WIDTH-1 : 0]    reg_id;
    logic [DSA_OPR_ADDR_WIDTH-1 : 0]    mem_addr;
} instr_struct_t;

// DSA INSTRUCTIONS LIST
localparam opcode_t DSA_UOP_NOP           = '{op_sel:1'b0,   wr_en:1'b0, rd_en:1'b0, pm_cmd:no_cmd,      hmac_drbg_en:1'b0, sca_en:1'b0}; // = 8'b0000_0000;
localparam opcode_t DSA_UOP_WR_CORE       = '{op_sel:1'b0,   wr_en:1'b1, rd_en:1'b0, pm_cmd:no_cmd,      hmac_drbg_en:1'b0, sca_en:1'b0}; // = 8'b0000_0010;
localparam opcode_t DSA_UOP_WR_SCALAR     = '{op_sel:1'b1,   wr_en:1'b1, rd_en:1'b0, pm_cmd:no_cmd,      hmac_drbg_en:1'b0, sca_en:1'b0}; // = 8'b0000_0011;
localparam opcode_t DSA_UOP_RD_CORE       = '{op_sel:1'b0,   wr_en:1'b0, rd_en:1'b1, pm_cmd:no_cmd,      hmac_drbg_en:1'b0, sca_en:1'b0}; // = 8'b0000_0100;
localparam opcode_t DSA_UOP_KEYGEN        = '{op_sel:1'b0,   wr_en:1'b0, rd_en:1'b0, pm_cmd:keygen_cmd,  hmac_drbg_en:1'b0, sca_en:1'b0}; // = 8'b0000_1000;
localparam opcode_t DSA_UOP_SIGN          = '{op_sel:1'b0,   wr_en:1'b0, rd_en:1'b0, pm_cmd:sign_cmd,    hmac_drbg_en:1'b0, sca_en:1'b0}; // = 8'b0001_0000;
localparam opcode_t DSA_UOP_VERIFY0       = '{op_sel:1'b0,   wr_en:1'b0, rd_en:1'b0, pm_cmd:verify0_cmd, hmac_drbg_en:1'b0, sca_en:1'b0}; // = 8'b0010_0000;
localparam opcode_t DSA_UOP_VERIFY1       = '{op_sel:1'b0,   wr_en:1'b0, rd_en:1'b0, pm_cmd:verify1_cmd, hmac_drbg_en:1'b0, sca_en:1'b0}; // = 8'b0010_1000;
localparam opcode_t DSA_UOP_VERIFY2       = '{op_sel:1'b0,   wr_en:1'b0, rd_en:1'b0, pm_cmd:verify2_cmd, hmac_drbg_en:1'b0, sca_en:1'b0}; // = 8'b0011_0000;
localparam opcode_t DSA_UOP_PK_CHK        = '{op_sel:1'b0,   wr_en:1'b0, rd_en:1'b0, pm_cmd:pk_chk_cmd,  hmac_drbg_en:1'b0, sca_en:1'b0}; // = 8'b0011_1000;
localparam opcode_t DSA_UOP_HMAC_DRBG     = '{op_sel:1'b0,   wr_en:1'b0, rd_en:1'b0, pm_cmd:no_cmd,      hmac_drbg_en:1'b1, sca_en:1'b0}; // = 8'b0100_0000;
localparam opcode_t DSA_UOP_SCALAR_SCA    = '{op_sel:1'b0,   wr_en:1'b0, rd_en:1'b0, pm_cmd:no_cmd,      hmac_drbg_en:1'b0, sca_en:1'b1}; // = 8'b1000_0000;
localparam opcode_t DH_UOP_SHAREDKEY      = '{op_sel:1'b0,   wr_en:1'b0, rd_en:1'b0, pm_cmd:shared_key_cmd,  hmac_drbg_en:1'b0, sca_en:1'b0}; // = 8'b0000_1000;

// DSA REGISTERS ID listing
localparam [DSA_OPR_ADDR_WIDTH-1 : 0] NOP_ID                   = 6'd0;
localparam [DSA_OPR_ADDR_WIDTH-1 : 0] CONST_ZERO_ID            = 6'd1;
localparam [DSA_OPR_ADDR_WIDTH-1 : 0] CONST_ONE_ID             = 6'd2;
localparam [DSA_OPR_ADDR_WIDTH-1 : 0] CONST_E_a_MONT_ID        = 6'd3;
localparam [DSA_OPR_ADDR_WIDTH-1 : 0] CONST_E_3b_MONT_ID       = 6'd4;
localparam [DSA_OPR_ADDR_WIDTH-1 : 0] CONST_ONE_p_MONT_ID      = 6'd5;
localparam [DSA_OPR_ADDR_WIDTH-1 : 0] CONST_R2_p_MONT_ID       = 6'd6;
localparam [DSA_OPR_ADDR_WIDTH-1 : 0] CONST_G_X_MONT_ID        = 6'd7;
localparam [DSA_OPR_ADDR_WIDTH-1 : 0] CONST_G_Y_MONT_ID        = 6'd8;
localparam [DSA_OPR_ADDR_WIDTH-1 : 0] CONST_R2_q_MONT_ID       = 6'd9;
localparam [DSA_OPR_ADDR_WIDTH-1 : 0] CONST_ONE_q_MONT_ID      = 6'd10;
localparam [DSA_OPR_ADDR_WIDTH-1 : 0] CONST_E_b_MONT_ID        = 6'd11;

localparam [DSA_OPR_ADDR_WIDTH-1 : 0] SEED_ID                  = 6'd16;
localparam [DSA_OPR_ADDR_WIDTH-1 : 0] MSG_ID                   = 6'd17;
localparam [DSA_OPR_ADDR_WIDTH-1 : 0] PRIVKEY_ID               = 6'd18;
localparam [DSA_OPR_ADDR_WIDTH-1 : 0] PUBKEYX_ID               = 6'd19;
localparam [DSA_OPR_ADDR_WIDTH-1 : 0] PUBKEYY_ID               = 6'd20;
localparam [DSA_OPR_ADDR_WIDTH-1 : 0] R_ID                     = 6'd21;
localparam [DSA_OPR_ADDR_WIDTH-1 : 0] S_ID                     = 6'd22;
localparam [DSA_OPR_ADDR_WIDTH-1 : 0] SCALAR_ID                = 6'd23;
localparam [DSA_OPR_ADDR_WIDTH-1 : 0] SCALAR_G_ID              = 6'd24;
localparam [DSA_OPR_ADDR_WIDTH-1 : 0] SCALAR_PK_ID             = 6'd25;
localparam [DSA_OPR_ADDR_WIDTH-1 : 0] VERIFY_R_ID              = 6'd26;
localparam [DSA_OPR_ADDR_WIDTH-1 : 0] LAMBDA_ID                = 6'd27;
localparam [DSA_OPR_ADDR_WIDTH-1 : 0] MASKING_ID               = 6'd28;
localparam [DSA_OPR_ADDR_WIDTH-1 : 0] PK_VALID_ID              = 6'd29;
localparam [DSA_OPR_ADDR_WIDTH-1 : 0] DH_SHAREDKEY_ID          = 6'd30;


// DSA Subroutine listing
localparam [DSA_PROG_ADDR_W-1 : 0] ECC_RESET                    = 7'd0;
localparam [DSA_PROG_ADDR_W-1 : 0] ECC_NOP                      = 7'd12;  
localparam [DSA_PROG_ADDR_W-1 : 0] DSA_KG_S                     = ECC_NOP + 2; 
localparam [DSA_PROG_ADDR_W-1 : 0] DSA_KG_E                     = DSA_KG_S + 12; 
localparam [DSA_PROG_ADDR_W-1 : 0] DSA_SGN_S                    = DSA_KG_E + 2; 
localparam [DSA_PROG_ADDR_W-1 : 0] DSA_SGN_E                    = DSA_SGN_S + 14; 
localparam [DSA_PROG_ADDR_W-1 : 0] DSA_VER_S                    = DSA_SGN_E + 2; 
localparam [DSA_PROG_ADDR_W-1 : 0] DSA_VER_E                    = DSA_VER_S + 23;
localparam [DSA_PROG_ADDR_W-1 : 0] DH_SHARED_S                  = DSA_VER_E + 2; 
localparam [DSA_PROG_ADDR_W-1 : 0] DH_SHARED_E                  = DH_SHARED_S + 17; 


endpackage

`endif
