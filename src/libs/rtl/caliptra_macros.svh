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


`ifndef CALIPTRA_MACROS
`define CALIPTRA_MACROS

//Flip-Flop Macros for use in Caliptra project
//These macros should be the only to reference sequentials
//This standardizes their use and avoids bugs

//D Flip-Flop
`define CLP_FF(q, d, clk)             \
    always_ff @(posedge (clk)) begin  \
        q <= d;                       \
    end

//D FLip-Flop with enable
`define CLP_EN_FF(q, d, clk, en)      \
    always_ff @(posedge (clk)) begin  \
        q <= en ? d : q;              \
    end

//D Flip-Flop with asynchronous active-low reset and specified reset value
`define CLP_RSTD_FF(q, d, clk, rst_b, rst_val)         \
    always_ff @(posedge (clk) or negedge(rst_b)) begin \
        if (!rst_b) begin                              \
            q <= rst_val;                              \
        end else begin                                 \
            q <= d;                                    \
        end                                            \
    end

//D Flip-Flop with enable and asynchronous active-low reset and specified reset value
`define CLP_EN_RSTD_FF(q, d, clk, en, rst_b, rst_val)  \
    always_ff @(posedge (clk) or negedge(rst_b)) begin \
        if (!rst_b) begin                              \
            q <= rst_val;                              \
        end else begin                                 \
            q <= en ? d : q;                           \
        end                                            \
    end

//D Flip-Flop with asynchronous active-low reset to 0
`define CLP_RST_FF(q, d, clk, rst_b)  \
    `CLP_RSTD_FF(q, d, clk, rst_b, '0)

//D Flip-Flop with enable and asynchronous active-low reset to 0
`define CLP_EN_RST_FF(q, d, clk, en, rst_b)  \
    `CLP_EN_RSTD_FF(q, d, clk, en, rst_b, '0)

`endif
