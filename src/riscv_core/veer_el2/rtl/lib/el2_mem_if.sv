//********************************************************************************
// SPDX-License-Identifier: Apache-2.0
// Copyright 2020 Western Digital Corporation or its affiliates.
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
//********************************************************************************


// *************************************************
//
// Filename: el2_mem_if.sv
// Contributing company: MICROSOFT
// Creation Date: 2022/9/16
//
// Description:
//   This file is added to the VeeR-EL2 code-base after
//   the initial download, specifically for the Caliptra
//   security module project.
//   This file is used to bring synthesizable memory
//   components to the top-level of an SoC project so that
//   they may be manipulated according to the target fabrication
//   process. Exported memory blocks include:
//    - I-Cache
//    - ICCM
//    - DCCM
//
// LICENSE NOTES:
//
// *************************************************

import el2_pkg::*;
interface el2_mem_if #(
    `include "el2_param.vh"
) (
);


//////////////////////////////////////////
// Clock
logic clk;


//////////////////////////////////////////
// ICCM
logic [pt.ICCM_NUM_BANKS-1:0]                                        iccm_clken;
logic [pt.ICCM_NUM_BANKS-1:0]                                        iccm_wren_bank;
logic [pt.ICCM_NUM_BANKS-1:0] [pt.ICCM_BITS-1:pt.ICCM_BANK_INDEX_LO] iccm_addr_bank;

logic [pt.ICCM_NUM_BANKS-1:0] [38:0]                                 iccm_bank_wr_data;
logic [pt.ICCM_NUM_BANKS-1:0] [38:0]                                 iccm_bank_dout;


//////////////////////////////////////////
// DCCM
logic [pt.DCCM_NUM_BANKS-1:0]                                        dccm_clken;
logic [pt.DCCM_NUM_BANKS-1:0]                                        dccm_wren_bank;
logic [pt.DCCM_NUM_BANKS-1:0] [pt.DCCM_BITS-1:(pt.DCCM_BANK_BITS+2)] dccm_addr_bank;
logic [pt.DCCM_NUM_BANKS-1:0][pt.DCCM_FDATA_WIDTH-1:0]               dccm_wr_data_bank;
logic [pt.DCCM_NUM_BANKS-1:0] [pt.DCCM_FDATA_WIDTH-1:0]              dccm_bank_dout;


//////////////////////////////////////////
// MODPORTS
modport veer_iccm (
    input clk,
    // ICCM
    output iccm_clken, iccm_wren_bank, iccm_addr_bank, iccm_bank_wr_data,
    input  iccm_bank_dout
);

modport veer_dccm (
    input clk,
    // DCCM
    output dccm_clken, dccm_wren_bank, dccm_addr_bank, dccm_wr_data_bank,
    input  dccm_bank_dout
);

modport top (
    input clk,
    // ICCM
    input  iccm_clken, iccm_wren_bank, iccm_addr_bank, iccm_bank_wr_data,
    output iccm_bank_dout,
    // DCCM
    input  dccm_clken, dccm_wren_bank, dccm_addr_bank, dccm_wr_data_bank,
    output dccm_bank_dout
);

endinterface
