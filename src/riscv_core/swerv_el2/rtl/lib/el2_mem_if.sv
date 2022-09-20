// *************************************************
//
// Filename: el2_mem_if.sv
// Contributing company: MICROSOFT
// Creation Date: 2022/9/16
//
// Description:
//   This file is added to the SweRV-EL2 code-base after
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
    input rst_b
);


//////////////////////////////////////////
// CLK
logic clk;


//////////////////////////////////////////
// IC (Cache) Data
logic [pt.ICACHE_BANKS_WAY-1:0][pt.ICACHE_NUM_WAYS-1:0]                                 ic_b_sb_wren;    //bank x ways
logic [pt.ICACHE_BANKS_WAY-1:0][pt.ICACHE_NUM_WAYS-1:0]                                 ic_bank_way_clken; // Different based on WAYPACK
logic [pt.ICACHE_BANKS_WAY-1:0][70:0]                                                   ic_sb_wr_data;
logic [pt.ICACHE_BANKS_WAY-1:0][pt.ICACHE_INDEX_HI : pt.ICACHE_DATA_INDEX_LO]           ic_rw_addr_bank_q;
logic [pt.ICACHE_BANKS_WAY-1:0] [((68+(pt.ICACHE_ECC ? 3 : 0))*pt.ICACHE_NUM_WAYS)-1:0] ic_b_sb_bit_en_vec, wb_dout_pre; // data and its bit enables WAYPACK = 1


//////////////////////////////////////////
// IC (Cache) Tag
logic [pt.ICACHE_NUM_WAYS-1:0]                     ic_tag_wren_q;
logic [pt.ICACHE_NUM_WAYS-1:0]                     ic_tag_clken_final; // Single bit for WAYPACK = 1
logic [25:0]                                       ic_tag_wr_data; // Replicated across all WAYS
logic [pt.ICACHE_INDEX_HI: pt.ICACHE_TAG_INDEX_LO] ic_rw_addr_q;
logic [(26*pt.ICACHE_NUM_WAYS)-1 :0]               ic_tag_wren_biten_vec; // Only exists for WAYPACK = 1
logic [(26*pt.ICACHE_NUM_WAYS)-1 :0]               ic_tag_data_raw_pre; // Differs by WAYPACK, use packed array for interface


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
logic [pt.DCCM_NUM_BANKS-1:0]                                        wren_bank;
logic [pt.DCCM_NUM_BANKS-1:0] [pt.DCCM_BITS-1:(pt.DCCM_BANK_BITS+2)] addr_bank;
logic [pt.DCCM_NUM_BANKS-1:0][pt.DCCM_FDATA_WIDTH-1:0]               wr_data_bank;
logic [pt.DCCM_NUM_BANKS-1:0] [pt.DCCM_FDATA_WIDTH-1:0]              dccm_bank_dout;


//////////////////////////////////////////
// MODPORTS
modport swerv_ic_data (
    input clk, rst_b,
    // IC (Cache) Data
    output ic_b_sb_wren, ic_bank_way_clken, ic_sb_wr_data, ic_rw_addr_bank_q, ic_b_sb_bit_en_vec,
    input  wb_dout_pre
);

modport swerv_ic_tag (
    input clk, rst_b,
    // IC (Cache) Tag
    output ic_tag_wren_q, ic_tag_clken_final, ic_tag_wr_data, ic_rw_addr_q, ic_tag_wren_biten_vec,
    input  ic_tag_data_raw_pre
);

modport swerv_iccm (
    input clk, rst_b,
    // ICCM
    output iccm_clken, iccm_wren_bank, iccm_addr_bank, iccm_bank_wr_data,
    input  iccm_bank_dout
);

modport swerv_dccm (
    input clk, rst_b,
    // DCCM
    output dccm_clken, wren_bank, addr_bank, wr_data_bank,
    input  dccm_bank_dout
);

modport top (
    input clk, rst_b,
    // IC (Cache) Data
    input  ic_b_sb_wren, ic_bank_way_clken, ic_sb_wr_data, ic_rw_addr_bank_q, ic_b_sb_bit_en_vec,
    output wb_dout_pre,
    // IC (Cache) Tag
    input  ic_tag_wren_q, ic_tag_clken_final, ic_tag_wr_data, ic_rw_addr_q, ic_tag_wren_biten_vec,
    output ic_tag_data_raw_pre,
    // ICCM
    input  iccm_clken, iccm_wren_bank, iccm_addr_bank, iccm_bank_wr_data,
    output iccm_bank_dout,
    // DCCM
    input  dccm_clken, wren_bank, addr_bank, wr_data_bank,
    output dccm_bank_dout
);

endinterface
