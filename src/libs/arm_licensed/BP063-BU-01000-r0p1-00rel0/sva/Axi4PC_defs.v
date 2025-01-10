//  ========================================================================--
//  The confidential and proprietary information contained in this file may
//  only be used by a person authorised under and to the extent permitted
//  by a subsisting licensing agreement from ARM Limited.
//  
//                   (C) COPYRIGHT 2010-2012 ARM Limited.
//                           ALL RIGHTS RESERVED
//  
//  This entire notice must be reproduced on all copies of this file
//  and copies of this file may only be made by a person if such person is
//  permitted to do so under the terms of a subsisting license agreement
//  from ARM Limited.
//  
//  ----------------------------------------------------------------------------
//  Version and Release Control Information:
//  
//  File Revision       : 132008
//
//  Date                :  2012-06-19 11:25:25 +0100 (Tue, 19 Jun 2012)
//  
//  Release Information : BP063-VL-70004-r0p1-00rel0
//  
//  ----------------------------------------------------------------------------
//  Purpose             : Standard AXI4 SVA Protocol Assertions defines
//  ========================================================================--

`ifndef AXI4PC_TYPES
    `define AXI4PC_TYPES
    // ALEN Encoding
    `define AXI4PC_ALEN_1            8'b00000000
    `define AXI4PC_ALEN_2            8'b00000001
    `define AXI4PC_ALEN_3            8'b00000010
    `define AXI4PC_ALEN_4            8'b00000011
    `define AXI4PC_ALEN_5            8'b00000100
    `define AXI4PC_ALEN_6            8'b00000101
    `define AXI4PC_ALEN_7            8'b00000110
    `define AXI4PC_ALEN_8            8'b00000111
    `define AXI4PC_ALEN_9            8'b00001000
    `define AXI4PC_ALEN_10           8'b00001001
    `define AXI4PC_ALEN_11           8'b00001010
    `define AXI4PC_ALEN_12           8'b00001011
    `define AXI4PC_ALEN_13           8'b00001100
    `define AXI4PC_ALEN_14           8'b00001101
    `define AXI4PC_ALEN_15           8'b00001110
    `define AXI4PC_ALEN_16           8'b00001111

    // ASIZE Encoding
    `define AXI4PC_ASIZE_8           3'b000
    `define AXI4PC_ASIZE_16          3'b001
    `define AXI4PC_ASIZE_32          3'b010
    `define AXI4PC_ASIZE_64          3'b011
    `define AXI4PC_ASIZE_128         3'b100
    `define AXI4PC_ASIZE_256         3'b101
    `define AXI4PC_ASIZE_512         3'b110
    `define AXI4PC_ASIZE_1024        3'b111

    // ABURST Encoding
    `define AXI4PC_ABURST_FIXED      2'b00
    `define AXI4PC_ABURST_INCR       2'b01 
    `define AXI4PC_ABURST_WRAP       2'b10 

    // ALOCK Encoding
    `define AXI4PC_ALOCK_EXCL        1'b1

    // RRESP / BRESP Encoding
    `define AXI4PC_RESP_OKAY         2'b00
    `define AXI4PC_RESP_EXOKAY       2'b01
    `define AXI4PC_RESP_SLVERR       2'b10
    `define AXI4PC_RESP_DECERR       2'b11

    //PROTOCOL define the protocol
    `define AXI4PC_AMBA_AXI4         2'b00
    `define AXI4PC_AMBA_ACE          2'b01
    `define AXI4PC_AMBA_ACE_LITE     2'b10
`endif

// --========================= End ===========================================--
