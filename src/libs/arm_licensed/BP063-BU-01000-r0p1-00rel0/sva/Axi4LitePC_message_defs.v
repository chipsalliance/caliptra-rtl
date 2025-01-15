//=============================================================================
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
//-----------------------------------------------------------------------------
//  Version and Release Control Information:
//  
//  File Revision       : 132975
//  
//  Date                :  2012-07-03 13:38:08 +0100 (Tue, 03 Jul 2012)
//
//  Release Information : BP063-VL-70004-r0p1-00rel0
//  
//-----------------------------------------------------------------------------
//  Purpose             : AXI4-Lite SV Protocol Assertions message `defines
//=============================================================================


`include "Axi4PC_message_defs.v"
`ifndef AXI4LITEPC_MESSAGES
        `define AXI4LITEPC_MESSAGES
        `define ERRS_AXI4LITE_BRESP_EXOKAY   "AXI4LITE_ERRS_BRESP_EXOKAY: A slave must not give an EXOKAY response on an Axi4Lite interface. Spec: section B1.1.1."
        `define ERRS_AXI4LITE_RRESP_EXOKAY   "AXI4LITE_ERRS_RRESP_EXOKAY: A slave must not give an EXOKAY response on an Axi4Lite interface. Spec: section B1.1.1."
        `define AUX_AXI4LITE_DATA_WIDTH      "AXI4LITE_AUX_DATA_WIDTH: Parameter DATA_WIDTH must be either 32 or 64."
`endif

// --========================= End ===========================================--
