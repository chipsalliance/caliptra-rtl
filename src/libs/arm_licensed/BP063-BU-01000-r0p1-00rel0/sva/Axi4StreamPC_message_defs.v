//============================================================================
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
//------------------------------------------------------------------------------
//  Version and Release Control Information:
//  
//  File Revision       : 133318
//  
//  Date                :  2012-07-09 10:49:37 +0100 (Mon, 09 Jul 2012)
//  
//  Release Information : BP063-VL-70004-r0p1-00rel0
//  
//------------------------------------------------------------------------------
//  Purpose             : AXI4-Stream SVA Protocol Assertions message `defines
//==============================================================================


`ifndef AXI4STREAMPC_MESSAGES
        `define AXI4STREAMPC_MESSAGES
        `define ERRM_TVALID_RESET         "AXI4STREAM_ERRM_TVALID_RESET. TVALID must be low for the first clock edge that ARESETn goes high. Spec: section 2.7.2, and figure 2-4 on page 2-11."
        `define ERRM_TID_STABLE           "AXI4STREAM_ERRM_TID_STABLE. TID must remain stable when TVALID is asserted and TREADY low. Spec: section 2.2.1, and figure 2-1, on page 2-3."
        `define ERRM_TDEST_STABLE         "AXI4STREAM_ERRM_TDEST_STABLE. TDEST must remain stable when TVALID is asserted and TREADY low. Spec: section 2.2.1, and figure 2-1, on page 2-3."
        `define ERRM_TKEEP_STABLE         "AXI4STREAM_ERRM_TKEEP_STABLE. TKEEP must remain stable when TVALID is asserted and TREADY low. Spec: section 2.2.1, and figure 2-1, on page 2-3."
        `define ERRM_TDATA_STABLE         "AXI4STREAM_ERRM_TDATA_STABLE. TDATA must remain stable when TVALID is asserted and TREADY low. Spec: section 2.2.1, and figure 2-1, on page 2-3."
        `define ERRM_TLAST_STABLE         "AXI4STREAM_ERRM_TLAST_STABLE. TLAST must remain stable when TVALID is asserted and TREADY low. Spec: section 2.2.1, and figure 2-1, on page 2-3."
        `define ERRM_TSTRB_STABLE         "AXI4STREAM_ERRM_TSTRB_STABLE. TSTRB must remain stable when TVALID is asserted and TREADY low. Spec: section 2.2.1, and figure 2-1, on page 2-3."
        `define ERRM_TVALID_STABLE        "AXI4STREAM_ERRM_TVALID_STABLE. Once TVALID is asserted, it must remain asserted until TREADY is high. Spec: section 2.2.1, and figure 2-1 on page 2-3."
        `define RECS_TREADY_MAX_WAIT      "AXI4STREAM_RECS_TREADY_MAX_WAIT. TREADY should be asserted within MAXWAITS cycles of TVALID being asserted."
        `define ERRM_TID_X                "AXI4STREAM_ERRM_TID_X. When TVALID is high, a value of X on TID is not permitted."
        `define ERRM_TDEST_X              "AXI4STREAM_ERRM_TDEST_X. When TVALID is high, a value of X on TDEST is not permitted."
        `define ERRM_TKEEP_X              "AXI4STREAM_ERRM_TKEEP_X. When TVALID is high, a value of X on TKEEP is not permitted."
        `define ERRM_TDATA_X              "AXI4STREAM_ERRM_TDATA_X. When TVALID is high, a value of X on active byte lanes of TDATA is not permitted."
        `define ERRM_TLAST_X              "AXI4STREAM_ERRM_TLAST_X. When TVALID is high, a value of X on TLAST is not permitted."
        `define ERRM_TSTRB_X              "AXI4STREAM_ERRM_TSTRB_X. When TVALID is high, a value of X on TSTRB is not permitted."
        `define ERRM_TVALID_X             "AXI4STREAM_ERRM_TVALID_X. When not in reset, a value of X on TVALID is not permitted."
        `define ERRS_TREADY_X             "AXI4STREAM_ERRS_TREADY_X. When not in reset, a value of X on TREADY is not permitted."
        `define ERRM_TUSER_X              "AXI4STREAM_ERRM_TUSER_X. When TVALID is high, a value of X on TUSER is not permitted."
        `define ERRM_TUSER_STABLE         "AXI4STREAM_ERRM_TUSER_STABLE. TUSER must remain stable when TVALID is asserted and TREADY low. Spec: section 2.2.1, and figure 2-1, on page 2-3."
        `define ERRM_TKEEP_TSTRB          "AXI4STREAM_ERRM_TKEEP_TSTRB. If TKEEP is deasserted then TSTRB must also be deasserted. Spec: section 2.4.3, and table 2-2, on page 2-9."
        `define ERRM_STREAM_ALL_DONE_EOS  "AXI4STREAM_ERRM_STREAM_ALL_DONE_EOS. There are active streams outstanding at the end of the simulation."
        `define ERRM_TDATA_TIEOFF         "AXI4STREAM_ERRM_TDATA_TIEOFF. TDATA must be stable when DATA_WIDTH_BYTES has been set to zero."
        `define ERRM_TKEEP_TIEOFF         "AXI4STREAM_ERRM_TKEEP_TIEOFF. TKEEP must be stable when DATA_WIDTH_BYTES has been set to zero."
        `define ERRM_TSTRB_TIEOFF         "AXI4STREAM_ERRM_TSTRB_TIEOFF. TSTRB must be stable when DATA_WIDTH_BYTES has been set to zero."
        `define ERRM_TID_TIEOFF           "AXI4STREAM_ERRM_TID_TIEOFF. TID must be stable when ID_WIDTH has been set to zero."
        `define ERRM_TDEST_TIEOFF         "AXI4STREAM_ERRM_TDEST_TIEOFF. TDEST must be stable when DEST_WIDTH has been set to zero."
        `define ERRM_TUSER_TIEOFF         "AXI4STREAM_ERRM_TUSER_TIEOFF. TUSER must be stable when USER_WIDTH has been set to zero."
        `define AUXM_TID_TDEST_WIDTH      "AXI4STREAM_AUXM_TID_TDEST_WIDTH. The value of ID_WIDTH + DEST_WIDTH must not exceed 24."
`endif

// --========================= End ===========================================--
