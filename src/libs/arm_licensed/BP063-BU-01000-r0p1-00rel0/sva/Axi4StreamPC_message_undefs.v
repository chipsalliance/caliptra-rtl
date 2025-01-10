//==============================================================================
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
//  Purpose             : AXI4-Stream SVA Protocol Assertions message undefines
//==============================================================================

`ifdef AXI4STREAMPC_MESSAGES
        `undef AXI4STREAMPC_MESSAGES  	
        `undef ERRM_TVALID_RESET         
        `undef ERRM_TID_STABLE           
        `undef ERRM_TDEST_STABLE         
        `undef ERRM_TKEEP_STABLE         
        `undef ERRM_TDATA_STABLE         
        `undef ERRM_TLAST_STABLE         
        `undef ERRM_TSTRB_STABLE         
        `undef ERRM_TVALID_STABLE        
        `undef RECS_TREADY_MAX_WAIT      
        `undef ERRM_TID_X                
        `undef ERRM_TDEST_X              
        `undef ERRM_TKEEP_X              
        `undef ERRM_TDATA_X              
        `undef ERRM_TLAST_X              
        `undef ERRM_TSTRB_X              
        `undef ERRM_TVALID_X             
        `undef ERRS_TREADY_X             
        `undef ERRM_TUSER_X              
        `undef ERRM_TUSER_STABLE         
        `undef ERRM_TKEEP_TSTRB          
        `undef ERRM_STREAM_ALL_DONE_EOS  
        `undef ERRM_TDATA_TIEOFF         
        `undef ERRM_TKEEP_TIEOFF         
        `undef ERRM_TSTRB_TIEOFF         
        `undef ERRM_TID_TIEOFF           
        `undef ERRM_TDEST_TIEOFF         
        `undef ERRM_TUSER_TIEOFF 
        `undef AUXM_TID_TDEST_WIDTH        
`endif

// --========================= End ===========================================--
