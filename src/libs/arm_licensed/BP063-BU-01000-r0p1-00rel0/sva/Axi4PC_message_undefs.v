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
//  File Revision       : 133319
//
//  Date                :  2012-07-09 11:07:18 +0100 (Mon, 09 Jul 2012)
//  
//  Release Information : BP063-VL-70004-r0p1-00rel0
//  
//  ----------------------------------------------------------------------------
//  Purpose             : AXI4 SV Protocol Assertions Error Message undefines
//  ========================================================================--


`ifdef AXI4PC_MESSAGES
        `undef AXI4PC_MESSAGES
        `undef ERRM_AWADDR_BOUNDARY      
        `undef ERRM_AWADDR_WRAP_ALIGN    
        `undef ERRM_AWBURST              
        `undef ERRM_AWCACHE              
        `undef ERRM_ARCACHE              
        `undef ERRM_AWLEN_WRAP           
        `undef ERRM_AWSIZE               
        `undef ERRM_AWVALID_RESET        
        `undef ERRM_AWADDR_STABLE        
        `undef ERRM_AWBURST_STABLE       
        `undef ERRM_AWCACHE_STABLE       
        `undef ERRM_AWID_STABLE          
        `undef ERRM_AWLEN_STABLE         
        `undef ERRM_AWLOCK_STABLE        
        `undef ERRM_AWPROT_STABLE        
        `undef ERRM_AWSIZE_STABLE        
        `undef ERRM_AWQOS_STABLE         
        `undef ERRM_AWREGION_STABLE      
        `undef ERRM_AWVALID_STABLE       
        `undef ERRM_AWADDR_X             
        `undef ERRM_AWBURST_X            
        `undef ERRM_AWCACHE_X            
        `undef ERRM_AWID_X               
        `undef ERRM_AWLEN_X              
        `undef ERRM_AWLOCK_X             
        `undef ERRM_AWPROT_X             
        `undef ERRM_AWSIZE_X             
        `undef ERRM_AWQOS_X              
        `undef ERRM_AWREGION_X           
        `undef ERRM_AWVALID_X            
        `undef ERRS_AWREADY_X            
        `undef ERRM_WDATA_NUM            
        `undef ERRM_WSTRB                
        `undef ERRM_WVALID_RESET         
        `undef ERRM_WDATA_STABLE         
        `undef ERRM_WLAST_STABLE         
        `undef ERRM_WSTRB_STABLE         
        `undef ERRM_WVALID_STABLE        
        `undef ERRM_WDATA_X              
        `undef ERRM_WLAST_X              
        `undef ERRM_WSTRB_X              
        `undef ERRM_WVALID_X             
        `undef ERRS_WREADY_X             
        `undef ERRS_BRESP_WLAST          
        `undef ERRS_BRESP_ALL_DONE_EOS   
        `undef ERRS_BRESP_EXOKAY         
        `undef ERRS_BVALID_RESET         
        `undef ERRS_BRESP_AW             
        `undef ERRS_BID_STABLE           
        `undef ERRS_BRESP_STABLE         
        `undef ERRS_BVALID_STABLE        
        `undef ERRM_BREADY_X             
        `undef ERRS_BID_X                
        `undef ERRS_BRESP_X              
        `undef ERRS_BVALID_X             
        `undef ERRM_ARADDR_BOUNDARY      
        `undef ERRM_ARADDR_WRAP_ALIGN    
        `undef ERRM_ARBURST              
        `undef ERRM_ARLEN_FIXED          
        `undef ERRM_AWLEN_FIXED          
        `undef ERRM_AWLEN_LOCK           
        `undef ERRM_ARLEN_LOCK           
        `undef ERRM_ARLEN_WRAP           
        `undef ERRM_ARSIZE               
        `undef ERRM_ARVALID_RESET        
        `undef ERRM_ARADDR_STABLE        
        `undef ERRM_ARBURST_STABLE       
        `undef ERRM_ARCACHE_STABLE       
        `undef ERRM_ARID_STABLE          
        `undef ERRM_ARLEN_STABLE         
        `undef ERRM_ARLOCK_STABLE        
        `undef ERRM_ARPROT_STABLE        
        `undef ERRM_ARSIZE_STABLE        
        `undef ERRM_ARQOS_STABLE         
        `undef ERRM_ARREGION_STABLE      
        `undef ERRM_ARVALID_STABLE       
        `undef ERRM_ARADDR_X             
        `undef ERRM_ARBURST_X            
        `undef ERRM_ARCACHE_X            
        `undef ERRM_ARID_X               
        `undef ERRM_ARLEN_X              
        `undef ERRM_ARLOCK_X             
        `undef ERRM_ARPROT_X             
        `undef ERRM_ARSIZE_X             
        `undef ERRM_ARQOS_X              
        `undef ERRM_ARREGION_X           
        `undef ERRM_ARVALID_X            
        `undef ERRS_ARREADY_X            
        `undef ERRS_RDATA_NUM            
        `undef ERRS_RLAST_ALL_DONE_EOS   
        `undef ERRS_RID                  
        `undef ERRS_RRESP_EXOKAY         
        `undef ERRS_RVALID_RESET         
        `undef ERRS_RDATA_STABLE         
        `undef ERRS_RID_STABLE           
        `undef ERRS_RLAST_STABLE         
        `undef ERRS_RRESP_STABLE         
        `undef ERRS_RVALID_STABLE        
        `undef ERRS_RDATA_X              
        `undef ERRM_RREADY_X             
        `undef ERRS_RID_X                
        `undef ERRS_RLAST_X              
        `undef ERRS_RRESP_X              
        `undef ERRS_RVALID_X             
        `undef ERRL_CSYSACK_FALL         
        `undef ERRL_CSYSACK_RISE         
        `undef ERRL_CSYSREQ_FALL         
        `undef ERRL_CSYSREQ_RISE         
        `undef ERRL_CACTIVE_X            
        `undef ERRL_CSYSACK_X            
        `undef ERRL_CSYSREQ_X            
        `undef ERRM_EXCL_ALIGN           
        `undef ERRM_EXCL_LEN             
        `undef ERRM_EXCL_MAX             
        `undef ERRM_AWUSER_STABLE        
        `undef ERRM_WUSER_STABLE         
        `undef ERRS_BUSER_STABLE         
        `undef ERRM_ARUSER_STABLE        
        `undef ERRS_RUSER_STABLE         
        `undef ERRM_AWUSER_X             
        `undef ERRM_WUSER_X              
        `undef ERRS_BUSER_X              
        `undef ERRM_ARUSER_X             
        `undef ERRS_RUSER_X              
        `undef ERRM_AWUSER_TIEOFF
        `undef ERRM_WUSER_TIEOFF
        `undef ERRS_BUSER_TIEOFF
        `undef ERRM_ARUSER_TIEOFF
        `undef ERRS_RUSER_TIEOFF
        `undef ERRM_AWID_TIEOFF 
        `undef ERRS_BID_TIEOFF 
        `undef ERRM_ARID_TIEOFF 
        `undef ERRS_RID_TIEOFF 
        `undef AUX_DATA_WIDTH           
        `undef AUX_ADDR_WIDTH           
        `undef AUX_EXMON_WIDTH          
        `undef AUX_MAXRBURSTS           
        `undef AUX_MAXWBURSTS           
        `undef AUX_RCAM_OVERFLOW        
        `undef AUX_RCAM_UNDERFLOW       
        `undef AUX_WCAM_OVERFLOW        
        `undef AUX_WCAM_UNDERFLOW       
        `undef AUX_EXCL_OVERFLOW        
        `undef RECM_EXCL_PAIR 
        `undef RECM_EXCL_R_W           
        `undef RECS_AWREADY_MAX_WAIT     
        `undef RECS_WREADY_MAX_WAIT      
        `undef RECM_BREADY_MAX_WAIT      
        `undef RECS_ARREADY_MAX_WAIT     
        `undef RECM_RREADY_MAX_WAIT      
        `undef RECM_EXCL_MATCH           
`endif

// --========================= End ===========================================--
