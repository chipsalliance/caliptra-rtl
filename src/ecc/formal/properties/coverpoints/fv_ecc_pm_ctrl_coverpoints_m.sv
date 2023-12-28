// -------------------------------------------------
// Contact: contact@lubis-eda.com
// Author: Tobias Ludwig, Michael Schwarz
// -------------------------------------------------
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
module fv_ecc_pm_ctrl_coverpoints_m import ecc_pm_uop_pkg::*;(
    input logic clk,
    input logic reset_n,
    input logic zeroize
);
    
    default clocking default_clk @(posedge clk); endclocking

    //cover zeroize
    cover_zeroize: cover property(disable iff(!reset_n) ecc_pm_ctrl.zeroize );

   //cover sca_en_i
    cover_sca_en_always: cover property(disable iff(!reset_n || zeroize)
                ecc_pm_ctrl.sca_en_i ==1);


    //cover req_digit when keygen cmd
    cover_req_digit_keygen: cover property(disable iff(!reset_n || zeroize) 
            ecc_pm_ctrl.ecc_cmd_i==KEYGEN_CMD &&
            ecc_pm_ctrl.prog_cntr == NOP
            ##1
            ecc_pm_ctrl.req_digit_o[->576]);

    //cover req_digit when signing cmd
    cover_req_digit_signing: cover property(disable iff(!reset_n|| zeroize) 
            ecc_pm_ctrl.ecc_cmd_i==SIGN_CMD &&
            ecc_pm_ctrl.prog_cntr == NOP
            ##1 
            
                ecc_pm_ctrl.req_digit_o[->576]);

    //cover req_digit when verifying cmd
    cover_req_digit_verifying1: cover property(disable iff(!reset_n|| zeroize) 
            ecc_pm_ctrl.ecc_cmd_i== VER_PART1_CMD &&
            ecc_pm_ctrl.prog_cntr == NOP
            ##1 
                ecc_pm_ctrl.req_digit_o[->384]);

    cover_req_digit_verifying2: cover property(disable iff(!reset_n|| zeroize) 
            ecc_pm_ctrl.prog_cntr== PM_INIT_PK_S &&
            ecc_pm_ctrl.ecc_cmd_reg == VER_PART2_CMD
            ##1 
                ecc_pm_ctrl.req_digit_o[->384]);
    
    /*
    // Keygen Sequence

    cover_keygen_sequence: cover property(disable iff(!reset_n || zeroize) keygen_sequence);

        sequence keygen_sequence;
            ecc_pm_ctrl.ecc_cmd_i == KEYGEN_CMD 
            ##0 ecc_pm_ctrl.prog_cntr == NOP
            ##1 ecc_pm_ctrl.prog_cntr == PM_INIT_G_S     
            ##123 ecc_pm_ctrl.prog_cntr == PM_INIT_S     
            ##16 ecc_pm_ctrl.prog_cntr == PA_S           
            ##789 ecc_pm_ctrl.prog_cntr == PD_S          
            ##910443 ecc_pm_ctrl.prog_cntr == INV_S          
            ##21201 ecc_pm_ctrl.prog_cntr == CONV_S         
            ##167 ecc_pm_ctrl.prog_cntr == CONV_E 
            ##1 ecc_pm_ctrl.prog_cntr == NOP;
        endsequence


    // Signing Sequence

     cover_signing_sequence: cover property(disable iff(!reset_n || zeroize) signing_sequence);
        sequence signing_sequence;
            ecc_pm_ctrl.ecc_cmd_i == SIGN_CMD 
            ##0 ecc_pm_ctrl.prog_cntr == NOP
            ##1 ecc_pm_ctrl.prog_cntr == PM_INIT_G_S  
            ##123 ecc_pm_ctrl.prog_cntr == PM_INIT_S 
            ##16 ecc_pm_ctrl.prog_cntr == PA_S      
            ##789 ecc_pm_ctrl.prog_cntr == PD_S      
            ##910443 ecc_pm_ctrl.prog_cntr == INV_S     
            ##21201 ecc_pm_ctrl.prog_cntr == CONV_S    
            ##168 ecc_pm_ctrl.prog_cntr == SIGN0_S   
            ##311 ecc_pm_ctrl.prog_cntr == INVq_S    
            ##21205 ecc_pm_ctrl.prog_cntr == SIGN1_S   
            ##131 ecc_pm_ctrl.prog_cntr == NOP;
        endsequence

    // Verify Sequence
    cover_verify_part0_sequence: cover property(disable iff(!reset_n || zeroize) verify_part0_sequence);
        sequence verify_part0_sequence;
            ecc_pm_ctrl.ecc_cmd_i == VER_PART0_CMD 
            ##0 ecc_pm_ctrl.prog_cntr == NOP
            ##1 ecc_pm_ctrl.prog_cntr == VER0_P0_S   
            ##127 ecc_pm_ctrl.prog_cntr == INVq_S   
            ##21205 ecc_pm_ctrl.prog_cntr == VER0_P1_S
            ##168 ecc_pm_ctrl.prog_cntr == NOP;
        endsequence

    cover_verify_part1_sequence: cover property(disable iff(!reset_n || zeroize) verify_part1_sequence);
        sequence verify_part1_sequence;
            ecc_pm_ctrl.ecc_cmd_i == VER_PART1_CMD 
            ##0 ecc_pm_ctrl.prog_cntr == NOP
            ##1 ecc_pm_ctrl.prog_cntr == PM_INIT_G_S 
            ##123 ecc_pm_ctrl.prog_cntr == PM_INIT_S
            ##16 ecc_pm_ctrl.prog_cntr == PA_S     
            ##789 ecc_pm_ctrl.prog_cntr == PD_S     
            ##606699 ecc_pm_ctrl.prog_cntr == NOP;    
        endsequence

    cover_verify_part2_sequence: cover property(disable iff(!reset_n || zeroize) verify_part2_sequence);
     
     sequence verify_part2_sequence;
        ecc_pm_ctrl.ecc_cmd_i == VER_PART2_CMD
        ##0 ecc_pm_ctrl.prog_cntr == NOP
        ##1 ecc_pm_ctrl.prog_cntr == VER1_ST_S       
        ##12 ecc_pm_ctrl.prog_cntr == PM_INIT_PK_S 
        ##86 ecc_pm_ctrl.prog_cntr == PM_INIT_S    
        ##16 ecc_pm_ctrl.prog_cntr == PA_S         
        ##789 ecc_pm_ctrl.prog_cntr == PD_S         
        ##606699 ecc_pm_ctrl.prog_cntr == VER2_PA_S    
        ##793 ecc_pm_ctrl.prog_cntr == INV_S        
        ##21201 ecc_pm_ctrl.prog_cntr == CONV_S       
        ##168 ecc_pm_ctrl.prog_cntr == NOP;   
     endsequence      

*/
endmodule

  bind ecc_pm_ctrl fv_ecc_pm_ctrl_coverpoints_m fv_ecc_pm_ctrl_coverpoints(
      .clk(clk),
      .reset_n(reset_n),
      .zeroize(zeroize)
  );
