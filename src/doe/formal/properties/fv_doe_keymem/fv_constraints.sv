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

import doe_core_cbc_pkg::*;

module fv_key_constraints_m(
  
   ////////////////////////////
   // Input / Output signals //
   ////////////////////////////
   input             clk,         
   input             reset_n,          

   input  [255 : 0]  key,         
   input             keylen,      
   input             init_cmd,      

   input     [3 : 0] round,       
   input   [127 : 0] round_key,      
   input             ready,       


   input  [31 : 0]  sboxw,        
   input  [31 : 0]  new_sboxw     

);

////////////////////////
//   Default Clock    //
////////////////////////
default clocking default_clk @(posedge clk); endclocking

//Internal Signals
logic [31:0] fv_sbox;

//Helper Logic
assign fv_sbox = get_sbox(sboxw);

////////////////////////////////////
//  KeyMem Constraint Properties  //
///////////////////////////////////

//Constraint to drive correct value to new_sboxw input
sbox_constraint_a: assume property  (disable iff(!reset_n) sbox_constraint_p);
property sbox_constraint_p;
   new_sboxw == fv_sbox
;endproperty

//Constraint to keep keylen input stable
stable_keylen_a: assume property (disable iff(!reset_n) stable_keylen_p);
property stable_keylen_p;
   $stable(keylen) || ready
;endproperty

//Constraint to keep key input stable
stable_key_a: assume property (disable iff(!reset_n) stable_key_p);
property stable_key_p;
    $stable(key) || ready
;endproperty

//Constraint to get init_cmd only when the design is in IDLE state
init_only_in_idle_a: assume property (disable iff(!reset_n) init_only_in_idle_p);
property init_only_in_idle_p;
   init_cmd 
|->
   doe_key_mem.key_mem_ctrl_reg == 0
;endproperty

endmodule

//Connect this constraints module with the DUV
bind doe_key_mem fv_key_constraints_m fv_keymem_constraints(.*
	);