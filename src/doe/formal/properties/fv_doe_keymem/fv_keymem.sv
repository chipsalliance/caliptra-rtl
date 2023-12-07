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

module fv_keymem_checker_m	(
  
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
  input  [31 : 0]  new_sboxw,
   
  input  [127 : 0] roundkey_mem [14 : 0],

	//////////////////////
 	//       States     //
 	//////////////////////

  input IDLE,
  input Keyexpansion_128,
  input Keyexpansion_256

);

//localparams - Respective delays
localparam DLY_128 = 14; //no. of cycles the key expansion takes for 128B configuration
localparam DLY_256 = 18; //no. of cycles the key expansion takes for 256B configuration

////////////////////////
//   Default Clock    //
////////////////////////
default clocking default_clk @(posedge clk); endclocking

////////////////////////////////////
//  KeyMem Checker Properties    //
///////////////////////////////////

logic [6:0] curr_bit;
logic [3:0] idx;

////////////////////////
//   Symbolic Logic   //
////////////////////////
sym_bit: assume property (##1 $stable(curr_bit));
sym_idx: assume property (##1 $stable(idx));

//////////////////////////////////
//  KeyMem Checker Properties  //
/////////////////////////////////

// Checks if the design is in IDLE state and ready is low
reset_a: assert property (reset_p);
property reset_p;
  $past(!reset_n) |->
  IDLE &&
  ready == 0 
;endproperty

// Checks if ready stays same during IDLE to IDLE state transition
IDLE_to_IDLE_a: assert property (disable iff(!reset_n) IDLE_to_IDLE_p);
property IDLE_to_IDLE_p;
  IDLE &&
  !init_cmd
|->
  ##1
  IDLE &&
  ready == $past(ready, 1)
;endproperty

// Checks if ready is low during IDLE to Keyexpansion128 state transition
IDLE_to_keyExpansion128_a: assert property (disable iff(!reset_n) IDLE_to_keyExpansion128_p);
property IDLE_to_keyExpansion128_p;
  IDLE &&
  init_cmd &&
  !keylen
|->
  ##1
  Keyexpansion_128 &&
  (ready == 0)
;endproperty

// Checks if ready is low during IDLE to Keyexpansion256 state transition
IDLE_to_keyExpansion256_a: assert property (disable iff(!reset_n) IDLE_to_keyExpansion256_p);
property IDLE_to_keyExpansion256_p;
  IDLE &&
  init_cmd &&
  keylen
|->
  ##1
  Keyexpansion_256 &&
  ready == 0
;endproperty

//Properties to load when CBC is considered as top module
`ifdef CBC_BIND

  roundkey_check_128_cbc_a: assert property (disable iff(!reset_n) roundkey_check_128_cbc_p);
  property roundkey_check_128_cbc_p;
    logic [255:0] tracked_key;
    logic [127:0] result;

    ##0 init_cmd 
    ##0 !keylen 
    ##0 (1'b1, tracked_key = key)
    ##0 (idx < 11)
  
    ##DLY_128 (1'b1, result = compute_key_expansion_128(tracked_key[255:128], idx))
  |->
    ##0 roundkey_mem[idx][curr_bit] == result[curr_bit]
    ##0 ready 
  ;endproperty

  roundkey_check_256_cbc_a: assert property (disable iff(!reset_n) roundkey_check_256_cbc_p);
  property roundkey_check_256_cbc_p;
    logic [255:0] tracked_key;
    logic [127:0] result;

    ##0 init_cmd 
    ##0 keylen 
    ##0 (1'b1, tracked_key = key)
    ##0 (idx < 15)
  
    ##DLY_256 (1'b1, result = compute_key_expansion_256(tracked_key, idx))
  |->
    ##0 roundkey_mem[idx][curr_bit] == result[curr_bit]
    ##0 ready 
  ;endproperty

    // Checks computed roundkeys for 128bit configuration and the ready signal
    for (genvar rnd = 0; rnd < 11; rnd++) begin: rndkey128
      roundkey_check_a: assert property (disable iff(!reset_n) roundkey_check_128_p(rnd));
    end
    property roundkey_check_128_p(rndcnt);
      logic [255:0] tracked_key;
      logic [127:0] result;

      ##0 init_cmd 
      ##0 !keylen 
      ##0 (1'b1, tracked_key = key)
    
      ##DLY_128 round == rndcnt 
      ##0 (1'b1, result = compute_key_expansion_128(tracked_key[255:128], round)) 
    |->
      ##0 round_key[curr_bit] == result[curr_bit]
      ##0 ready 
    ;endproperty

    // Checks computed roundkeys for 256bit configuration and the ready signal
    for (genvar rnd = 0; rnd < 15; rnd++) begin: rndkey256
      roundkey_check_a: assert property (disable iff(!reset_n) roundkey_check_256_p(rnd));
    end
    property roundkey_check_256_p(rndcnt);
      logic [255:0] tracked_key;
      logic [127:0] result;

      ##0 init_cmd 
      ##0 keylen 
      ##0 (1'b1, tracked_key = key)
    
      ##DLY_256 round == rndcnt 
      ##0 (1'b1, result = compute_key_expansion_256(tracked_key[255:0], round)) 
    |->
      ##0 round_key[curr_bit] == result[curr_bit]
      ##0 ready 
    ;endproperty

//Properties to load when doe_key_mem is considered as top module
`else

  // Checks computed roundkeys for 128bit configuration and the ready signal
  for (genvar rnd = 0; rnd < 11; rnd++) begin: rndkey128
    roundkey_check_a: assert property (disable iff(!reset_n) roundkey_check_128_p(rnd));
  end
  property roundkey_check_128_p(rndcnt);
    logic [255:0] tracked_key;
    logic [127:0] result;

    ##0 init_cmd 
    ##0 !keylen 
    ##0 (1'b1, tracked_key = key)
  
    ##DLY_128 round == rndcnt 
    ##0 (1'b1, result = compute_key_expansion_128(tracked_key[255:128], round)) 
  |->
    ##0 round_key[curr_bit] == result[curr_bit]
    ##0 ready 
  ;endproperty

  // Checks computed roundkeys for 256bit configuration and the ready signal
  for (genvar rnd = 0; rnd < 15; rnd++) begin: rndkey256
    roundkey_check_a: assert property (disable iff(!reset_n) roundkey_check_256_p(rnd));
  end
  property roundkey_check_256_p(rndcnt);
    logic [255:0] tracked_key;
    logic [127:0] result;

    ##0 init_cmd 
    ##0 keylen 
    ##0 (1'b1, tracked_key = key)
  
    ##DLY_256 round == rndcnt 
    ##0 (1'b1, result = compute_key_expansion_256(tracked_key[255:0], round)) 
  |->
    ##0 round_key[curr_bit] == result[curr_bit]
    ##0 ready 
  ;endproperty

`endif

endmodule

//Inputs driven from doe_core_cbc
`ifdef CBC_BIND

  bind doe_key_mem fv_keymem_checker_m fv_key_mem (
    .clk(doe_core_cbc.keymem.clk),
    .reset_n(doe_core_cbc.keymem.reset_n && !doe_core_cbc.keymem.zeroize),
    .key(doe_core_cbc.keymem.key),      
    .keylen(doe_core_cbc.keymem.keylen),   
    .init_cmd(doe_core_cbc.keymem.init_cmd), 
    .round(doe_core_cbc.keymem.round),    
    .round_key(doe_core_cbc.keymem.round_key),
    .ready(doe_core_cbc.keymem.ready),    
    .sboxw(doe_core_cbc.keymem.sboxw),    
    .new_sboxw(doe_core_cbc.keymem.new_sboxw),
    .roundkey_mem(doe_core_cbc.keymem.key_mem [14 : 0]),
    .IDLE(doe_key_mem.key_mem_ctrl_reg == 0),
    .Keyexpansion_128((doe_key_mem.key_mem_ctrl_reg == 1) && !keylen),
    .Keyexpansion_256((doe_key_mem.key_mem_ctrl_reg == 1) && keylen)
  );

//Inputs driven with constraints on doe_key_mem
`else

  bind doe_key_mem fv_keymem_checker_m fv_key_mem (.*,
    .clk(clk),
    .reset_n(reset_n && !zeroize),
    .roundkey_mem(doe_key_mem.key_mem [14 : 0]),
    .IDLE(doe_key_mem.key_mem_ctrl_reg == 0),
    .Keyexpansion_128((doe_key_mem.key_mem_ctrl_reg == 1) && !keylen),
    .Keyexpansion_256((doe_key_mem.key_mem_ctrl_reg == 1) && keylen)
  );

`endif