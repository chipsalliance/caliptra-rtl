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

module fv_constraints_m(
  
  ////////////////////////////
  // Input / Output signals //
  ////////////////////////////
  // Clock and reset.
  input             clk,
  input             reset_n,

  input             encdec,
  input             init_cmd,
  input             next_cmd,
  input             ready,
  input             IV_updated,
  input             keylen,
  input [255:0]     key,
  input [127:0]     block_msg,
  input [127:0]     IV
);

logic init_reg, iv_updated_reg, next_cmd_reg;
logic keyexp_start,keyexp_done;
logic iv_start, iv_done;

////////////////////////
//   Default Clock    //
////////////////////////

default clocking default_clk @(posedge clk); endclocking


////////////////////////
//    Helper Logic    //
////////////////////////

//keyexpansion helper logic
always @ (posedge clk or negedge reset_n)
  begin : key_expansion
      if (!reset_n) begin 
          keyexp_start <= 1'b0;
          keyexp_done <= 1'b0;
      end
      else if (init_cmd) begin
          keyexp_start <= 1'b1;
          keyexp_done <= 1'b0;
      end
      else if (keyexp_start && doe_core_cbc.key_ready) begin
          keyexp_start <= 1'b0;
          keyexp_done <= 1'b1;
      end
      else if (keyexp_done && init_cmd) begin
          keyexp_start <= 1'b1;
          keyexp_done <= 1'b0;
      end
  end

//IV helper logic
always @ (posedge clk or negedge reset_n)
  begin : iv_control
      if (!reset_n) begin
          iv_start <= 1'b0;
          iv_done <= 1'b0;
      end
      else if (keyexp_done && IV_updated) begin
          iv_start <= 1'b1;
          iv_done <= 1'b0;
      end
      else if (iv_start && next_cmd) begin
          iv_start <= 1'b0;
          iv_done <= 1'b1;
      end
      else if (iv_done && init_cmd) begin
          iv_start <= 1'b0;
          iv_done <= 1'b0;
      end
  end


////////////////////////////////////
//  CBC Constraint Properties  //
///////////////////////////////////

//init_cmd, next_cmd and IV_updated can be only received if the doe_core_cbc is ready
cmd_on_ready_a: assume property (disable iff(!reset_n) cmd_on_ready_p);
property cmd_on_ready_p;
    !ready
|->
    !init_cmd && !next_cmd && !IV_updated
;endproperty

//next_cmd can only be received once there is an IV_updated before
next_cmd_order_a: assume property (disable iff(!reset_n) next_cmd_order_p);
property next_cmd_order_p;
    !iv_start 
|=> 
    !next_cmd || iv_done
;endproperty

//next_cmd can only be received once the keyexpansion is done
next_cmd_keyexp_order_a: assume property (disable iff(!reset_n) next_cmd_keyexp_order_p);
property next_cmd_keyexp_order_p;
    !keyexp_done 
|-> 
    !next_cmd
;endproperty

//IV_updated can only be received once there is an IV_updated before
IV_updated_order_a: assume property (disable iff(!reset_n) IV_updated_order_p);
property IV_updated_order_p;
    iv_done 
|-> 
    !IV_updated
;endproperty

//IV_updated is a pulse
iv_updated_pulse_a: assume property (disable iff(!reset_n) iv_updated_pulse_p);
property iv_updated_pulse_p;
    IV_updated |=> !IV_updated
;endproperty

//init_cmd and next_cmd doesn't come together
init_next_a: assume property (disable iff(!reset_n) init_next_p);
property init_next_p;
    !(init_cmd && next_cmd) 
;endproperty

//init_cmd and IV_updated doesn't come together
init_iv_a: assume property (disable iff(!reset_n) init_iv_p);
property init_iv_p;
    !(init_cmd && IV_updated)
;endproperty

//IV_updated and next_cmd doesn't come together
next_iv_a: assume property (disable iff(!reset_n) next_iv_p);
property next_iv_p;
    !(next_cmd && IV_updated)
;endproperty

//keylen is stable until there is a new init_cmd 
stable_keylen_a: assume property (disable iff(!reset_n) keylen_stable);
property keylen_stable;
   $stable(keylen) || init_cmd
;endproperty

//key is stable until there is a new init_cmd
key_stable_during_expansion_a: assume property (disable iff(!reset_n) key_stable_during_expansion);
property key_stable_during_expansion;
  $stable(key) || init_cmd
;endproperty

//encdec is stable until there is a new next_cmd
encdec_during_operation_a: assume property (disable iff(!reset_n) encdec_during_operation_p);
property encdec_during_operation_p;
    $stable(encdec) || next_cmd
;endproperty

//block message is stable until doe_core_cbc is ready
blkmsg_during_operation_a: assume property (disable iff(!reset_n) blkmsg_during_operation_p);
property blkmsg_during_operation_p;
  $stable(block_msg) || ready
;endproperty

//IV has stable until encrypted block_msg sent to enc_block
iv_during_operation_a: assume property (disable iff(!reset_n) iv_during_operation_p);
property iv_during_operation_p;
  ready || !iv_done
  |->
  $stable(IV) 
;endproperty

endmodule

//Connect this constraints module with the DUV
bind doe_core_cbc fv_constraints_m fv_constraints(
  .clk(clk),
  .reset_n(reset_n && !zeroize),
  .encdec(encdec),
  .init_cmd(init_cmd),
  .next_cmd(next_cmd),
  .ready(ready),
  .IV_updated(IV_updated),
  .key(key),
  .block_msg(block_msg),
  .keylen(keylen),
  .IV(IV)
);

