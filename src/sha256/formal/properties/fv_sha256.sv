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
import sha256_package::*;


// Functions

function logic unsigned [7:0] compute_winternitz_iterations(logic unsigned [7:0] winternitz_w);
  if ((winternitz_w == 8'd0))
    return 8'd0;
  else if ((winternitz_w == 8'd2))
    return 8'd2;
  else if ((winternitz_w == 8'd4))
    return 8'd14;
  else if ((winternitz_w == 8'd8))
    return 8'd254;
  else
    return 8'd0;
endfunction

function logic invalid_winternitz_j(logic unsigned [7:0] winternitz_loop_init, logic unsigned [7:0] loop_iterations);
  return (winternitz_loop_init > loop_iterations);
endfunction

function logic invalid_winternitz_mode(logic is_sha256_mode);
  return !is_sha256_mode;
endfunction

function logic invalid_winternitz_w(logic unsigned [7:0] winternitz_w);
  return ((((winternitz_w != 8'd1) && (winternitz_w != 8'd2)) && (winternitz_w != 8'd4)) && (winternitz_w != 8'd8));
endfunction


module fv_sha256 (
  input logic reset_n,
  input logic top_reset_n,
  input logic clk,

  // Ports
  input logic sha_core_response_port_vld,
  input logic sha_core_response_port_rdy,
  input st_Sha256CoreResponse sha_core_response_port,

  input logic sha_core_winternitz192_response_port_vld,
  input logic sha_core_winternitz192_response_port_rdy,
  input st_Sha256CoreWinternitz192Response sha_core_winternitz192_response_port,

  input logic sha_core_winternitz256_response_port_vld,
  input logic sha_core_winternitz256_response_port_rdy,
  input st_Sha256CoreWinternitz256Response sha_core_winternitz256_response_port,

  input logic sha_request_port_vld,
  input logic sha_request_port_rdy,
  input st_Sha256Request sha_request_port,

  input st_Sha256Request sha_shared_request_port,

  input logic sha_core_request_port_vld,
  input st_Sha256CoreRequest sha_core_request_port,

  input logic sha_core_winternitz192_request_port_vld,
  input st_Sha256CoreWinternitz192Request sha_core_winternitz192_request_port,

  input logic sha_core_winternitz256_request_port_vld,
  input st_Sha256CoreWinternitz256Request sha_core_winternitz256_request_port,

  input logic sha_response_port_vld,
  input st_Sha256Response sha_response_port,

  // Registers
  input logic unsigned [7:0] loop_boundary,
  input logic unsigned [7:0] loop_counter,
  input st_Sha256Request sha_request,
  input logic unsigned [127:0] winternitz_I,
  input logic unsigned [15:0] winternitz_i,
  input logic unsigned [31:0] winternitz_q,

  // States
  input logic idle,
  input logic lms_1st_256,
  input logic lms_others_256,
  input logic lms_1st_192,
  input logic lms_others_192,
  input logic sha,

  // Manual
  input logic hwif_in_register_error_reset,
  input logic hwif_in_winternitz_error,
  input logic hwif_in_sha_operation_error,
  input logic hwif_in_error2,
  input logic hwif_in_error3,
  input logic hwif_in_command_done,
  input logic [31:0] hwif_in_name0,
  input logic [31:0] hwif_in_name1,
  input logic [31:0] hwif_in_version0,
  input logic [31:0] hwif_in_version1,
  input logic hwif_in_valid,
  input logic hwif_in_ready,
  input logic hwif_in_wntz_busy,
  input logic hwif_in_digest_clear,
  input logic hwif_in_block_clear,
  input logic hwif_in_control_zeroize,
  input logic hwif_in_register_error_interrupt,
  input logic hwif_in_register_notification_interrupt,
  input logic error_interrupt,
  input logic notification_interrupt,
  input logic error,
  input logic powergood,
  input logic register_read_error,
  input logic register_write_error,
  input logic valid_register,
  input logic ready_register,
  input logic [2:0] wntz_fsm_next,
  input logic [2:0] wntz_fsm,
  input logic wntz_busy_register,
  input logic core_init,
  input logic core_next,
  input logic core_digest_valid,
  input logic debug_scan_switch,
  input logic ready_flag_register,
  input logic [0 : 7][31 : 0] digest_register,
  input logic valid_flag_register,
  input logic zeroize_register
);


default clocking default_clk @(posedge clk); endclocking


// Define a SHA state for the DUV
logic sha_next;
logic sha_state;

assign sha_next =
    ((core_init || core_next) && wntz_fsm_next == WNTZ_IDLE) ||
    (!core_digest_valid && sha_state);

always @(posedge clk or negedge reset_n) begin
  if(!reset_n)
    sha_state <= 1'b0;
  else
    sha_state <= sha_next;
end


// Define instances of data we receive from the ports
st_Sha256CoreResponse sha_core_response_0_i;
assign sha_core_response_0_i = '{
  digest_block: '{ 0: 0, 1: 0, 2: 0, 3: 0, 4: 0, 5: 0, 6: 0, 7: 0 }
};

st_Sha256Request sha_request_0_i;
assign sha_request_0_i = '{
  is_init: 0,
  is_next: 0,
  is_sha256_mode: 0,
  is_winternitz: 0,
  winternitz_n_mode: 0,
  winternitz_w: 8'd0,
  winternitz_loop_init: 8'd0,
  zeroize: 0,
  message_block: '{
      0: 0,
      1: 0,
      2: 0,
      3: 0,
      4: 0,
      5: 0,
      6: 0,
      7: 0,
      8: 0,
      9: 0,
      10: 0,
      11: 0,
      12: 0,
      13: 0,
      14: 0,
      15: 0
  }
};

st_Sha256CoreRequest sha_core_request_1_i;
assign sha_core_request_1_i = '{
  init_command: 1,
  next_command: 0,
  is_sha256_mode: sha_request_port.is_sha256_mode,
  zeroize: sha_request_port.zeroize,
  message_block: sha_request_port.message_block
};

st_Sha256CoreRequest sha_core_request_2_i;
assign sha_core_request_2_i = '{
  init_command: sha_request_port.is_init,
  next_command: sha_request_port.is_next,
  is_sha256_mode: sha_request_port.is_sha256_mode,
  zeroize: sha_request_port.zeroize,
  message_block: sha_request_port.message_block
};

st_Sha256CoreWinternitz256Request sha_core_winternitz256_request_1_i;
assign sha_core_winternitz256_request_1_i = '{
  init_command: 1,
  next_command: 0,
  is_sha256_mode: 1,
  zeroize: sha_request.zeroize,
  message_block: '{
    I: winternitz_I,
    q: winternitz_q,
    i: winternitz_i,
    j: 8'((loop_counter + 8'd1)),
    tmp: sha_core_winternitz256_response_port.tmp,
    padding: ((SHA256_ENDING << 72'd64) + 72'h1B8)
  }
};

st_Sha256Response sha_response_1_i;
assign sha_response_1_i = '{
  digest_block: sha_core_winternitz256_response_port.tmp
};

st_Sha256CoreWinternitz192Request sha_core_winternitz192_request_1_i;
assign sha_core_winternitz192_request_1_i = '{
  init_command: 1,
  next_command: 0,
  is_sha256_mode: 1,
  zeroize: sha_request.zeroize,
  message_block: '{
    I: winternitz_I,
    q: winternitz_q,
    i: winternitz_i,
    j: 8'((loop_counter + 8'd1)),
    tmp: sha_core_winternitz192_response_port.tmp,
    padding: ((SHA256_ENDING << 136'd128) + 136'h178)
  }
};

st_Sha256Response sha_response_2_i;
assign sha_response_2_i = '{
  digest_block: '{
    0: sha_core_winternitz192_response_port.tmp[64'd0],
    1: sha_core_winternitz192_response_port.tmp[64'd1],
    2: sha_core_winternitz192_response_port.tmp[64'd2],
    3: sha_core_winternitz192_response_port.tmp[64'd3],
    4: sha_core_winternitz192_response_port.tmp[64'd4],
    5: sha_core_winternitz192_response_port.tmp[64'd5],
    6: 0,
    7: 0
  }
};

st_Sha256CoreRequest sha_core_request_3_i;
assign sha_core_request_3_i = '{
  init_command: sha_shared_request_port.is_init,
  next_command: sha_shared_request_port.is_next,
  is_sha256_mode: sha_shared_request_port.is_sha256_mode,
  zeroize: sha_shared_request_port.zeroize,
  message_block: sha_shared_request_port.message_block
};

st_Sha256Response sha_response_3_i;
assign sha_response_3_i = '{
  digest_block: '{
    0: sha_core_response_port.digest_block['sd0],
    1: sha_core_response_port.digest_block['sd1],
    2: sha_core_response_port.digest_block['sd2],
    3: sha_core_response_port.digest_block['sd3],
    4: sha_core_response_port.digest_block['sd4],
    5: sha_core_response_port.digest_block['sd5],
    6: sha_core_response_port.digest_block['sd6],
    7: (sha_request.is_sha256_mode ? sha_core_response_port.digest_block[64'd7] : 0)
  }
};


assert_reset_zeroize: assert property(
    ##0 (hwif_in_control_zeroize || debug_scan_switch)
|->
    ##1 ready_register      == 1'b0
     && digest_register     == 1'b0
     && valid_flag_register == 1'b0
);

assert_reset_n: assert property (property_reset_n);
property property_reset_n;
  !top_reset_n
|->
  ##1 idle &&
  loop_boundary == 8'd0   &&
  loop_counter  == 8'd0   &&
  winternitz_I  == 128'd0 &&
  winternitz_i  == 16'd0  &&
  winternitz_q  == 0;
endproperty


assert_winternitz_error: assert property(
    disable iff(!reset_n)

    hwif_in_winternitz_error == (
        (
            (lms_1st_256 || lms_others_256 || lms_1st_192 || lms_others_192) &&
                (invalid_winternitz_mode(sha_request.is_sha256_mode) ||
                invalid_winternitz_w(sha_request.winternitz_w))
        ) || (
            sha_request_port.is_winternitz &&
                invalid_winternitz_j(
                    sha_request_port.winternitz_loop_init,
                    compute_winternitz_iterations(sha_request_port.winternitz_w)
                )
        )
    )
);

assert_sha_operation_error: assert property(
    disable iff(!reset_n)

    hwif_in_sha_operation_error == (
        sha_request.is_init &&
        sha_request.is_next
    )
);

assert_error2: assert property(
    disable iff(!reset_n)
    hwif_in_error2 == 1'b0
);

assert_error3: assert property(
    disable iff(!reset_n)
    hwif_in_error3 == 1'b0
);

assert_connectivity_interrupts: assert property(
    (error_interrupt        == hwif_in_register_error_interrupt)        &&
    (notification_interrupt == hwif_in_register_notification_interrupt) &&
    (error                  == register_read_error | register_write_error)
);

assert_connectivity_name_version: assert property(
    (hwif_in_name0    == sha256_params_pkg::SHA256_CORE_NAME0)    &&
    (hwif_in_name1    == sha256_params_pkg::SHA256_CORE_NAME1)    &&
    (hwif_in_version0 == sha256_params_pkg::SHA256_CORE_VERSION0) &&
    (hwif_in_version1 == sha256_params_pkg::SHA256_CORE_VERSION1)
);

assert_connectivity_status: assert property(
    hwif_in_ready     == ready_register &&
    hwif_in_valid     == valid_register &&
    hwif_in_wntz_busy == wntz_busy_register
);

assert_connectivity_powergood: assert property(
    powergood == hwif_in_register_error_reset
);

assert_connectivity_zeroize: assert property(
    (hwif_in_digest_clear == zeroize_register) &&
    (hwif_in_block_clear  == zeroize_register)
);

assert_command_done: assert property(
    hwif_in_command_done == (
        (wntz_fsm == WNTZ_IDLE) & core_digest_valid & ($past(!core_digest_valid) | $past(wntz_fsm != WNTZ_IDLE))
    )
);


assert_idle_to_lms_1st_192: assert property (disable iff(!reset_n) property_idle_to_lms_1st_192);
property property_idle_to_lms_1st_192;
  idle &&
  sha_request_port_vld &&
  sha_request_port.is_winternitz &&
  sha_request_port.is_init &&
  (sha_request_port.winternitz_loop_init <= compute_winternitz_iterations(sha_request_port.winternitz_w)) &&
  !sha_request_port.winternitz_n_mode
|->
  sha_core_request_port == sha_core_request_1_i
  ##1
  lms_1st_192 &&
  loop_boundary == compute_winternitz_iterations($past(sha_request_port.winternitz_w, 1)) &&
  loop_counter == $past(sha_request_port.winternitz_loop_init, 1) &&
  winternitz_I == 128'(
    (((($past(sha_request_port.message_block[64'd0], 1) << 128'd96) +
       ($past(sha_request_port.message_block[64'd1], 1) << 128'd64)) +
       ($past(sha_request_port.message_block[64'd2], 1) << 128'd32)) +
       $past(sha_request_port.message_block[64'd3], 1))
  ) &&
  winternitz_i == 16'(($past(sha_request_port.message_block[64'd5], 1) >> 16)) &&
  winternitz_q == $past(sha_request_port.message_block[64'd4], 1);
endproperty


assert_idle_to_lms_1st_256: assert property (disable iff(!reset_n) property_idle_to_lms_1st_256);
property property_idle_to_lms_1st_256;
  idle &&
  sha_request_port_vld &&
  sha_request_port.is_winternitz &&
  sha_request_port.is_init &&
  (sha_request_port.winternitz_loop_init <= compute_winternitz_iterations(sha_request_port.winternitz_w)) &&
  sha_request_port.winternitz_n_mode
|->
  sha_core_request_port == sha_core_request_1_i
  ##1
  lms_1st_256 &&
  loop_boundary == compute_winternitz_iterations($past(sha_request_port.winternitz_w, 1)) &&
  loop_counter == $past(sha_request_port.winternitz_loop_init, 1) &&
  winternitz_I == 128'(
    (((($past(sha_request_port.message_block[64'd0], 1) << 128'd96) +
       ($past(sha_request_port.message_block[64'd1], 1) << 128'd64)) +
       ($past(sha_request_port.message_block[64'd2], 1) << 128'd32)) +
       $past(sha_request_port.message_block[64'd3], 1))
  ) &&
  winternitz_i == 16'(($past(sha_request_port.message_block[64'd5], 1) >> 16)) &&
  winternitz_q == $past(sha_request_port.message_block[64'd4], 1);
endproperty


assert_idle_to_sha: assert property (disable iff(!reset_n) property_idle_to_sha);
property property_idle_to_sha;
  idle &&
  sha_request_port_vld &&
  !((sha_request_port.is_winternitz && sha_request_port.is_init) && (sha_request_port.winternitz_loop_init <= compute_winternitz_iterations(sha_request_port.winternitz_w))) &&
  (sha_request_port.is_init || sha_request_port.is_next)
|->
  sha_core_request_port == sha_core_request_2_i
  ##1
  sha_state &&
  loop_boundary == $past(loop_boundary, 1) &&
  loop_counter == $past(loop_counter, 1) &&
  winternitz_I == $past(winternitz_I, 1) &&
  winternitz_i == $past(winternitz_i, 1) &&
  winternitz_q == $past(winternitz_q, 1);
endproperty

assert_lms_1st_192_to_idle: assert property (disable iff(!reset_n) property_lms_1st_192_to_idle);
property property_lms_1st_192_to_idle;
  lms_1st_192 &&
  sha_core_winternitz192_response_port_vld &&
  (loop_boundary <= loop_counter)
|->
  ##1
  idle &&
  loop_boundary == $past(loop_boundary, 1) &&
  loop_counter == $past(loop_counter, 1) &&
  sha_response_port == $past(sha_response_2_i, 1) &&
  winternitz_I == $past(winternitz_I, 1) &&
  winternitz_i == $past(winternitz_i, 1) &&
  winternitz_q == $past(winternitz_q, 1);
endproperty



assert_lms_1st_192_to_lms_others_192: assert property (disable iff(!reset_n) property_lms_1st_192_to_lms_others_192);
property property_lms_1st_192_to_lms_others_192;
  lms_1st_192 &&
  sha_core_winternitz192_response_port_vld &&
  (loop_boundary > loop_counter)
|->
  ##1
  lms_others_192 &&
  loop_boundary == $past(loop_boundary, 1) &&
  loop_counter == 8'((1 + $past(loop_counter, 1))) &&
  sha_core_winternitz192_request_port.init_command   == $past(sha_core_winternitz192_request_1_i.init_command, 1) &&
  sha_core_winternitz192_request_port.next_command   == $past(sha_core_winternitz192_request_1_i.next_command, 1) &&
  sha_core_winternitz192_request_port.is_sha256_mode == $past(sha_core_winternitz192_request_1_i.is_sha256_mode, 1) &&
  sha_core_winternitz192_request_port.zeroize        == sha_core_winternitz192_request_1_i.zeroize &&
  sha_core_winternitz192_request_port.message_block  == $past(sha_core_winternitz192_request_1_i.message_block, 1) &&
  winternitz_I == $past(winternitz_I, 1) &&
  winternitz_i == $past(winternitz_i, 1) &&
  winternitz_q == $past(winternitz_q, 1);
endproperty


assert_lms_1st_256_to_idle: assert property (disable iff(!reset_n) property_lms_1st_256_to_idle);
property property_lms_1st_256_to_idle;
  lms_1st_256 &&
  sha_core_winternitz256_response_port_vld &&
  (loop_boundary <= loop_counter)
|->
  ##1
  idle &&
  loop_boundary == $past(loop_boundary, 1) &&
  loop_counter == $past(loop_counter, 1) &&
  sha_response_port == $past(sha_response_1_i, 1) &&
  winternitz_I == $past(winternitz_I, 1) &&
  winternitz_i == $past(winternitz_i, 1) &&
  winternitz_q == $past(winternitz_q, 1);
endproperty


assert_lms_1st_256_to_lms_others_256: assert property (disable iff(!reset_n) property_lms_1st_256_to_lms_others_256);
property property_lms_1st_256_to_lms_others_256;
  lms_1st_256 &&
  sha_core_winternitz256_response_port_vld &&
  (loop_boundary > loop_counter)
|->
  ##1
  lms_others_256 &&
  loop_boundary == $past(loop_boundary, 1) &&
  loop_counter == 8'((1 + $past(loop_counter, 1))) &&
  sha_core_winternitz256_request_port.init_command   == $past(sha_core_winternitz256_request_1_i.init_command, 1) &&
  sha_core_winternitz256_request_port.next_command   == $past(sha_core_winternitz256_request_1_i.next_command, 1) &&
  sha_core_winternitz256_request_port.is_sha256_mode == $past(sha_core_winternitz256_request_1_i.is_sha256_mode, 1) &&
  sha_core_winternitz256_request_port.zeroize        == sha_core_winternitz256_request_1_i.zeroize &&
  sha_core_winternitz256_request_port.message_block  == $past(sha_core_winternitz256_request_1_i.message_block, 1) &&
  winternitz_I == $past(winternitz_I, 1) &&
  winternitz_i == $past(winternitz_i, 1) &&
  winternitz_q == $past(winternitz_q, 1);
endproperty


assert_lms_others_192_to_idle: assert property (disable iff(!reset_n) property_lms_others_192_to_idle);
property property_lms_others_192_to_idle;
  lms_others_192 &&
  sha_core_winternitz192_response_port_vld &&
  (loop_boundary <= loop_counter)
|->
  ##1
  idle &&
  loop_boundary == $past(loop_boundary, 1) &&
  loop_counter == $past(loop_counter, 1) &&
  sha_response_port == $past(sha_response_2_i, 1) &&
  winternitz_I == $past(winternitz_I, 1) &&
  winternitz_i == $past(winternitz_i, 1) &&
  winternitz_q == $past(winternitz_q, 1);
endproperty


assert_lms_others_192_to_lms_others_192: assert property (disable iff(!reset_n) property_lms_others_192_to_lms_others_192);
property property_lms_others_192_to_lms_others_192;
  lms_others_192 &&
  sha_core_winternitz192_response_port_vld &&
  (loop_boundary > loop_counter)
|->
  ##1
  lms_others_192 &&
  loop_boundary == $past(loop_boundary, 1) &&
  loop_counter == 8'((1 + $past(loop_counter, 1))) &&
  sha_core_winternitz192_request_port.init_command   == $past(sha_core_winternitz192_request_1_i.init_command, 1) &&
  sha_core_winternitz192_request_port.next_command   == $past(sha_core_winternitz192_request_1_i.next_command, 1) &&
  sha_core_winternitz192_request_port.is_sha256_mode == $past(sha_core_winternitz192_request_1_i.is_sha256_mode, 1) &&
  sha_core_winternitz192_request_port.zeroize        == sha_core_winternitz192_request_1_i.zeroize &&
  sha_core_winternitz192_request_port.message_block  == $past(sha_core_winternitz192_request_1_i.message_block, 1) &&
  winternitz_I == $past(winternitz_I, 1) &&
  winternitz_i == $past(winternitz_i, 1) &&
  winternitz_q == $past(winternitz_q, 1);
endproperty


assert_lms_others_256_to_idle: assert property (disable iff(!reset_n) property_lms_others_256_to_idle);
property property_lms_others_256_to_idle;
  lms_others_256 &&
  sha_core_winternitz256_response_port_vld &&
  (loop_boundary <= loop_counter)
|->
  ##1
  idle &&
  loop_boundary == $past(loop_boundary, 1) &&
  loop_counter == $past(loop_counter, 1) &&
  sha_response_port == $past(sha_response_1_i, 1) &&
  winternitz_I == $past(winternitz_I, 1) &&
  winternitz_i == $past(winternitz_i, 1) &&
  winternitz_q == $past(winternitz_q, 1);
endproperty


assert_lms_others_256_to_lms_others_256: assert property (disable iff(!reset_n) property_lms_others_256_to_lms_others_256);
property property_lms_others_256_to_lms_others_256;
  lms_others_256 &&
  sha_core_winternitz256_response_port_vld &&
  (loop_boundary > loop_counter)
|->
  ##1
  lms_others_256 &&
  loop_boundary == $past(loop_boundary, 1) &&
  loop_counter == 8'((1 + $past(loop_counter, 1))) &&
  sha_core_winternitz256_request_port.init_command   == $past(sha_core_winternitz256_request_1_i.init_command, 1) &&
  sha_core_winternitz256_request_port.next_command   == $past(sha_core_winternitz256_request_1_i.next_command, 1) &&
  sha_core_winternitz256_request_port.is_sha256_mode == $past(sha_core_winternitz256_request_1_i.is_sha256_mode, 1) &&
  sha_core_winternitz256_request_port.zeroize        == sha_core_winternitz256_request_1_i.zeroize &&
  sha_core_winternitz256_request_port.message_block  == $past(sha_core_winternitz256_request_1_i.message_block, 1) &&
  winternitz_I == $past(winternitz_I, 1) &&
  winternitz_i == $past(winternitz_i, 1) &&
  winternitz_q == $past(winternitz_q, 1);
endproperty


assert_sha_to_idle: assert property (disable iff(!reset_n) property_sha_to_idle);
property property_sha_to_idle;
  sha_state &&
  sha_core_response_port_vld &&
  !sha_shared_request_port.is_init &&
  !sha_shared_request_port.is_next
|->
  ##1
  idle &&
  loop_boundary == $past(loop_boundary, 1) &&
  loop_counter == $past(loop_counter, 1) &&
  sha_response_port == $past(sha_response_3_i, 1) &&
  winternitz_I == $past(winternitz_I, 1) &&
  winternitz_i == $past(winternitz_i, 1) &&
  winternitz_q == $past(winternitz_q, 1);
endproperty


assert_sha_to_sha: assert property (disable iff(!reset_n) property_sha_to_sha);
property property_sha_to_sha;
  sha_state &&
  sha_core_response_port_vld &&
  (sha_shared_request_port.is_init || sha_shared_request_port.is_next)
|->
  sha_core_request_port == sha_core_request_3_i
  ##1
  sha_state &&
  loop_boundary == $past(loop_boundary, 1) &&
  loop_counter == $past(loop_counter, 1) &&
  sha_response_port == $past(sha_response_3_i, 1) &&
  winternitz_I == $past(winternitz_I, 1) &&
  winternitz_i == $past(winternitz_i, 1) &&
  winternitz_q == $past(winternitz_q, 1);
endproperty


assert_idle_wait: assert property (disable iff(!reset_n) property_idle_wait);
property property_idle_wait;
  idle &&
  !sha_request_port_vld
|->
  ##1
  idle &&
  loop_boundary == $past(loop_boundary, 1) &&
  loop_counter == $past(loop_counter, 1) &&
  winternitz_I == $past(winternitz_I, 1) &&
  winternitz_i == $past(winternitz_i, 1) &&
  winternitz_q == $past(winternitz_q, 1);
endproperty


assert_lms_1st_192_wait: assert property (disable iff(!reset_n) property_lms_1st_192_wait);
property property_lms_1st_192_wait;
  lms_1st_192 &&
  !sha_core_winternitz192_response_port_vld
|->
  ##1
  lms_1st_192 &&
  loop_boundary == $past(loop_boundary, 1) &&
  loop_counter == $past(loop_counter, 1) &&
  winternitz_I == $past(winternitz_I, 1) &&
  winternitz_i == $past(winternitz_i, 1) &&
  winternitz_q == $past(winternitz_q, 1);
endproperty


assert_lms_1st_256_wait: assert property (disable iff(!reset_n) property_lms_1st_256_wait);
property property_lms_1st_256_wait;
  lms_1st_256 &&
  !sha_core_winternitz256_response_port_vld
|->
  ##1
  lms_1st_256 &&
  loop_boundary == $past(loop_boundary, 1) &&
  loop_counter == $past(loop_counter, 1) &&
  winternitz_I == $past(winternitz_I, 1) &&
  winternitz_i == $past(winternitz_i, 1) &&
  winternitz_q == $past(winternitz_q, 1);
endproperty


assert_lms_others_192_wait: assert property (disable iff(!reset_n) property_lms_others_192_wait);
property property_lms_others_192_wait;
  lms_others_192 &&
  !sha_core_winternitz192_response_port_vld
|->
  ##1
  lms_others_192 &&
  loop_boundary == $past(loop_boundary, 1) &&
  loop_counter == $past(loop_counter, 1) &&
  winternitz_I == $past(winternitz_I, 1) &&
  winternitz_i == $past(winternitz_i, 1) &&
  winternitz_q == $past(winternitz_q, 1);
endproperty


assert_lms_others_256_wait: assert property (disable iff(!reset_n) property_lms_others_256_wait);
property property_lms_others_256_wait;
  lms_others_256 &&
  !sha_core_winternitz256_response_port_vld
|->
  ##1
  lms_others_256 &&
  loop_boundary == $past(loop_boundary, 1) &&
  loop_counter == $past(loop_counter, 1) &&
  winternitz_I == $past(winternitz_I, 1) &&
  winternitz_i == $past(winternitz_i, 1) &&
  winternitz_q == $past(winternitz_q, 1);
endproperty


assert_sha_wait: assert property (disable iff(!reset_n) property_sha_wait);
property property_sha_wait;
  sha_state &&
  !sha_core_response_port_vld
|->
  ##1
  sha_state &&
  loop_boundary == $past(loop_boundary, 1) &&
  loop_counter == $past(loop_counter, 1) &&
  winternitz_I == $past(winternitz_I, 1) &&
  winternitz_i == $past(winternitz_i, 1) &&
  winternitz_q == $past(winternitz_q, 1);
endproperty


endmodule


module fv_sha256_ref_wrapper;


default clocking default_clk @(posedge (sha256.clk)); endclocking


st_Sha256CoreRequest sha_core_request_port;
assign sha_core_request_port = '{
  init_command: (sha256.core_init),
  next_command: (sha256.core_next),
  is_sha256_mode: (sha256.core_mode),
  zeroize: (sha256.zeroize_reg),
  message_block: '{
    0: (sha256.core_block[511:480]),
    1: (sha256.core_block[479:448]),
    2: (sha256.core_block[447:416]),
    3: (sha256.core_block[415:384]),
    4: (sha256.core_block[383:352]),
    5: (sha256.core_block[351:320]),
    6: (sha256.core_block[319:288]),
    7: (sha256.core_block[287:256]),
    8: (sha256.core_block[255:224]),
    9: (sha256.core_block[223:192]),
    10: (sha256.core_block[191:160]),
    11: (sha256.core_block[159:128]),
    12: (sha256.core_block[127:96]),
    13: (sha256.core_block[95:64]),
    14: (sha256.core_block[63:32]),
    15: (sha256.core_block[31:0])
  }
};
st_Sha256CoreResponse sha_core_response_port;
assign sha_core_response_port = '{
  digest_block: '{
    0: (sha256.core_digest[0]),
    1: (sha256.core_digest[1]),
    2: (sha256.core_digest[2]),
    3: (sha256.core_digest[3]),
    4: (sha256.core_digest[4]),
    5: (sha256.core_digest[5]),
    6: (sha256.core_digest[6]),
    7: (sha256.core_digest[7])
  }
};
st_Sha256CoreWinternitz192Request sha_core_winternitz192_request_port;
assign sha_core_winternitz192_request_port = '{
  init_command: (sha256.core_init),
  next_command: (sha256.core_next),
  is_sha256_mode: (sha256.core_mode),
  zeroize: (sha256.zeroize_reg),
  message_block: '{
    I: (sha256.core_block[511:384]),
    q: (sha256.core_block[383:352]),
    i: (sha256.core_block[351:336]),
    j: (sha256.core_block[335:328]),
    tmp: '{
      0: (sha256.core_block[327:296]),
      1: (sha256.core_block[295:264]),
      2: (sha256.core_block[263:232]),
      3: (sha256.core_block[231:200]),
      4: (sha256.core_block[199:168]),
      5: (sha256.core_block[167:136])
    },
    padding: (sha256.core_block[135:0])
  }
};
st_Sha256CoreWinternitz192Response sha_core_winternitz192_response_port;
assign sha_core_winternitz192_response_port = '{
  tmp: '{
    0: (sha256.core_digest[0]),
    1: (sha256.core_digest[1]),
    2: (sha256.core_digest[2]),
    3: (sha256.core_digest[3]),
    4: (sha256.core_digest[4]),
    5: (sha256.core_digest[5])
  }
};
st_Sha256CoreWinternitz256Request sha_core_winternitz256_request_port;
assign sha_core_winternitz256_request_port = '{
  init_command: (sha256.core_init),
  next_command: (sha256.core_next),
  is_sha256_mode: (sha256.core_mode),
  zeroize: (sha256.zeroize_reg),
  message_block: '{
    I: (sha256.core_block[511:384]),
    q: (sha256.core_block[383:352]),
    i: (sha256.core_block[351:336]),
    j: (sha256.core_block[335:328]),
    tmp: '{
      0: (sha256.core_block[327:296]),
      1: (sha256.core_block[295:264]),
      2: (sha256.core_block[263:232]),
      3: (sha256.core_block[231:200]),
      4: (sha256.core_block[199:168]),
      5: (sha256.core_block[167:136]),
      6: (sha256.core_block[135:104]),
      7: (sha256.core_block[103:72])
    },
    padding: (sha256.core_block[71:0])
  }
};
st_Sha256CoreWinternitz256Response sha_core_winternitz256_response_port;
assign sha_core_winternitz256_response_port = '{
  tmp: '{
    0: (sha256.core_digest[0]),
    1: (sha256.core_digest[1]),
    2: (sha256.core_digest[2]),
    3: (sha256.core_digest[3]),
    4: (sha256.core_digest[4]),
    5: (sha256.core_digest[5]),
    6: (sha256.core_digest[6]),
    7: (sha256.core_digest[7])
  }
};
st_Sha256Request sha_request_port;
assign sha_request_port = '{
  is_init: (sha256.hwif_out.SHA256_CTRL.INIT.value),
  is_next: (sha256.hwif_out.SHA256_CTRL.NEXT.value),
  is_sha256_mode: (sha256.hwif_out.SHA256_CTRL.MODE.value),
  is_winternitz: (sha256.hwif_out.SHA256_CTRL.WNTZ_MODE.value),
  winternitz_n_mode: (sha256.hwif_out.SHA256_CTRL.WNTZ_N_MODE.value),
  winternitz_w: (sha256.hwif_out.SHA256_CTRL.WNTZ_W.value),
  winternitz_loop_init: (sha256.hwif_out.SHA256_BLOCK[5].BLOCK.value[15:8]),
  zeroize: (sha256.hwif_out.SHA256_CTRL.ZEROIZE.value || sha256.debugUnlock_or_scan_mode_switch),
  message_block: '{
    0: (sha256.hwif_out.SHA256_BLOCK[0].BLOCK.value),
    1: (sha256.hwif_out.SHA256_BLOCK[1].BLOCK.value),
    2: (sha256.hwif_out.SHA256_BLOCK[2].BLOCK.value),
    3: (sha256.hwif_out.SHA256_BLOCK[3].BLOCK.value),
    4: (sha256.hwif_out.SHA256_BLOCK[4].BLOCK.value),
    5: (sha256.hwif_out.SHA256_BLOCK[5].BLOCK.value),
    6: (sha256.hwif_out.SHA256_BLOCK[6].BLOCK.value),
    7: (sha256.hwif_out.SHA256_BLOCK[7].BLOCK.value),
    8: (sha256.hwif_out.SHA256_BLOCK[8].BLOCK.value),
    9: (sha256.hwif_out.SHA256_BLOCK[9].BLOCK.value),
    10: (sha256.hwif_out.SHA256_BLOCK[10].BLOCK.value),
    11: (sha256.hwif_out.SHA256_BLOCK[11].BLOCK.value),
    12: (sha256.hwif_out.SHA256_BLOCK[12].BLOCK.value),
    13: (sha256.hwif_out.SHA256_BLOCK[13].BLOCK.value),
    14: (sha256.hwif_out.SHA256_BLOCK[14].BLOCK.value),
    15: (sha256.hwif_out.SHA256_BLOCK[15].BLOCK.value)
  }
};
st_Sha256Response sha_response_port;
assign sha_response_port = '{
  digest_block: '{
    0: (sha256.hwif_in.SHA256_DIGEST[0].DIGEST.next),
    1: (sha256.hwif_in.SHA256_DIGEST[1].DIGEST.next),
    2: (sha256.hwif_in.SHA256_DIGEST[2].DIGEST.next),
    3: (sha256.hwif_in.SHA256_DIGEST[3].DIGEST.next),
    4: (sha256.hwif_in.SHA256_DIGEST[4].DIGEST.next),
    5: (sha256.hwif_in.SHA256_DIGEST[5].DIGEST.next),
    6: (sha256.hwif_in.SHA256_DIGEST[6].DIGEST.next),
    7: (sha256.hwif_in.SHA256_DIGEST[7].DIGEST.next)
  }
};
st_Sha256Request sha_shared_request_port;
assign sha_shared_request_port = '{
  is_init: (sha256.hwif_out.SHA256_CTRL.INIT.value),
  is_next: (sha256.hwif_out.SHA256_CTRL.NEXT.value),
  is_sha256_mode: (sha256.hwif_out.SHA256_CTRL.MODE.value),
  is_winternitz: (sha256.hwif_out.SHA256_CTRL.WNTZ_MODE.value),
  winternitz_n_mode: (sha256.hwif_out.SHA256_CTRL.WNTZ_N_MODE.value),
  winternitz_w: (sha256.hwif_out.SHA256_CTRL.WNTZ_W.value),
  winternitz_loop_init: (sha256.hwif_out.SHA256_BLOCK[5].BLOCK.value[15:8]),
  zeroize: (sha256.hwif_out.SHA256_CTRL.ZEROIZE.value || sha256.debugUnlock_or_scan_mode_switch),
  message_block: '{
    0: (sha256.hwif_out.SHA256_BLOCK[0].BLOCK.value),
    1: (sha256.hwif_out.SHA256_BLOCK[1].BLOCK.value),
    2: (sha256.hwif_out.SHA256_BLOCK[2].BLOCK.value),
    3: (sha256.hwif_out.SHA256_BLOCK[3].BLOCK.value),
    4: (sha256.hwif_out.SHA256_BLOCK[4].BLOCK.value),
    5: (sha256.hwif_out.SHA256_BLOCK[5].BLOCK.value),
    6: (sha256.hwif_out.SHA256_BLOCK[6].BLOCK.value),
    7: (sha256.hwif_out.SHA256_BLOCK[7].BLOCK.value),
    8: (sha256.hwif_out.SHA256_BLOCK[8].BLOCK.value),
    9: (sha256.hwif_out.SHA256_BLOCK[9].BLOCK.value),
    10: (sha256.hwif_out.SHA256_BLOCK[10].BLOCK.value),
    11: (sha256.hwif_out.SHA256_BLOCK[11].BLOCK.value),
    12: (sha256.hwif_out.SHA256_BLOCK[12].BLOCK.value),
    13: (sha256.hwif_out.SHA256_BLOCK[13].BLOCK.value),
    14: (sha256.hwif_out.SHA256_BLOCK[14].BLOCK.value),
    15: (sha256.hwif_out.SHA256_BLOCK[15].BLOCK.value)
  }
};
st_Sha256Request sha_request;
assign sha_request = '{
  is_init: (sha256.init_reg),
  is_next: (sha256.next_reg),
  is_sha256_mode: (sha256.mode_reg),
  is_winternitz: (sha256.wntz_mode),
  winternitz_n_mode: (sha256.wntz_n_mode),
  winternitz_w: (sha256.wntz_w_reg),
  winternitz_loop_init: (sha256.wntz_iter),
  zeroize: (sha256.zeroize_reg),
  message_block: '{
    0: (sha256.block_reg[0]),
    1: (sha256.block_reg[1]),
    2: (sha256.block_reg[2]),
    3: (sha256.block_reg[3]),
    4: (sha256.block_reg[4]),
    5: (sha256.block_reg[5]),
    6: (sha256.block_reg[6]),
    7: (sha256.block_reg[7]),
    8: (sha256.block_reg[8]),
    9: (sha256.block_reg[9]),
    10: (sha256.block_reg[10]),
    11: (sha256.block_reg[11]),
    12: (sha256.block_reg[12]),
    13: (sha256.block_reg[13]),
    14: (sha256.block_reg[14]),
    15: (sha256.block_reg[15])
  }
};

// Symbolic digest element
logic [$clog2(8)-1               : 0] digest_position;
assume_stable_digest_position: assume property(##1 $stable(digest_position));

// Symbolic block element
logic [$clog2(sha256.BLOCK_NO)-1 : 0] block_position;
assume_stable_block_position: assume property(##1 $stable(block_position));

fv_sha256 fv_sha256_i (
  .reset_n(sha256.reset_n && sha256.cptra_pwrgood && !$past(sha256.zeroize_reg)),
  .top_reset_n(sha256.reset_n),
  .clk(sha256.clk),

  // Ports
  .sha_core_response_port_vld(sha256.core_digest_valid),
  .sha_core_response_port_rdy(1'b1),
  .sha_core_response_port(sha_core_response_port),

  .sha_core_winternitz192_response_port_vld(sha256.core_digest_valid && !sha256.core_init && !sha256.core_next),
  .sha_core_winternitz192_response_port_rdy(1'b1),
  .sha_core_winternitz192_response_port(sha_core_winternitz192_response_port),

  .sha_core_winternitz256_response_port_vld(sha256.core_digest_valid && !sha256.core_init && !sha256.core_next),
  .sha_core_winternitz256_response_port_rdy(1'b1),
  .sha_core_winternitz256_response_port(sha_core_winternitz256_response_port),

  .sha_request_port_vld(sha256.hwif_out.SHA256_CTRL.INIT.value || sha256.hwif_out.SHA256_CTRL.NEXT.value),
  .sha_request_port_rdy($past(!sha256.reset_n) ? !sha256.hwif_in.SHA256_STATUS.READY.next : sha256.hwif_in.SHA256_STATUS.READY.next),
  .sha_request_port(sha_request_port),

  .sha_shared_request_port(sha_shared_request_port),

  .sha_core_request_port_vld(sha256.core_init),
  .sha_core_request_port(sha_core_request_port),

  .sha_core_winternitz192_request_port_vld(sha256.core_init),
  .sha_core_winternitz192_request_port(sha_core_winternitz192_request_port),

  .sha_core_winternitz256_request_port_vld(sha256.core_init),
  .sha_core_winternitz256_request_port(sha_core_winternitz256_request_port),

  .sha_response_port_vld(sha256.hwif_in.SHA256_STATUS.VALID.next),
  .sha_response_port(sha_response_port),

  // Registers
  .loop_boundary(sha256.wntz_iter_reg),
  .loop_counter(sha256.wntz_j_reg),
  .sha_request(sha_request),
  .winternitz_I(sha256.wntz_prefix[175:48]),
  .winternitz_i(sha256.wntz_prefix[15:0]),
  .winternitz_q(sha256.wntz_prefix[47:16]),

  // States
  .idle($past(sha256.core_ready) && sha256.core_ready && sha256.wntz_fsm == WNTZ_IDLE),
  .lms_1st_256(sha256.wntz_fsm == WNTZ_1ST && sha256.wntz_n_mode_reg),
  .lms_others_256(sha256.wntz_fsm == WNTZ_OTHERS && sha256.wntz_n_mode_reg),
  .lms_1st_192(sha256.wntz_fsm == WNTZ_1ST && !sha256.wntz_n_mode_reg),
  .lms_others_192(sha256.wntz_fsm == WNTZ_OTHERS && !sha256.wntz_n_mode_reg),
  .sha(((sha256.core_init || sha256.core_next) && sha256.wntz_fsm_next == WNTZ_IDLE)),

  // Manually added signals for manually added assertions
  .hwif_in_register_error_reset            (sha256.hwif_in.error_reset_b),
  .hwif_in_winternitz_error                (sha256.hwif_in.intr_block_rf.error_internal_intr_r.error0_sts.hwset),
  .hwif_in_sha_operation_error             (sha256.hwif_in.intr_block_rf.error_internal_intr_r.error1_sts.hwset),
  .hwif_in_error2                          (sha256.hwif_in.intr_block_rf.error_internal_intr_r.error2_sts.hwset),
  .hwif_in_error3                          (sha256.hwif_in.intr_block_rf.error_internal_intr_r.error3_sts.hwset),
  .hwif_in_command_done                    (sha256.hwif_in.intr_block_rf.notif_internal_intr_r.notif_cmd_done_sts.hwset),
  .hwif_in_name0                           (sha256.hwif_in.SHA256_NAME[0].NAME.next),
  .hwif_in_name1                           (sha256.hwif_in.SHA256_NAME[1].NAME.next),
  .hwif_in_version0                        (sha256.hwif_in.SHA256_VERSION[0].VERSION.next),
  .hwif_in_version1                        (sha256.hwif_in.SHA256_VERSION[1].VERSION.next),
  .hwif_in_valid                           (sha256.hwif_in.SHA256_STATUS.READY.next),
  .hwif_in_ready                           (sha256.hwif_in.SHA256_STATUS.VALID.next),
  .hwif_in_wntz_busy                       (sha256.hwif_in.SHA256_STATUS.WNTZ_BUSY.next),
  .hwif_in_digest_clear                    (sha256.hwif_in.SHA256_DIGEST[digest_position].DIGEST.hwclr),
  .hwif_in_block_clear                     (sha256.hwif_in.SHA256_BLOCK[block_position].BLOCK.hwclr),
  .hwif_in_control_zeroize                 (sha256.hwif_out.SHA256_CTRL.ZEROIZE.value),
  .hwif_in_register_error_interrupt        (sha256.hwif_out.intr_block_rf.error_global_intr_r.intr),
  .hwif_in_register_notification_interrupt (sha256.hwif_out.intr_block_rf.notif_global_intr_r.intr),
  .error_interrupt                         (sha256.error_intr),
  .notification_interrupt                  (sha256.notif_intr),
  .error                                   (sha256.err),
  .powergood                               (sha256.cptra_pwrgood),
  .register_read_error                     (sha256.read_error),
  .register_write_error                    (sha256.write_error),
  .valid_register                          (sha256.ready_reg),
  .ready_register                          (sha256.digest_valid_reg),
  .wntz_fsm_next                           (sha256.wntz_fsm_next),
  .wntz_fsm                                (sha256.wntz_fsm),
  .wntz_busy_register                      (sha256.wntz_busy),
  .core_init                               (sha256.core_init),
  .core_next                               (sha256.core_next),
  .core_digest_valid                       (sha256.core_digest_valid),
  .debug_scan_switch                       (sha256.debugUnlock_or_scan_mode_switch),
  .ready_flag_register                     (sha256.ready_flag_reg),
  .digest_register                         (sha256.digest_reg),
  .valid_flag_register                     (sha256.valid_flag_reg),
  .zeroize_register                        (sha256.zeroize_reg)
);


endmodule


bind sha256 fv_sha256_ref_wrapper fv_sha256_ref_wrapper_i();
