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

module entropy_src_cov_bind;
  `ifdef FCOV
  bind entropy_src_core entropy_src_cov_if i_entropy_src_cov_if (
    .clk_i         (clk_i),
    .rst_ni        (rst_ni),
    .zeroize       (zeroize),
    .zeroize_reg   (reg2hw.entropy_src_ctrl.qe && reg2hw.entropy_src_ctrl.q),
    .zeroize_pin   (debugUnlock_or_scan_mode_switch),
    .main_sm_state (u_entropy_src_main_sm.state_q),
    .ack_sm_state  (u_entropy_src_ack_sm.state_q)
  );
  `endif
endmodule
