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

module entropy_combiner_cov_bind;
  `ifdef FCOV
  // In bypass mode, the ES0 request is the CSRNG request passed through, so only
  // the requests of the combine mode count as pending.
  bind entropy_combiner entropy_combiner_cov_if i_entropy_combiner_cov_if (
    .clk         (clk),
    .reset_n     (reset_n),
    .zeroize     (zeroize),
    .state       (state_q),
    .op_is_kat   (op_is_kat_q),
    .es0_pending (!bypass_active && es0_hw_if_req_o.es_req),
    .es1_pending (!bypass_active && es1_hw_if_req_o.es_req)
  );
  `endif
endmodule
