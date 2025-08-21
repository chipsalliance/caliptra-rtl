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


module aes_cov_bind;
    `ifdef FCOV
    bind aes_clp_wrapper aes_cov_if #(
        .AHB_ADDR_WIDTH(`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_AES)),
        .AHB_DATA_WIDTH(`CALIPTRA_AHB_HDATA_SIZE),
        .CIF_DATA_WIDTH(32) // FIXME hardcoded value?
        )
        i_aes_cov_if (.*);
    `endif
endmodule
