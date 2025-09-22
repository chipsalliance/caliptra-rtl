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


module clp_abr_top_cov_bind;
    `ifdef FCOV
    bind abr_top clp_abr_top_cov_if i_clp_abr_top_cov_if(.*);
    //put this back when the two cover if's are distinct
    //bind abr_top abr_top_cov_if i_abr_top_cov_if(.*);
    `endif
endmodule
