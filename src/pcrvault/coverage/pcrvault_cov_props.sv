// SPDX-License-Identifier: Apache-2.0
// Copyright 2019 Western Digital Corporation or its affiliates.
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

module pcrvault_cov_props
    import pv_defines_pkg::*;
    ();

    `ifndef VERILATOR
    
    generate
        for(genvar i = 0; i < PV_NUM_PCR; i++) begin

            //clear followed by warm reset in the next clk
            //Expectation: PCRs cleared before warm reset
            property cover_prop_clear_warm_rst;
                @(posedge pv.clk)
                (pv.pv_reg_hwif_out.PCR_CTRL[i].clear |-> ##[1:$] !pv.rst_b);
            endproperty
            covprop_clear_warmrst: cover property(cover_prop_clear_warm_rst);
        
            //locks, followed by clear, followed by warm reset in the next clk
            //Expectation: Unlocked PCRs cleared before warm reset, locks cleared on warm reset
            property cover_prop_lock_clear_warm_rst;
                @(posedge pv.clk)
                (pv.pv_reg_hwif_out.PCR_CTRL[i].lock |-> ##[0:$] pv.pv_reg_hwif_out.PCR_CTRL[i].clear |-> ##[1:$] !pv.rst_b);
            endproperty
            covprop_lock_clear_warmrst: cover property(cover_prop_lock_clear_warm_rst);
        
            //locks, followed by clear, followed by cold reset in the next clk
            //Expectation: Unlocked PCRs cleared before cold reset, everything cleared on cold reset
            property cover_prop_lock_clear_cold_rst;
                @(posedge pv.clk)
                (pv.pv_reg_hwif_out.PCR_CTRL[i].lock |-> ##[0:$] pv.pv_reg_hwif_out.PCR_CTRL[i].clear |-> ##[1:$] !pv.cptra_pwrgood);
            endproperty
            covprop_lock_clear_coldrst: cover property(cover_prop_lock_clear_cold_rst);
        end
    endgenerate

  `endif

endmodule