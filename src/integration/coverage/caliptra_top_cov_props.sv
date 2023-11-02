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

// This file contains properties that define various sequences of events in KV

module caliptra_top_cov_props();

    `ifndef VERILATOR
    
            //------------------------------------------------------------------------------
            //Check that WDT was enabled before issuing warm reset
            //------------------------------------------------------------------------------
            property cover_prop_wdt_t1_warmrst;
                @(posedge soc_ifc_top1.i_wdt.clk)
                ($rose(soc_ifc_top1.i_wdt.timer1_en) |-> ##[0:$] !soc_ifc_top1.i_wdt.cptra_rst_b);
            endproperty
            covprop_wdt_t1_warmrst: cover property(cover_prop_wdt_t1_warmrst);

            property cover_prop_wdt_t2_warmrst;
                @(posedge soc_ifc_top1.i_wdt.clk)
                ($rose(soc_ifc_top1.i_wdt.timer2_en) |-> ##[0:$] !soc_ifc_top1.i_wdt.cptra_rst_b);
            endproperty
            covprop_wdt_t2_warmrst: cover property(cover_prop_wdt_t2_warmrst);

            //------------------------------------------------------------------------------
            //Check that locks/clear were set before issuing cold reset
            //------------------------------------------------------------------------------
            property cover_prop_wdt_t1_coldrst;
                @(posedge soc_ifc_top1.clk)
                ($rose(soc_ifc_top1.i_wdt.timer1_en) |=> ##[0:$] !soc_ifc_top1.cptra_pwrgood);
            endproperty
            covprop_wdt_t1_coldrst: cover property(cover_prop_wdt_t1_coldrst);

            property cover_prop_wdt_t2_coldrst;
                @(posedge soc_ifc_top1.clk)
                ($rose(soc_ifc_top1.i_wdt.timer2_en) |=> ##[0:$] !soc_ifc_top1.cptra_pwrgood);
            endproperty
            covprop_wdt_t2_coldrst: cover property(cover_prop_wdt_t2_coldrst);

    `endif

endmodule