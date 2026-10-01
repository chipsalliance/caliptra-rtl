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
        
            //lock and clear active simultaneously, followed by warm reset
            //Expectation: PCRs cleared before warm reset, locks cleared on warm reset
            property cover_prop_lock_clear_warm_rst;
                @(posedge pv.clk)
                (pv.pv_reg_hwif_out.PCR_CTRL[i].lock && pv.pv_reg_hwif_out.PCR_CTRL[i].clear |-> ##[1:$] !pv.rst_b);
            endproperty
            covprop_lock_clear_warmrst: cover property(cover_prop_lock_clear_warm_rst);
        
            //lock and clear active simultaneously, followed by cold reset
            //Expectation: PCRs cleared before cold reset, everything cleared on cold reset
            property cover_prop_lock_clear_cold_rst;
                @(posedge pv.clk)
                (pv.pv_reg_hwif_out.PCR_CTRL[i].lock && pv.pv_reg_hwif_out.PCR_CTRL[i].clear |-> ##[1:$] !pv.cptra_pwrgood);
            endproperty
            covprop_lock_clear_coldrst: cover property(cover_prop_lock_clear_cold_rst);

            //lock set followed by core-only reset
            //Expectation: lock clears on core_only_rst_b, but data survives (cptra_pwrgood stays up)
            //During core reset, fw_update_rst_window opens the swwel bypass, but the MCU is in
            //reset so no AHB clear can fire — the bypass exists for the HW boot FSM, not SW.
            property cover_prop_lock_core_rst;
                @(posedge pv.clk)
                ($rose(pv.pv_reg_hwif_out.PCR_CTRL[i].lock) |-> ##[0:$] !pv.core_only_rst_b);
            endproperty
            covprop_lock_core_rst: cover property(cover_prop_lock_core_rst);

            //crypto write to same entry concurrent with clear (same cycle)
            //Expectation: write data wins over hwclr in RTL when both fire simultaneously
            property cover_prop_write_during_clear;
                @(posedge pv.clk)
                (pv.pv_reg_hwif_out.PCR_CTRL[i].clear &&
                 pv.pv_write[0].write_en && (pv.pv_write[0].write_entry == i));
            endproperty
            covprop_write_during_clear: cover property(cover_prop_write_during_clear);
        end
    endgenerate

  `endif

endmodule
