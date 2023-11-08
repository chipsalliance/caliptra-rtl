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

module keyvault_cov_props
    import kv_defines_pkg::*;
    ();

    `ifndef VERILATOR
    
    //clear_secrets followed by warm reset in the next clk
    //Expectation: Keys cleared before warm reset
    property cover_prop_clear_secr_warm_rst;
        @(posedge kv.clk)
        (kv.kv_reg_hwif_out.CLEAR_SECRETS.wr_debug_values |-> ##[1:$] !kv.rst_b);
    endproperty
    covprop_clear_secr_warmrst: cover property(cover_prop_clear_secr_warm_rst);

    generate
        for(genvar i = 0; i < KV_NUM_KEYS; i++) begin

            //------------------------------------------------------------------------------
            //lock write => clear secrets => warm reset in next clk
            //Expectation: Keys will be flushed since reset is not seen until next clk, locks are reset    
            //------------------------------------------------------------------------------
            property cover_prop_locks_clear_secr_warm_rst;
                @(posedge kv.clk)
                (kv.kv_reg_hwif_out.KEY_CTRL[i].lock_wr && kv.kv_reg_hwif_out.CLEAR_SECRETS.wr_debug_values |-> ##[1:$] !kv.rst_b);
            endproperty
            covprop_lock_clear_secr_warmrst: cover property(cover_prop_locks_clear_secr_warm_rst);

            //------------------------------------------------------------------------------
            //lock write => clear secrets => cold reset in next clk
            //Expectation: Keys will be flushed since reset is not seen until next clk, locks and keys are reset once cold reset happens
            //------------------------------------------------------------------------------
            property cover_prop_locks_clear_secr_cold_rst;
                @(posedge kv.clk)
                (kv.kv_reg_hwif_out.KEY_CTRL[i].lock_wr && kv.kv_reg_hwif_out.CLEAR_SECRETS.wr_debug_values |-> ##[1:$] !kv.cptra_pwrgood);
            endproperty
            covprop_lock_clear_secr_coldrst: cover property(cover_prop_locks_clear_secr_cold_rst);

            //------------------------------------------------------------------------------
            //Check that locks/clear were set before issuing warm reset
            //------------------------------------------------------------------------------
            property cover_prop_lock_wr_warmrst;
                @(posedge kv.clk)
                ($rose(kv.kv_reg_hwif_out.KEY_CTRL[i].lock_wr) |-> ##[0:$] !kv.rst_b);
            endproperty
            covprop_lock_wr_warmrst: cover property(cover_prop_lock_wr_warmrst);

            property cover_prop_lock_use_warmrst;
                @(posedge kv.clk)
                ($rose(kv.kv_reg_hwif_out.KEY_CTRL[i].lock_use) |-> ##[0:$] !kv.rst_b);
            endproperty
            covprop_lock_use_warmrst: cover property(cover_prop_lock_use_warmrst);

            property cover_prop_clear_warmrst;
                @(posedge kv.clk)
                (kv.kv_reg_hwif_out.KEY_CTRL[i].clear |-> ##[0:$] !kv.rst_b);
            endproperty
            covprop_clear_warmrst: cover property(cover_prop_clear_warmrst);

            //------------------------------------------------------------------------------
            //Check that locks/clear were set before issuing cold reset
            //------------------------------------------------------------------------------
            property cover_prop_lock_wr_coldrst;
                @(posedge kv.clk)
                ($rose(kv.kv_reg_hwif_out.KEY_CTRL[i].lock_wr) |-> ##[0:$] !kv.cptra_pwrgood);
            endproperty
            covprop_lock_wr_coldrst: cover property(cover_prop_lock_wr_coldrst);

            property cover_prop_lock_use_coldrst;
                @(posedge kv.clk)
                ($rose(kv.kv_reg_hwif_out.KEY_CTRL[i].lock_use) |-> ##[0:$] !kv.cptra_pwrgood);
            endproperty
            covprop_lock_use_coldrst: cover property(cover_prop_lock_use_coldrst);

            property cover_prop_clear_coldrst;
                @(posedge kv.clk)
                (kv.kv_reg_hwif_out.KEY_CTRL[i].clear |-> ##[0:$] !kv.cptra_pwrgood);
            endproperty
            covprop_clear_coldrst: cover property(cover_prop_clear_coldrst);

            //------------------------------------------------------------------------------
            //Check that locks/clear were set before issuing core reset
            //------------------------------------------------------------------------------
            property cover_prop_lock_wr_corerst;
                @(posedge kv.clk)
                ($rose(kv.kv_reg_hwif_out.KEY_CTRL[i].lock_wr) |-> ##[0:$] !kv.core_only_rst_b);
            endproperty
            covprop_lock_wr_corerst: cover property(cover_prop_lock_wr_corerst);

            property cover_prop_lock_use_corerst;
                @(posedge kv.clk)
                ($rose(kv.kv_reg_hwif_out.KEY_CTRL[i].lock_use) |-> ##[0:$] !kv.core_only_rst_b);
            endproperty
            covprop_lock_use_corerst: cover property(cover_prop_lock_use_corerst);

            property cover_prop_clear_corerst;
                @(posedge kv.clk)
                (kv.kv_reg_hwif_out.KEY_CTRL[i].clear |-> ##[0:$] !kv.core_only_rst_b);
            endproperty
            covprop_clear_corerst: cover property(cover_prop_clear_corerst);
        end
    endgenerate

    `endif

endmodule