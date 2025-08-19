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

module kv_write_rule_check
import kv_defines_pkg::*;
(
    input logic clk,
    input logic rst_b,

    input  var kv_write_filter_metrics_t write_metrics,
    output logic                         write_allow
);


    // --------------------------------------- //
    // Signals                                 //
    // --------------------------------------- //
    struct packed {
        logic aes_only_to_key_release; // NO crypto other than AES can write to key release slot
        logic std_to_std; // Standard slot inputs can only write to standard outputs
        logic lock_to_lock; // OCP Lock slot inputs can only write to OCP Lock outputs
        logic aes_dec_to_rt_obf_key;
    } rule_fail;


    // --------------------------------------- //
    // Rules                                   //
    // --------------------------------------- //
    // IF (OCP_LOCK_IN_PROGRESS)
    //   THEN (NO CRYPTO may write to OCP_LOCK_KEY_RELEASE_KV_SLOT, other than AES)
    always_comb begin
        rule_fail.aes_only_to_key_release = write_metrics.ocp_lock_in_progress &&
                                            // Any write source indicated (other than AES) causes rule failure
                                          |(write_metrics.kv_write_src & ~(KV_NUM_WRITE'(1) << KV_WRITE_IDX_AES)) &&
                                            write_metrics.kv_write_entry == OCP_LOCK_KEY_RELEASE_KV_SLOT;
    end

    // IF (OCP_LOCK_IN_PROGRESS) AND (input inside [STD region])
    //   THEN (dest = [STD region])
    always_comb begin
        rule_fail.std_to_std = write_metrics.ocp_lock_in_progress &&
                             ((write_metrics.kv_data0_present &&
                               write_metrics.kv_data0_entry   inside {[KV_STANDARD_SLOT_LOW:KV_STANDARD_SLOT_HI]}) ||
                              (write_metrics.kv_data1_present &&
                               write_metrics.kv_data1_entry   inside {[KV_STANDARD_SLOT_LOW:KV_STANDARD_SLOT_HI]})) &&
                             !(write_metrics.kv_write_entry inside {[KV_STANDARD_SLOT_LOW:KV_STANDARD_SLOT_HI]});
    end

    // IF (OCP_LOCK_IN_PROGRESS) AND (input inside [LOCK region])
    //   THEN (dest = [LOCK region])
    always_comb begin
        rule_fail.lock_to_lock = write_metrics.ocp_lock_in_progress &&
                               ((write_metrics.kv_data0_present &&
                                 write_metrics.kv_data0_entry   inside {[KV_OCP_LOCK_SLOT_LOW:KV_OCP_LOCK_SLOT_HI]}) ||
                                (write_metrics.kv_data1_present &&
                                 write_metrics.kv_data1_entry   inside {[KV_OCP_LOCK_SLOT_LOW:KV_OCP_LOCK_SLOT_HI]})) &&
                               !(write_metrics.kv_write_entry inside {[KV_OCP_LOCK_SLOT_LOW:KV_OCP_LOCK_SLOT_HI]});
    end

    // NOTE: This rule also needs to work in reverse, i.e. if AES is doing a KV write, then
    //       all of these conditions must be met.
    //       Therefore, this implementation fails if any condition is not met.
    // IF (OCP_LOCK_IN_PROGRESS) AND (AES ECB decrypt) AND (key = OCP_LOCK_RT_OBF_KEY_KV_SLOT)
    //   THEN (dest = OCP_LOCK_KEY_RELEASE_KV_SLOT)
    // ELSEIF (AES any other op)
    //   THEN (dest = FW)
    // NOTE: aes.sv enforces this rule by blocking the register output when kv write is expected due to input criteria being met
    always_comb begin
        rule_fail.aes_dec_to_rt_obf_key = write_metrics.kv_write_src[KV_WRITE_IDX_AES] &&
                                          (!write_metrics.ocp_lock_in_progress ||
                                           !write_metrics.aes_decrypt_ecb_op ||
                                           !write_metrics.kv_data0_present ||
                                            write_metrics.kv_data0_entry != OCP_LOCK_RT_OBF_KEY_KV_SLOT ||
                                            write_metrics.kv_write_entry != OCP_LOCK_KEY_RELEASE_KV_SLOT);
    end


    // --------------------------------------- //
    // Output                                  //
    // --------------------------------------- //
    // Register the rule-check status; all of the input metrics will be stabilized long before dest write data
    // becomes valid, so registering the output status reduces combinatorial depth
    always_ff@(posedge clk or negedge rst_b) begin
        if (!rst_b) begin
            write_allow <= 1'b0;
        end
        else begin
            write_allow <= ~|rule_fail;
        end
    end

endmodule
