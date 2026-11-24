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
// Check DCLS enable transitions in soc_ifc_tb and soc_ifc_tb_ss.
task dcls_hw_config_test;
    strq_t reglist;
    dword_t predicted;
    dword_t expected_fields;
    dword_t mode_mask;
    WordTransaction expected_config;
    begin
        reglist.push_back("CPTRA_HW_CONFIG");
        mode_mask = dword_t'(`SOC_IFC_REG_CPTRA_HW_CONFIG_DCLS_EN_MASK |
                            `SOC_IFC_REG_CPTRA_HW_CONFIG_OCP_LOCK_MODE_EN_MASK |
                            `SOC_IFC_REG_CPTRA_HW_CONFIG_SUBSYSTEM_MODE_EN_MASK);
        simulate_caliptra_boot();
        // Seed the scoreboard entry for this read-only register.
        expected_config = new();
        expected_config.update_byname("CPTRA_HW_CONFIG", get_initval("CPTRA_HW_CONFIG"), 1);
        sb.record_entry(expected_config, SET_DIRECT);
        for (int ocp = 0; ocp < 2; ocp++) begin
            for (int step = 0; step < 4; step++) begin
                @(negedge clk_tb);
                ocp_lock_en_tb = 1'(ocp);
                dcls_en_tb = 1'(step % 2);
                predicted = update_CPTRA_HW_CONFIG();
                expected_fields = dcls_en_tb ? dword_t'(`SOC_IFC_REG_CPTRA_HW_CONFIG_DCLS_EN_MASK) : '0;
                if (subsystem_mode_tb) begin
                    expected_fields |= dword_t'(`SOC_IFC_REG_CPTRA_HW_CONFIG_SUBSYSTEM_MODE_EN_MASK);
                    if (ocp_lock_en_tb)
                        expected_fields |= dword_t'(`SOC_IFC_REG_CPTRA_HW_CONFIG_OCP_LOCK_MODE_EN_MASK);
                end
                assert ((predicted & mode_mask) === expected_fields) else begin
                    $error("DCLS HW_CONFIG prediction disagrees with profile/input values");
                    error_ctr++;
                end
                assert (get_initval("CPTRA_HW_CONFIG") === predicted) else begin
                    $error("Active HW_CONFIG initial-value dictionary was not updated");
                    error_ctr++;
                end
                repeat (3) @(posedge clk_tb);
                tc_ctr++;
                read_regs(GET_AXI, reglist, -1, 1);
                read_regs(GET_AHB, reglist, -1, 1);
                $display("DCLS HW_CONFIG profile=%0b OCP=%0b DCLS=%0b verified",
                         subsystem_mode_tb, ocp_lock_en_tb, dcls_en_tb);
            end
        end
        error_ctr += sb.err_count;
    end
endtask
