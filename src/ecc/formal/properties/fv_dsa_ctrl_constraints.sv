// -------------------------------------------------
// Contact: contact@lubis-eda.com
// Author: Tobias Ludwig, Michael Schwarz
// -------------------------------------------------
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
module fv_dsa_ctrl_constraints_m 
    import ecc_params_pkg::*;
    import ecc_dsa_uop_pkg::*;
    import ecc_reg_pkg::*;
    import kv_defines_pkg::*; #(
        parameter PM_DLY = 5,
        parameter SCA_DLY = 3,
        parameter HMAC_DLY = 4
    )
    (
    // Clock and reset.
    input wire           clk,
    input wire           reset_n,
    input wire           cptra_pwrgood,

    // Reg ports.
    input ecc_reg__out_t hwif_out,
    input ecc_reg__in_t hwif_in,

    // KV interface
    input kv_read_t [1:0] kv_read,
    input kv_write_t kv_write,
    input kv_rd_resp_t [1:0] kv_rd_resp,
    input kv_wr_resp_t kv_wr_resp,

    //PCR Signing
    input pcr_signing_t pcr_signing_data,

    // Interrupts (from ecc_reg)
    input logic error_intr,
    input logic notif_intr,
    input  logic debugUnlock_or_scan_mode_switch
    );

    default clocking default_clk @(posedge clk); endclocking

    ////////////////////////////////////////////////////
    // stability of the primary inputs
    ////////////////////////////////////////////////////

    logic fv_end_step;
    logic fv_new_inp;
    always_comb begin: end_step
        fv_end_step = (ecc_dsa_ctrl.prog_cntr == DSA_KG_E-1)||(ecc_dsa_ctrl.prog_cntr == DSA_SGN_E-1)||(ecc_dsa_ctrl.prog_cntr == DSA_VER_E-1);
    end
    always_ff @(posedge clk, negedge reset_n) begin
        if(!reset_n) begin
            fv_new_inp <= 0;
        end
        else if (hwif_out.ECC_CTRL.ZEROIZE.value || debugUnlock_or_scan_mode_switch) begin
          fv_new_inp <= 0;
        end
        else begin
            if(hwif_in.ecc_ready) begin 
                fv_new_inp <= 1;
            end
            else if(fv_end_step) begin
                fv_new_inp <= 0;
            end
        end
    end




    property stable_input_p(inp);
       fv_new_inp |-> $stable(inp);
    endproperty

for (genvar word=0; word < 12; word++)begin 
    stable_privkey: assume property(stable_input_p(hwif_out.ECC_PRIVKEY_IN[11-word].PRIVKEY_IN.value));
    stable_seed: assume property(stable_input_p(hwif_out.ECC_SEED[11-word].SEED.value));
    stable_nonce: assume property(stable_input_p(hwif_out.ECC_NONCE[11-word].NONCE.value));
    stable_msg: assume property(stable_input_p(hwif_out.ECC_MSG[11-word].MSG.value));
    stable_pubkx: assume property(stable_input_p(hwif_out.ECC_PUBKEY_X[11-word].PUBKEY_X.value));
    stable_pubky: assume property(stable_input_p(hwif_out.ECC_PUBKEY_Y[11-word].PUBKEY_Y.value));
    stable_r: assume property(stable_input_p(hwif_out.ECC_SIGN_R[11-word].SIGN_R.value));
    stable_s: assume property(stable_input_p(hwif_out.ECC_SIGN_S[11-word].SIGN_S.value));
    stable_IV: assume property(stable_input_p(hwif_out.ECC_IV[11-word].IV.value));
    stable_cmd: assume property(stable_input_p(hwif_out.ECC_CTRL.CTRL.value));
    stable_pcr: assume property(stable_input_p(hwif_out.ECC_CTRL.PCR_SIGN.value));
end


    property no_cmd_when_not_ready_p;
        (ecc_dsa_ctrl.prog_cntr < DSA_NOP)
        |->
        hwif_out.ECC_CTRL.CTRL.value == '0;
    endproperty

    no_cmd_a: assume property(no_cmd_when_not_ready_p);

`ifndef TOP

    ////////////////////////////////////////////////////
    // Reduced working model for busy in order to check the 
    // design doesn't have deadlock
    ////////////////////////////////////////////////////

    logic [5:0] pm_cntr;
    logic [5:0] sca_cntr;
    logic [5:0] hmac_cntr;
    logic pm_busy;
    logic sca_busy;
    logic hmc_busy;

    always_ff @(posedge clk, negedge reset_n) begin
        if(!reset_n) begin
            pm_busy <= 0;
            hmc_busy <= 0;
            sca_busy <= 0;
            pm_cntr <= 0;
            hmac_cntr <= 0;
            sca_cntr <= 0;
        end
        else if (hwif_out.ECC_CTRL.ZEROIZE.value || debugUnlock_or_scan_mode_switch) begin
            pm_busy <= 0;
            hmc_busy <= 0;
            sca_busy <= 0;
            pm_cntr <= 0;
            hmac_cntr <= 0;
            sca_cntr <= 0;
        end
        else begin
            if(ecc_dsa_ctrl.pm_cmd_reg!=no_cmd)begin
                pm_cntr <= PM_DLY;
            end
            if(ecc_dsa_ctrl.hmac_init) begin
                hmac_cntr <= HMAC_DLY;
            end
           
            if(ecc_dsa_ctrl.scalar_sca_en) begin
                sca_cntr <= SCA_DLY;
            end
            if(pm_cntr > 0) begin
                pm_busy <= 1;
                pm_cntr <= pm_cntr-1;
            end
            if(pm_cntr == 0) begin
                pm_busy <= 0;
            end
            if(sca_cntr > 0) begin
                sca_busy <= 1;
                sca_cntr <= sca_cntr-1;
            end
            if(sca_cntr == 0) begin
                sca_busy <= 0;
            end
            if(hmac_cntr > 0) begin
                hmc_busy <= 1;
                hmac_cntr <= hmac_cntr-1;
            end
            if(hmac_cntr == 0) begin
                hmc_busy <= 0;
            end
        end
    end


    pm_busy_assume: assume property(ecc_dsa_ctrl.pm_busy_o == pm_busy);
    sca_busy_assume: assume property(ecc_dsa_ctrl.scalar_sca_busy_o == sca_busy);
    hmac_busy_assume: assume property(ecc_dsa_ctrl.hmac_busy == hmc_busy);

`endif


endmodule

bind ecc_dsa_ctrl fv_dsa_ctrl_constraints_m fv_dsa_ctrl_constraints (
    .clk(clk),
        .reset_n(reset_n),
        .cptra_pwrgood(cptra_pwrgood),

        .hwif_out(hwif_out),
        .hwif_in(hwif_in),

        .kv_read(kv_read),
        .kv_rd_resp(kv_rd_resp),
        .kv_write(kv_write),
        .kv_wr_resp(kv_wr_resp),
        .pcr_signing_data(pcr_signing_data),
        
        .error_intr(error_intr),
        .notif_intr(notif_intr),
        .debugUnlock_or_scan_mode_switch(debugUnlock_or_scan_mode_switch)
    );