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

#include "caliptra_defines.h"
#include "printf.h"
#include "sha256.h"
#include "caliptra_isr.h"

extern volatile caliptra_intr_received_s cptra_intr_rcv;

void wait_for_sha256_intr(uint32_t notif, uint32_t error){
    VPRINTF(LOW, "SHA256 flow in progress...\n");
    while(((cptra_intr_rcv.sha256_error & error) != error) || ((cptra_intr_rcv.sha256_notif & notif) != notif)){
        __asm__ volatile ("wfi"); // "Wait for interrupt"
        // Sleep during SHA256 operation to allow ISR to execute and show idle time in sims
        for (uint16_t slp = 0; slp < 100; slp++) {
            __asm__ volatile ("nop"); // Sleep loop as "nop"
        }
    };
    if (error) {
        VPRINTF(LOW, "Received SHA256 err intr with status = %d\n", cptra_intr_rcv.sha256_error);
    }
    else {
        VPRINTF(LOW, "Received SHA256 notif intr with status = %d\n", cptra_intr_rcv.sha256_notif);
    }
    cptra_intr_rcv.sha256_notif &= ~notif;
    cptra_intr_rcv.sha256_error &= ~error;
}

void sha256_zeroize(){
    VPRINTF(LOW, "SHA256 zeroize flow.\n");
    lsu_write_32(CLP_SHA256_REG_SHA256_CTRL, (1 << SHA256_REG_SHA256_CTRL_ZEROIZE_LOW) & SHA256_REG_SHA256_CTRL_ZEROIZE_MASK);
}

void sha256_flow(sha256_io block, uint8_t mode, uint8_t wntz_mode, uint8_t wntz_w, uint8_t wntz_n, sha256_io digest){
    volatile uint32_t * reg_ptr;
    uint8_t offset;
    uint8_t fail_cmd = 0x1;
    uint32_t sha256_digest [8];

    // wait for SHA to be ready
    while((lsu_read_32(CLP_SHA256_REG_SHA256_STATUS) & SHA256_REG_SHA256_STATUS_READY_MASK) == 0);

    // Write SHA256 block
    reg_ptr = (uint32_t*) CLP_SHA256_REG_SHA256_BLOCK_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_SHA256_REG_SHA256_BLOCK_15) {
        *reg_ptr++ = block.data[offset++];
    }

    // Enable SHA256 core 
    VPRINTF(LOW, "Enable SHA256\n");
    lsu_write_32(CLP_SHA256_REG_SHA256_CTRL, SHA256_REG_SHA256_CTRL_INIT_MASK | 
                                            ((mode << SHA256_REG_SHA256_CTRL_MODE_LOW) & SHA256_REG_SHA256_CTRL_MODE_MASK) |
                                            ((wntz_mode << SHA256_REG_SHA256_CTRL_WNTZ_MODE_LOW) & SHA256_REG_SHA256_CTRL_WNTZ_MODE_MASK) |
                                            ((wntz_w << SHA256_REG_SHA256_CTRL_WNTZ_W_LOW) & SHA256_REG_SHA256_CTRL_WNTZ_W_MASK) |
                                            ((wntz_n << SHA256_REG_SHA256_CTRL_WNTZ_N_MODE_LOW) & SHA256_REG_SHA256_CTRL_WNTZ_N_MODE_MASK));
    
    // wait for SHA to be valid
    wait_for_sha256_intr(SHA256_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK, 0);
    reg_ptr = (uint32_t *) CLP_SHA256_REG_SHA256_DIGEST_0;
    VPRINTF(LOW, "Load DIGEST data from SHA256\n");
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_SHA256_REG_SHA256_DIGEST_7) {
        sha256_digest[offset] = *reg_ptr;
        if (sha256_digest[offset] != digest.data[offset]) {
            VPRINTF(LOW, "At offset [%d], sha_digest data mismatch!\n", offset);
            VPRINTF(LOW, "Actual   data: 0x%x\n", sha256_digest[offset]);
            VPRINTF(LOW, "Expected data: 0x%x\n", digest.data[offset]);
            SEND_STDOUT_CTRL(fail_cmd);
            while(1);
        }
        reg_ptr++;
        offset++;
    }

}

void sha256_error_flow(sha256_io block, uint8_t mode, uint8_t next, uint8_t wntz_mode, uint8_t wntz_w, uint8_t wntz_n, sha256_io digest, uint32_t error) {
    volatile uint32_t * reg_ptr;
    uint8_t offset;
    uint8_t fail_cmd = 0x1;
    uint32_t sha256_digest [8];

    // wait for SHA to be ready
    while((lsu_read_32(CLP_SHA256_REG_SHA256_STATUS) & SHA256_REG_SHA256_STATUS_READY_MASK) == 0);

    // Write SHA256 block
    reg_ptr = (uint32_t*) CLP_SHA256_REG_SHA256_BLOCK_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_SHA256_REG_SHA256_BLOCK_15) {
        *reg_ptr++ = block.data[offset++];
    }

    // init and next triggers error1 bit. Check to make sure correct error arg is given
    if (next & (error == SHA256_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR0_STS_MASK)) {
        VPRINTF(LOW, "Error1 is expected when init and next are asserted at the same time. Check args given to sha256_error_flow()\n");
        SEND_STDOUT_CTRL(fail_cmd);
    }
    else if (~next & (error == SHA256_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR1_STS_MASK)) {
        VPRINTF(LOW, "Error0 is expected for invalid wntz_mode or w. Check args given to sha256_error_flow()\n");
        SEND_STDOUT_CTRL(fail_cmd);
    }

    // Enable SHA256 core 
    VPRINTF(LOW, "Enable SHA256\n");
    lsu_write_32(CLP_SHA256_REG_SHA256_CTRL, SHA256_REG_SHA256_CTRL_INIT_MASK | 
                                            ((next << SHA256_REG_SHA256_CTRL_NEXT_LOW) & SHA256_REG_SHA256_CTRL_NEXT_MASK) |
                                            ((mode << SHA256_REG_SHA256_CTRL_MODE_LOW) & SHA256_REG_SHA256_CTRL_MODE_MASK) |
                                            ((wntz_mode << SHA256_REG_SHA256_CTRL_WNTZ_MODE_LOW) & SHA256_REG_SHA256_CTRL_WNTZ_MODE_MASK) |
                                            ((wntz_w << SHA256_REG_SHA256_CTRL_WNTZ_W_LOW) & SHA256_REG_SHA256_CTRL_WNTZ_W_MASK) |
                                            ((wntz_n << SHA256_REG_SHA256_CTRL_WNTZ_N_MODE_LOW) & SHA256_REG_SHA256_CTRL_WNTZ_N_MODE_MASK));
    
    // wait for SHA to trig error
    wait_for_sha256_intr(0, error);

}

void sha256_flow_wntz_rand(uint8_t mode) {
    // wait for SHA to be ready
    while((lsu_read_32(CLP_SHA256_REG_SHA256_STATUS) & SHA256_REG_SHA256_STATUS_READY_MASK) == 0);

    // Enable SHA256 core 
    VPRINTF(LOW, "Enable SHA256\n");
    // lsu_write_32(CLP_SHA256_REG_SHA256_CTRL, SHA256_REG_SHA256_CTRL_INIT_MASK | 
    //                                         ((mode << SHA256_REG_SHA256_CTRL_MODE_LOW) & SHA256_REG_SHA256_CTRL_MODE_MASK));
                                            // SHA256_REG_SHA256_CTRL_WNTZ_MODE_MASK |
                                            // ((wntz_w << SHA256_REG_SHA256_CTRL_WNTZ_W_LOW) & SHA256_REG_SHA256_CTRL_WNTZ_W_MASK) |
                                            // ((wntz_n << SHA256_REG_SHA256_CTRL_WNTZ_N_MODE_LOW) & SHA256_REG_SHA256_CTRL_WNTZ_N_MODE_MASK));
    
    // wait for SHA to be valid
    wait_for_sha256_intr(SHA256_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK, 0);
}
