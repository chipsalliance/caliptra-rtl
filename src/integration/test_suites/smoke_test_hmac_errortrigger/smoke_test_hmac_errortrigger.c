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
#include "caliptra_isr.h"
#include "riscv_hw_if.h"
#include "riscv-csr.h"
#include <string.h>
#include <stdint.h>
#include "printf.h"
#include "hmac.h"

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif
volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count       = 0;
volatile uint32_t  rst_count __attribute__((section(".dccm.persistent"))) = 0;

volatile caliptra_intr_received_s cptra_intr_rcv = {0};


void main() {

    //Call interrupt init
    init_interrupts();

    // Entry message
    VPRINTF(LOW, "----------------------------------\n");
    VPRINTF(LOW, " HMAC error_trigger smoke test !!\n"         );
    VPRINTF(LOW, "----------------------------------\n");

    volatile uint32_t * reg_ptr;
    uint8_t key_slot = 5;
    uint8_t key_inject_cmd;

    if(rst_count == 0) {
        VPRINTF(LOW, " ***** HMAC512 key_zero_error !!\n");
        // wait for HMAC to be ready
        while((lsu_read_32(CLP_HMAC_REG_HMAC512_STATUS) & HMAC_REG_HMAC512_STATUS_READY_MASK) == 0);

        //inject zero to kv key reg (in RTL)
        key_inject_cmd = 0xa8;
        SEND_STDOUT_CTRL(key_inject_cmd);

        // Program KEY Read from key_kv_id
        lsu_write_32(CLP_HMAC_REG_HMAC512_KV_RD_KEY_CTRL, HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_EN_MASK |
                                                        ((key_slot << HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_ENTRY_LOW) & HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_ENTRY_MASK));

        // Check that HMAC KEY is loaded
        while((lsu_read_32(CLP_HMAC_REG_HMAC512_KV_RD_KEY_STATUS) & HMAC_REG_HMAC512_KV_RD_KEY_STATUS_VALID_MASK) == 0);

        // Enable HMAC core
        lsu_write_32(CLP_HMAC_REG_HMAC512_CTRL, HMAC_REG_HMAC512_CTRL_INIT_MASK |
                                                    (HMAC512_MODE << HMAC_REG_HMAC512_CTRL_MODE_LOW));
        // wait for HMAC process to be done
        wait_for_hmac_intr();
        if ((cptra_intr_rcv.hmac_error == 0)){
            VPRINTF(ERROR, "\nHMAC key_zero error is not detected.\n");
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }
        hmac_zeroize();
        //Issue warm reset
        rst_count++;
        SEND_STDOUT_CTRL(0xf6);
    }
    else if(rst_count == 1) {
        VPRINTF(LOW, " ***** HMAC384 key_zero_error !!\n");
        // wait for HMAC to be ready
        while((lsu_read_32(CLP_HMAC_REG_HMAC512_STATUS) & HMAC_REG_HMAC512_STATUS_READY_MASK) == 0);

        //inject zero to kv key reg (in RTL)
        key_inject_cmd = 0xa8;
        SEND_STDOUT_CTRL(key_inject_cmd);

        // Program KEY Read from key_kv_id
        lsu_write_32(CLP_HMAC_REG_HMAC512_KV_RD_KEY_CTRL, HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_EN_MASK |
                                                        ((key_slot << HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_ENTRY_LOW) & HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_ENTRY_MASK));

        // Check that HMAC KEY is loaded
        while((lsu_read_32(CLP_HMAC_REG_HMAC512_KV_RD_KEY_STATUS) & HMAC_REG_HMAC512_KV_RD_KEY_STATUS_VALID_MASK) == 0);

        // Enable HMAC core
        lsu_write_32(CLP_HMAC_REG_HMAC512_CTRL, HMAC_REG_HMAC512_CTRL_NEXT_MASK |
                                                    (HMAC384_MODE << HMAC_REG_HMAC512_CTRL_MODE_LOW));
        // wait for HMAC process to be done
        wait_for_hmac_intr();
        if ((cptra_intr_rcv.hmac_error == 0)){
            VPRINTF(ERROR, "\nHMAC key_zero error is not detected.\n");
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }
        hmac_zeroize();
        //Issue warm reset
        rst_count++;
        SEND_STDOUT_CTRL(0xf6);
    }
    if(rst_count == 2) {
        VPRINTF(LOW, " ***** HMAC key_mode_error !!\n");
        
        //inject hmac384_key to kv key reg (in RTL)
        key_inject_cmd = 0xa0 + (key_slot & 0x7);
        SEND_STDOUT_CTRL(key_inject_cmd);

        // wait for HMAC to be ready
        while((lsu_read_32(CLP_HMAC_REG_HMAC512_STATUS) & HMAC_REG_HMAC512_STATUS_READY_MASK) == 0);

        // Program KEY Read from key_kv_id
        lsu_write_32(CLP_HMAC_REG_HMAC512_KV_RD_KEY_CTRL, HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_EN_MASK |
                                                        ((key_slot << HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_ENTRY_LOW) & HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_ENTRY_MASK));

        // Check that HMAC KEY is loaded
        while((lsu_read_32(CLP_HMAC_REG_HMAC512_KV_RD_KEY_STATUS) & HMAC_REG_HMAC512_KV_RD_KEY_STATUS_VALID_MASK) == 0);

        // Enable HMAC core with wrong MODE
        lsu_write_32(CLP_HMAC_REG_HMAC512_CTRL, HMAC_REG_HMAC512_CTRL_INIT_MASK |
                                                    (HMAC512_MODE << HMAC_REG_HMAC512_CTRL_MODE_LOW));
        // wait for HMAC process to be done
        wait_for_hmac_intr();
        if ((cptra_intr_rcv.hmac_error == 0)){
            VPRINTF(ERROR, "\nHMAC key_mode_error is not detected.\n");
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }
        hmac_zeroize();
    }
    // Write 0xff to STDOUT for TB to terminate test.
    SEND_STDOUT_CTRL( 0xff);
    while(1);

}
