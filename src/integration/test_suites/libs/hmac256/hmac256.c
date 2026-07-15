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
#include "hmac256.h"
#include "caliptra_isr.h"

extern volatile caliptra_intr_received_s cptra_intr_rcv;

void wait_for_hmac256_intr(void) {
    VPRINTF(LOW, "HMAC256 flow in progress...\n");
    while ((cptra_intr_rcv.hmac256_error == 0) & (cptra_intr_rcv.hmac256_notif == 0)) {
        __asm__ volatile ("wfi");
        for (uint16_t slp = 0; slp < 100; slp++) {
            __asm__ volatile ("nop");
        }
    }
    VPRINTF(LOW, "Received HMAC256 notif/err intr with status = %d/ %d\n",
            cptra_intr_rcv.hmac256_notif, cptra_intr_rcv.hmac256_error);
}

void hmac256_zeroize(void) {
    VPRINTF(LOW, "HMAC256 zeroize flow.\n");
    lsu_write_32(CLP_HMAC256_REG_HMAC256_CTRL,
                 (1 << HMAC256_REG_HMAC256_CTRL_ZEROIZE_LOW) &
                  HMAC256_REG_HMAC256_CTRL_ZEROIZE_MASK);
}

void write_hmac256_reg(volatile uint32_t *base_addr,
                       uint32_t *data, uint32_t size) {
    for (uint32_t i = 0; i < size; i++) {
        base_addr[i] = data[i];
    }
}

void hmac256_wait_ready(void) {
    while ((lsu_read_32(CLP_HMAC256_REG_HMAC256_STATUS) &
            HMAC256_REG_HMAC256_STATUS_READY_MASK) == 0);
}

void hmac256_wait_valid(void) {
    while ((lsu_read_32(CLP_HMAC256_REG_HMAC256_STATUS) &
            HMAC256_REG_HMAC256_STATUS_VALID_MASK) == 0);
}

void hmac256_load_inputs(uint32_t *key, uint32_t *block, uint32_t *lfsr_seed) {
    write_hmac256_reg((volatile uint32_t *)CLP_HMAC256_REG_HMAC256_KEY_0,       key,       HMAC256_KEY_SIZE);
    write_hmac256_reg((volatile uint32_t *)CLP_HMAC256_REG_HMAC256_BLOCK_0,     block,     HMAC256_BLOCK_SIZE);
    write_hmac256_reg((volatile uint32_t *)CLP_HMAC256_REG_HMAC256_LFSR_SEED_0, lfsr_seed, HMAC256_LFSR_SEED_SIZE);
}

void hmac256_ctrl_write(uint32_t ctrl_bits, uint8_t mode) {
    uint32_t reg = ctrl_bits |
                   ((uint32_t)mode << HMAC256_REG_HMAC256_CTRL_MODE_LOW);
    lsu_write_32(CLP_HMAC256_REG_HMAC256_CTRL, reg);
}

void hmac256_flow(hmac256_io key, hmac256_io block, hmac256_io lfsr_seed,
                  hmac256_io tag, BOOL init, BOOL last, BOOL mode) {
    volatile uint32_t *reg_ptr;
    uint32_t hmac256_tag[HMAC256_TAG_SIZE];
    uint8_t  tag_dwords = mode ? HMAC256_TAG_SIZE : HMAC224_TAG_SIZE;

    while ((lsu_read_32(CLP_HMAC256_REG_HMAC256_STATUS) &
            HMAC256_REG_HMAC256_STATUS_READY_MASK) == 0) {
    }

    reg_ptr = (uint32_t *) CLP_HMAC256_REG_HMAC256_KEY_0;
    write_hmac256_reg(reg_ptr, key.data, key.data_size);

    reg_ptr = (uint32_t *) CLP_HMAC256_REG_HMAC256_LFSR_SEED_0;
    write_hmac256_reg(reg_ptr, lfsr_seed.data, lfsr_seed.data_size);

    reg_ptr = (uint32_t *) CLP_HMAC256_REG_HMAC256_BLOCK_0;
    write_hmac256_reg(reg_ptr, block.data, block.data_size);

    uint32_t ctrl_val = 0;
    if (init) ctrl_val |= HMAC256_REG_HMAC256_CTRL_INIT_MASK;
    else      ctrl_val |= HMAC256_REG_HMAC256_CTRL_NEXT_MASK;
    if (last) ctrl_val |= HMAC256_REG_HMAC256_CTRL_LAST_MASK;
    if (mode) ctrl_val |= HMAC256_REG_HMAC256_CTRL_MODE_MASK;
    lsu_write_32(CLP_HMAC256_REG_HMAC256_CTRL, ctrl_val);

    wait_for_hmac256_intr();

    if (!last) {
        VPRINTF(LOW, "HMAC256 intermediate block accepted\n");
        return;
    }

    reg_ptr = (uint32_t *) CLP_HMAC256_REG_HMAC256_TAG_0;
    for (uint8_t i = 0; i < tag_dwords; i++) {
        hmac256_tag[i] = reg_ptr[i];
    }

    for (uint8_t i = 0; i < tag_dwords; i++) {
        if (hmac256_tag[i] != tag.data[i]) {
            VPRINTF(FATAL, "HMAC256 TAG[%d] mismatch: got %08x expected %08x\n",
                    i, hmac256_tag[i], tag.data[i]);
            SEND_STDOUT_CTRL(0x1);
            while (1);
        }
    }
    VPRINTF(LOW, "HMAC256 TAG matched (%d dwords)\n", tag_dwords);
}
