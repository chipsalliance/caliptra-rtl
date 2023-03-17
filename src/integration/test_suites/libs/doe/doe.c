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

#include "doe.h"
#include "caliptra_reg.h"
#include "riscv_hw_if.h"
#include "printf.h"

/**
 * @brief Initialize deobfuscation engine
 * @param iv_data_uds Init Vector for UDS. Pointer to 4-entry array of 32-bit values
 * @param iv_data_fe Init Vector for Field Entropy. Pointer to 4-entry array of 32-bit values
 */
void doe_init(uint32_t * iv_data_uds, uint32_t * iv_data_fe, uint32_t kv_dest_fe) {
    uint8_t offset;
    uint32_t* reg_ptr;

    VPRINTF(LOW, "DOE: Init\n");

    // Write IV
    VPRINTF(MEDIUM,"DOE: Writing UDS IV\n");
    reg_ptr = (uint32_t*) CLP_DOE_REG_DOE_IV_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_DOE_REG_DOE_IV_3) {
        *reg_ptr++ = iv_data_uds[offset++];
    }

    //start UDS and store in KV0
    VPRINTF(MEDIUM,"DOE: Starting UDS Deobfuscation flow\n");
    lsu_write_32(CLP_DOE_REG_DOE_CTRL, DOE_UDS << DOE_REG_DOE_CTRL_CMD_LOW);

    // Check that UDS flow is done
    while((lsu_read_32(CLP_DOE_REG_DOE_STATUS) & DOE_REG_DOE_STATUS_VALID_MASK) == 0);
    VPRINTF(MEDIUM,"DOE: UDS Deobfuscation flow complete\n");

    // Write IV
    VPRINTF(MEDIUM,"DOE: Writing Field Entropy IV\n");
    reg_ptr = (uint32_t*) CLP_DOE_REG_DOE_IV_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_DOE_REG_DOE_IV_3) {
        *reg_ptr++ = iv_data_fe[offset++];
    }

    //start FE and store in KV6/7
    VPRINTF(MEDIUM,"DOE: Starting Field Entropy Deobfuscation flow\n");
    lsu_write_32(CLP_DOE_REG_DOE_CTRL, (DOE_FE << DOE_REG_DOE_CTRL_CMD_LOW) |
                                       (kv_dest_fe << DOE_REG_DOE_CTRL_DEST_LOW));

    // Check that FE flow is done
    while((lsu_read_32(CLP_DOE_REG_DOE_STATUS) & DOE_REG_DOE_STATUS_VALID_MASK) == 0);
    VPRINTF(MEDIUM,"DOE: Field Entropy Deobfuscation flow complete\n");

}

void doe_clear_secrets() {
    // Clear Secrets
    VPRINTF(MEDIUM,"DOE: Clear secrets\n");
    lsu_write_32(CLP_DOE_REG_DOE_CTRL, DOE_CLEAR_OBF_SECRETS);
}
