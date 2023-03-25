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
// Description:
//   This file defines firmware that is initialized to memory at the testbench
//   level (outside Caliptra) and loaded to Caliptra RV memory via mailbox
//   firmware update.
//   Firmware defined here will execute from ICCM

#include "caliptra_defines.h"
#include "riscv_hw_if.h"
#include "aes.h"
#include "doe.h"
#include "ecc.h"
#include "hmac.h"
#include "keyvault.h"
#include "sha256.h"
#include "sha512.h"
#include "soc_ifc.h"
#include <string.h>
#include <stdint.h>
#include "printf.h"

/* --------------- Global symbols/typedefs --------------- */
extern uintptr_t STACK;

/* --------------- Global vars --------------- */
volatile char*                    stdout           = (char *)STDOUT;
#ifdef CPT_VERBOSITY
    enum printf_verbosity             verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity             verbosity_g = LOW;
#endif


/* --------------- Function Definitions --------------- */
void caliptra_fmc() {
    // Set stack pointer value pointed in linker script
    __asm__ volatile ("la sp, %0"
                      : /* output */
                      : "i" ((uintptr_t) &STACK) /* input: */
                      : /* clobbers */);

    mbox_op_s op;
    void (* iccm_fn) (void) = (void*) RV_ICCM_SADR + MBOX_ICCM_OFFSET_RT;

    VPRINTF(MEDIUM, "----------------------------------\n");
    VPRINTF(LOW,    "- Caliptra Validation FMC!!\n"       );
    VPRINTF(MEDIUM, "----------------------------------\n");

    // TODO
    // Do other stuff before jumping immediately to Runtime image?

    //read the mbox command
    op = soc_ifc_read_mbox_cmd();
    if (op.cmd == MBOX_CMD_RT_UPDATE) {
        //TODO: Enhancement - Check the integrity of the firmware

        // Load RT FW from mailbox
        soc_ifc_mbox_fw_flow(op);

        // Lock ICCM
        soc_ifc_set_iccm_lock();
    }
    else {
        VPRINTF(FATAL, "Received invalid mailbox command from SOC! Expected 0x%x, got 0x%x\n", MBOX_CMD_RT_UPDATE, op.cmd);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    // Jump to ICCM (this is the Runtime image, a.k.a. Section 1)
    iccm_fn();

    // Should never get here
    VPRINTF(FATAL, "----------------------------------\n");
    VPRINTF(FATAL, " Reached end of FMC FW image unexpectedly! \n");
    VPRINTF(FATAL, "----------------------------------\n");
    SEND_STDOUT_CTRL(0x1);
    while(1);
}
