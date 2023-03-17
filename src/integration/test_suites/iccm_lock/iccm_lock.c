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
#include "riscv-csr.h"
#include "veer-csr.h"
#include "riscv_hw_if.h"
#include <string.h>
#include <stdint.h>
#include "printf.h"


//int whisperPrintf(const char* format, ...);
//#define ee_printf whisperPrintf


volatile char* stdout = (char *)STDOUT;
volatile uint32_t intr_count;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

extern uintptr_t iccm_code0_start, iccm_code0_end;
extern uintptr_t iccm_code1_start, iccm_code1_end;
extern uintptr_t iccm_code2_start, iccm_code2_end;
static uint32_t persistent_exec_cnt __attribute__ ((section(".dccm.persistent"))) = 0; // Allocate in .dccm
static uint8_t  persistent_is_second_pass __attribute__ ((section(".dccm.persistent"))) = 0; // Allocate in .dccm
static uint8_t  persistent_nmi_expected __attribute__ ((section(".dccm.persistent"))) = 0; // Allocate in .dccm

void execute_first_pass_from_iccm (void) __attribute__ ((aligned(4),section (".data_iccm0")));
void execute_second_pass_from_iccm (void) __attribute__ ((aligned(4),section (".data_iccm1")));
void execute_fatal_from_iccm (void) __attribute__ ((aligned(4),section (".data_iccm2")));

void main(void) {
        int argc=0;
        char *argv[1];

        uint32_t * ICCM = (uint32_t *) RV_ICCM_SADR;

        volatile uint32_t * soc_ifc_error_iccm_blocked_ctr = (uint32_t *) (CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_ICCM_BLOCKED_INTR_COUNT_R);
        volatile uint32_t * soc_ifc_iccm_lock              = (uint32_t *) (CLP_SOC_IFC_REG_INTERNAL_ICCM_LOCK);
        volatile uint32_t * soc_ifc_nmi_vector             = (uint32_t *) (CLP_SOC_IFC_REG_INTERNAL_NMI_VECTOR);

        uint32_t * code_word = 0;
        uint32_t * iccm_dest = ICCM;
        void (* iccm_fn) (void) = (void*) ICCM;

        VPRINTF(LOW, "----------------------------------\nICCM Lock Test from VeeR EL2  !!\n----------------------------------\n");

        // Setup the interrupt CSR configuration
        init_interrupts();
        *soc_ifc_nmi_vector = RV_ICCM_SADR;

        // Initialize the globals
        intr_count = 0;
        persistent_nmi_expected = 0;

        // Check ICCM_LOCK is not currently set
        if (*soc_ifc_iccm_lock & SOC_IFC_REG_INTERNAL_ICCM_LOCK_LOCK_MASK == SOC_IFC_REG_INTERNAL_ICCM_LOCK_LOCK_MASK) {
            VPRINTF(ERROR, "ERROR: ICCM_LOCK set unexpectedly!\n");
            SEND_STDOUT_CTRL( 0x1);
            while(1);
        }

        // Copy code section from Mailbox to ICCM
        //   1. Check if this is the first or Nth pass through main (by reading from a non-reset location e.g. in Mailbox)
        //   2. If 1st:
        //     a. Copy section (A) to ICCM
        //   3. Else:
        //     a. Copy section (B) to ICCM (different print)
        if (persistent_is_second_pass) {
            code_word = (uint32_t *) &iccm_code1_start;
            VPRINTF(LOW, "Copying code from %x [through %x] to %x\n", (uintptr_t) code_word, &iccm_code1_end, (uintptr_t) iccm_dest);
            while (code_word < (uint32_t *) &iccm_code1_end) {
                VPRINTF(ALL, "at %x: %x\n", (uintptr_t) code_word, *code_word);
                *iccm_dest++ = *code_word++;
            }
        } else {
            code_word = (uint32_t *) &iccm_code0_start;
            VPRINTF(LOW, "Copying code from %x [through %x] to %x\n", (uintptr_t) code_word, &iccm_code0_end, (uintptr_t) iccm_dest);
            while (code_word < (uint32_t *) &iccm_code0_end) {
                VPRINTF(ALL, "at %x: %x\n", (uintptr_t) code_word, *code_word);
                *iccm_dest++ = *code_word++;
            }
        }

        // Check interrupt count (die if !0)
        if (intr_count) {
            VPRINTF(ERROR, "ERROR: Detected interrupt while copying code to unlocked ICCM!\n");
            SEND_STDOUT_CTRL( 0x1);
        }

        // Execute code from ICCM
        iccm_fn();

        // Code from ICCM (1) increments persistent_exec_cnt. If > 1, then die (it executed > once)
        // Code from ICCM (2) does not increment.
        if (persistent_exec_cnt > 1) {
            VPRINTF(ERROR, "ERROR: First pass code executed from ICCM during second pass (after reset)!\n");
            SEND_STDOUT_CTRL(0x1);
        }

        // Lock ICCM Writes
        *soc_ifc_iccm_lock = SOC_IFC_REG_INTERNAL_ICCM_LOCK_LOCK_MASK;
        if (*soc_ifc_iccm_lock & SOC_IFC_REG_INTERNAL_ICCM_LOCK_LOCK_MASK != SOC_IFC_REG_INTERNAL_ICCM_LOCK_LOCK_MASK) {
            VPRINTF(ERROR, "ERROR: Failed to set ICCM_LOCK!\n");
            SEND_STDOUT_CTRL(0x1);
        }


         // Read ICCM here to see if there is any error when its being read while ICCM is being locked and that reads are getting expected data
        iccm_dest = ICCM;
        if (persistent_is_second_pass) {
            code_word = (uint32_t *) &iccm_code1_start;
            VPRINTF(LOW,"Comparing second pass of the copy code from %x [through %x] to %x\n", (uintptr_t) code_word, &iccm_code1_end, (uintptr_t) iccm_dest);
            while (code_word < (uint32_t *) &iccm_code1_end) {
                VPRINTF(ALL,"at %x: %x\n", (uintptr_t) iccm_dest, *iccm_dest);
                if(*iccm_dest++ != *code_word++) {
                    VPRINTF(ERROR,"ERROR: Reads mismatched on second pass\n");
                    SEND_STDOUT_CTRL( 0x1);
                }
            }
        } else {
            code_word = (uint32_t *) &iccm_code0_start;
            VPRINTF(LOW,"Comparing first pass of the copy code from %x [through %x] to %x\n", (uintptr_t) code_word, &iccm_code0_end, (uintptr_t) iccm_dest);
            while (code_word < (uint32_t *) &iccm_code0_end) {
                VPRINTF(ALL,"at %x: %x\n", (uintptr_t) iccm_dest, *iccm_dest);
                if(*iccm_dest++ != *code_word++) {
                    VPRINTF(ERROR,"ERROR: Reads mismatched on first pass\n");
                    SEND_STDOUT_CTRL( 0x1);
                }
            }
        }

        // Copy error code section from Mailbox to ICCM
        //   - This code section will kill the sim with error if executed
        //   - Copy of this code section is expected to fail since ICCM_LOCK=1
        //     which will result in AHB error response and NMI
        code_word = (uint32_t *) &iccm_code2_start;
        iccm_dest = ICCM;
        VPRINTF(LOW, "Copying code from %x [through %x] to %x\n", (uintptr_t) code_word, &iccm_code2_end, (uintptr_t) iccm_dest);
        persistent_nmi_expected = 1;
        while (code_word < (uint32_t *) &iccm_code2_end) {
            VPRINTF(ALL, "at %x: %x\n", (uintptr_t) code_word, *code_word);
            *iccm_dest++ = *code_word++;
        }

        // The above code should cause NMI resulting in the end of the firmware
        // run. If we get to this point, it's an error and we should kill the sim
        VPRINTF(ERROR, "ERROR: Did not receive expected NMI while writing to Locked ICCM!\n");
        SEND_STDOUT_CTRL( 0x1);
        while(1);

        return;
}

void execute_first_pass_from_iccm (void) {
    // If we got here via NMI (D-Bus Store Error), document the iteration status
    // and reset the core
    if ((csr_read_mcause() & MCAUSE_NMI_BIT_MASK) == MCAUSE_NMI_BIT_MASK) {
        VPRINTF(LOW, "**** NMI ****\n");
        intr_count++;
        if (!persistent_nmi_expected) {
            VPRINTF(ERROR, "ERROR: Entered NMI with mcause [0x%x] while not expecting an error!\n", csr_read_mcause());
            VPRINTF(ERROR, "       mepc [0x%x]\n", csr_read_mepc());
            SEND_STDOUT_CTRL(0x1);
            while(1);
        } else {
            persistent_nmi_expected = 0;
        }
        //   1. Check if this is the first or Nth pass through main (by reading from a non-reset location e.g. in Mailbox)
        //   2. If 1st:
        //     a. Set the second pass flag in some non-reset location (in the Mailbox)
        //     b. Trigger core reset
        //   3. Else:
        //     a. End simulation with fail message
        if (persistent_is_second_pass) {
            VPRINTF(ERROR, "ERROR: Entered first pass subroutine while expecting to enter second pass!\n");
            SEND_STDOUT_CTRL(0x1);
            while(1);
        } else {
            VPRINTF(LOW, "At the end of first pass through ICCM LOCK test: resetting the core!\n");
            persistent_is_second_pass = 1;
            lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET, SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET_CORE_RST_MASK);
            while(1);
        }
    }
    //   1. Check if this is the first or Nth pass through main (by reading from a non-reset location e.g. in Mailbox)
    //   2. If 1st:
    //     a. Increment value in some non-reset location (in the Mailbox)
    //   3. Else:
    //     a. End simulation with fail message
    if (persistent_is_second_pass) {
        VPRINTF(ERROR, "ERROR: Entered first pass subroutine while expecting to enter second pass!\n");
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
    VPRINTF(LOW, "First pass through ICCM LOCK test!\n");
    persistent_exec_cnt++;
}

void execute_second_pass_from_iccm (void) {
    // If we got here via expected NMI (D-Bus Store Error), document the
    // iteration status and end the test with success
    if ((csr_read_mcause() & MCAUSE_NMI_BIT_MASK) == MCAUSE_NMI_BIT_MASK) {
        VPRINTF(LOW, "**** NMI ****\n");
        intr_count++;
        if (!persistent_nmi_expected) {
            VPRINTF(ERROR, "ERROR: Entered NMI with mcause [0x%x] while not expecting an error!\n", csr_read_mcause());
            SEND_STDOUT_CTRL(0x1);
            while(1);
        } else {
            persistent_nmi_expected = 0;
        }
        //   1. Check if this is the first or second pass through main (by reading from a non-reset location e.g. in Mailbox)
        //   2. If 1st:
        //     a. End simulation with fail message
        //   3. Else:
        //     a. End simulation with success message
        if (persistent_is_second_pass) {
            VPRINTF(LOW, "Success! Reached end of ICCM lock firmware during second iteration\n");
            SEND_STDOUT_CTRL(0xff);
            while(1);
        } else {
            VPRINTF(ERROR, "ERROR: Entered second pass subroutine unexpectedly!\n");
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }
    }
    VPRINTF(LOW, "Second pass through ICCM LOCK test!\n");
}

void execute_fatal_from_iccm (void) {
    // This ensures that even if only a single instruction gets copied to ICCM
    // from this routine, something happens
    __asm__ volatile goto ("j %l[bad_code]\n"
                           ".rept 1000\n\tnop\n\t.endr\n"
                           : /* output */
                           : /* input: */
                           : /* clobbers */
                           : bad_code /* goto_labels */);
    bad_code:
    VPRINTF(FATAL, "Error! Fatal subroutine is executing from ICCM even though locked when written!\n");
    SEND_STDOUT_CTRL(0x1); // Kills simulation with error
    while(1);
}
