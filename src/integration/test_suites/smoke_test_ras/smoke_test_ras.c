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

// DESCRIPTION:
//   Test Reliability, Availability, Servicability (RAS) features in
//   Caliptra SOC Interface
//   Test objectives:
//     1. Demonstrate all reported events can be properly detected and reported
//        to uC
//     2. Demonstrate correct reset behavior for FATAL and NON_FATAL events
//        (a) FATAL events must result in a Caliptra system reset (by SOC i.e.
//            the testbench)
//        (b) Following a reset, no further interrupt observed; SOC manually
//            clears ERROR reg
//        (c) NON_FATAL events should be observed and cleared by SOC
//     3. Demonstrate correct behavior of the error mask registers, which should
//        prevent error assertion
//        (a) When masked, ERROR register bits should be set, not generate an
//            interrupt, and then the uC should reset them
//
//   Several of the above features may only be properly validated in concert
//   with Testbench level code that confirms signal behavior and drives resets
//   as required.
//   That behavior is requested by FW via writes to GENERIC_OUTPUT_WIRES (which
//   currently operates as STDOUT in sims)
//   The TB may also signal response activity by driving GENERIC_INPUT_WIRES
//   (resulting in interrupt to uC)
//

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "riscv_hw_if.h"
#include "riscv-interrupts.h"
#include "riscv-csr.h"
#include "veer-csr.h"
#include <string.h>
#include <stdint.h>
#include "printf.h"

////////////////////////////////////////////////////////////////////
// Typedefs
//

// Matches the STDOUT code value as decoded in caliptra_top_tb_services
enum ecc_error_mode_type {
    ERROR_NONE  = 0xe4,
    ICCM_SINGLE = 0xe0,
    ICCM_DOUBLE = 0xe1,
    DCCM_SINGLE = 0xe2,
    DCCM_DOUBLE = 0xe3,
    MBOX_SINGLE = 0xfd,
    MBOX_DOUBLE = 0xfe
};

// Value driven by TB to GENERIC_INPUT_WIRES
enum tb_resp_value {
    MBOX_NON_FATAL_OBSERVED         = 0x600dab1e,
    PROT_NO_LOCK_NON_FATAL_OBSERVED = 0x600dbabe,
    PROT_OOO_NON_FATAL_OBSERVED     = 0x600dcafe,
    ICCM_FATAL_OBSERVED             = 0xdeadaca1,
    DCCM_FATAL_OBSERVED             = 0xdeadbeef,
    NMI_FATAL_OBSERVED              = 0xdeadc0a7,
    DMA_ERROR_OBSERVED              = 0xfadebadd,
    ERROR_NONE_SET                  = 0xba5eba11, /* default value for a test with no activity observed by TB */
};

enum mask_config {
    WITH_MASK,
    NO_MASK
};

enum read_config {
    FROM_IFU,
    FROM_LSU,
};
enum dccm_read_config {
    DATA_LOAD,
    FORCE_DMA
};

enum recovery_config {
    WARM_RESET,
    FORCE_UNLOCK
};

enum test_status {
    SUCCESS          =       0,
    INTR_COUNT_0     = 1 <<  0,
    INTR_COR_COUNT_0 = 1 <<  1,
    INTR_UNC_COUNT_0 = 1 <<  2,
    BAD_EXCP_CODE    = 1 <<  3,
    UNEXP_ARG        = 1 <<  4,
    BAD_CPTRA_SIG    = 1 <<  5,
    INV_STATE        = 1 <<  6,
};

enum test_progress {
    NOT_STARTED,
    SKIPPED,
    RUN_NOT_CHECKED,
    RUN_AND_FAILED,
    RUN_AND_PASSED
};

// Used to index into the global array of test progress
// TODO Test the FW FATAL/NON_FATAL regs
enum test_list {
    MBOX_SRAM_ECC_SINGLE_UNMASKED     ,
    MBOX_SRAM_ECC_DOUBLE_UNMASKED     ,
    MBOX_SRAM_ECC_SINGLE_MASKED       ,
    MBOX_SRAM_ECC_DOUBLE_MASKED       ,
    ICCM_SRAM_ECC_SINGLE_IFU_UNMASKED ,
    ICCM_SRAM_ECC_DOUBLE_IFU_UNMASKED ,
    ICCM_SRAM_ECC_SINGLE_IFU_MASKED   ,
    ICCM_SRAM_ECC_DOUBLE_IFU_MASKED   ,
    ICCM_SRAM_ECC_SINGLE_LSU_UNMASKED ,
    ICCM_SRAM_ECC_DOUBLE_LSU_UNMASKED ,
    ICCM_SRAM_ECC_SINGLE_LSU_MASKED   ,
    ICCM_SRAM_ECC_DOUBLE_LSU_MASKED   ,
    DCCM_SRAM_ECC_SINGLE_LOAD_UNMASKED,
    DCCM_SRAM_ECC_DOUBLE_LOAD_UNMASKED,
    DCCM_SRAM_ECC_SINGLE_LOAD_MASKED  ,
    DCCM_SRAM_ECC_DOUBLE_LOAD_MASKED  ,
    DCCM_SRAM_ECC_SINGLE_DMA_UNMASKED ,
    DCCM_SRAM_ECC_DOUBLE_DMA_UNMASKED ,
    DCCM_SRAM_ECC_SINGLE_DMA_MASKED   ,
    DCCM_SRAM_ECC_DOUBLE_DMA_MASKED   ,
    NMI_UNMASKED                      ,
    NMI_MASKED                        ,
    PROT_NO_LOCK_UNMASKED             ,
    PROT_NO_LOCK_MASKED               ,
    PROT_OOO_UNMASKED                 ,
    PROT_OOO_MASKED                   ,
    TEST_COUNT                        ,
};
enum boot_count_list {
    BEFORE_FIRST_ICCM_FAILURE  = 1,
    BEFORE_SECOND_ICCM_FAILURE    ,
    BEFORE_THIRD_ICCM_FAILURE     ,
    BEFORE_FIRST_DCCM_FAILURE     ,
    BEFORE_SECOND_DCCM_FAILURE    ,
    BEFORE_FIRST_NMI_FAILURE      ,
    BEFORE_SECOND_NMI_FAILURE     ,
    BEFORE_THIRD_NMI_FAILURE      ,
    AFTER_THIRD_NMI_FAILURE       ,
    AFTER_FIRST_MBOX_OOO_FAILURE  ,
    AFTER_SECOND_MBOX_OOO_FAILURE
};
//enum boot_count_list {
//    RUN_MBOX_AND_FIRST_ICCM_SRAM_ECC  = 1,
//    RUN_AND_CHK_ICCM_SRAM_ECC_MASKED     ,
//    RUN_DCCM_SRAM_ECC_UNMASKED           ,
//    RUN_AND_CHK_DCCM_SRAM_ECC_MASKED     ,
//    RUN_AND_CHK_NMI_MASKED               ,
//    RUN_AND_CHK_MBOX_PROT_ERROR          ,
//};

////////////////////////////////////////////////////////////////////
// Globals
//
extern uintptr_t iccm_code0_start, iccm_code0_end;
volatile char* stdout = (char *)STDOUT;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = HIGH;
#endif

volatile uint32_t intr_count;
volatile caliptra_intr_received_s cptra_intr_rcv = {
    .doe_error        = 0,
    .doe_notif        = 0,
    .ecc_error        = 0,
    .ecc_notif        = 0,
    .hmac_error       = 0,
    .hmac_notif       = 0,
    .kv_error         = 0,
    .kv_notif         = 0,
    .sha512_error     = 0,
    .sha512_notif     = 0,
    .sha256_error     = 0,
    .sha256_notif     = 0,
    .qspi_error       = 0,
    .qspi_notif       = 0,
    .uart_error       = 0,
    .uart_notif       = 0,
    .i3c_error        = 0,
    .i3c_notif        = 0,
    .soc_ifc_error    = 0,
    .soc_ifc_notif    = 0,
    .sha512_acc_error = 0,
    .sha512_acc_notif = 0,
};
volatile rv_exception_struct_s exc_flag __attribute__((section(".dccm.persistent"))); // WARNING: if DCCM ERROR injection is enabled, writes to this may be corrupted
volatile uint32_t boot_count __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t generic_input_wires_0_before_rst __attribute__((section(".dccm.persistent")));
// Track test progress across resets by allocating the variable in DCCM, which
// is initialized only once at time 0
enum test_progress test_progress_g[TEST_COUNT] __attribute__((section(".dccm.persistent"))) = {
    NOT_STARTED,
    NOT_STARTED,
    NOT_STARTED,
    NOT_STARTED,
    NOT_STARTED,
    NOT_STARTED,
    NOT_STARTED,
    NOT_STARTED,
    NOT_STARTED,
    NOT_STARTED,
    NOT_STARTED,
    NOT_STARTED,
    NOT_STARTED,
    NOT_STARTED,
    NOT_STARTED,
    NOT_STARTED,
    NOT_STARTED,
    NOT_STARTED,
    NOT_STARTED,
    NOT_STARTED,
    NOT_STARTED,
    NOT_STARTED,
    NOT_STARTED,
    NOT_STARTED,
    NOT_STARTED,
    NOT_STARTED
};


////////////////////////////////////////////////////////////////////
// Function Prototypes
//
/* MBOX ECC */
void     run_mbox_sram_ecc  (enum ecc_error_mode_type type, enum mask_config test_mask);
uint32_t check_mbox_sram_ecc(enum ecc_error_mode_type type, enum mask_config test_mask);
uint32_t test_mbox_sram_ecc       (enum mask_config test_mask);

/* ICCM ECC */
uint32_t run_iccm_sram_ecc        (enum mask_config test_mask, enum read_config read_mask);
uint32_t check_iccm_sram_ecc      (enum mask_config test_mask, enum read_config read_mask);

/* DCCM ECC */
uint32_t run_dccm_sram_ecc        (enum mask_config test_mask, enum dccm_read_config read_path);
uint32_t check_dccm_sram_ecc      (enum mask_config test_mask, enum dccm_read_config read_path);

/* MBOX PROT */
void     run_mbox_no_lock_error  (enum mask_config test_mask);
uint32_t check_mbox_no_lock_error(enum mask_config test_mask);
void     run_mbox_ooo_error      (enum mask_config test_mask);
uint32_t check_mbox_ooo_error    (enum mask_config test_mask);

/* NMI */
void     run_nmi_test             (enum mask_config test_mask);
uint32_t check_nmi_test           (enum mask_config test_mask);

/* Supporting code */
void nmi_handler       (void);
void execute_from_iccm (void) __attribute__ ((aligned(4),section (".data_iccm0")));


////////////////////////////////////////////////////////////////////
// Function Definitions
//
void run_mbox_sram_ecc(enum ecc_error_mode_type type, enum mask_config test_mask) {
    enum test_list cur_test;

    VPRINTF(MEDIUM, "\n*** Run Mbox SRAM ECC Err ***\n  Type: %s\n  Masked: %d\n\n", (type == MBOX_SINGLE) ? "1-bit" : "2-bit", test_mask == WITH_MASK);

    // Grab test enum
    if      (type == MBOX_SINGLE && test_mask == WITH_MASK) { cur_test = MBOX_SRAM_ECC_SINGLE_MASKED;   }
    else if (type == MBOX_SINGLE && test_mask == NO_MASK)   { cur_test = MBOX_SRAM_ECC_SINGLE_UNMASKED; }
    else if (type == MBOX_DOUBLE && test_mask == WITH_MASK) { cur_test = MBOX_SRAM_ECC_DOUBLE_MASKED;   }
    else if (type == MBOX_DOUBLE && test_mask == NO_MASK)   { cur_test = MBOX_SRAM_ECC_DOUBLE_UNMASKED; }
    else                                                    { cur_test = TEST_COUNT;                    }

    // Acquire the mailbox lock
    while((lsu_read_32(CLP_MBOX_CSR_MBOX_LOCK) & MBOX_CSR_MBOX_LOCK_LOCK_MASK) != 0);

    // Set the Error Injection
    SEND_STDOUT_CTRL((uint32_t) type);

    // Set the MASK mode
    if (test_mask == WITH_MASK && type == MBOX_DOUBLE) {
        lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK, SOC_IFC_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK_MASK_MBOX_ECC_UNC_MASK);
    } else if (test_mask == NO_MASK || type == MBOX_SINGLE) {
        uint32_t mask_val = lsu_read_32(CLP_SOC_IFC_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK);
        mask_val &= ~SOC_IFC_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK_MASK_MBOX_ECC_UNC_MASK;
        lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK, mask_val);
    }

    // Allocate an array in Mailbox SRAM
    volatile uint32_t* myarray = (uint32_t*) MBOX_DIR_BASE_ADDR;
    for (uint32_t ii; ii < 64; ii++) {
        myarray[ii] = 64-ii;
    }

    // Read the array from the Mailbox and write to STDOUT
    for (uint32_t ii; ii < 64; ii++) {
        printf("[%d]:%x\n", ii, myarray[ii]); // no verbosity control -- dereferencing the array IS the test
    }

    // Log that the test ran
    test_progress_g[cur_test] = RUN_NOT_CHECKED;
}

uint32_t check_mbox_sram_ecc(enum ecc_error_mode_type type, enum mask_config test_mask) {
    uint32_t sts = 0;
    uint32_t rsp = 0;
    enum test_list cur_test;

    VPRINTF(MEDIUM, "\n*** Check Mbox SRAM ECC Err ***\n  Type: %s\n  Masked: %d\n\n", (type == MBOX_SINGLE) ? "1-bit" : "2-bit", test_mask == WITH_MASK);

    // Check that the test ran
    if      (type == MBOX_SINGLE && test_mask == WITH_MASK) { cur_test = MBOX_SRAM_ECC_SINGLE_MASKED;   }
    else if (type == MBOX_SINGLE && test_mask == NO_MASK)   { cur_test = MBOX_SRAM_ECC_SINGLE_UNMASKED; }
    else if (type == MBOX_DOUBLE && test_mask == WITH_MASK) { cur_test = MBOX_SRAM_ECC_DOUBLE_MASKED;   }
    else if (type == MBOX_DOUBLE && test_mask == NO_MASK)   { cur_test = MBOX_SRAM_ECC_DOUBLE_UNMASKED; }
    else                                                    { cur_test = TEST_COUNT;
                                                              sts     |= UNEXP_ARG;                     }

    if (test_progress_g[cur_test] != RUN_NOT_CHECKED) {
        VPRINTF(ERROR, "Mbox chkr hit unexpected state. Idx: %d Prog: %d\n", cur_test, test_progress_g[cur_test]);
        sts |= INV_STATE;
    }

    // Check Interrupt Counts
    if (type == MBOX_SINGLE && !(cptra_intr_rcv.soc_ifc_notif & SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_MBOX_ECC_COR_STS_MASK)) {
        VPRINTF(ERROR, "ERROR: No notif intr rcv (cor errors) in ECC sram test\n");
        sts |= INTR_COUNT_0;
    } else {
        cptra_intr_rcv.soc_ifc_notif &= ~SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_MBOX_ECC_COR_STS_MASK;
    }
    if (type == MBOX_DOUBLE && !(cptra_intr_rcv.soc_ifc_error & SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_MBOX_ECC_UNC_STS_MASK)) {
        VPRINTF(ERROR, "ERROR: No err intr rcv for unc err in ECC sram test\n");
        sts |= INTR_COUNT_0;
    } else {
        cptra_intr_rcv.soc_ifc_error &= ~SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_MBOX_ECC_UNC_STS_MASK;
    }
    // Sleep in between checking/clearing intr_count to allow any ISR to execute and show idle time in sims
    for (uint16_t slp = 0; slp < 100; slp++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }
    intr_count = 0;

    // Get the interrupt count for the expected type
    if (type == MBOX_SINGLE) {
        if (lsu_read_32(CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_MBOX_ECC_COR_INTR_COUNT_R) == 0) {
            VPRINTF(ERROR, "ERROR: 0 count value for cor ECC errors\n");
            sts |= INTR_COR_COUNT_0;
        } else {
            VPRINTF(LOW, "Cor ECC err no.: %x\n", lsu_read_32(CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_MBOX_ECC_COR_INTR_COUNT_R));
        }
    } else if (type == MBOX_DOUBLE) {
        if (lsu_read_32(CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_MBOX_ECC_UNC_INTR_COUNT_R) == 0) {
            VPRINTF(ERROR, "ERROR: 0 count value for unc ECC errors\n");
            sts |= INTR_UNC_COUNT_0;
        } else {
            VPRINTF(LOW, "Unc ECC err no.: %x\n", lsu_read_32(CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_MBOX_ECC_UNC_INTR_COUNT_R));
        }
    } else {
        VPRINTF(ERROR, "ERROR: ecc_error_mode: %x\n", type);
        sts |= UNEXP_ARG;
    }

    // For Correctable Errors, only expect internal interrupts (no output to SOC)
    // For Masked Uncorrectable Errors, interrupt should not go to SOC
    if (type == MBOX_DOUBLE) {
        uint32_t resp = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_INPUT_WIRES_0);
        // Check GENERIC_INPUT_WIRES for detection of cptra_error_non_fatal
        if (test_mask == NO_MASK && resp != MBOX_NON_FATAL_OBSERVED) {
            VPRINTF(ERROR, "ERROR: Bad resp from TB. Got: 0x%x Exp 0x%x\n", resp, MBOX_NON_FATAL_OBSERVED);
            sts |= BAD_CPTRA_SIG;
        }
        else if (test_mask == WITH_MASK && resp == ERROR_NONE_SET) {
            lsu_write_32(CLP_SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL, SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL_MBOX_ECC_UNC_MASK);
        }
        else if (test_mask == WITH_MASK) {
            VPRINTF(ERROR, "ERROR: Bad resp from TB. Got: 0x%x Exp 0x%x\n", resp, ERROR_NONE_SET);
            sts |= BAD_CPTRA_SIG;
        }
    }

    // Unlock Mailbox
    lsu_write_32(CLP_MBOX_CSR_MBOX_UNLOCK, MBOX_CSR_MBOX_UNLOCK_UNLOCK_MASK);

    // Reset the Error Injection Function
    SEND_STDOUT_CTRL((uint32_t) ERROR_NONE);

    // Increment test progress
    if (sts) {
        test_progress_g[cur_test] = RUN_AND_FAILED;
        VPRINTF(ERROR, "ERROR: Test fail. Sts: 0x%x\n", sts);
    } else {
        test_progress_g[cur_test] = RUN_AND_PASSED;
    }

    return sts;
}

uint32_t test_mbox_sram_ecc (enum mask_config test_mask) {
    VPRINTF(MEDIUM, "\nEnter Mbox SRAM ECC Err test\n  Masked: %d\n", test_mask == WITH_MASK);

    // Single-bit Correctable ECC Error injection
    run_mbox_sram_ecc(MBOX_SINGLE, test_mask);
    check_mbox_sram_ecc(MBOX_SINGLE, test_mask);
    // Double-bit Uncorrectable ECC Error injection
    run_mbox_sram_ecc(MBOX_DOUBLE, test_mask);
    check_mbox_sram_ecc(MBOX_DOUBLE, test_mask);
}

uint32_t run_iccm_sram_ecc (enum mask_config test_mask, enum read_config read_mask) {
    enum test_list cur_test;

    uint32_t * ICCM = (uint32_t *) RV_ICCM_SADR;
    uint32_t * code_word = 0;
    uint32_t * iccm_dest = ICCM;
    void (* iccm_fn) (void) = (void*) ICCM;
    uint32_t * actual_iccm_code_end = 0;

    uint32_t resp;
    uint32_t tmp_reg;

    VPRINTF(MEDIUM, "\n*** Run ICCM SRAM ECC Err ***\n  Masked: %d\n  IFU:    %d\n\n", test_mask == WITH_MASK, read_mask == FROM_IFU);

    // Grab test enum
    if      (test_mask == WITH_MASK && read_mask == FROM_IFU) { cur_test = ICCM_SRAM_ECC_SINGLE_IFU_MASKED;   }
    else if (test_mask == NO_MASK && read_mask == FROM_IFU)   { cur_test = ICCM_SRAM_ECC_SINGLE_IFU_UNMASKED; }
    else if (test_mask == WITH_MASK && read_mask == FROM_LSU) { cur_test = ICCM_SRAM_ECC_SINGLE_LSU_MASKED;   }
    else if (test_mask == NO_MASK && read_mask == FROM_LSU)   { cur_test = ICCM_SRAM_ECC_SINGLE_LSU_UNMASKED; }
    else                                                      { cur_test = TEST_COUNT;                        }

    // Request that TB inject ICCM SRAM single-bit errors
    // This should not result in any reset or reporting activity
    SEND_STDOUT_CTRL(ICCM_SINGLE);

    // Copy routine to ICCM
    code_word = (uint32_t *) &iccm_code0_start;
    VPRINTF(LOW, "Copy code from %x [thru %x] to %x\n", (uintptr_t) code_word, &iccm_code0_end, (uintptr_t) iccm_dest);
    while (code_word < (uint32_t *) &iccm_code0_end) {
        VPRINTF(ALL, "at %x: %x\n", (uintptr_t) code_word, *code_word);
        *iccm_dest++ = *code_word++;
    }
    actual_iccm_code_end = iccm_dest;

    // Reset the Error Injection Function
    SEND_STDOUT_CTRL((uint32_t) ERROR_NONE);

    // Flag Single-bit test as having run
    test_progress_g[cur_test] = RUN_NOT_CHECKED;

    // Run ICCM routine
    VPRINTF(MEDIUM, "Single-bit:\n");
    if (read_mask == FROM_IFU) {
        iccm_fn();
    // Read from ICCM instead
    } else if (read_mask == FROM_LSU) {
        code_word = (uint32_t *) ICCM;
        VPRINTF(LOW, "Read code from %x [through %x]\n", (uintptr_t) code_word, (uintptr_t) actual_iccm_code_end);
        while (code_word < actual_iccm_code_end) {
            tmp_reg ^= *code_word++;
        }
        VPRINTF(LOW, "Data in ICCM: 0x%x\n", tmp_reg);
    }

    // Confirm TB reports no observed activity
    resp = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_INPUT_WIRES_0);
    if (resp != ERROR_NONE_SET) {
        VPRINTF(ERROR, "ERROR: Bad resp from TB. Got: 0x%x Exp 0x%x\n", resp, ERROR_NONE_SET);
        test_progress_g[cur_test] = RUN_AND_FAILED;
    } else {
        __asm__ volatile ("csrr    %0, %1"
                          : "=r" (resp)  /* output : register */
                          : "i" (VEER_CSR_MICCMECT) /* input : immediate */
                          : /* clobbers: none */);
        if (resp == 0) {
            VPRINTF(ERROR, "ERROR: ICCM Cor error count is 0\n");
            test_progress_g[cur_test] = RUN_AND_FAILED;
        } else {
            test_progress_g[cur_test] = RUN_AND_PASSED;
        }
    }

    // Should return here after encountering single-bit (correctable) ECC errors
    // while running ICCM routine
    // Set new test enum
    if      (test_mask == WITH_MASK && read_mask == FROM_IFU) { cur_test = ICCM_SRAM_ECC_DOUBLE_IFU_MASKED;   }
    else if (test_mask == NO_MASK && read_mask == FROM_IFU)   { cur_test = ICCM_SRAM_ECC_DOUBLE_IFU_UNMASKED; }
    else if (test_mask == WITH_MASK && read_mask == FROM_LSU) { cur_test = ICCM_SRAM_ECC_DOUBLE_LSU_MASKED;   }
    else if (test_mask == NO_MASK && read_mask == FROM_LSU)   { cur_test = ICCM_SRAM_ECC_DOUBLE_LSU_UNMASKED; }
    else                                                      { cur_test = TEST_COUNT;                        }

    // Now, set the MASK (per arg)
    if (test_mask == WITH_MASK) {
        lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_HW_ERROR_FATAL_MASK, SOC_IFC_REG_INTERNAL_HW_ERROR_FATAL_MASK_MASK_ICCM_ECC_UNC_MASK);
    } else if (test_mask == NO_MASK) {
        uint32_t mask_val = lsu_read_32(CLP_SOC_IFC_REG_INTERNAL_HW_ERROR_FATAL_MASK);
        mask_val &= ~SOC_IFC_REG_INTERNAL_HW_ERROR_FATAL_MASK_MASK_ICCM_ECC_UNC_MASK;
        lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_HW_ERROR_FATAL_MASK, mask_val);
    }

    // Request that TB inject ICCM SRAM double-bit errors
    // This should result in FATAL error and caliptra reset
    SEND_STDOUT_CTRL(ICCM_DOUBLE);

    // Copy routine to ICCM
    code_word = (uint32_t *) &iccm_code0_start;
    iccm_dest = ICCM;
    VPRINTF(LOW, "Copy code from %x [thru %x] to %x\n", (uintptr_t) code_word, &iccm_code0_end, (uintptr_t) iccm_dest);
    while (code_word < (uint32_t *) &iccm_code0_end) {
        VPRINTF(ALL, "at %x: %x\n", (uintptr_t) code_word, *code_word);
        *iccm_dest++ = *code_word++;
    }

    // Reset the Error Injection Function
    SEND_STDOUT_CTRL((uint32_t) ERROR_NONE);

    // Clear the exception flag so we can properly check that it was set for an unmasked test
    exc_flag.exception_hit = 0;
    exc_flag.mcause        = 0;
    exc_flag.mscause       = 0;

    // Flag Double-bit test as having run
    test_progress_g[cur_test] = RUN_NOT_CHECKED;

    // Run ICCM routine
    // If FATAL error unmasked, this will trigger a reset.
    // Else, we'll observe a precise exception, which should do a firmware reset
    VPRINTF(MEDIUM, "Double-bit:\n");
    if (read_mask == FROM_IFU) {
        iccm_fn();
    // Read from ICCM instead
    } else if (read_mask == FROM_LSU) {
        code_word = (uint32_t *) ICCM;
        VPRINTF(LOW, "Read code from %x [through %x]\n", (uintptr_t) code_word, (uintptr_t) actual_iccm_code_end);
        while (code_word < actual_iccm_code_end) {
            tmp_reg = *code_word++;
            VPRINTF(LOW, "Data in ICCM: 0x%x\n", tmp_reg);
        }
    }

    // Wait for the reset to occur
    if (test_mask == NO_MASK) { VPRINTF(HIGH, "...\n"); while(1); }

}

uint32_t check_iccm_sram_ecc (enum mask_config test_mask, enum read_config read_mask) {
    enum test_list cur_test;
    uint32_t resp;
    uint32_t sts = SUCCESS;

    VPRINTF(MEDIUM, "\n*** Check ICCM SRAM ECC Err ***\n  Masked: %d\n  IFU:    %d\n\n", test_mask == WITH_MASK, read_mask == FROM_IFU);

    // Get test ID
    if      (test_mask == WITH_MASK && read_mask == FROM_IFU) { cur_test = ICCM_SRAM_ECC_DOUBLE_IFU_MASKED;   }
    else if (test_mask == NO_MASK && read_mask == FROM_IFU  ) { cur_test = ICCM_SRAM_ECC_DOUBLE_IFU_UNMASKED; }
    else if (test_mask == WITH_MASK && read_mask == FROM_LSU) { cur_test = ICCM_SRAM_ECC_DOUBLE_LSU_MASKED;   }
    else if (test_mask == NO_MASK && read_mask == FROM_LSU  ) { cur_test = ICCM_SRAM_ECC_DOUBLE_LSU_UNMASKED; }
    else                                                      { cur_test = TEST_COUNT;}
    // Verify correct response path was taken
    resp = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_INPUT_WIRES_0);

    if (test_mask == WITH_MASK && read_mask == FROM_LSU) {
        // No generic input toggle expected out of reset
        if ((cptra_intr_rcv.soc_ifc_notif & SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_GEN_IN_TOGGLE_STS_MASK) && (lsu_read_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_INPUT_WIRES_0) != generic_input_wires_0_before_rst)) {
            VPRINTF(ERROR, "ERROR: Gen-in tgl with bad val\n");
            sts |= BAD_CPTRA_SIG;
            test_progress_g[cur_test] = RUN_AND_FAILED;
        } else {
            sts |= SUCCESS;
            test_progress_g[cur_test] = RUN_AND_PASSED;
        }

        lsu_write_32(CLP_SOC_IFC_REG_CPTRA_HW_ERROR_FATAL, SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_ICCM_ECC_UNC_MASK);
    } else if (test_mask == WITH_MASK && read_mask == FROM_IFU) {
        // For a MASKED error, we only expect the exception path and no response from TB
        if (exc_flag.exception_hit == 0) {
            test_progress_g[cur_test] = RUN_AND_FAILED;
            sts |= INTR_COUNT_0;
        } else if (exc_flag.mcause  != RISCV_EXCP_INSTRUCTION_ACCESS_FAULT ||
                   exc_flag.mscause != RISC_EXCP_MSCAUSE_ICCM_INST_UNC_ECC_ERR) {
            test_progress_g[cur_test] = RUN_AND_FAILED;
            sts |= BAD_EXCP_CODE;
        } else if (resp != ERROR_NONE_SET) {
            test_progress_g[cur_test] = RUN_AND_FAILED;
            sts |= BAD_CPTRA_SIG;
        } else {
            test_progress_g[cur_test] = RUN_AND_PASSED;
        }
        lsu_write_32(CLP_SOC_IFC_REG_CPTRA_HW_ERROR_FATAL, SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_ICCM_ECC_UNC_MASK);
    } else {
        // For an UNMASKED error, we expect ICCM ECC FATAL Error to trigger TB reset and input val
        if (resp == ICCM_FATAL_OBSERVED) {
            test_progress_g[cur_test] = RUN_AND_PASSED;
        } else {
            test_progress_g[cur_test] = RUN_AND_FAILED;
            sts |= BAD_CPTRA_SIG;
        }
    }

    return sts;
}

// TODO should test both DMA slave and internal DCCM accesses?
uint32_t run_dccm_sram_ecc (enum mask_config test_mask, enum dccm_read_config read_path) {
    enum test_list cur_test;

    uint32_t array_in_dccm [10]; // stack is in DCCM, so this automatically goes there
    uint32_t* safe_iter = (uint32_t*) MBOX_DIR_BASE_ADDR; // Pointer to mailbox memory allows us to define an iteration variable that will not be corrupted by DCCM error injection

    uint32_t resp = lsu_read_32(CLP_SOC_IFC_REG_INTERNAL_RV_MTIME_L);

    VPRINTF(MEDIUM, "\n*** Run DCCM SRAM ECC Err ***\n  Masked: %d\n  Path:   %s\n\n", test_mask == WITH_MASK, read_path == DATA_LOAD ? "LOAD" : "DMA");

    // Grab test enum
    if      (test_mask == WITH_MASK && read_path == DATA_LOAD) { cur_test = DCCM_SRAM_ECC_SINGLE_LOAD_MASKED;   }
    else if (test_mask == NO_MASK   && read_path == DATA_LOAD) { cur_test = DCCM_SRAM_ECC_SINGLE_LOAD_UNMASKED; }
    else if (test_mask == WITH_MASK && read_path == FORCE_DMA) { cur_test = DCCM_SRAM_ECC_SINGLE_DMA_MASKED;   }
    else if (test_mask == NO_MASK   && read_path == FORCE_DMA) { cur_test = DCCM_SRAM_ECC_SINGLE_DMA_UNMASKED; }
    else                                                       { cur_test = TEST_COUNT;                    }

    // Skip the FORCE_DMA test if running in Verilator - it's bugged FIXME
    if (read_path == FORCE_DMA) {
        SEND_STDOUT_CTRL((uint32_t) ERROR_NONE);
        if (lsu_read_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_INPUT_WIRES_1) == ('v' | 'l' << 8 | 't' << 16 | 'r' << 24)) {
            VPRINTF(LOW, "Skipping DMA path in Verilator\n");
            test_progress_g[cur_test] = SKIPPED;
            if (test_mask == NO_MASK) {
                SEND_STDOUT_CTRL(0xf6); // Warm reset
            }
            return 0;
        }
    }

    // Acquire the mailbox lock (to allow direct-mode use of safe_iter)
    while((lsu_read_32(CLP_MBOX_CSR_MBOX_LOCK) & MBOX_CSR_MBOX_LOCK_LOCK_MASK) != 0) {
        VPRINTF(MEDIUM, "Get mbox lock\n");
    }

    // Request that TB inject DCCM SRAM single-bit errors
    // This should not result in any reset or reporting activity
    SEND_STDOUT_CTRL(DCCM_SINGLE);

    // Populate array in DCCM (should be corrupted)
    *safe_iter = 0;
    while(*safe_iter < 10) {
        resp = (resp << 1) ^ lsu_read_32(CLP_SOC_IFC_REG_INTERNAL_RV_MTIME_L);
        array_in_dccm[*safe_iter] = resp;
        *safe_iter = (*safe_iter) + 1;
    }

    // Reset the Error Injection Function
    SEND_STDOUT_CTRL((uint32_t) ERROR_NONE);
    __asm__ volatile ("fence.i");

    // Flag Single-bit test as having run
    test_progress_g[cur_test] = RUN_NOT_CHECKED;

    // Read-back the array in DCCM
    VPRINTF(MEDIUM, "Single-bit:\n");
    *safe_iter = 0;
    if (read_path == DATA_LOAD) {
        while(*safe_iter < 10) {
            printf("[%d]:%x\n", *safe_iter, array_in_dccm[*safe_iter]); // no verbosity control -- dereferencing the array IS the test
            *safe_iter = (*safe_iter) + 1;
        }
    } else if (read_path == FORCE_DMA) {
        VPRINTF(LOW, "Trigger TB to force DMA burst\n");
        lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_1, (uint32_t) &array_in_dccm);
        lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0, (10 << 12) | 0xdf);
    }

    // Unlock Mailbox
    lsu_write_32(CLP_MBOX_CSR_MBOX_UNLOCK, MBOX_CSR_MBOX_UNLOCK_UNLOCK_MASK);

    // Confirm TB reports no observed activity
    resp = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_INPUT_WIRES_0);
    if (resp != ERROR_NONE_SET) {
        VPRINTF(ERROR, "ERROR: Bad resp from TB. Got: 0x%x Exp 0x%x\n", resp, ERROR_NONE_SET);
        test_progress_g[cur_test] = RUN_AND_FAILED;
    } else {
        __asm__ volatile ("csrr    %0, %1"
                          : "=r" (resp)  /* output : register */
                          : "i" (VEER_CSR_MDCCMECT) /* input : immediate */
                          : /* clobbers: none */);
        if (resp == 0) {
            VPRINTF(ERROR, "ERROR: DCCM Cor error count is 0\n");
            test_progress_g[cur_test] = RUN_AND_FAILED;
        } else {
            test_progress_g[cur_test] = RUN_AND_PASSED;
        }
    }

    // Should return here after encountering single-bit (correctable) ECC errors
    // while running DCCM routine
    // Set new test enum
    if      (test_mask == WITH_MASK && read_path == DATA_LOAD) { cur_test = DCCM_SRAM_ECC_DOUBLE_LOAD_MASKED;   }
    else if (test_mask == NO_MASK   && read_path == DATA_LOAD) { cur_test = DCCM_SRAM_ECC_DOUBLE_LOAD_UNMASKED; }
    else if (test_mask == WITH_MASK && read_path == FORCE_DMA) { cur_test = DCCM_SRAM_ECC_DOUBLE_DMA_MASKED;    }
    else if (test_mask == NO_MASK   && read_path == FORCE_DMA) { cur_test = DCCM_SRAM_ECC_DOUBLE_DMA_UNMASKED;  }
    else                                                       { cur_test = TEST_COUNT;                         }

    // Now, set the MASK (per arg)
    if (test_mask == WITH_MASK) {
        lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_HW_ERROR_FATAL_MASK, SOC_IFC_REG_INTERNAL_HW_ERROR_FATAL_MASK_MASK_DCCM_ECC_UNC_MASK);
    } else if (test_mask == NO_MASK) {
        uint32_t mask_val = lsu_read_32(CLP_SOC_IFC_REG_INTERNAL_HW_ERROR_FATAL_MASK);
        mask_val &= ~SOC_IFC_REG_INTERNAL_HW_ERROR_FATAL_MASK_MASK_DCCM_ECC_UNC_MASK;
        lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_HW_ERROR_FATAL_MASK, mask_val);
    }

    // Acquire the mailbox lock (to allow direct-mode use of safe_iter)
    while((lsu_read_32(CLP_MBOX_CSR_MBOX_LOCK) & MBOX_CSR_MBOX_LOCK_LOCK_MASK) != 0) {
        VPRINTF(MEDIUM, "Get mbox lock\n");
    }

    // Request that TB inject DCCM SRAM double-bit errors
    // This should result in FATAL error and caliptra reset
    // when reading back
    SEND_STDOUT_CTRL(DCCM_DOUBLE);

    // Populate array in DCCM (should be corrupted)
    *safe_iter = 0;
    while(*safe_iter < 10) {
        resp = (resp << 1) ^ lsu_read_32(CLP_SOC_IFC_REG_INTERNAL_RV_MTIME_L);
        array_in_dccm[*safe_iter] = resp;
        *safe_iter = (*safe_iter) + 1;
    }

    // Reset the Error Injection Function
    SEND_STDOUT_CTRL((uint32_t) ERROR_NONE);
    __asm__ volatile ("fence.i");

    // TODO check for AMO/Store exception here?

    // Clear the exception flag so we can properly check that it was set for an unmasked test
    exc_flag.exception_hit = 0;
    exc_flag.mcause        = 0;
    exc_flag.mscause       = 0;

    // Flag Double-bit test as having run
    test_progress_g[cur_test] = RUN_NOT_CHECKED;

    // Read-back the array in DCCM
    // If FATAL error unmasked, this will trigger a reset.
    // If FATAL error masked, but using DMA path, this only results in generic input wire value
    // Else, we'll observe a precise exception
    VPRINTF(MEDIUM, "Double-bit:\n");
    *safe_iter = 0;
    if (read_path == DATA_LOAD) {
        while(*safe_iter < 10) {
            printf("[%d]:%x\n", *safe_iter, array_in_dccm[*safe_iter]); // no verbosity control -- dereferencing the array IS the test
            *safe_iter = (*safe_iter) + 1;
        }
    } else if (read_path == FORCE_DMA) {
        VPRINTF(LOW, "Trigger TB to force DMA burst\n");
        lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_1, (uint32_t) &array_in_dccm);
        lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0, (10 << 12) | 0xdf);
    }

    // Unlock Mailbox
    lsu_write_32(CLP_MBOX_CSR_MBOX_UNLOCK, MBOX_CSR_MBOX_UNLOCK_UNLOCK_MASK);

    // Wait for the reset to occur
    if (test_mask == NO_MASK) { VPRINTF(HIGH, "...\n"); while(1); }

}

uint32_t check_dccm_sram_ecc (enum mask_config test_mask, enum dccm_read_config read_path) {
    enum test_list cur_test;
    uint32_t resp;
    uint32_t sts = SUCCESS;

    VPRINTF(MEDIUM, "\n*** Check DCCM SRAM ECC Err ***\n  Masked: %d\n  Path:   %s\n\n", test_mask == WITH_MASK, read_path == DATA_LOAD ? "LOAD" : "DMA");

    // Get test ID
    if      (test_mask == WITH_MASK && read_path == DATA_LOAD) { cur_test = DCCM_SRAM_ECC_DOUBLE_LOAD_MASKED;   }
    else if (test_mask == NO_MASK   && read_path == DATA_LOAD) { cur_test = DCCM_SRAM_ECC_DOUBLE_LOAD_UNMASKED; }
    else if (test_mask == WITH_MASK && read_path == FORCE_DMA) { cur_test = DCCM_SRAM_ECC_DOUBLE_DMA_MASKED;    }
    else if (test_mask == NO_MASK   && read_path == FORCE_DMA) { cur_test = DCCM_SRAM_ECC_DOUBLE_DMA_UNMASKED;  }
    else                                                       { cur_test = TEST_COUNT;                         }

    // Skip the FORCE_DMA test if running in Verilator - it's bugged FIXME
    if (read_path == FORCE_DMA) {
        if (lsu_read_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_INPUT_WIRES_1) == ('v' | 'l' << 8 | 't' << 16 | 'r' << 24)) {
            VPRINTF(LOW, "Skipping DMA path in Verilator\n");
            test_progress_g[cur_test] = SKIPPED;
            return sts;
        }
    }

    // Verify correct response path was taken
    resp = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_INPUT_WIRES_0);
    if (test_mask == WITH_MASK && read_path == DATA_LOAD) {
        // For a MASKED error, we only expect the exception path and no response from TB
        if (exc_flag.exception_hit == 0) {
            test_progress_g[cur_test] = RUN_AND_FAILED;
            sts |= INTR_COUNT_0;
            VPRINTF(ERROR, "ERROR: No excpn\n");
        } else if (exc_flag.mcause  != RISCV_EXCP_LOAD_ACCESS_FAULT ||
                   exc_flag.mscause != RISC_EXCP_MSCAUSE_DCCM_LOAD_UNC_ECC_ERR) {
            test_progress_g[cur_test] = RUN_AND_FAILED;
            sts |= BAD_EXCP_CODE;
            VPRINTF(ERROR, "ERROR: Wrong excpn cause. Got: 0x%x msc 0x%x\n", exc_flag.mcause, exc_flag.mscause);
        } else if (resp != ERROR_NONE_SET) {
            test_progress_g[cur_test] = RUN_AND_FAILED;
            sts |= BAD_CPTRA_SIG;
            VPRINTF(ERROR, "ERROR: Wrong TB resp\n");
        } else {
            test_progress_g[cur_test] = RUN_AND_PASSED;
        }
        lsu_write_32(CLP_SOC_IFC_REG_CPTRA_HW_ERROR_FATAL, SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_DCCM_ECC_UNC_MASK);
    } else if (test_mask == WITH_MASK && read_path == FORCE_DMA) {
        // For a MASKED error through the DMA force-access path, expect a TB response
        // but no reset, no exceptions, and the FATAL error bit should be set
        if (exc_flag.exception_hit == 1) {
            test_progress_g[cur_test] = RUN_AND_FAILED;
            sts |= BAD_EXCP_CODE;
            VPRINTF(ERROR, "ERROR: Unexpected excpn\n");
        } else if (resp != DMA_ERROR_OBSERVED) {
            test_progress_g[cur_test] = RUN_AND_FAILED;
            sts |= BAD_CPTRA_SIG;
            VPRINTF(ERROR, "ERROR: Wrong TB resp. Got 0x%x, exp 0x%x\n", resp, DMA_ERROR_OBSERVED);
        } else if (!(lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_ERROR_FATAL) & SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_DCCM_ECC_UNC_MASK)) {
            test_progress_g[cur_test] = RUN_AND_FAILED;
            sts |= INV_STATE;
            VPRINTF(ERROR, "ERROR: DCCM ECC UNC FATAL not set by TB\n");
        } else {
            test_progress_g[cur_test] = RUN_AND_PASSED;
        }
        lsu_write_32(CLP_SOC_IFC_REG_CPTRA_HW_ERROR_FATAL, SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_DCCM_ECC_UNC_MASK);
    } else {
        // For an UNMASKED error, we expect DCCM ECC FATAL Error to trigger TB reset and input val
        if (resp == DCCM_FATAL_OBSERVED) {
            test_progress_g[cur_test] = RUN_AND_PASSED;
        } else {
            test_progress_g[cur_test] = RUN_AND_FAILED;
            sts |= BAD_CPTRA_SIG;
            VPRINTF(ERROR, "ERROR: Wrong TB resp. Exp 0x%x Got 0x%x\n", DCCM_FATAL_OBSERVED, resp);
        }
    }

    return sts;
}

void run_nmi_test (enum mask_config test_mask) {
    enum test_list cur_test;
    VPRINTF(MEDIUM, "\n*** Run Non-Maskable Intr ***\n  Masked: %d\n\n", test_mask == WITH_MASK);

    // Get test ID
    if (test_mask == WITH_MASK) { cur_test = NMI_MASKED;   }
    else                        { cur_test = NMI_UNMASKED; }

    //Enable WDT so that both timers time out and NMI is issued
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD_0, 0x00000040);
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD_1, 0x00000000);
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD_0, 0x00000040);
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD_1, 0x00000000);
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_WDT_TIMER1_EN, SOC_IFC_REG_CPTRA_WDT_TIMER1_EN_TIMER1_EN_MASK);

    //Set mask
    if (test_mask == WITH_MASK) {
        lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_HW_ERROR_FATAL_MASK, SOC_IFC_REG_INTERNAL_HW_ERROR_FATAL_MASK_MASK_NMI_PIN_MASK);
    }
    // Wait for interrupt
    while(1) {
        __asm__ volatile ("wfi"); // "Wait for interrupt"
        // Continuously loop to allow the ICCM ECC ERROR to trigger system reset
        for (uint16_t slp = 0; slp < 1000; slp++) {
            __asm__ volatile ("nop"); // Sleep loop as "nop"
        }
        putchar('.');
    }

    test_progress_g[cur_test] = RUN_NOT_CHECKED;

    return;
}

uint32_t check_nmi_test (enum mask_config test_mask) {
    uint32_t sts = 0;
    enum test_list cur_test;
    VPRINTF(MEDIUM, "\n*** Check Non-Maskable Intr ***\n  Masked: %d\n\n", test_mask == WITH_MASK);
    // Get test ID
    if (test_mask == WITH_MASK) { cur_test = NMI_MASKED;   }
    else                        { cur_test = NMI_UNMASKED; }
    //test_progress_g[cur_test] = RUN_AND_PASSED;

    if (test_mask == WITH_MASK) {
        // No generic input toggle expected out of reset
        if ((cptra_intr_rcv.soc_ifc_notif & SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_GEN_IN_TOGGLE_STS_MASK) && (lsu_read_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_INPUT_WIRES_0) != generic_input_wires_0_before_rst)) {
            VPRINTF(ERROR, "ERROR: Gen-in tgl with bad val\n");
            sts |= BAD_CPTRA_SIG;
            test_progress_g[cur_test] = RUN_AND_FAILED;
        } else {
            sts |= SUCCESS;
            test_progress_g[cur_test] = RUN_AND_PASSED;
        }

        lsu_write_32(CLP_SOC_IFC_REG_CPTRA_HW_ERROR_FATAL, SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_NMI_PIN_MASK);
    } else {
        // Check for generic_input_wires activity
        if (!(cptra_intr_rcv.soc_ifc_notif & SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_GEN_IN_TOGGLE_STS_MASK)) {
            VPRINTF(ERROR, "ERROR: Gen-in did not tgl\n");
            sts |= BAD_CPTRA_SIG;
            test_progress_g[cur_test] = RUN_AND_FAILED;
        } else if (lsu_read_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_INPUT_WIRES_0) != NMI_FATAL_OBSERVED) {
            VPRINTF(ERROR, "ERROR: Gen-in bad val\n");
            sts |= BAD_CPTRA_SIG;
            test_progress_g[cur_test] = RUN_AND_FAILED;
        } else {
            sts |= SUCCESS;
            test_progress_g[cur_test] = RUN_AND_PASSED;
        }
    }


    return sts;
}

void run_mbox_no_lock_error(enum mask_config test_mask) {
    enum test_list cur_test;
    VPRINTF(MEDIUM, "\n*** Run Mbox No Lock ***\n  Masked: %d\n\n", test_mask == WITH_MASK);

    // Get test ID
    if      (test_mask == WITH_MASK) { cur_test = PROT_NO_LOCK_MASKED;   }
    else if (test_mask == NO_MASK)   { cur_test = PROT_NO_LOCK_UNMASKED; }
    else                             { cur_test = TEST_COUNT;            }

    // Generic input wires should toggle if unmasked, clear the flag so we can see it update
    cptra_intr_rcv.soc_ifc_notif = 0;
    // Also clear the mbox cmd fail flag
    cptra_intr_rcv.soc_ifc_error = 0;

    //Set the mask
    if (test_mask == WITH_MASK)
        lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK, SOC_IFC_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK_MASK_MBOX_PROT_NO_LOCK_MASK);

    // run test (try to read dataout without having lock)
    lsu_write_32(CLP_MBOX_CSR_MBOX_UNLOCK,MBOX_CSR_MBOX_UNLOCK_UNLOCK_MASK); // Be sure it's unlocked
    // Instruct TB to do bad mailbox flow
    SEND_STDOUT_CTRL(0xe5);

    // Flag test as having run
    test_progress_g[cur_test] = RUN_NOT_CHECKED;

}

void run_mbox_ooo_error(enum mask_config test_mask) {
    enum test_list cur_test;
    VPRINTF(MEDIUM, "\n*** Run Mbox Out-of-order ***\n  Masked: %d\n\n", test_mask == WITH_MASK);

    // Get test ID
    if      (test_mask == WITH_MASK) { cur_test = PROT_OOO_MASKED;   }
    else if (test_mask == NO_MASK)   { cur_test = PROT_OOO_UNMASKED; }
    else                             { cur_test = TEST_COUNT;        }

    // Generic input wires should toggle if unmasked, clear the flag so we can see it update
    cptra_intr_rcv.soc_ifc_notif = 0;
    // Also clear the mbox cmd fail flag
    cptra_intr_rcv.soc_ifc_error = 0;

    //Set the mask
    if (test_mask == WITH_MASK)
        lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK, SOC_IFC_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK_MASK_MBOX_PROT_OOO_MASK);

    // Flag test as having run
    test_progress_g[cur_test] = RUN_NOT_CHECKED;

    // run test (try to read dataout without having lock)
    // Instruct TB to do bad mailbox flow
    SEND_STDOUT_CTRL(0xe6); //Mailbox unlocked through ISR

    //return;

}

uint32_t check_mbox_no_lock_error(enum mask_config test_mask) {
    enum test_list cur_test;
    uint32_t sts = 0;
    VPRINTF(MEDIUM, "\n*** Check Mbox No Lock ***\n  Masked: %d\n\n", test_mask == WITH_MASK);

    // Get test ID
    if      (test_mask == WITH_MASK) { cur_test = PROT_NO_LOCK_MASKED;   }
    else if (test_mask == NO_MASK)   { cur_test = PROT_NO_LOCK_UNMASKED; }
    else                             { cur_test = TEST_COUNT;            }

    if (!(cptra_intr_rcv.soc_ifc_error & SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_CMD_FAIL_STS_MASK)) {
        VPRINTF(ERROR, "ERROR: No cmd fail intr\n");
        sts |= INTR_COUNT_0;
        test_progress_g[cur_test] = RUN_AND_FAILED;
    } else if (test_mask == WITH_MASK) {
        // Check for generic_input_wires activity
        if (cptra_intr_rcv.soc_ifc_notif & SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_GEN_IN_TOGGLE_STS_MASK) {
            VPRINTF(ERROR, "ERROR: Gen-in tgl\n");
            sts |= BAD_CPTRA_SIG;
            test_progress_g[cur_test] = RUN_AND_FAILED;
        } else {
            sts |= SUCCESS;
            test_progress_g[cur_test] = RUN_AND_PASSED;
        }
        lsu_write_32(CLP_SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL, SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL_MBOX_PROT_NO_LOCK_MASK);
    } else {
        // Check for generic_input_wires activity
        if (!(cptra_intr_rcv.soc_ifc_notif & SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_GEN_IN_TOGGLE_STS_MASK)) {
            VPRINTF(ERROR, "ERROR: Gen-in did not tgl\n");
            sts |= BAD_CPTRA_SIG;
            test_progress_g[cur_test] = RUN_AND_FAILED;
        } else if (lsu_read_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_INPUT_WIRES_0) != PROT_NO_LOCK_NON_FATAL_OBSERVED) {
            VPRINTF(ERROR, "ERROR: Gen-in bad val\n");
            sts |= BAD_CPTRA_SIG;
            test_progress_g[cur_test] = RUN_AND_FAILED;
        } else {
            sts |= SUCCESS;
            test_progress_g[cur_test] = RUN_AND_PASSED;
        }
    }

    //Unlock mailbox
    lsu_write_32(CLP_MBOX_CSR_MBOX_UNLOCK,MBOX_CSR_MBOX_UNLOCK_UNLOCK_MASK);

    return sts;
}

uint32_t check_mbox_ooo_error(enum mask_config test_mask) {
    enum test_list cur_test;
    uint32_t sts = 0;
    VPRINTF(MEDIUM, "\n*** Check Mbox Out-of-order ***\n  Masked: %d\n\n", test_mask == WITH_MASK);

    // Get test ID
    if      (test_mask == WITH_MASK) { cur_test = PROT_OOO_MASKED;   }
    else if (test_mask == NO_MASK)   { cur_test = PROT_OOO_UNMASKED; }
    else                             { cur_test = TEST_COUNT;        }

    if (!(cptra_intr_rcv.soc_ifc_error & SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_CMD_FAIL_STS_MASK)) {
        VPRINTF(ERROR, "ERROR: No cmd fail intr\n");
        sts |= INTR_COUNT_0;
        test_progress_g[cur_test] = RUN_AND_FAILED;
    } else if (test_mask == WITH_MASK) {
        // Check for generic_input_wires activity
        if (cptra_intr_rcv.soc_ifc_notif & SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_GEN_IN_TOGGLE_STS_MASK) {
            VPRINTF(ERROR, "ERROR: Gen-in tgl\n");
            sts |= BAD_CPTRA_SIG;
            test_progress_g[cur_test] = RUN_AND_FAILED;
        } else {
            sts |= SUCCESS;
            test_progress_g[cur_test] = RUN_AND_PASSED;
        }
        lsu_write_32(CLP_SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL, SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL_MBOX_PROT_OOO_MASK);

        //Reset out-of-order access flag
        SEND_STDOUT_CTRL(0xe7);
    } else {
        // Check for generic_input_wires activity
        if (!(cptra_intr_rcv.soc_ifc_notif & SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_GEN_IN_TOGGLE_STS_MASK)) {
            VPRINTF(ERROR, "ERROR: Gen-in did not tgl\n");
            sts |= BAD_CPTRA_SIG;
            test_progress_g[cur_test] = RUN_AND_FAILED;
        } else if (lsu_read_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_INPUT_WIRES_0) != PROT_OOO_NON_FATAL_OBSERVED) {
            VPRINTF(ERROR, "ERROR: Gen-in bad val\n");
            sts |= BAD_CPTRA_SIG;
            test_progress_g[cur_test] = RUN_AND_FAILED;
        } else {
            sts |= SUCCESS;
            test_progress_g[cur_test] = RUN_AND_PASSED;
        }
    }

    return sts;
}

void execute_from_iccm (void) {
    // Do a bunch of nonsense tasks just to populate the code space.
    // When running this routine, we expect to encounter ICCM ECC Errors and
    // get reset by TB
    uint32_t tmp_reg, tmp_reg2;
    VPRINTF(LOW, "Exec from ICCM\n");
    tmp_reg = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_CONFIG);
    VPRINTF(LOW, "HW_CFG: 0x%x\n", tmp_reg);
    tmp_reg  = lsu_read_32(CLP_SOC_IFC_REG_INTERNAL_RV_MTIMECMP_L);
    tmp_reg2 = lsu_read_32(CLP_SOC_IFC_REG_INTERNAL_RV_MTIMECMP_H);
    VPRINTF(LOW, "MTIMECMP: 0x%x %x\n", tmp_reg2, tmp_reg);
    tmp_reg  = lsu_read_32(CLP_SOC_IFC_REG_INTERNAL_RV_MTIME_L);
    tmp_reg2 = lsu_read_32(CLP_SOC_IFC_REG_INTERNAL_RV_MTIME_H);
    VPRINTF(LOW, "MTIME: 0x%x %x\n", tmp_reg2, tmp_reg);
    // This reg isn't even writable, so nothing should happen...
    if (tmp_reg2) {
        lsu_write_32(CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R, tmp_reg2 ^ tmp_reg);
    } else {
        lsu_write_32(CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R, (tmp_reg2 - 1) ^ tmp_reg);
    }
    tmp_reg = csr_read_mepc();
    tmp_reg2 = csr_read_mtval();
    tmp_reg ^= csr_read_mtvec();
    tmp_reg2 ^= csr_read_mie();
    tmp_reg ^= csr_read_mip();
    tmp_reg2 ^= csr_read_mvendorid();
    tmp_reg ^= tmp_reg2;
    VPRINTF(LOW, "Nonsense result: 0x%x\n", tmp_reg);
    // ERROR_FATAL interrupt will only go to TB if running the unmasked
    // double-bit error test, so we expect to get here successfully and return
    // in other test cases
    if (test_progress_g[ICCM_SRAM_ECC_DOUBLE_IFU_UNMASKED] == RUN_NOT_CHECKED &&
        test_progress_g[ICCM_SRAM_ECC_SINGLE_IFU_MASKED  ] == NOT_STARTED) {
        while(1) {
            __asm__ volatile ("wfi"); // "Wait for interrupt"
            // Continuously loop to allow the ICCM ECC ERROR to trigger system reset
            for (uint16_t slp = 0; slp < 1000; slp++) {
                __asm__ volatile ("nop"); // Sleep loop as "nop"
            }
            putchar('.');
        }
    } else {
        return;
    }
}

// In the ROM .text section
void nmi_handler (void) {
    VPRINTF(LOW, "**** NMI ****\n");
    if (boot_count != BEFORE_FIRST_NMI_FAILURE && boot_count != BEFORE_SECOND_NMI_FAILURE && boot_count != BEFORE_THIRD_NMI_FAILURE) {
        VPRINTF(ERROR, "ERROR: NMI unexpected. mcause [0x%x]!\n", csr_read_mcause()); // did not expect NMI
        VPRINTF(ERROR, "       mepc [0x%x]\n", csr_read_mepc());
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
    // If we got here via internal NMI, it's an error - kill the sim
    if ((boot_count != BEFORE_THIRD_NMI_FAILURE) && ((csr_read_mcause() & MCAUSE_NMI_BIT_MASK) == MCAUSE_NMI_BIT_MASK)) {
        VPRINTF(ERROR, "ERROR: NMI w/ mcause [0x%x]!\n", csr_read_mcause());
        VPRINTF(ERROR, "       mepc [0x%x]\n", csr_read_mepc());
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
    // NMI occurred, check if we had a fatal error
    if (lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_ERROR_FATAL) & (SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_ICCM_ECC_UNC_MASK |
                                                             SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_NMI_PIN_MASK)) {
        //Save generic_input_wires value before reset to compare later. This is to avoid flagging the toggle during reset as an error
        generic_input_wires_0_before_rst = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_INPUT_WIRES_0);
        VPRINTF(MEDIUM, "NMI w/ mcause [0x%x] during NMI test\n", csr_read_mcause());
        VPRINTF(MEDIUM, "mepc [0x%x]\n", csr_read_mepc());
        // If the FATAL Error bit for ECC UNC or NMI is masked, manually trigger firmware reset
        if (lsu_read_32(CLP_SOC_IFC_REG_INTERNAL_HW_ERROR_FATAL_MASK) & (SOC_IFC_REG_INTERNAL_HW_ERROR_FATAL_MASK_MASK_NMI_PIN_MASK |
                                                                         SOC_IFC_REG_INTERNAL_HW_ERROR_FATAL_MASK_MASK_ICCM_ECC_UNC_MASK)) {
            VPRINTF(LOW, "FATAL_ERROR bit is masked, no rst exp from TB: rst core manually!\n");
            //lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET, SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET_CORE_RST_MASK);
            SEND_STDOUT_CTRL(0xf6);
        // Otherwise, wait for core reset
        } else {
            VPRINTF(LOW, "NMI bit unmasked, wait for TB rst!\n");
            while(1);
        }
    }
}

void main(void) {

        uint32_t sts;
        uint8_t test_fail = 0;

        VPRINTF(LOW, "\n----------------------------------\nRAS Smoke Test!!\n----------------------------------\n");

        // Setup the interrupt CSR configuration
        init_interrupts();

        // Initialize the counter
        intr_count = 0;
        boot_count++; // After first boot should be 1

        // Setup the NMI Handler
        lsu_write_32((uintptr_t) (CLP_SOC_IFC_REG_INTERNAL_NMI_VECTOR), (uint32_t) (nmi_handler));

        // Test Mailbox SRAM ECC
        if (boot_count == BEFORE_FIRST_ICCM_FAILURE) {
            test_mbox_sram_ecc(NO_MASK);
            test_mbox_sram_ecc(WITH_MASK);
        }
        // No reset expected following MBOX SRAM ECC Error injection

        // Test ICCM SRAM ECC
        if      (boot_count == BEFORE_FIRST_ICCM_FAILURE)  {   run_iccm_sram_ecc(NO_MASK,   FROM_IFU); }
        else if (boot_count == BEFORE_SECOND_ICCM_FAILURE) { check_iccm_sram_ecc(NO_MASK,   FROM_IFU);
                                                               run_iccm_sram_ecc(WITH_MASK, FROM_IFU); }
        else if (boot_count == BEFORE_THIRD_ICCM_FAILURE)  { check_iccm_sram_ecc(WITH_MASK, FROM_IFU);
                                                               run_iccm_sram_ecc(NO_MASK,   FROM_LSU); }
        else if (boot_count == BEFORE_FIRST_DCCM_FAILURE)  { check_iccm_sram_ecc(NO_MASK,   FROM_LSU); }

        // Test DCCM SRAM ECC
        if      (boot_count == BEFORE_FIRST_DCCM_FAILURE) {   run_dccm_sram_ecc(NO_MASK  , DATA_LOAD); }
        else if (boot_count == BEFORE_SECOND_DCCM_FAILURE){ check_dccm_sram_ecc(NO_MASK  , DATA_LOAD);
                                                              run_dccm_sram_ecc(WITH_MASK, DATA_LOAD);
                                                            check_dccm_sram_ecc(WITH_MASK, DATA_LOAD);
                                                              run_dccm_sram_ecc(NO_MASK  , FORCE_DMA); }
        else if (boot_count == BEFORE_FIRST_NMI_FAILURE)  { check_dccm_sram_ecc(NO_MASK  , FORCE_DMA);
                                                              run_dccm_sram_ecc(WITH_MASK, FORCE_DMA);
                                                            check_dccm_sram_ecc(WITH_MASK, FORCE_DMA); }

        // Test WDT Expiration
        if      (boot_count == BEFORE_FIRST_NMI_FAILURE) {                 run_nmi_test(NO_MASK  ); }
        else if (boot_count == BEFORE_SECOND_NMI_FAILURE){               check_nmi_test(NO_MASK  );
                                                                           run_nmi_test(WITH_MASK); }
        else if (boot_count == BEFORE_THIRD_NMI_FAILURE) {               check_nmi_test(WITH_MASK);
        // Test NMI from Masked ICCM ECC through LSU
                                                            run_iccm_sram_ecc(WITH_MASK, FROM_LSU); }
        else if (boot_count == AFTER_THIRD_NMI_FAILURE) { check_iccm_sram_ecc(WITH_MASK, FROM_LSU); }

        // Test Mailbox Protocol Violations (no reset expected)
        if      (boot_count == AFTER_THIRD_NMI_FAILURE) {    run_mbox_no_lock_error  (  NO_MASK);
                                                           check_mbox_no_lock_error  (  NO_MASK);
                                                             run_mbox_ooo_error      (  NO_MASK);
                                                           check_mbox_ooo_error      (  NO_MASK);
                                                             run_mbox_no_lock_error  (WITH_MASK);
                                                           check_mbox_no_lock_error  (WITH_MASK);
                                                             run_mbox_ooo_error      (WITH_MASK);
                                                           check_mbox_ooo_error      (WITH_MASK); }

        // Final Report
        VPRINTF(MEDIUM, "Eval test progress...\n");
        for (enum test_list tests = 0; tests < TEST_COUNT; tests++) {
            if (test_progress_g[tests] == SKIPPED) {
                VPRINTF(WARNING, "Test [%d] skipped!\n", tests);
            } else if (test_progress_g[tests] != RUN_AND_PASSED) {
                VPRINTF(ERROR, "Test [%d] failed! Progress: %d\n", tests, test_progress_g[tests]);
                test_fail = 1;
            }
        }

        if (test_fail) {
            VPRINTF(ERROR, "RAS error injection test failed\n");
            SEND_STDOUT_CTRL(0x1);
            while(1);
        } else {
            VPRINTF(LOW, "RAS test pass\n");
        }

        return;

}
