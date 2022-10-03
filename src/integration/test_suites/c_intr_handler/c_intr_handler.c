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
#include <string.h>
#include "riscv-csr.h"
#include "swerv-csr.h"
#include "riscv-interrupts.h"
#include "mbox_reg.h"


//int whisperPrintf(const char* format, ...);
//#define ee_printf whisperPrintf


const char* const print_data = "----------------------------------\nDirect ISR Test from SweRV EL2 @WDC !!\n----------------------------------\n";
volatile char* stdout = (char *)STDOUT;
volatile uint32_t intr_count;

//////////////////////////////////////////////////////////////////////////////
// Function Declarations
//

// Writes binary contents of register to stdout
static void print_reg_to_console(char* msg, uint32_t value);

// Performs all the CSR setup to configure and enable vectored external interrupts
static void init_interrupts(void);

// Initial ISR for first redirection following an external intr trap (pointed to by mtvec)
// Machine mode interrupt service routine
// Force the alignment for mtvec.BASE.
static void std_rv_isr(void) __attribute__ ((interrupt ("machine"), aligned(4)));

void std_rv_mtvec_exception(void) __attribute__ ((interrupt ("machine"), aligned(4)));

// Nop handlers for unimplemented events "Software" and "Timer" Interrupts
// "External Interrupts" are also included in this unimplemented list, just because the
// std_rv_isr_vector_table should never reroute to External Interrupts -- Fast
// Redirect takes care of that separately
void std_rv_nop_machine(void) __attribute__ ((interrupt ("machine"), aligned(4)));
void std_rv_mtvec_mei(void) __attribute__ ((interrupt ("machine") , aligned(4) , weak, alias("std_rv_nop_machine") ));
void std_rv_mtvec_msi(void) __attribute__ ((interrupt ("machine") , aligned(4) , weak, alias("std_rv_nop_machine") ));
void std_rv_mtvec_mti(void) __attribute__ ((interrupt ("machine") , aligned(4) , weak, alias("std_rv_nop_machine") ));
void std_rv_mtvec_sei(void) __attribute__ ((interrupt ("machine") , aligned(4) , weak, alias("std_rv_nop_machine") ));
void std_rv_mtvec_ssi(void) __attribute__ ((interrupt ("machine") , aligned(4) , weak, alias("std_rv_nop_machine") ));
void std_rv_mtvec_sti(void) __attribute__ ((interrupt ("machine") , aligned(4) , weak, alias("std_rv_nop_machine") ));


// SweRV Per-Source Vectored ISR functions
static void nonstd_swerv_isr_aes_error    (void) __attribute__ ((interrupt ("machine")));
static void nonstd_swerv_isr_aes_notif    (void) __attribute__ ((interrupt ("machine")));
static void nonstd_swerv_isr_ecc_error    (void) __attribute__ ((interrupt ("machine")));
static void nonstd_swerv_isr_ecc_notif    (void) __attribute__ ((interrupt ("machine")));
static void nonstd_swerv_isr_hmac_error   (void) __attribute__ ((interrupt ("machine")));
static void nonstd_swerv_isr_hmac_notif   (void) __attribute__ ((interrupt ("machine")));
static void nonstd_swerv_isr_kv_error     (void) __attribute__ ((interrupt ("machine")));
static void nonstd_swerv_isr_kv_notif     (void) __attribute__ ((interrupt ("machine")));
static void nonstd_swerv_isr_sha512_error (void) __attribute__ ((interrupt ("machine")));
static void nonstd_swerv_isr_sha512_notif (void) __attribute__ ((interrupt ("machine")));
static void nonstd_swerv_isr_sha256_error (void) __attribute__ ((interrupt ("machine")));
static void nonstd_swerv_isr_sha256_notif (void) __attribute__ ((interrupt ("machine")));
static void nonstd_swerv_isr_qspi_error   (void) __attribute__ ((interrupt ("machine")));
static void nonstd_swerv_isr_qspi_notif   (void) __attribute__ ((interrupt ("machine")));
static void nonstd_swerv_isr_uart_error   (void) __attribute__ ((interrupt ("machine")));
static void nonstd_swerv_isr_uart_notif   (void) __attribute__ ((interrupt ("machine")));
static void nonstd_swerv_isr_i3c_error    (void) __attribute__ ((interrupt ("machine")));
static void nonstd_swerv_isr_i3c_notif    (void) __attribute__ ((interrupt ("machine")));
static void nonstd_swerv_isr_mbox_error   (void) __attribute__ ((interrupt ("machine")));
static void nonstd_swerv_isr_mbox_notif   (void) __attribute__ ((interrupt ("machine")));

// Could be much more fancy with C preprocessing to pair up the ISR with Vector
// numbers as defined in caliptra_defines.h.... TODO
static void          nonstd_swerv_isr_0   (void) __attribute__ ((interrupt ("machine")));
static void (* const nonstd_swerv_isr_1 ) (void) = nonstd_swerv_isr_aes_error   ;
static void (* const nonstd_swerv_isr_2 ) (void) = nonstd_swerv_isr_aes_notif   ;
static void (* const nonstd_swerv_isr_3 ) (void) = nonstd_swerv_isr_ecc_error   ;
static void (* const nonstd_swerv_isr_4 ) (void) = nonstd_swerv_isr_ecc_notif   ;
static void (* const nonstd_swerv_isr_5 ) (void) = nonstd_swerv_isr_hmac_error  ;
static void (* const nonstd_swerv_isr_6 ) (void) = nonstd_swerv_isr_hmac_notif  ;
static void (* const nonstd_swerv_isr_7 ) (void) = nonstd_swerv_isr_kv_error    ;
static void (* const nonstd_swerv_isr_8 ) (void) = nonstd_swerv_isr_kv_notif    ;
static void (* const nonstd_swerv_isr_9 ) (void) = nonstd_swerv_isr_sha512_error;
static void (* const nonstd_swerv_isr_10) (void) = nonstd_swerv_isr_sha512_notif;
static void (* const nonstd_swerv_isr_11) (void) = nonstd_swerv_isr_sha256_error;
static void (* const nonstd_swerv_isr_12) (void) = nonstd_swerv_isr_sha256_notif;
static void (* const nonstd_swerv_isr_13) (void) = nonstd_swerv_isr_qspi_error  ;
static void (* const nonstd_swerv_isr_14) (void) = nonstd_swerv_isr_qspi_notif  ;
static void (* const nonstd_swerv_isr_15) (void) = nonstd_swerv_isr_uart_error  ;
static void (* const nonstd_swerv_isr_16) (void) = nonstd_swerv_isr_uart_notif  ;
static void (* const nonstd_swerv_isr_17) (void) = nonstd_swerv_isr_i3c_error   ;
static void (* const nonstd_swerv_isr_18) (void) = nonstd_swerv_isr_i3c_notif   ;
static void (* const nonstd_swerv_isr_19) (void) = nonstd_swerv_isr_mbox_error  ;
static void (* const nonstd_swerv_isr_20) (void) = nonstd_swerv_isr_mbox_notif  ;
static void (* const nonstd_swerv_isr_21) (void) = std_rv_nop_machine; // --------.
static void (* const nonstd_swerv_isr_22) (void) = std_rv_nop_machine; //         |
static void (* const nonstd_swerv_isr_23) (void) = std_rv_nop_machine; //         |
static void (* const nonstd_swerv_isr_24) (void) = std_rv_nop_machine; //         |
static void (* const nonstd_swerv_isr_25) (void) = std_rv_nop_machine; //         |
static void (* const nonstd_swerv_isr_26) (void) = std_rv_nop_machine; // Unimplemented ISR
static void (* const nonstd_swerv_isr_27) (void) = std_rv_nop_machine; //         |
static void (* const nonstd_swerv_isr_28) (void) = std_rv_nop_machine; //         |
static void (* const nonstd_swerv_isr_29) (void) = std_rv_nop_machine; //         |
static void (* const nonstd_swerv_isr_30) (void) = std_rv_nop_machine; //         |
static void (* const nonstd_swerv_isr_31) (void) = std_rv_nop_machine; // --------'

// Table defines the SweRV non-standard vectored entries as an array of
// function pointers.
// The entries in this table are entered depending on the Ext. Interrupt ID
// E.g., Interrupt ID 2 routes to the ISR defined at offset 2*4 of this table
//       Interrupt ID 0 is (by definition) not assigned, and routes to an empty ISR
// Note that each function pointer (i.e. each entry in the vector table) must
// be 4-byte aligned per the SweRV PRM, and the base address of the table (i.e.
// the value of meivt) must be 1024-byte aligned, also per the PRM
// For support of Fast Interrupt Redirect feature, this should be in DCCM
static void (* __attribute__ ((aligned(4))) nonstd_swerv_isr_vector_table [RV_PIC_TOTAL_INT_PLUS1]) (void) __attribute__ ((aligned(1024),section (".dccm.nonstd_isr.vec_table"))) = {
    nonstd_swerv_isr_0,
    nonstd_swerv_isr_1,
    nonstd_swerv_isr_2,
    nonstd_swerv_isr_3,
    nonstd_swerv_isr_4,
    nonstd_swerv_isr_5,
    nonstd_swerv_isr_6,
    nonstd_swerv_isr_7,
    nonstd_swerv_isr_8,
    nonstd_swerv_isr_9,
    nonstd_swerv_isr_10,
    nonstd_swerv_isr_11,
    nonstd_swerv_isr_12,
    nonstd_swerv_isr_13,
    nonstd_swerv_isr_14,
    nonstd_swerv_isr_15,
    nonstd_swerv_isr_16,
    nonstd_swerv_isr_17,
    nonstd_swerv_isr_18,
    nonstd_swerv_isr_19,
    nonstd_swerv_isr_20,
    nonstd_swerv_isr_21,
    nonstd_swerv_isr_22,
    nonstd_swerv_isr_23,
    nonstd_swerv_isr_24,
    nonstd_swerv_isr_25,
    nonstd_swerv_isr_26,
    nonstd_swerv_isr_27,
    nonstd_swerv_isr_28,
    nonstd_swerv_isr_29,
    nonstd_swerv_isr_30,
    nonstd_swerv_isr_31
};

// Table defines the RV standard vectored entries pointed to by mtvec
// The entries in this table are entered depending on mcause
// I.e. Exceptions and External Interrupts route to entries of this table
// This table is only consulted when MTVEC[1:0] indicates a vectored mode
static void std_rv_isr_vector_table(void) __attribute__ ((naked));

void main(void) {
        int argc=0;
        char *argv[1];

        char unsigned hw_ii = 0;

        volatile char* stdout = (char *)STDOUT;
        char* DCCM = (char *) RV_DCCM_SADR;
        char* ICCM = (char *) RV_ICCM_SADR;
        uint32_t * mbox_error_trig = (uint32_t *) (MBOX_REG_BASE + MBOX_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R);
        uint32_t * mbox_notif_trig = (uint32_t *) (MBOX_REG_BASE + MBOX_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R);

        // Hack to force reset on the irq generator
        // (useful for NMI testing when we restart at PC=0)
        *stdout = 0xfd;

        while (print_data[hw_ii] != 0) {
            *stdout = print_data[hw_ii++];
        }

        // Setup the interrupt CSR configuration
        init_interrupts();

        // Initialize the counter
        intr_count = 0;

        // Hack to release reset on the irq generator
        *stdout = 0xfe;

        // Busy loop
        while (intr_count < 64) {
            // Trigger interrupt manually
            if (intr_count & 0x4) {
                *mbox_notif_trig = MBOX_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_AVAIL_TRIG_MASK;
            } else {
                *mbox_error_trig = 1 << (intr_count & 0x3);
            }
            __asm__ volatile ("wfi"); // "Wait for interrupt"
            // Sleep in between triggers to allow ISR to execute and show idle time in sims
            for (uint16_t slp = 0; slp < 100; slp++) {
                __asm__ volatile ("nop"); // Sleep loop as "nop"
            }
        }

        // Disable interrutps and print count at end
        csr_clr_bits_mstatus(MSTATUS_MIE_BIT_MASK);
        print_reg_to_console("main end - intr_cnt", intr_count);

        return;
}

// FIXME replace this with an actual printf eventually
static void print_reg_to_console(char* msg, uint32_t value) {
    uint8_t ii = 0;
    char digit;
    while (msg[ii] != 0) {
        *stdout = msg[ii++];
    }
    *stdout = ':';
//    for (ii = 31; ii != 255; ii--) {
//        *stdout = ((value >> ii) & 0x1) + 0x30; // Print binary representation bit-by-bit
//                                                // Starting with MSB
//        if ((ii > 0) && ((ii%8) == 0)) {
//            *stdout = '_';
//        }
//    }
    for (ii = 28; ii != 252; ii-=4) {
        digit = ((value >> ii) & 0xf); // Grab a single hex digit
        *stdout = digit + ((digit < 0xa) ? 0x30 : 0x37); // Print hex representation digit-by-digit
                                                         // Starting with MSB
        if ((ii == 16)) {
            *stdout = '_';
        }
    }
    *stdout = '\n';
}

static void init_interrupts(void) {

    volatile uint32_t * const mpiccfg    = (uint32_t*) SWERV_MM_PIC_MPICCFG;
    volatile uint32_t * const meipls     = (uint32_t*) SWERV_MM_PIC_MEIPLS;     //
    volatile uint32_t * const meies      = (uint32_t*) SWERV_MM_PIC_MEIES;      // Treat these
    volatile uint32_t * const meigwctrls = (uint32_t*) SWERV_MM_PIC_MEIGWCTRLS; // as arrays
    volatile uint32_t * const meigwclrs  = (uint32_t*) SWERV_MM_PIC_MEIGWCLRS;  //
    volatile uint32_t * const mbox_reg   = (uint32_t*) MBOX_REG_BASE;
    char* DCCM = (char *) RV_DCCM_SADR;
    uint32_t value;

    /* -- Enable standard RISC-V interrupts (mtvec etc.) -- */

    // MSTATUS (disable mie prior to setting up SweRV PIC
    // Global interrupt disable
    csr_clr_bits_mstatus(MSTATUS_MIE_BIT_MASK);

    // MTVEC
    // Setup the IRQ handler entry point
    // MODE = 1 (Vectored), this needs to point to std_rv_isr_vector_table()
    // For MODE = 0 (Basic), this needs to point to std_rv_isr()
    csr_write_mtvec((uint_xlen_t) std_rv_isr_vector_table | 1);


    /* -- Enable non-standard SweRV interrupts (PIC, meivt etc.) -- */

    // MEIVT - write the nonstd vector table base address
    __asm__ volatile ("la t0, %0;\n"
                      "csrw %1, t0;\n"
                      : /* output: none */
                      : "i" ((uintptr_t) &nonstd_swerv_isr_vector_table), "i" (SWERV_CSR_MEIVT)  /* input : immediate  */
                      : "t0"/* clobbers: t0 */);

    // MPICCFG
    *mpiccfg = 0x0; // 0x0 - Standard compliant priority order: 0=lowest,15=highest
                    // 0x1 - Reverse priority order: 0=highest,15=lowest
    __asm__ volatile ("fence");

    // MEIPT - No interrupts masked
    __asm__ volatile ("csrwi    %0, %1" \
                      : /* output: none */        \
                      : "i" (SWERV_CSR_MEIPT), "i" (0x00)  /* input : immediate  */ \
                      : /* clobbers: none */);

    // MEIPL_S - assign interrupt priorities
    meipls[SWERV_INTR_VEC_AES_ERROR   ] = SWERV_INTR_PRIO_AES_ERROR   ; __asm__ volatile ("fence");
    meipls[SWERV_INTR_VEC_AES_NOTIF   ] = SWERV_INTR_PRIO_AES_NOTIF   ; __asm__ volatile ("fence");
    meipls[SWERV_INTR_VEC_ECC_ERROR   ] = SWERV_INTR_PRIO_ECC_ERROR   ; __asm__ volatile ("fence");
    meipls[SWERV_INTR_VEC_ECC_NOTIF   ] = SWERV_INTR_PRIO_ECC_NOTIF   ; __asm__ volatile ("fence");
    meipls[SWERV_INTR_VEC_HMAC_ERROR  ] = SWERV_INTR_PRIO_HMAC_ERROR  ; __asm__ volatile ("fence");
    meipls[SWERV_INTR_VEC_HMAC_NOTIF  ] = SWERV_INTR_PRIO_HMAC_NOTIF  ; __asm__ volatile ("fence");
    meipls[SWERV_INTR_VEC_KV_ERROR    ] = SWERV_INTR_PRIO_KV_ERROR    ; __asm__ volatile ("fence");
    meipls[SWERV_INTR_VEC_KV_NOTIF    ] = SWERV_INTR_PRIO_KV_NOTIF    ; __asm__ volatile ("fence");
    meipls[SWERV_INTR_VEC_SHA512_ERROR] = SWERV_INTR_PRIO_SHA512_ERROR; __asm__ volatile ("fence");
    meipls[SWERV_INTR_VEC_SHA512_NOTIF] = SWERV_INTR_PRIO_SHA512_NOTIF; __asm__ volatile ("fence");
    meipls[SWERV_INTR_VEC_SHA256_ERROR] = SWERV_INTR_PRIO_SHA256_ERROR; __asm__ volatile ("fence");
    meipls[SWERV_INTR_VEC_SHA256_NOTIF] = SWERV_INTR_PRIO_SHA256_NOTIF; __asm__ volatile ("fence");
    meipls[SWERV_INTR_VEC_QSPI_ERROR  ] = SWERV_INTR_PRIO_QSPI_ERROR  ; __asm__ volatile ("fence");
    meipls[SWERV_INTR_VEC_QSPI_NOTIF  ] = SWERV_INTR_PRIO_QSPI_NOTIF  ; __asm__ volatile ("fence");
    meipls[SWERV_INTR_VEC_UART_ERROR  ] = SWERV_INTR_PRIO_UART_ERROR  ; __asm__ volatile ("fence");
    meipls[SWERV_INTR_VEC_UART_NOTIF  ] = SWERV_INTR_PRIO_UART_NOTIF  ; __asm__ volatile ("fence");
    meipls[SWERV_INTR_VEC_I3C_ERROR   ] = SWERV_INTR_PRIO_I3C_ERROR   ; __asm__ volatile ("fence");
    meipls[SWERV_INTR_VEC_I3C_NOTIF   ] = SWERV_INTR_PRIO_I3C_NOTIF   ; __asm__ volatile ("fence");
    meipls[SWERV_INTR_VEC_MBOX_ERROR  ] = SWERV_INTR_PRIO_MBOX_ERROR  ; __asm__ volatile ("fence");
    meipls[SWERV_INTR_VEC_MBOX_NOTIF  ] = SWERV_INTR_PRIO_MBOX_NOTIF  ; __asm__ volatile ("fence");
    for (uint8_t undef = SWERV_INTR_VEC_MAX_ASSIGNED+1; undef <= RV_PIC_TOTAL_INT; undef++) {
        meipls[undef] = 0; __asm__ volatile ("fence"); // Set to 0 meaning NEVER interrupt
    }

    // MEICIDPL - Initialize the Claim ID priority level to 0
    //            to allow nesting interrupts (Per PRM 6.5.1)
    __asm__ volatile ("csrwi    %0, %1" \
                      : /* output: none */        \
                      : "i" (SWERV_CSR_MEICIDPL), "i" (0x00)  /* input : immediate  */ \
                      : /* clobbers: none */);

    // MEICURPL - Initialize the current priority level to 0
    //            to allow all ext intr to preempt
    __asm__ volatile ("csrwi    %0, %1" \
                      : /* output: none */        \
                      : "i" (SWERV_CSR_MEICURPL), "i" (0x00)  /* input : immediate  */ \
                      : /* clobbers: none */);

    for (uint8_t vec = 1; vec <= RV_PIC_TOTAL_INT; vec++) {
        // MEIGWCTRL_S
        meigwctrls[vec] = SWERV_MEIGWCTRL_ACTIVE_HI_LEVEL;  __asm__ volatile ("fence");

        // MEIGWCLRS - Ensure all pending bits are clear in the gateway
        //             NOTE: Any write value clears the pending bit
        meigwclrs[vec]  = 0; __asm__ volatile ("fence");

        // MEIE_S - Enable implemented interrupt sources
        meies[vec]  = (vec <= SWERV_INTR_VEC_MAX_ASSIGNED); __asm__ volatile ("fence");
    }

    /* -- Re-enable global interrupts -- */

    // Enable Interrupts for each component
    // Mailbox
    mbox_reg[MBOX_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R /sizeof(uint32_t)] = MBOX_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_INTERNAL_EN_MASK |
                                                                         MBOX_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_INV_DEV_EN_MASK  |
                                                                         MBOX_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_CMD_FAIL_EN_MASK |
                                                                         MBOX_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_BAD_FUSE_EN_MASK;
    mbox_reg[MBOX_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R /sizeof(uint32_t)] = MBOX_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_CMD_AVAIL_EN_MASK;
    mbox_reg[MBOX_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R/sizeof(uint32_t)] = MBOX_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_MASK |
                                                                         MBOX_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_MASK;

    // MIE
    // Enable MIE.MEI (External Interrupts)
    // Do not enable Timer or SW Interrupts
    csr_set_bits_mie(MIE_MEI_BIT_MASK);

    // Global interrupt enable
    csr_set_bits_mstatus(MSTATUS_MIE_BIT_MASK);

}

void std_rv_nop_machine(void)  {
    // Nop machine mode interrupt.
}

static void std_rv_isr(void) {
    void (* isr) (void); // Function pointer to source-specific ISR
    *stdout=0xfb; //FIXME
    uint_xlen_t this_cause = csr_read_mcause();
    print_reg_to_console("In:Std ISR\nmcause", this_cause);
    if (this_cause &  MCAUSE_INTERRUPT_BIT_MASK) {
        this_cause &= 0xFF;
        // Known exceptions
        switch (this_cause) {
        case RISCV_INT_MASK_MTI :
            // Timer exception, keep up the one second tick.
            //mtimer_set_raw_time_cmp(MTIMER_SECONDS_TO_CLOCKS(1));
            //timestamp = mtimer_get_raw_time();
            break;
        case RISCV_INT_MASK_MEI :
            // Read MIP register - should have MEIP set
            // Read MEIPX register - should != 0
            //uint32_t * const meipx      = (uint32_t*) SWERV_MM_PIC_MEIPX;      // FIXME
            // External Interrupt, branch to the SweRV handler
            // (TODO) in a loop until all interrupts at current priority level
            // are handled (aka Interrupt Chaining is supported)
            //   * NOTE: incompatible with Fast Redirect
            do {
                // Capture the priority and ID
                __asm__ volatile ("csrwi    %0, 0" \
                                  : /* output: none */        \
                                  : "i" (SWERV_CSR_MEICPCT) /* input : immediate */ \
                                  : /* clobbers: none */);
                // Look up the handler address in MEIHAP
                __asm__ volatile ("csrr    %0, %1"
                                  : "=r" (isr)  /* output : register */
                                  : "i" (SWERV_CSR_MEIHAP) /* input : immediate */
                                  : /* clobbers: none */);
                // Call the ID-specific handler
                isr(); // ISR here is a function pointer indexed into the mtvec table
                    // For Interrupt NESTING support, the handler should:
                    //  * Save meicurpl
                    //  * Read meicidpl
                    //  * Set current Priority in meicurpl
                    //  * enable mstatus.mei
                    //  * Restore meicurpl prev. value
                    //  * disable mstatus.mei
                // Re-read MIP.MEIP
                // Check MIE.MEIE
                // Re-read MEIPX
                // Check MEIES
            } while (0); // FIXME
            break;
        }
    } else {
        switch (this_cause) {
        case RISCV_EXCP_LOAD_ACCESS_FAULT :
            // mscause
            __asm__ volatile ("csrr    %0, 0x7ff"
                              : "=r" (this_cause)  /* output : register */
                              : /* input : none */
                              : /* clobbers: none */);
            print_reg_to_console("mscause",this_cause);
            // mepc
            this_cause = csr_read_mepc();
            print_reg_to_console("mepc",this_cause);
            // mtval
            this_cause = csr_read_mtval();
            print_reg_to_console("mtval",this_cause);
            break;
        }
    }
    *stdout=0xfc; //FIXME
    return;
}

// This vector table (should be) only indexed into when MTVEC.MODE = Vectored
// based on the value of mcause when the trap occurs
// For MTVEC.MODE = Direct, trap events always route straight to the base value
// of MTVEC, which should be pointing at the std_rv_isr() routine above.
static void std_rv_isr_vector_table(void) {
    // see https://five-embeddev.com/baremetal/vectored_interrupts/ for example
    __asm__ volatile (
        ".org  std_rv_isr_vector_table + 0*4;"
        "jal   zero,std_rv_mtvec_exception;"  /* 0  */
        ".org  std_rv_isr_vector_table + 1*4;"
        "jal   zero,std_rv_mtvec_ssi;"  /* 1  */
        ".org  std_rv_isr_vector_table + 3*4;"
        "jal   zero,std_rv_mtvec_msi;"  /* 3  */
        ".org  std_rv_isr_vector_table + 5*4;"
        "jal   zero,std_rv_mtvec_sti;"  /* 5  */
        ".org  std_rv_isr_vector_table + 7*4;"
        "jal   zero,std_rv_mtvec_mti;"  /* 7  */
        ".org  std_rv_isr_vector_table + 9*4;"
        "jal   zero,std_rv_mtvec_sei;"  /* 9  */
        ".org  std_rv_isr_vector_table + 11*4;"
        "jal   zero,std_rv_mtvec_mei;"  /* 11 */
//        #ifndef VECTOR_TABLE_MTVEC_PLATFORM_INTS
//        ".org  std_rv_isr_vector_table + 16*4;"
//        "jal   std_rv_mtvec_platform_irq0;"
//        "jal   std_rv_mtvec_platform_irq1;"
//        "jal   std_rv_mtvec_platform_irq2;"
//        "jal   std_rv_mtvec_platform_irq3;"
//        "jal   std_rv_mtvec_platform_irq4;"
//        "jal   std_rv_mtvec_platform_irq5;"
//        "jal   std_rv_mtvec_platform_irq6;"
//        "jal   std_rv_mtvec_platform_irq7;"
//        "jal   std_rv_mtvec_platform_irq8;"
//        "jal   std_rv_mtvec_platform_irq9;"
//        "jal   std_rv_mtvec_platform_irq10;"
//        "jal   std_rv_mtvec_platform_irq11;"
//        "jal   std_rv_mtvec_platform_irq12;"
//        "jal   std_rv_mtvec_platform_irq13;"
//        "jal   std_rv_mtvec_platform_irq14;"
//        "jal   std_rv_mtvec_platform_irq15;"
//        #endif
        : /* output: none */
        : /* input : immediate */
        : /* clobbers: none */
    );
}

// Exception handler for Standard RISC-V Vectored operation
void std_rv_mtvec_exception(void) {
    *stdout=0xfb; //FIXME
    uint_xlen_t this_cause = csr_read_mcause();
    print_reg_to_console("In:Std Excptn\nmcause", this_cause);
    if (this_cause &  MCAUSE_INTERRUPT_BIT_MASK) {
        print_reg_to_console("Unexpected Intr bit", 0xFFFFFFFF);
    } else {
        switch (this_cause) {
        case RISCV_EXCP_LOAD_ACCESS_FAULT :
            // mscause
            __asm__ volatile ("csrr    %0, 0x7ff"
                              : "=r" (this_cause)  /* output : register */
                              : /* input : none */
                              : /* clobbers: none */);
            print_reg_to_console("mscause",this_cause);
            // mepc
            this_cause = csr_read_mepc();
            print_reg_to_console("mepc",this_cause);
            // mtval
            this_cause = csr_read_mtval();
            print_reg_to_console("mtval",this_cause);
            break;
        case RISCV_EXCP_ILLEGAL_INSTRUCTION :
            // mscause
            __asm__ volatile ("csrr    %0, 0x7ff"
                              : "=r" (this_cause)  /* output : register */
                              : /* input : none */
                              : /* clobbers: none */);
            print_reg_to_console("mscause",this_cause);
            // mepc
            this_cause = csr_read_mepc();
            print_reg_to_console("mepc",this_cause);
            // mtval
            this_cause = csr_read_mtval();
            print_reg_to_console("mtval",this_cause);
            break;
        default :
            // mepc
            this_cause = csr_read_mepc();
            print_reg_to_console("mepc",this_cause);
            break;
        }
    }
    *stdout=0x1; // KILL THE SIMULATION with "ERROR"
    *stdout=0xfc; //FIXME
    return;
}

// Non-Standard Vectored Interrupt Handler (vector 0)
// ISR 0 is, by definition, not implemented and simply returns
static void nonstd_swerv_isr_0 (void) {
    *stdout=0xfb; //FIXME
    const char* const msg = "In:0\n";
    unsigned char hw_ii = 0;
    while (msg[hw_ii] != 0) {
        *stdout = msg[hw_ii++];
    }
    *stdout=0xfc; //FIXME
    return;
}

// These macros are used to insert event-specific functionality into the
// otherwise generic ISR that gets laid down by the parameterized macro "nonstd_swerv_isr"
// Didn't try messing with 'inline', that may work too
#define service_aes_error_intr
#define service_aes_notif_intr
#define service_ecc_error_intr
#define service_ecc_notif_intr
#define service_hmac_error_intr
#define service_hmac_notif_intr
#define service_kv_error_intr
#define service_kv_notif_intr
#define service_sha512_error_intr
#define service_sha512_notif_intr
#define service_sha256_error_intr
#define service_sha256_notif_intr
#define service_qspi_error_intr
#define service_qspi_notif_intr
#define service_uart_error_intr
#define service_uart_notif_intr
#define service_i3c_error_intr
#define service_i3c_notif_intr
#define service_mbox_error_intr                                                                     \
    uint32_t * reg = (uint32_t *) (MBOX_REG_BASE + MBOX_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R);   \
    uint32_t sts = *reg;                                                                            \
    /* Write 1 to Clear the pending interrupt */                                                    \
    if (sts & MBOX_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_INTERNAL_STS_MASK) {               \
        *reg = MBOX_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_INTERNAL_STS_MASK;                \
    }                                                                                               \
    if (sts & MBOX_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_INV_DEV_STS_MASK) {                \
        *reg = MBOX_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_INV_DEV_STS_MASK;                 \
    }                                                                                               \
    if (sts & MBOX_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_CMD_FAIL_STS_MASK) {               \
        *reg = MBOX_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_CMD_FAIL_STS_MASK;                \
    }                                                                                               \
    if (sts & MBOX_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_BAD_FUSE_STS_MASK) {               \
        *reg = MBOX_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_BAD_FUSE_STS_MASK;                \
    }                                                                                               \
    if (sts == 0) {                                                                                 \
        print_reg_to_console("bad mbox_error_intr sts", sts);                                       \
    }

#define service_mbox_notif_intr                                                                     \
    uint32_t * reg = (uint32_t *) (MBOX_REG_BASE + MBOX_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R);   \
    uint32_t sts = *reg;                                                                            \
    /* Write 1 to Clear the pending interrupt */                                                    \
    if (sts & MBOX_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_AVAIL_STS_MASK) {              \
        *reg = MBOX_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_AVAIL_STS_MASK;               \
    }                                                                                               \
    if (sts == 0) {                                                                                 \
        print_reg_to_console("bad mbox_notif_intr sts", sts);                                       \
    }

// Macro used to lay down mostly equivalent ISR for each of the supported
// interrupt sources, with the only unique functionality provided by the service_xxx_intr
// macro
// Using macros instead of calling event-specific functions from inside a single
// generic function reduces the overhead from context switches (which is critical
// in an ISR)
#define stringify(text) #text
#define nonstd_swerv_isr(name) static void nonstd_swerv_isr_##name (void) {                           \
    *stdout=0xfb; /*FIXME*/                                                                           \
    const char* const msg = "In:"stringify(name)"\n";                                                 \
    unsigned char hw_ii = 0;                                                                          \
                                                                                                      \
    /* Print msg before enabling nested interrupts so it                                              \
     * completes printing and is legible                                                              \
     */                                                                                               \
    while (msg[hw_ii] != 0) {                                                                         \
        *stdout = msg[hw_ii++];                                                                       \
    }                                                                                                 \
                                                                                                      \
    /* Save Context to Stack */                                                                       \
    uint32_t meicidpl;                                                                                \
    uint32_t prev_meicurpl;                                                                           \
    uint_xlen_t prev_mepc;                                                                            \
    uint_xlen_t prev_mstatus;                                                                         \
    uint_xlen_t prev_mie;                                                                             \
    __asm__ volatile ("csrr    %0, %1"                                                                \
                      : "=r" (meicidpl)  /* output : register */                                      \
                      : "i" (SWERV_CSR_MEICIDPL) /* input : immediate */                              \
                      : /* clobbers: none */);                                                        \
    __asm__ volatile ("csrr    %0, %1"                                                                \
                      : "=r" (prev_meicurpl)  /* output : register */                                 \
                      : "i" (SWERV_CSR_MEICURPL) /* input : immediate */                              \
                      : /* clobbers: none */);                                                        \
    prev_mepc    = csr_read_mepc();                                                                   \
    prev_mstatus = csr_read_mstatus();                                                                \
    prev_mie     = csr_read_mie();                                                                    \
                                                                                                      \
    /* Set the priority threshold to current priority */                                              \
    __asm__ volatile ("csrw    %0, %1"                                                                \
                      : /* output: none */                                                            \
                      : "i" (SWERV_CSR_MEICURPL), "r" (meicidpl)  /* input : immediate  */            \
                      : /* clobbers: none */);                                                        \
                                                                                                      \
    /* Reenable interrupts (nesting) */                                                               \
    csr_set_bits_mstatus(MSTATUS_MIE_BIT_MASK);                                                       \
                                                                                                      \
    /* Service the interrupt (clear the interrupt source) */                                          \
    intr_count++;                                                                                     \
    print_reg_to_console("cnt_"stringify(name),intr_count);                                           \
    /* Fill in with macro contents, e.g. "service_mbox_error_intr" */                                 \
    service_##name##_intr                                                                             \
                                                                                                      \
    /* Disable interrupts */                                                                          \
    csr_clr_bits_mstatus(MSTATUS_MIE_BIT_MASK);                                                       \
                                                                                                      \
    /* Restore Context from Stack */                                                                  \
    __asm__ volatile ("csrw    %0, %1"                                                                \
                      : /* output: none */                                                            \
                      : "i" (SWERV_CSR_MEICURPL), "r" (prev_meicurpl)  /* input : immediate  */       \
                      : /* clobbers: none */);                                                        \
    csr_write_mepc(prev_mepc);                                                                        \
    csr_set_bits_mstatus(prev_mstatus & (MSTATUS_MPIE_BIT_MASK | MSTATUS_MPP_BIT_MASK));              \
    csr_set_bits_mie(prev_mie & (MIE_MSI_BIT_MASK | MIE_MTI_BIT_MASK | MIE_MEI_BIT_MASK));            \
                                                                                                      \
    /* Done */                                                                                        \
    *stdout=0xfc; /*FIXME */                                                                          \
    return;                                                                                           \
}

////////////////////////////////////////////////////////////////////////////////
// Auto define ISR for each interrupt source using a macro
// Resulting defined functions are, e.g. "nonstd_swerv_isr_aes_error" (for Vector 1)

// Non-Standard Vectored Interrupt Handler (AES Error = Vector 1)
nonstd_swerv_isr(aes_error)
// Non-Standard Vectored Interrupt Handler (AES Notification = vector 2)
nonstd_swerv_isr(aes_notif)
// Non-Standard Vectored Interrupt Handler (ECC Error = vector 3)
nonstd_swerv_isr(ecc_error)
// Non-Standard Vectored Interrupt Handler (ECC Notification = vector 4)
nonstd_swerv_isr(ecc_notif)
// Non-Standard Vectored Interrupt Handler (HMAC Error = vector 5)
nonstd_swerv_isr(hmac_error)
// Non-Standard Vectored Interrupt Handler (HMAC Notification = vector 6)
nonstd_swerv_isr(hmac_notif)
// Non-Standard Vectored Interrupt Handler (KeyVault Error = vector 7)
nonstd_swerv_isr(kv_error)
// Non-Standard Vectored Interrupt Handler (KeyVault Notification = vector 8)
nonstd_swerv_isr(kv_notif)
// Non-Standard Vectored Interrupt Handler (SHA512 Error = vector 9)
nonstd_swerv_isr(sha512_error)
// Non-Standard Vectored Interrupt Handler (SHA512 Notification = vector 10)
nonstd_swerv_isr(sha512_notif)
// Non-Standard Vectored Interrupt Handler (SHA256 Error = vector 11)
nonstd_swerv_isr(sha256_error)
// Non-Standard Vectored Interrupt Handler (SHA256 Notification = vector 12)
nonstd_swerv_isr(sha256_notif)
// Non-Standard Vectored Interrupt Handler (QSPI Error = vector 13)
nonstd_swerv_isr(qspi_error)
// Non-Standard Vectored Interrupt Handler (QSPI Notification = vector 14)
nonstd_swerv_isr(qspi_notif)
// Non-Standard Vectored Interrupt Handler (UART Error = vector 15)
nonstd_swerv_isr(uart_error)
// Non-Standard Vectored Interrupt Handler (UART Notification = vector 16)
nonstd_swerv_isr(uart_notif)
// Non-Standard Vectored Interrupt Handler (I3C Error = vector 17)
nonstd_swerv_isr(i3c_error)
// Non-Standard Vectored Interrupt Handler (I3C Notification = vector 18)
nonstd_swerv_isr(i3c_notif)
// Non-Standard Vectored Interrupt Handler (Mbox Error = vector 19)
nonstd_swerv_isr(mbox_error)
// Non-Standard Vectored Interrupt Handler (Mbox Notification = vector 20)
nonstd_swerv_isr(mbox_notif)

