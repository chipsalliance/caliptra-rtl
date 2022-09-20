#include "caliptra_defines.h"
#include <string.h>
#include "riscv-csr.h"
#include "swerv-csr.h"
#include "riscv-interrupts.h"

#define ITERATIONS 1


/*
Author : Shay Gal-On, EEMBC

This file is part of  EEMBC(R) and CoreMark(TM), which are Copyright (C) 2009
All rights reserved.

EEMBC CoreMark Software is a product of EEMBC and is provided under the terms of the
CoreMark License that is distributed with the official EEMBC COREMARK Software release.
If you received this EEMBC CoreMark Software without the accompanying CoreMark License,
you must discontinue use and download the official release from www.coremark.org.

Also, if you are publicly displaying scores generated from the EEMBC CoreMark software,
make sure that you are in compliance with Run and Reporting rules specified in the accompanying readme.txt file.

EEMBC
4354 Town Center Blvd. Suite 114-200
El Dorado Hills, CA, 95762
*/

//#include "/wd/users/jrahmeh/coremark_v1.0/riscv/coremark.h"

/*
Author : Shay Gal-On, EEMBC

This file is part of  EEMBC(R) and CoreMark(TM), which are Copyright (C) 2009
All rights reserved.

EEMBC CoreMark Software is a product of EEMBC and is provided under the terms of the
CoreMark License that is distributed with the official EEMBC COREMARK Software release.
If you received this EEMBC CoreMark Software without the accompanying CoreMark License,
you must discontinue use and download the official release from www.coremark.org.

Also, if you are publicly displaying scores generated from the EEMBC CoreMark software,
make sure that you are in compliance with Run and Reporting rules specified in the accompanying readme.txt file.

EEMBC
4354 Town Center Blvd. Suite 114-200
El Dorado Hills, CA, 95762
*/
/* Topic: Description
        This file contains  declarations of the various benchmark functions.
*/

/* Configuration: TOTAL_DATA_SIZE
        Define total size for data algorithms will operate on
*/
#ifndef TOTAL_DATA_SIZE
#define TOTAL_DATA_SIZE 2*1000
#endif

#define SEED_ARG 0
#define SEED_FUNC 1
#define SEED_VOLATILE 2

#define MEM_STATIC 0
#define MEM_MALLOC 1
#define MEM_STACK 2

/* File : core_portme.h */

/*
        Author : Shay Gal-On, EEMBC
        Legal : TODO!
*/
/* Topic : Description
        This file contains configuration constants required to execute on different platforms
*/
#ifndef CORE_PORTME_H
#define CORE_PORTME_H
/************************/
/* Data types and settings */
/************************/
/* Configuration : HAS_FLOAT
        Define to 1 if the platform supports floating point.
*/
#ifndef HAS_FLOAT
#define HAS_FLOAT 0
#endif
/* Configuration : HAS_TIME_H
        Define to 1 if platform has the time.h header file,
        and implementation of functions thereof.
*/
#ifndef HAS_TIME_H
#define HAS_TIME_H 0
#endif
/* Configuration : USE_CLOCK
        Define to 1 if platform has the time.h header file,
        and implementation of functions thereof.
*/
#ifndef USE_CLOCK
#define USE_CLOCK 0
#endif
/* Configuration : HAS_STDIO
        Define to 1 if the platform has stdio.h.
*/
#ifndef HAS_STDIO
#define HAS_STDIO 0
#endif
/* Configuration : HAS_PRINTF
        Define to 1 if the platform has stdio.h and implements the printf function.
*/
#ifndef HAS_PRINTF
#define HAS_PRINTF 1
int whisperPrintf(const char* format, ...);
#define ee_printf whisperPrintf
#endif

/* Configuration : CORE_TICKS
        Define type of return from the timing functions.
 */
#include <time.h>
typedef clock_t CORE_TICKS;

/* Definitions : COMPILER_VERSION, COMPILER_FLAGS, MEM_LOCATION
        Initialize these strings per platform
*/
#ifndef COMPILER_VERSION
 #ifdef __GNUC__
 #define COMPILER_VERSION "GCC"__VERSION__
 #else
 #define COMPILER_VERSION "Please put compiler version here (e.g. gcc 4.1)"
 #endif
#endif
#ifndef COMPILER_FLAGS
 #define COMPILER_FLAGS "-O2"
#endif

#ifndef MEM_LOCATION
// #define MEM_LOCATION "STACK"
 #define MEM_LOCATION "STATIC"
#endif

/* Data Types :
        To avoid compiler issues, define the data types that need ot be used for 8b, 16b and 32b in <core_portme.h>.

        *Imprtant* :
        ee_ptr_int needs to be the data type used to hold pointers, otherwise coremark may fail!!!
*/
typedef signed short ee_s16;
typedef unsigned short ee_u16;
typedef signed int ee_s32;
typedef double ee_f32;
typedef unsigned char ee_u8;
typedef unsigned int ee_u32;
typedef ee_u32 ee_ptr_int;
typedef size_t ee_size_t;
/* align_mem :
        This macro is used to align an offset to point to a 32b value. It is used in the Matrix algorithm to initialize the input memory blocks.
*/
#define align_mem(x) (void *)(4 + (((ee_ptr_int)(x) - 1) & ~3))

/* Configuration : SEED_METHOD
        Defines method to get seed values that cannot be computed at compile time.

        Valid values :
        SEED_ARG - from command line.
        SEED_FUNC - from a system function.
        SEED_VOLATILE - from volatile variables.
*/
#ifndef SEED_METHOD
#define SEED_METHOD SEED_VOLATILE
#endif

/* Configuration : MEM_METHOD
        Defines method to get a block of memry.

        Valid values :
        MEM_MALLOC - for platforms that implement malloc and have malloc.h.
        MEM_STATIC - to use a static memory array.
        MEM_STACK - to allocate the data block on the stack (NYI).
*/
#ifndef MEM_METHOD
//#define MEM_METHOD MEM_STACK
#define MEM_METHOD MEM_STATIC
#endif

/* Configuration : MULTITHREAD
        Define for parallel execution

        Valid values :
        1 - only one context (default).
        N>1 - will execute N copies in parallel.

        Note :
        If this flag is defined to more then 1, an implementation for launching parallel contexts must be defined.

        Two sample implementations are provided. Use <USE_PTHREAD> or <USE_FORK> to enable them.

        It is valid to have a different implementation of <core_start_parallel> and <core_end_parallel> in <core_portme.c>,
        to fit a particular architecture.
*/
#ifndef MULTITHREAD
#define MULTITHREAD 1
#define USE_PTHREAD 0
#define USE_FORK 0
#define USE_SOCKET 0
#endif

/* Configuration : MAIN_HAS_NOARGC
        Needed if platform does not support getting arguments to main.

        Valid values :
        0 - argc/argv to main is supported
        1 - argc/argv to main is not supported

        Note :
        This flag only matters if MULTITHREAD has been defined to a value greater then 1.
*/
#ifndef MAIN_HAS_NOARGC
#define MAIN_HAS_NOARGC 1
#endif

/* Configuration : MAIN_HAS_NORETURN
        Needed if platform does not support returning a value from main.

        Valid values :
        0 - main returns an int, and return value will be 0.
        1 - platform does not support returning a value from main
*/
#ifndef MAIN_HAS_NORETURN
#define MAIN_HAS_NORETURN 1
#endif

/* Variable : default_num_contexts
        Not used for this simple port, must cintain the value 1.
*/
extern ee_u32 default_num_contexts;

typedef struct CORE_PORTABLE_S {
        ee_u8   portable_id;
} core_portable;

/* target specific init/fini */
void portable_init(core_portable *p, int *argc, char *argv[]);
void portable_fini(core_portable *p);

#if !defined(PROFILE_RUN) && !defined(PERFORMANCE_RUN) && !defined(VALIDATION_RUN)
#if (TOTAL_DATA_SIZE==1200)
#define PROFILE_RUN 1
#elif (TOTAL_DATA_SIZE==2000)
#define PERFORMANCE_RUN 1
#else
#define VALIDATION_RUN 1
#endif
#endif

#endif /* CORE_PORTME_H */


#if HAS_STDIO
#include <stdio.h>
#endif
#if HAS_PRINTF
#ifndef ee_printf
#define ee_printf printf
#endif
#endif

/* Actual benchmark execution in iterate */
void *iterate(void *pres);

/* Typedef: secs_ret
        For machines that have floating point support, get number of seconds as a double.
        Otherwise an unsigned int.
*/
#if HAS_FLOAT
typedef double secs_ret;
#else
typedef ee_u32 secs_ret;
#endif

#if MAIN_HAS_NORETURN
#define MAIN_RETURN_VAL
#define MAIN_RETURN_TYPE void
#else
#define MAIN_RETURN_VAL 0
#define MAIN_RETURN_TYPE int
#endif

void start_time(void);
void stop_time(void);
CORE_TICKS get_time(void);
secs_ret time_in_secs(CORE_TICKS ticks);

/* Misc useful functions */
ee_u16 crcu8(ee_u8 data, ee_u16 crc);
ee_u16 crc16(ee_s16 newval, ee_u16 crc);
ee_u16 crcu16(ee_u16 newval, ee_u16 crc);
ee_u16 crcu32(ee_u32 newval, ee_u16 crc);
ee_u8 check_data_types();
void *portable_malloc(ee_size_t size);
void portable_free(void *p);
ee_s32 parseval(char *valstring);

#if (MEM_METHOD==MEM_STATIC)
ee_u8 static_memblk[TOTAL_DATA_SIZE];
#endif
char *mem_name[3] = {"Static","Heap","Stack"};
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
// "External Interrupts" are also included here, just because the
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
static void nonstd_swerv_isr_0 (void) __attribute__ ((interrupt ("machine")));
static void nonstd_swerv_isr_1 (void) __attribute__ ((interrupt ("machine")));
static void nonstd_swerv_isr_2 (void) __attribute__ ((interrupt ("machine")));
static void nonstd_swerv_isr_3 (void) __attribute__ ((interrupt ("machine")));
static void nonstd_swerv_isr_4 (void) __attribute__ ((interrupt ("machine")));
static void nonstd_swerv_isr_5 (void) __attribute__ ((interrupt ("machine")));
static void nonstd_swerv_isr_6 (void) __attribute__ ((interrupt ("machine")));
static void nonstd_swerv_isr_7 (void) __attribute__ ((interrupt ("machine")));
static void nonstd_swerv_isr_8 (void) __attribute__ ((interrupt ("machine")));

// Table defines the SweRV non-standard vectored entries as an array of
// function pointers.
// The entries in this table are entered depending on the Ext. Interrupt ID
// E.g., Interrupt ID 2 routes to the ISR defined at offset 2*4 of this table
//       Interrupt ID 0 is (by definition) not assigned, and routes to an empty ISR
// Note that each function pointer (i.e. each entry in the vector table) must
// be 4-byte aligned per the SweRV PRM, and the base address of the table (i.e.
// the value of meivt) must be 1024-byte aligned, also per the PRM
// For support of Fast Interrupt Redirect feature, this should be in DCCM
static void (* __attribute__ ((aligned(4))) nonstd_swerv_isr_vector_table [256]) (void) __attribute__ ((aligned(1024),section (".dccm.nonstd_isr.vec_table"))) = {
    nonstd_swerv_isr_0,
    nonstd_swerv_isr_1,
    nonstd_swerv_isr_2,
    nonstd_swerv_isr_3,
    nonstd_swerv_isr_4,
    nonstd_swerv_isr_5,
    nonstd_swerv_isr_6,
    nonstd_swerv_isr_7,
    nonstd_swerv_isr_8
};

// Table defines the RV standard vectored entries pointed to by mtvec
// The entries in this table are entered depending on mcause
// I.e. Exceptions and External Interrupts route to entries of this table
// This table is only consulted when MTVEC[1:0] indicates a vectored mode
static void std_rv_isr_vector_table(void) __attribute__ ((naked));

#if MAIN_HAS_NOARGC
MAIN_RETURN_TYPE main(void) {
        int argc=0;
        char *argv[1];
#else
MAIN_RETURN_TYPE main(int argc, char *argv[]) {
#endif

        char unsigned hw_ii = 0;

        volatile char* stdout = (char *)STDOUT;
        char* DCCM = (char *) RV_DCCM_SADR;
        char* ICCM = (char *) RV_ICCM_SADR;

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
        do {
            __asm__ volatile ("wfi"); // "Wait for interrupt"
        } while (intr_count < 64);

        // Disable interrutps and print count at end
        csr_clr_bits_mstatus(MSTATUS_MIE_BIT_MASK);
        print_reg_to_console("main end - intr_cnt", intr_count);

        return MAIN_RETURN_VAL;
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
    // arbitrary
    meipls[1]  = 5; __asm__ volatile ("fence");
    meipls[2]  = 6; __asm__ volatile ("fence"); // <---.
    meipls[3]  = 1; __asm__ volatile ("fence"); // <-. |
    meipls[4]  = 3; __asm__ volatile ("fence"); //   | |
    meipls[5]  = 4; __asm__ volatile ("fence"); //  1| |6
    meipls[6]  = 2; __asm__ volatile ("fence"); //   | |
    meipls[7]  = 6; __asm__ volatile ("fence"); // <-|-'
    meipls[8]  = 1; __asm__ volatile ("fence"); // <-'
    meipls[9]  = 0; __asm__ volatile ("fence"); //------.
    meipls[10] = 0; __asm__ volatile ("fence"); //      |
    meipls[11] = 0; __asm__ volatile ("fence"); //      |
    meipls[12] = 0; __asm__ volatile ("fence"); //      |
    meipls[13] = 0; __asm__ volatile ("fence"); //      |
    meipls[14] = 0; __asm__ volatile ("fence"); //      |
    meipls[15] = 0; __asm__ volatile ("fence"); //      |
    meipls[16] = 0; __asm__ volatile ("fence"); //      |
    meipls[17] = 0; __asm__ volatile ("fence"); //      | Set to 0
    meipls[18] = 0; __asm__ volatile ("fence"); //      | meaning
    meipls[19] = 0; __asm__ volatile ("fence"); //      | NEVER
    meipls[20] = 0; __asm__ volatile ("fence"); //      | interrupt
    meipls[21] = 0; __asm__ volatile ("fence"); //      |
    meipls[22] = 0; __asm__ volatile ("fence"); //      |
    meipls[23] = 0; __asm__ volatile ("fence"); //      |
    meipls[24] = 0; __asm__ volatile ("fence"); //      |
    meipls[25] = 0; __asm__ volatile ("fence"); //      |
    meipls[26] = 0; __asm__ volatile ("fence"); //      |
    meipls[27] = 0; __asm__ volatile ("fence"); //      |
    meipls[28] = 0; __asm__ volatile ("fence"); //      |
    meipls[29] = 0; __asm__ volatile ("fence"); //      |
    meipls[30] = 0; __asm__ volatile ("fence"); //      |
    meipls[31] = 0; __asm__ volatile ("fence"); //------'

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

    // MEIGWCTRL_S
    // Configured according to the sim_irq_gen config driven in caliptra_top
    meigwctrls[1]  = SWERV_MEIGWCTRL_ACTIVE_HI_LEVEL;  __asm__ volatile ("fence");
    meigwctrls[2]  = SWERV_MEIGWCTRL_ACTIVE_HI_EDGE;   __asm__ volatile ("fence");
    meigwctrls[3]  = SWERV_MEIGWCTRL_ACTIVE_HI_LEVEL;  __asm__ volatile ("fence");
    meigwctrls[4]  = SWERV_MEIGWCTRL_ACTIVE_HI_EDGE;   __asm__ volatile ("fence");
    meigwctrls[5]  = SWERV_MEIGWCTRL_ACTIVE_LO_LEVEL;  __asm__ volatile ("fence");
    meigwctrls[6]  = SWERV_MEIGWCTRL_ACTIVE_LO_EDGE;   __asm__ volatile ("fence");
    meigwctrls[7]  = SWERV_MEIGWCTRL_ACTIVE_LO_LEVEL;  __asm__ volatile ("fence");
    meigwctrls[8]  = SWERV_MEIGWCTRL_ACTIVE_LO_EDGE;   __asm__ volatile ("fence");
    meigwctrls[9]  = SWERV_MEIGWCTRL_ACTIVE_HI_LEVEL;  __asm__ volatile ("fence");
    meigwctrls[10] = SWERV_MEIGWCTRL_ACTIVE_HI_LEVEL;  __asm__ volatile ("fence");
    meigwctrls[11] = SWERV_MEIGWCTRL_ACTIVE_HI_LEVEL;  __asm__ volatile ("fence");
    meigwctrls[12] = SWERV_MEIGWCTRL_ACTIVE_HI_LEVEL;  __asm__ volatile ("fence");
    meigwctrls[13] = SWERV_MEIGWCTRL_ACTIVE_HI_LEVEL;  __asm__ volatile ("fence");
    meigwctrls[14] = SWERV_MEIGWCTRL_ACTIVE_HI_LEVEL;  __asm__ volatile ("fence");
    meigwctrls[15] = SWERV_MEIGWCTRL_ACTIVE_HI_LEVEL;  __asm__ volatile ("fence");
    meigwctrls[16] = SWERV_MEIGWCTRL_ACTIVE_HI_LEVEL;  __asm__ volatile ("fence");
    meigwctrls[17] = SWERV_MEIGWCTRL_ACTIVE_HI_LEVEL;  __asm__ volatile ("fence");
    meigwctrls[18] = SWERV_MEIGWCTRL_ACTIVE_HI_LEVEL;  __asm__ volatile ("fence");
    meigwctrls[19] = SWERV_MEIGWCTRL_ACTIVE_HI_LEVEL;  __asm__ volatile ("fence");
    meigwctrls[20] = SWERV_MEIGWCTRL_ACTIVE_HI_LEVEL;  __asm__ volatile ("fence");
    meigwctrls[21] = SWERV_MEIGWCTRL_ACTIVE_HI_LEVEL;  __asm__ volatile ("fence");
    meigwctrls[22] = SWERV_MEIGWCTRL_ACTIVE_HI_LEVEL;  __asm__ volatile ("fence");
    meigwctrls[23] = SWERV_MEIGWCTRL_ACTIVE_HI_LEVEL;  __asm__ volatile ("fence");
    meigwctrls[24] = SWERV_MEIGWCTRL_ACTIVE_HI_LEVEL;  __asm__ volatile ("fence");
    meigwctrls[25] = SWERV_MEIGWCTRL_ACTIVE_HI_LEVEL;  __asm__ volatile ("fence");
    meigwctrls[26] = SWERV_MEIGWCTRL_ACTIVE_HI_LEVEL;  __asm__ volatile ("fence");
    meigwctrls[27] = SWERV_MEIGWCTRL_ACTIVE_HI_LEVEL;  __asm__ volatile ("fence");
    meigwctrls[28] = SWERV_MEIGWCTRL_ACTIVE_HI_LEVEL;  __asm__ volatile ("fence");
    meigwctrls[29] = SWERV_MEIGWCTRL_ACTIVE_HI_LEVEL;  __asm__ volatile ("fence");
    meigwctrls[30] = SWERV_MEIGWCTRL_ACTIVE_HI_LEVEL;  __asm__ volatile ("fence");
    meigwctrls[31] = SWERV_MEIGWCTRL_ACTIVE_HI_LEVEL;  __asm__ volatile ("fence");

    // MEIGWCLRS - Ensure all pending bits are clear in the gateway
    //             NOTE: Any write value clears the pending bit
    meigwclrs[1]  = 0; __asm__ volatile ("fence");
    meigwclrs[2]  = 0; __asm__ volatile ("fence");
    meigwclrs[3]  = 0; __asm__ volatile ("fence");
    meigwclrs[4]  = 0; __asm__ volatile ("fence");
    meigwclrs[5]  = 0; __asm__ volatile ("fence");
    meigwclrs[6]  = 0; __asm__ volatile ("fence");
    meigwclrs[7]  = 0; __asm__ volatile ("fence");
    meigwclrs[8]  = 0; __asm__ volatile ("fence");
    meigwclrs[9]  = 0; __asm__ volatile ("fence");
    meigwclrs[10] = 0; __asm__ volatile ("fence");
    meigwclrs[11] = 0; __asm__ volatile ("fence");
    meigwclrs[12] = 0; __asm__ volatile ("fence");
    meigwclrs[13] = 0; __asm__ volatile ("fence");
    meigwclrs[14] = 0; __asm__ volatile ("fence");
    meigwclrs[15] = 0; __asm__ volatile ("fence");
    meigwclrs[16] = 0; __asm__ volatile ("fence");
    meigwclrs[17] = 0; __asm__ volatile ("fence");
    meigwclrs[18] = 0; __asm__ volatile ("fence");
    meigwclrs[19] = 0; __asm__ volatile ("fence");
    meigwclrs[20] = 0; __asm__ volatile ("fence");
    meigwclrs[21] = 0; __asm__ volatile ("fence");
    meigwclrs[22] = 0; __asm__ volatile ("fence");
    meigwclrs[23] = 0; __asm__ volatile ("fence");
    meigwclrs[24] = 0; __asm__ volatile ("fence");
    meigwclrs[25] = 0; __asm__ volatile ("fence");
    meigwclrs[26] = 0; __asm__ volatile ("fence");
    meigwclrs[27] = 0; __asm__ volatile ("fence");
    meigwclrs[28] = 0; __asm__ volatile ("fence");
    meigwclrs[29] = 0; __asm__ volatile ("fence");
    meigwclrs[30] = 0; __asm__ volatile ("fence");
    meigwclrs[31] = 0; __asm__ volatile ("fence");

    // MEIE_S - Enable 8 interrupt sources
    meies[1]  = 1; __asm__ volatile ("fence");
    meies[2]  = 1; __asm__ volatile ("fence");
    meies[3]  = 1; __asm__ volatile ("fence");
    meies[4]  = 1; __asm__ volatile ("fence");
    meies[5]  = 1; __asm__ volatile ("fence");
    meies[6]  = 1; __asm__ volatile ("fence");
    meies[7]  = 1; __asm__ volatile ("fence");
    meies[8]  = 1; __asm__ volatile ("fence");
    meies[9]  = 0; __asm__ volatile ("fence");
    meies[10] = 0; __asm__ volatile ("fence");
    meies[11] = 0; __asm__ volatile ("fence");
    meies[12] = 0; __asm__ volatile ("fence");
    meies[13] = 0; __asm__ volatile ("fence");
    meies[14] = 0; __asm__ volatile ("fence");
    meies[15] = 0; __asm__ volatile ("fence");
    meies[16] = 0; __asm__ volatile ("fence");
    meies[17] = 0; __asm__ volatile ("fence");
    meies[18] = 0; __asm__ volatile ("fence");
    meies[19] = 0; __asm__ volatile ("fence");
    meies[20] = 0; __asm__ volatile ("fence");
    meies[21] = 0; __asm__ volatile ("fence");
    meies[22] = 0; __asm__ volatile ("fence");
    meies[23] = 0; __asm__ volatile ("fence");
    meies[24] = 0; __asm__ volatile ("fence");
    meies[25] = 0; __asm__ volatile ("fence");
    meies[26] = 0; __asm__ volatile ("fence");
    meies[27] = 0; __asm__ volatile ("fence");
    meies[28] = 0; __asm__ volatile ("fence");
    meies[29] = 0; __asm__ volatile ("fence");
    meies[30] = 0; __asm__ volatile ("fence");
    meies[31] = 0; __asm__ volatile ("fence");


    /* -- Re-enable global interrupts -- */

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

// Non-Standard Vectored Interrupt Handler (vector 1)
// ISR 1 is an active high, level interrupt at the generator
static void nonstd_swerv_isr_1 (void) {
    *stdout=0xfb; //FIXME
    const char* const msg = "In:1\n";
    unsigned char hw_ii = 0;

    // Print msg before enabling nested interrupts so it
    // completes printing and is legible
    while (msg[hw_ii] != 0) {
        *stdout = msg[hw_ii++];
    }

//    // Capture the priority and ID
//    __asm__ volatile ("csrwi    %0, 0" \
//                      : /* output: none */        \
//                      : "i" (SWERV_CSR_MEICPCT) /* input : immediate */ \
//                      : /* clobbers: none */);

    // Save Context to Stack
    uint32_t meicidpl;
    uint32_t prev_meicurpl;
    uint_xlen_t prev_mepc;
    uint_xlen_t prev_mstatus;
    uint_xlen_t prev_mie;
    __asm__ volatile ("csrr    %0, %1"
                      : "=r" (meicidpl)  /* output : register */
                      : "i" (SWERV_CSR_MEICIDPL) /* input : immediate */
                      : /* clobbers: none */);
    __asm__ volatile ("csrr    %0, %1"
                      : "=r" (prev_meicurpl)  /* output : register */
                      : "i" (SWERV_CSR_MEICURPL) /* input : immediate */
                      : /* clobbers: none */);
    prev_mepc    = csr_read_mepc();
    prev_mstatus = csr_read_mstatus();
    prev_mie     = csr_read_mie();

    // Set the priority threshold to current priority
    __asm__ volatile ("csrw    %0, %1" \
                      : /* output: none */        \
                      : "i" (SWERV_CSR_MEICURPL), "r" (meicidpl)  /* input : immediate  */ \
                      : /* clobbers: none */);

    // Reenable interrupts (nesting)
    csr_set_bits_mstatus(MSTATUS_MIE_BIT_MASK);

    // Service the interrupt (here, just increment counter)
    intr_count++;
    print_reg_to_console("cnt1",intr_count);

    // Clear the Interrupt Source
    *stdout = 0x80;

    // Disable interrupts
    csr_clr_bits_mstatus(MSTATUS_MIE_BIT_MASK);

    // Restore Context from Stack
    __asm__ volatile ("csrw    %0, %1" \
                      : /* output: none */        \
                      : "i" (SWERV_CSR_MEICURPL), "r" (prev_meicurpl)  /* input : immediate  */ \
                      : /* clobbers: none */);
    csr_write_mepc(prev_mepc);
    csr_set_bits_mstatus(prev_mstatus & (MSTATUS_MPIE_BIT_MASK | MSTATUS_MPP_BIT_MASK));
    csr_set_bits_mie(prev_mie & (MIE_MSI_BIT_MASK | MIE_MTI_BIT_MASK | MIE_MEI_BIT_MASK));

    // Done
    *stdout=0xfc; //FIXME
    return;
}

// Non-Standard Vectored Interrupt Handler (vector 2)
// ISR 2 is an active high, pulse interrupt at the generator
static void nonstd_swerv_isr_2 (void) {
    *stdout=0xfb; //FIXME
    volatile uint32_t * const meigwclrs  = (uint32_t*) SWERV_MM_PIC_MEIGWCLR(2);
    const char* const msg = "In:2\n";
    unsigned char hw_ii = 0;

    // Print msg before enabling nested interrupts so it
    // completes printing and is legible
    while (msg[hw_ii] != 0) {
        *stdout = msg[hw_ii++];
    }

    // Capture the priority and ID
//    __asm__ volatile ("csrwi    %0, 0" \
//                      : /* output: none */        \
//                      : "i" (SWERV_CSR_MEICPCT) /* input : immediate */ \
//                      : /* clobbers: none */);

    // Save Context to Stack
    uint32_t meicidpl;
    uint32_t prev_meicurpl;
    uint_xlen_t prev_mepc;
    uint_xlen_t prev_mstatus;
    uint_xlen_t prev_mie;
    __asm__ volatile ("csrr    %0, %1"
                      : "=r" (meicidpl)  /* output : register */
                      : "i" (SWERV_CSR_MEICIDPL) /* input : immediate */
                      : /* clobbers: none */);
    __asm__ volatile ("csrr    %0, %1"
                      : "=r" (prev_meicurpl)  /* output : register */
                      : "i" (SWERV_CSR_MEICURPL) /* input : immediate */
                      : /* clobbers: none */);
    prev_mepc    = csr_read_mepc();
    prev_mstatus = csr_read_mstatus();
    prev_mie     = csr_read_mie();

    // Set the priority threshold to current priority
    __asm__ volatile ("csrw    %0, %1" \
                      : /* output: none */        \
                      : "i" (SWERV_CSR_MEICURPL), "r" (meicidpl)  /* input : immediate  */ \
                      : /* clobbers: none */);

    // Reenable interrupts (nesting)
    csr_set_bits_mstatus(MSTATUS_MIE_BIT_MASK);

    // Service the interrupt (here, just increment counter)
    intr_count++;
    print_reg_to_console("cnt2",intr_count);

    // Clear the Interrupt Source (i.e. Gateway)
    *stdout = 0x81;
    *meigwclrs = 0x0; __asm__ volatile ("fence");

    // Disable interrupts
    csr_clr_bits_mstatus(MSTATUS_MIE_BIT_MASK);

    // Restore Context from Stack
    __asm__ volatile ("csrw    %0, %1" \
                      : /* output: none */        \
                      : "i" (SWERV_CSR_MEICURPL), "r" (prev_meicurpl)  /* input : immediate  */ \
                      : /* clobbers: none */);
    csr_write_mepc(prev_mepc);
    csr_set_bits_mstatus(prev_mstatus & (MSTATUS_MPIE_BIT_MASK | MSTATUS_MPP_BIT_MASK));
    csr_set_bits_mie(prev_mie & (MIE_MSI_BIT_MASK | MIE_MTI_BIT_MASK | MIE_MEI_BIT_MASK));

    // Done
    *stdout=0xfc; //FIXME
    return;
}

// Non-Standard Vectored Interrupt Handler (vector 3)
// ISR 3 is an active high, level interrupt at the generator
static void nonstd_swerv_isr_3 (void) {
    *stdout=0xfb; //FIXME
    const char* const msg = "In:3\n";
    unsigned char hw_ii = 0;

    // Print msg before enabling nested interrupts so it
    // completes printing and is legible
    while (msg[hw_ii] != 0) {
        *stdout = msg[hw_ii++];
    }

    // Capture the priority and ID
//    __asm__ volatile ("csrwi    %0, 0" \
//                      : /* output: none */        \
//                      : "i" (SWERV_CSR_MEICPCT) /* input : immediate */ \
//                      : /* clobbers: none */);

    // Save Context to Stack
    uint32_t meicidpl;
    uint32_t prev_meicurpl;
    uint_xlen_t prev_mepc;
    uint_xlen_t prev_mstatus;
    uint_xlen_t prev_mie;
    __asm__ volatile ("csrr    %0, %1"
                      : "=r" (meicidpl)  /* output : register */
                      : "i" (SWERV_CSR_MEICIDPL) /* input : immediate */
                      : /* clobbers: none */);
    __asm__ volatile ("csrr    %0, %1"
                      : "=r" (prev_meicurpl)  /* output : register */
                      : "i" (SWERV_CSR_MEICURPL) /* input : immediate */
                      : /* clobbers: none */);
    prev_mepc    = csr_read_mepc();
    prev_mstatus = csr_read_mstatus();
    prev_mie     = csr_read_mie();

    // Set the priority threshold to current priority
    __asm__ volatile ("csrw    %0, %1" \
                      : /* output: none */        \
                      : "i" (SWERV_CSR_MEICURPL), "r" (meicidpl)  /* input : immediate  */ \
                      : /* clobbers: none */);

    // Reenable interrupts (nesting)
    csr_set_bits_mstatus(MSTATUS_MIE_BIT_MASK);

    // Service the interrupt (here, just increment counter)
    intr_count++;
    print_reg_to_console("cnt3",intr_count);

    // Clear the Interrupt Source
    *stdout = 0x82;

    // Disable interrupts
    csr_clr_bits_mstatus(MSTATUS_MIE_BIT_MASK);

    // Restore Context from Stack
    __asm__ volatile ("csrw    %0, %1" \
                      : /* output: none */        \
                      : "i" (SWERV_CSR_MEICURPL), "r" (prev_meicurpl)  /* input : immediate  */ \
                      : /* clobbers: none */);
    csr_write_mepc(prev_mepc);
    csr_set_bits_mstatus(prev_mstatus & (MSTATUS_MPIE_BIT_MASK | MSTATUS_MPP_BIT_MASK));
    csr_set_bits_mie(prev_mie & (MIE_MSI_BIT_MASK | MIE_MTI_BIT_MASK | MIE_MEI_BIT_MASK));

    // Done
    *stdout=0xfc; //FIXME
    return;
}

// Non-Standard Vectored Interrupt Handler (vector 4)
// ISR 4 is an active high, pulse interrupt at the generator
static void nonstd_swerv_isr_4 (void) {
    *stdout=0xfb; //FIXME
    volatile uint32_t * const meigwclrs  = (uint32_t*) SWERV_MM_PIC_MEIGWCLR(4);
    const char* const msg = "In:4\n";
    unsigned char hw_ii = 0;

    // Print msg before enabling nested interrupts so it
    // completes printing and is legible
    while (msg[hw_ii] != 0) {
        *stdout = msg[hw_ii++];
    }

    // Capture the priority and ID
//    __asm__ volatile ("csrwi    %0, 0" \
//                      : /* output: none */        \
//                      : "i" (SWERV_CSR_MEICPCT) /* input : immediate */ \
//                      : /* clobbers: none */);

    // Save Context to Stack
    uint32_t meicidpl;
    uint32_t prev_meicurpl;
    uint_xlen_t prev_mepc;
    uint_xlen_t prev_mstatus;
    uint_xlen_t prev_mie;
    __asm__ volatile ("csrr    %0, %1"
                      : "=r" (meicidpl)  /* output : register */
                      : "i" (SWERV_CSR_MEICIDPL) /* input : immediate */
                      : /* clobbers: none */);
    __asm__ volatile ("csrr    %0, %1"
                      : "=r" (prev_meicurpl)  /* output : register */
                      : "i" (SWERV_CSR_MEICURPL) /* input : immediate */
                      : /* clobbers: none */);
    prev_mepc    = csr_read_mepc();
    prev_mstatus = csr_read_mstatus();
    prev_mie     = csr_read_mie();

    // Set the priority threshold to current priority
    __asm__ volatile ("csrw    %0, %1" \
                      : /* output: none */        \
                      : "i" (SWERV_CSR_MEICURPL), "r" (meicidpl)  /* input : immediate  */ \
                      : /* clobbers: none */);

    // Reenable interrupts (nesting)
    csr_set_bits_mstatus(MSTATUS_MIE_BIT_MASK);

    // Service the interrupt (here, just increment counter)
    intr_count++;
    print_reg_to_console("cnt4",intr_count);

    // Clear the Interrupt Source (i.e. Gateway)
    *stdout = 0x83;
    *meigwclrs = 0x0; __asm__ volatile ("fence");

    // Disable interrupts
    csr_clr_bits_mstatus(MSTATUS_MIE_BIT_MASK);

    // Restore Context from Stack
    __asm__ volatile ("csrw    %0, %1" \
                      : /* output: none */        \
                      : "i" (SWERV_CSR_MEICURPL), "r" (prev_meicurpl)  /* input : immediate  */ \
                      : /* clobbers: none */);
    csr_write_mepc(prev_mepc);
    csr_set_bits_mstatus(prev_mstatus & (MSTATUS_MPIE_BIT_MASK | MSTATUS_MPP_BIT_MASK));
    csr_set_bits_mie(prev_mie & (MIE_MSI_BIT_MASK | MIE_MTI_BIT_MASK | MIE_MEI_BIT_MASK));

    // Done
    *stdout=0xfc; //FIXME
    return;
}

// Non-Standard Vectored Interrupt Handler (vector 5)
// ISR 5 is an active low, level interrupt at the generator
static void nonstd_swerv_isr_5 (void) {
    *stdout=0xfb; //FIXME
    const char* const msg = "In:5\n";
    unsigned char hw_ii = 0;

    // Print msg before enabling nested interrupts so it
    // completes printing and is legible
    while (msg[hw_ii] != 0) {
        *stdout = msg[hw_ii++];
    }

    // Capture the priority and ID
//    __asm__ volatile ("csrwi    %0, 0" \
//                      : /* output: none */        \
//                      : "i" (SWERV_CSR_MEICPCT) /* input : immediate */ \
//                      : /* clobbers: none */);

    // Save Context to Stack
    uint32_t meicidpl;
    uint32_t prev_meicurpl;
    uint_xlen_t prev_mepc;
    uint_xlen_t prev_mstatus;
    uint_xlen_t prev_mie;
    __asm__ volatile ("csrr    %0, %1"
                      : "=r" (meicidpl)  /* output : register */
                      : "i" (SWERV_CSR_MEICIDPL) /* input : immediate */
                      : /* clobbers: none */);
    __asm__ volatile ("csrr    %0, %1"
                      : "=r" (prev_meicurpl)  /* output : register */
                      : "i" (SWERV_CSR_MEICURPL) /* input : immediate */
                      : /* clobbers: none */);
    prev_mepc    = csr_read_mepc();
    prev_mstatus = csr_read_mstatus();
    prev_mie     = csr_read_mie();

    // Set the priority threshold to current priority
    __asm__ volatile ("csrw    %0, %1" \
                      : /* output: none */        \
                      : "i" (SWERV_CSR_MEICURPL), "r" (meicidpl)  /* input : immediate  */ \
                      : /* clobbers: none */);

    // Reenable interrupts (nesting)
    csr_set_bits_mstatus(MSTATUS_MIE_BIT_MASK);

    // Service the interrupt (here, just increment counter)
    intr_count++;
    print_reg_to_console("cnt5",intr_count);

    // Clear the Interrupt Source
    *stdout = 0x84;

    // Disable interrupts
    csr_clr_bits_mstatus(MSTATUS_MIE_BIT_MASK);

    // Restore Context from Stack
    __asm__ volatile ("csrw    %0, %1" \
                      : /* output: none */        \
                      : "i" (SWERV_CSR_MEICURPL), "r" (prev_meicurpl)  /* input : immediate  */ \
                      : /* clobbers: none */);
    csr_write_mepc(prev_mepc);
    csr_set_bits_mstatus(prev_mstatus & (MSTATUS_MPIE_BIT_MASK | MSTATUS_MPP_BIT_MASK));
    csr_set_bits_mie(prev_mie & (MIE_MSI_BIT_MASK | MIE_MTI_BIT_MASK | MIE_MEI_BIT_MASK));

    // Done
    *stdout=0xfc; //FIXME
    return;
}

// Non-Standard Vectored Interrupt Handler (vector 6)
// ISR 6 is an active low, pulse interrupt at the generator
static void nonstd_swerv_isr_6 (void) {
    *stdout=0xfb; //FIXME
    volatile uint32_t * const meigwclrs  = (uint32_t*) SWERV_MM_PIC_MEIGWCLR(6);
    const char* const msg = "In:6\n";
    unsigned char hw_ii = 0;

    // Print msg before enabling nested interrupts so it
    // completes printing and is legible
    while (msg[hw_ii] != 0) {
        *stdout = msg[hw_ii++];
    }

    // Capture the priority and ID
//    __asm__ volatile ("csrwi    %0, 0" \
//                      : /* output: none */        \
//                      : "i" (SWERV_CSR_MEICPCT) /* input : immediate */ \
//                      : /* clobbers: none */);

    // Save Context to Stack
    uint32_t meicidpl;
    uint32_t prev_meicurpl;
    uint_xlen_t prev_mepc;
    uint_xlen_t prev_mstatus;
    uint_xlen_t prev_mie;
    __asm__ volatile ("csrr    %0, %1"
                      : "=r" (meicidpl)  /* output : register */
                      : "i" (SWERV_CSR_MEICIDPL) /* input : immediate */
                      : /* clobbers: none */);
    __asm__ volatile ("csrr    %0, %1"
                      : "=r" (prev_meicurpl)  /* output : register */
                      : "i" (SWERV_CSR_MEICURPL) /* input : immediate */
                      : /* clobbers: none */);
    prev_mepc    = csr_read_mepc();
    prev_mstatus = csr_read_mstatus();
    prev_mie     = csr_read_mie();

    // Set the priority threshold to current priority
    __asm__ volatile ("csrw    %0, %1" \
                      : /* output: none */        \
                      : "i" (SWERV_CSR_MEICURPL), "r" (meicidpl)  /* input : immediate  */ \
                      : /* clobbers: none */);

    // Reenable interrupts (nesting)
    csr_set_bits_mstatus(MSTATUS_MIE_BIT_MASK);

    // Service the interrupt (here, just increment counter)
    intr_count++;
    print_reg_to_console("cnt6",intr_count);

    // Clear the Interrupt Source (i.e. Gateway)
    *stdout = 0x85;
    *meigwclrs = 0x0; __asm__ volatile ("fence");

    // Disable interrupts
    csr_clr_bits_mstatus(MSTATUS_MIE_BIT_MASK);

    // Restore Context from Stack
    __asm__ volatile ("csrw    %0, %1" \
                      : /* output: none */        \
                      : "i" (SWERV_CSR_MEICURPL), "r" (prev_meicurpl)  /* input : immediate  */ \
                      : /* clobbers: none */);
    csr_write_mepc(prev_mepc);
    csr_set_bits_mstatus(prev_mstatus & (MSTATUS_MPIE_BIT_MASK | MSTATUS_MPP_BIT_MASK));
    csr_set_bits_mie(prev_mie & (MIE_MSI_BIT_MASK | MIE_MTI_BIT_MASK | MIE_MEI_BIT_MASK));

    // Done
    *stdout=0xfc; //FIXME
    return;
}

// Non-Standard Vectored Interrupt Handler (vector 7)
// ISR 7 is an active low, level interrupt at the generator
static void nonstd_swerv_isr_7 (void) {
    *stdout=0xfb; //FIXME
    const char* const msg = "In:7\n";
    unsigned char hw_ii = 0;

    // Print msg before enabling nested interrupts so it
    // completes printing and is legible
    while (msg[hw_ii] != 0) {
        *stdout = msg[hw_ii++];
    }

    // Capture the priority and ID
//    __asm__ volatile ("csrwi    %0, 0" \
//                      : /* output: none */        \
//                      : "i" (SWERV_CSR_MEICPCT) /* input : immediate */ \
//                      : /* clobbers: none */);

    // Save Context to Stack
    uint32_t meicidpl;
    uint32_t prev_meicurpl;
    uint_xlen_t prev_mepc;
    uint_xlen_t prev_mstatus;
    uint_xlen_t prev_mie;
    __asm__ volatile ("csrr    %0, %1"
                      : "=r" (meicidpl)  /* output : register */
                      : "i" (SWERV_CSR_MEICIDPL) /* input : immediate */
                      : /* clobbers: none */);
    __asm__ volatile ("csrr    %0, %1"
                      : "=r" (prev_meicurpl)  /* output : register */
                      : "i" (SWERV_CSR_MEICURPL) /* input : immediate */
                      : /* clobbers: none */);
    prev_mepc    = csr_read_mepc();
    prev_mstatus = csr_read_mstatus();
    prev_mie     = csr_read_mie();

    // Set the priority threshold to current priority
    __asm__ volatile ("csrw    %0, %1" \
                      : /* output: none */        \
                      : "i" (SWERV_CSR_MEICURPL), "r" (meicidpl)  /* input : immediate  */ \
                      : /* clobbers: none */);

    // Reenable interrupts (nesting)
    csr_set_bits_mstatus(MSTATUS_MIE_BIT_MASK);

    // Service the interrupt (here, just increment counter)
    intr_count++;
    print_reg_to_console("cnt7",intr_count);

    // Clear the Interrupt Source
    *stdout = 0x86;

    // Disable interrupts
    csr_clr_bits_mstatus(MSTATUS_MIE_BIT_MASK);

    // Restore Context from Stack
    __asm__ volatile ("csrw    %0, %1" \
                      : /* output: none */        \
                      : "i" (SWERV_CSR_MEICURPL), "r" (prev_meicurpl)  /* input : immediate  */ \
                      : /* clobbers: none */);
    csr_write_mepc(prev_mepc);
    csr_set_bits_mstatus(prev_mstatus & (MSTATUS_MPIE_BIT_MASK | MSTATUS_MPP_BIT_MASK));
    csr_set_bits_mie(prev_mie & (MIE_MSI_BIT_MASK | MIE_MTI_BIT_MASK | MIE_MEI_BIT_MASK));

    // Done
    *stdout=0xfc; //FIXME
    return;
}

// Non-Standard Vectored Interrupt Handler (vector 8)
// ISR 8 is an active low, pulse interrupt at the generator
static void nonstd_swerv_isr_8 (void) {
    *stdout=0xfb; //FIXME
    volatile uint32_t * const meigwclrs  = (uint32_t*) SWERV_MM_PIC_MEIGWCLR(8);
    const char* const msg = "In:8\n";
    unsigned char hw_ii = 0;

    // Print msg before enabling nested interrupts so it
    // completes printing and is legible
    while (msg[hw_ii] != 0) {
        *stdout = msg[hw_ii++];
    }

    // Capture the priority and ID
//    __asm__ volatile ("csrwi    %0, 0" \
//                      : /* output: none */        \
//                      : "i" (SWERV_CSR_MEICPCT) /* input : immediate */ \
//                      : /* clobbers: none */);

    // Save Context to Stack
    uint32_t meicidpl;
    uint32_t prev_meicurpl;
    uint_xlen_t prev_mepc;
    uint_xlen_t prev_mstatus;
    uint_xlen_t prev_mie;
    __asm__ volatile ("csrr    %0, %1"
                      : "=r" (meicidpl)  /* output : register */
                      : "i" (SWERV_CSR_MEICIDPL) /* input : immediate */
                      : /* clobbers: none */);
    __asm__ volatile ("csrr    %0, %1"
                      : "=r" (prev_meicurpl)  /* output : register */
                      : "i" (SWERV_CSR_MEICURPL) /* input : immediate */
                      : /* clobbers: none */);
    prev_mepc    = csr_read_mepc();
    prev_mstatus = csr_read_mstatus();
    prev_mie     = csr_read_mie();

    // Set the priority threshold to current priority
    __asm__ volatile ("csrw    %0, %1" \
                      : /* output: none */        \
                      : "i" (SWERV_CSR_MEICURPL), "r" (meicidpl)  /* input : immediate  */ \
                      : /* clobbers: none */);

    // Reenable interrupts (nesting)
    csr_set_bits_mstatus(MSTATUS_MIE_BIT_MASK);

    // Service the interrupt (here, just increment counter)
    intr_count++;
    print_reg_to_console("cnt8",intr_count);

    // Clear the Interrupt Source (i.e. Gateway)
    *stdout = 0x87;
    *meigwclrs = 0x0; __asm__ volatile ("fence");

    // Disable interrupts
    csr_clr_bits_mstatus(MSTATUS_MIE_BIT_MASK);

    // Restore Context from Stack
    __asm__ volatile ("csrw    %0, %1" \
                      : /* output: none */        \
                      : "i" (SWERV_CSR_MEICURPL), "r" (prev_meicurpl)  /* input : immediate  */ \
                      : /* clobbers: none */);
    csr_write_mepc(prev_mepc);
    csr_set_bits_mstatus(prev_mstatus & (MSTATUS_MPIE_BIT_MASK | MSTATUS_MPP_BIT_MASK));
    csr_set_bits_mie(prev_mie & (MIE_MSI_BIT_MASK | MIE_MTI_BIT_MASK | MIE_MEI_BIT_MASK));

    // Done
    *stdout=0xfc; //FIXME
    return;
}
