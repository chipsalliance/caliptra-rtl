#include "defines.h"
#include <string.h>

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
const char* const print_data = "----------------------------------\nHello World from SweRV EL2 @WDC !!\n----------------------------------\n";

#if MAIN_HAS_NOARGC
MAIN_RETURN_TYPE main(void) {
        int argc=0;
        char *argv[1];
#else
MAIN_RETURN_TYPE main(int argc, char *argv[]) {
#endif

        char unsigned hw_ii = 0;

        //ee_printf("Hello World\n");
        volatile char* stdout = (char *)STDOUT;
        char* DCCM = (char *)(0xf0040000);
        char* ICCM = (char *) 0xee000000;

        __uint32_t dummy = 0xDEADBEEF;
        __uint32_t dummy2 = 0xC001C0DE;

        //memcpy(stdout, &dummy, sizeof(dummy));

        while (print_data[hw_ii] != 0) {
            *stdout = print_data[hw_ii++];
        }

        memcpy(DCCM, &dummy, sizeof(dummy)); // Prints 63DEADBEEF?
        memcpy(&ICCM[0], &dummy, sizeof(dummy));
        memcpy(&ICCM[4], &dummy2, sizeof(dummy2));

        return MAIN_RETURN_VAL;
}
