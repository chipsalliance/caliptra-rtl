#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "riscv-csr.h"
#include "veer-csr.h"
#include "riscv_hw_if.h"
#include <stdint.h>
#include "printf.h"


#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif
volatile uint32_t  intr_count;
volatile caliptra_intr_received_s cptra_intr_rcv = {0};
volatile uint32_t* stdout = (uint32_t*) STDOUT;


#define MAIL_SUCC                          0xff
#define MAIL_FAIL                          0x1
#define MAIL_DCLS                          0xc8

#define DCLS_CMD_RELEASE_ALL               0x0
#define DCLS_CMD_FORCE_ERROR               0x1
#define DCLS_CMD_RELEASE_ERROR             0x2
#define DCLS_CMD_FORCE_DISABLE_DETECTION   0x3
#define DCLS_CMD_RELEASE_DISABLE_DETECTION 0x4

#define SEND_DCLS_MAIL(cmd) *stdout = (((uint32_t)cmd << 8) | MAIL_DCLS)
#define NOP(cyc) for (uint32_t slp = 0; slp < cyc; slp++) __asm__ volatile ("nop");


void main(void) {
    VPRINTF(LOW, "(DCLS TEST) Injecting error\n");
    SEND_DCLS_MAIL(DCLS_CMD_FORCE_ERROR);
    NOP(20);
    SEND_DCLS_MAIL(DCLS_CMD_RELEASE_ERROR);
    NOP(20);

    VPRINTF(LOW, "(DCLS TEST) Injecting error with disabled detection\n");
    SEND_DCLS_MAIL(DCLS_CMD_FORCE_DISABLE_DETECTION);
    NOP(20);
    SEND_DCLS_MAIL(DCLS_CMD_FORCE_ERROR);
    NOP(20);
    SEND_DCLS_MAIL(DCLS_CMD_RELEASE_ALL);
    NOP(20);

    SEND_STDOUT_CTRL(MAIL_SUCC);
}
