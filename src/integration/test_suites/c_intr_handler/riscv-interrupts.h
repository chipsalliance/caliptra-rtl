/*
   RISC-V machine interrupts.
   SPDX-License-Identifier: Unlicense

   https://five-embeddev.com/

*/

#ifndef RISCV_INTERRUPTS_H
#define RISCV_INTERRUPTS_H

enum {
    RISCV_INT_POS_MSI = 3,
    RISCV_INT_POS_MTI = 7,
    RISCV_INT_POS_MEI = 11,
    RISCV_INT_POS_SSI = 1,
    RISCV_INT_POS_STI = 5,
    RISCV_INT_POS_SEI = 9,
    RISCV_INT_POS_USI = 0,
    RISCV_INT_POS_UTI = 4,
    RISCV_INT_POS_UEI = 8,
};

enum {
    RISCV_INT_MASK_MSI = (1UL<<RISCV_INT_POS_MSI),
    RISCV_INT_MASK_MTI = (1UL<<RISCV_INT_POS_MTI),
    RISCV_INT_MASK_MEI = (1UL<<RISCV_INT_POS_MEI),
    RISCV_INT_MASK_SSI = (1UL<<RISCV_INT_POS_SSI),
    RISCV_INT_MASK_STI = (1UL<<RISCV_INT_POS_STI),
    RISCV_INT_MASK_SEI = (1UL<<RISCV_INT_POS_SEI),
    RISCV_INT_MASK_USI = (1UL<<RISCV_INT_POS_USI),
    RISCV_INT_MASK_UTI = (1UL<<RISCV_INT_POS_UTI),
    RISCV_INT_MASK_UEI = (1UL<<RISCV_INT_POS_UEI),
};

enum {
    RISCV_EXCP_INSTRUCTION_ADDRESS_MISALIGNED=0,	/* Instruction address misaligned */
    RISCV_EXCP_INSTRUCTION_ACCESS_FAULT=1,	/* Instruction access fault	*/
    RISCV_EXCP_ILLEGAL_INSTRUCTION=2,	/* Illegal instruction */
    RISCV_EXCP_BREAKPOINT=3,	/* Breakpoint */
    RISCV_EXCP_LOAD_ADDRESS_MISALIGNED=4,	/* Load address misaligned */
    RISCV_EXCP_LOAD_ACCESS_FAULT=5,	/* Load access fault */
    RISCV_EXCP_STORE_AMO_ADDRESS_MISALIGNED	=6,	/* Store/AMO address misaligned	 */
    RISCV_EXCP_STORE_AMO_ACCESS_FAULT=7,	/* Store/AMO access fault */
    RISCV_EXCP_ENVIRONMENT_CALL_FROM_U_MODE=8,	/* Environment call from U-mode	*/
    RISCV_EXCP_ENVIRONMENT_CALL_FROM_S_MODE=9,	/* Environment call from S-mode	*/
    RISCV_EXCP_RESERVED10=10,	/* Reserved	*/
    RISCV_EXCP_ENVIRONMENT_CALL_FROM_M_MODE=11,	/* Environment call from M-mode	*/
    RISCV_EXCP_INSTRUCTION_PAGE_FAULT=12,	/* Instruction page fault */
    RISCV_EXCP_LOAD_PAGE_FAULT=13,	/* Load page fault */
    RISCV_EXCP_RESERVED14=14,	/* Reserved	*/
    RISCV_EXCP_STORE_AMO_PAGE_FAULT=15,	/* Store/AMO page fault */
};


#endif /* RISCV_INTERRUPTS_H */
